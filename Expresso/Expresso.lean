import Lean


/-
# Semantic framework

The framework supplies the denotational layer shared by all reasoning
procedures: state types, pattern semantics, and rule semantics. It does not
own equational theories or a particular unification algorithm.
-/
namespace framework

universe u v w x y

-- α is the type of states
class State (α : Type u) : Prop where

/-
## Patterns

All definitions whose primary purpose is to represent or compare patterns live
under this namespace. They are exported from `framework` below to preserve the
compact user-facing names used by existing models.
-/
namespace Patterns

/- ### Data Structure: Atomic Patterns -/
-- P is a type of atomic patterns denoting sets of α-states.
class APatt (α : outParam (Type u)) [State α] (P : Type v) where
  semantics : P → α → Prop -- read "P contains α"

/-- The body returned by a constrained pattern closure. -/
structure APattBody (α : Type u) where
  term : α -- TODO: require \a to be state
  requires : Prop := True -- TODO: rename it to cond

-- case 1: unconstrained ground terms (e.g., f(a,b) : APatt)
instance {α : Type u} [State α] : APatt α α where
  semantics p state := p = state

-- case 2:  constrained ground terms (e.g., ⟨f(a,b), a>b⟩ : APatt)
instance {α : Type u} [State α] : APatt α (APattBody α) where
  semantics p state := p.term = state ∧ p.requires

-- case 3) constrained terms w/ bound variables (e.g., λx.λy.⟨f(x,y), x>y⟩ : APatt)
instance {α : Type u} {A : Type v} {P : Type w}
    [State α] [APatt α P] : APatt α (A → P) where
  semantics p state := ∃ x, APatt.semantics (p x) state

/- ### Data Structure: Composite Patterns (via Disjunction) -/
/-- Patterns are atomic patterns closed under finite disjunction. -/
class Pattern (α : outParam (Type u)) [State α] (P : Type v) where
  semantics : P → α → Prop

/-- A heterogeneous disjunction of two pattern representations. -/
structure Disjunction (P : Type v) (Q : Type w) where
  left : P
  right : Q

infixr:65 " ⊔ " => framework.Patterns.Disjunction.mk

/-- The empty pattern, used when narrowing returns no alternatives. -/
inductive EmptyPattern (α : Type u) where
  | empty : EmptyPattern α

-- case 1: atomic patterns
instance {α : Type u} {P : Type v}
    [State α] [APatt α P] :
    Pattern α P where
  semantics := APatt.semantics

-- case 2: disjuncted patterns
instance {α : Type u} {P : Type v} {Q : Type w}
    [State α] [Pattern α P] [Pattern α Q] :
    Pattern α (Disjunction P Q) where
  semantics patterns state :=
    Pattern.semantics patterns.left state ∨
    Pattern.semantics patterns.right state

-- case 3: empty patterns
instance {α : Type u} [State α] :
    APatt α (EmptyPattern α) where
  semantics _ _ := False

/- ### Derived Notions -/
/-- Semantic inclusion between two possibly different pattern representations. -/
def Subsumes {α : Type u} {P : Type v} {Q : Type w}
    [State α] [Pattern α P] [Pattern α Q]
    (source : P) (target : Q) : Prop :=
  ∀ state, Pattern.semantics source state →
    Pattern.semantics target state

infix:50 " ⊑ " => Subsumes

end Patterns


/-
## Rules

Rule representations and all judgments that fundamentally mention a rule live
under this namespace.
-/
namespace Rules

open Patterns

/- ### Data Structure: Rules -/
/-- The body returned by a constrained rewrite-rule closure. -/
structure RuleBody (α : Type u) where
  lhs : α
  rhs : α
  requires : Prop := True

-- TODO: rename it to just "Rule"
-- Atomic rules and their Lean closures denote binary transition relations.
class AtRule (α : outParam (Type u)) [State α] (R : Type v) where
  semantics : R → α → α → Prop

-- case 1: unquantified ground rules
instance {α : Type u} [State α] :
    AtRule α (RuleBody α) where
  semantics rule before after :=
    rule.lhs = before ∧ rule.rhs = after ∧ rule.requires

-- case 2: quantified rules
instance {α : Type u} {A : Type v} {R : Type w}
    [State α] [AtRule α R] : AtRule α (A → R) where
  semantics rule before after :=
    ∃ argument, AtRule.semantics (rule argument) before after

/- ### Derived Notions -/
/- used for defining narrowsTo -/
def postImage {α : Type u} {P : Type v} {R : Type w}
    [State α] [Pattern α P] [AtRule α R]
    (rule : R) (source : P) (after : α) : Prop :=
  ∃ before,
    Pattern.semantics source before ∧
    AtRule.semantics rule before after

/-- Semantic post-image distributes over finite pattern disjunction. -/
theorem postImage_disjunction
    {α : Type u} {P : Type v} {Q : Type w} {R : Type x}
    [State α] [Pattern α P] [Pattern α Q] [AtRule α R]
    (rule : R) (left : P) (right : Q) (after : α) :
    postImage rule (left ⊔ right) after ↔
      postImage rule left after ∨ postImage rule right after := by
  constructor
  · rintro ⟨before, hleft | hright, hrule⟩
    · exact Or.inl ⟨before, hleft, hrule⟩
    · exact Or.inr ⟨before, hright, hrule⟩
  · rintro (⟨before, hleft, hrule⟩ | ⟨before, hright, hrule⟩)
    · exact ⟨before, Or.inl hleft, hrule⟩
    · exact ⟨before, Or.inr hright, hrule⟩

-- TODO: NarrowsTo -> narrowsTo
/- R ⊢ P ↝ Q iff ∀ q ∈ Q, ∃ p ∈ P, R p q -/
def NarrowsTo {α : Type u} {P : Type v} {Post : Type w} {R : Type x}
    [State α] [Pattern α P] [Pattern α Post] [AtRule α R]
    (rule : R) (source : P) (post : Post) : Prop :=
  ∀ after,
    Pattern.semantics post after ↔ postImage rule source after

notation:40 rule " ⊢ " source " ↝ " post =>
  NarrowsTo rule source post

/- R ⊢ P ↪ Q iff ∀ p,q ∈ α, p ∈ P → R p q → q ∈ Q -/
def mapsInto {α : Type u} {P : Type v} {Q : Type w} {R : Type x}
    [State α] [Pattern α P] [Pattern α Q] [AtRule α R]
    (rule : R) (source : P) (target : Q) : Prop :=
  ∀ before after,
    Pattern.semantics source before →
    AtRule.semantics rule before after →
    Pattern.semantics target after

notation:40 rule " ⊢ " source " ↪ " target =>
  mapsInto rule source target

/- ### Useful Lemmas -/
/-
  rule ⊢ source ↝ post
  post ⊑ target
  ────────────────────
  rule ⊢ source ↪ target
-/
theorem mapsInto_of_narrowsTo_of_subsumes
    {α : Type u} {P : Type v} {Post : Type w} {Q : Type x}
    {R : Type y} [State α] [Pattern α P] [Pattern α Post]
    [Pattern α Q] [AtRule α R]
    {rule : R} {source : P} {post : Post} {target : Q}
    (hnarrow : NarrowsTo rule source post)
    (hsubsumes : Subsumes post target) :
    mapsInto rule source target := by
  intro before after hsource hrule
  apply hsubsumes after
  exact (hnarrow after).2 ⟨before, hsource, hrule⟩

/--
Prove `mapsInto` through an existentially generated post.  The post
representation itself is existential because a heterogeneous disjunction's
concrete Lean type is not known before narrowing.
  (∃ Post, ∃ postPattern, ∃ post)
  rule ⊢ source ↝ post
  post ⊑ target
  ─────────────────────────────
  rule ⊢ source ↪ target
-/
theorem mapsInto_via_narrowing
    {α : Type u} {P : Type v} {Q : Type w} {R : Type x}
    [state : State α] [sourcePattern : Pattern α P]
    [targetPattern : Pattern α Q] [ruleSemantics : AtRule α R]
    {rule : R} {source : P} {target : Q}
    (decomposition :
      ∃ (Post : Type y) (postPattern : Pattern α Post) (post : Post),
        @NarrowsTo α P Post R state sourcePattern postPattern ruleSemantics
            rule source post ∧
        @Subsumes α Post Q state postPattern targetPattern post target) :
    mapsInto rule source target := by
  rcases decomposition with
    ⟨Post, postPattern, post, narrowing, subsumption⟩
  exact @mapsInto_of_narrowsTo_of_subsumes α P Post Q R
    state sourcePattern postPattern targetPattern ruleSemantics
    rule source post target narrowing subsumption

/-- Once the exact post is known, `mapsInto` is precisely subsumption. -/
theorem mapsInto_iff_subsumes_of_narrowsTo
    {α : Type u} {P : Type v} {Post : Type w} {Q : Type x}
    {R : Type y} [State α] [Pattern α P] [Pattern α Post]
    [Pattern α Q] [AtRule α R]
    {rule : R} {source : P} {post : Post} {target : Q}
    (hnarrow : NarrowsTo rule source post) :
    mapsInto rule source target ↔ Subsumes post target := by
  constructor
  · intro hmaps state hpost
    obtain ⟨before, hsource, hrule⟩ := (hnarrow state).1 hpost
    exact hmaps before state hsource hrule
  · exact mapsInto_of_narrowsTo_of_subsumes hnarrow

end Rules

-- Preserve the concise modelling API while keeping declaration ownership
-- visible in the namespace tree.
export Patterns (APatt APattBody Pattern Disjunction EmptyPattern Subsumes)
export Rules (RuleBody AtRule postImage NarrowsTo mapsInto
  mapsInto_of_narrowsTo_of_subsumes mapsInto_via_narrowing
  mapsInto_iff_subsumes_of_narrowsTo)

end framework




