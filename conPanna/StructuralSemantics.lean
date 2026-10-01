import Expresso.Expresso
import conPanna.Structural

/-!
Theory-indexed pattern and rewrite semantics. Raw model terms remain ordinary
Lean values; semantic matching uses the relation selected by the theory.
-/
namespace framework

universe u v w x y t

variable {T : Type t}

namespace Patterns

class APattMod (theory : T)
    (α : outParam (Type u)) [State α] (P : Type v) where
  semantics : P → α → Prop

instance {theory : T} {α : Type u} [State α]
    [Structural.ModRelation theory α] : APattMod theory α α where
  semantics pattern state := Structural.eqModOf theory pattern state

instance {theory : T} {α : Type u} [State α]
    [Structural.ModRelation theory α] : APattMod theory α (APattBody α) where
  semantics pattern state :=
    Structural.eqModOf theory pattern.term state ∧ pattern.requires

instance {theory : T} {α : Type u} {A : Type v}
    {P : Type w} [State α] [APattMod theory α P] :
    APattMod theory α (A → P) where
  semantics pattern state :=
    ∃ argument, APattMod.semantics theory (pattern argument) state

class PatternMod (theory : T)
    (α : outParam (Type u)) [State α] (P : Type v) where
  semantics : P → α → Prop

instance {theory : T} {α : Type u} {P : Type v}
    [State α] [APattMod theory α P] : PatternMod theory α P where
  semantics := APattMod.semantics theory

instance {theory : T} {α : Type u}
    {P : Type v} {Q : Type w} [State α]
    [PatternMod theory α P] [PatternMod theory α Q] :
    PatternMod theory α (Disjunction P Q) where
  semantics patterns state :=
    PatternMod.semantics theory patterns.left state ∨
    PatternMod.semantics theory patterns.right state

instance {theory : T} {α : Type u} [State α] :
    APattMod theory α (EmptyPattern α) where
  semantics _ _ := False

def SubsumesMod (theory : T)
    {α : Type u} {P : Type v} {Q : Type w}
    [State α] [PatternMod theory α P] [PatternMod theory α Q]
    (source : P) (target : Q) : Prop :=
  ∀ state, PatternMod.semantics theory source state →
    PatternMod.semantics theory target state

notation:50 source " ⊑[" theory "] " target =>
  SubsumesMod theory source target

/-- A disjunction is subsumed when each of its branches is subsumed. -/
theorem disjunction_subsumes_mod
    {theory : T}
    {α : Type u} {P : Type v} {Q : Type w} {R : Type x}
    [State α] [PatternMod theory α P] [PatternMod theory α Q]
    [PatternMod theory α R]
    {left : P} {right : Q} {target : R}
    (hleft : SubsumesMod theory left target)
    (hright : SubsumesMod theory right target) :
    SubsumesMod theory (left ⊔ right) target := by
  intro state source
  cases source with
  | inl source => exact hleft state source
  | inr source => exact hright state source

end Patterns


namespace Rules

open Patterns

/-- Theory-indexed semantics of one atomic rule representation. -/
class RuleMod (theory : T)
    (α : outParam (Type u)) [State α] (R : Type v) where
  semantics : R → α → α → Prop

instance {theory : T} {α : Type u} [State α]
    [Structural.ModRelation theory α] : RuleMod theory α (RuleBody α) where
  semantics rule before after :=
    Structural.eqModOf theory rule.lhs before ∧
    Structural.eqModOf theory rule.rhs after ∧ rule.requires

instance {theory : T} {α : Type u}
    {A : Type v} {R : Type w} [State α] [RuleMod theory α R] :
    RuleMod theory α (A → R) where
  semantics rule before after :=
    ∃ argument, RuleMod.semantics theory (rule argument) before after

/-- Theory-indexed semantics of a finite nondeterministic rule collection. -/
class RulesMod (theory : T)
    (α : outParam (Type u)) [State α] (R : Type v) where
  semantics : R → α → α → Prop

instance {theory : T} {α : Type u} {R : Type v}
    [State α] [RuleMod theory α R] : RulesMod theory α R where
  semantics := RuleMod.semantics theory

instance {theory : T} {α : Type u}
    {R : Type v} {S : Type w} [State α]
    [RulesMod theory α R] [RulesMod theory α S] :
    RulesMod theory α (Disjunction R S) where
  semantics rules before after :=
    RulesMod.semantics theory rules.left before after ∨
    RulesMod.semantics theory rules.right before after

def postImageMod (theory : T)
    {α : Type u} {P : Type v} {R : Type w}
    [State α] [PatternMod theory α P] [RulesMod theory α R]
    (rule : R) (source : P) (after : α) : Prop :=
  ∃ before,
    PatternMod.semantics theory source before ∧
    RulesMod.semantics theory rule before after

/-- Strong narrowing: `post` is exactly the semantic one-step image. -/
def MapsInAndOnto (theory : T)
    {α : Type u} {P : Type v} {Post : Type w} {R : Type x}
    [State α] [PatternMod theory α P] [PatternMod theory α Post]
    [RulesMod theory α R]
    (rule : R) (source : P) (post : Post) : Prop :=
  ∀ after,
    PatternMod.semantics theory post after ↔
      postImageMod theory rule source after

notation:40 rule:41 " ⊢ " source:41 " ↝[" theory "] " post:41 =>
  MapsInAndOnto theory rule source post

/-- Keep constraints on the original assignments; `family` records their factorization. -/
def witnessPost {α : Type u} {A : Type v} {B : Type w}
    (rule : A → RuleBody α) (source : B → APattBody α)
    (family : A → B → Prop) : A → B → APattBody α :=
  fun a b => ⟨(rule a).rhs, family a b ∧ (rule a).requires ∧ (source b).requires⟩

/-- Exact unification lifts to an exact post without any constraint congruence assumption. -/
theorem witnessPost_exact {theory : T} {α : Type u} {A : Type v} {B : Type w}
    [State α] [Structural.ModRelation theory α]
    (equiv : Equivalence (Structural.eqModOf theory (α := α)))
    (rule : A → RuleBody α) (source : B → APattBody α) (family : A → B → Prop)
    (exactness : ∀ a b, (rule a).lhs =[theory] (source b).term ↔ family a b) :
    MapsInAndOnto theory rule source (witnessPost rule source family) := by
  intro after
  constructor
  · rintro ⟨a, b, hrhs, hfamily, hrule, hsource⟩
    exact ⟨(source b).term, ⟨b, equiv.refl _, hsource⟩,
      a, (exactness a b).mpr hfamily, hrhs, hrule⟩
  · rintro ⟨before, ⟨b, hsource, hcond⟩, a, hlhs, hrhs, hrule⟩
    exact ⟨a, b, hrhs, (exactness a b).mp (equiv.trans hlhs (equiv.symm hsource)),
      hrule, hcond⟩

def mapsIntoMod (theory : T)
    {α : Type u} {P : Type v} {Q : Type w} {R : Type x}
    [State α] [PatternMod theory α P] [PatternMod theory α Q]
    [RulesMod theory α R]
    (rule : R) (source : P) (target : Q) : Prop :=
  ∀ before after,
    PatternMod.semantics theory source before →
    RulesMod.semantics theory rule before after →
    PatternMod.semantics theory target after

notation:40 rule:41 " ⊢ " source:41 " ↪[" theory "] " target:41 =>
  mapsIntoMod theory rule source target

theorem mapsInto_of_mapsInAndOnto_of_subsumes_mod
    {theory : T}
    {α : Type u} {P : Type v} {Post : Type w} {Q : Type x}
    {R : Type y} [State α] [PatternMod theory α P]
    [PatternMod theory α Post] [PatternMod theory α Q]
    [RulesMod theory α R]
    {rule : R} {source : P} {post : Post} {target : Q}
    (hnarrow : MapsInAndOnto theory rule source post)
    (hsubsumes : SubsumesMod theory post target) :
    mapsIntoMod theory rule source target := by
  intro before after hsource hrule
  apply hsubsumes after
  exact (hnarrow after).2 ⟨before, hsource, hrule⟩

theorem mapsInto_of_mapsInto_of_subsumes_mod
    {theory : T}
    {α : Type u} {P : Type v} {Post : Type w} {Q : Type x}
    {R : Type y} [State α] [PatternMod theory α P]
    [PatternMod theory α Post] [PatternMod theory α Q]
    [RulesMod theory α R]
    {rule : R} {source : P} {post : Post} {target : Q}
    (hpost : mapsIntoMod theory rule source post)
    (hsubsumes : SubsumesMod theory post target) :
    mapsIntoMod theory rule source target := by
  intro before after hsource hrule
  apply hsubsumes after
  exact hpost before after hsource hrule

theorem mapsInto_via_narrowing_mod
    {theory : T}
    {α : Type u} {P : Type v} {Q : Type w} {R : Type x}
    [state : State α] [sourcePattern : PatternMod theory α P]
    [targetPattern : PatternMod theory α Q]
    [rulesSemantics : RulesMod theory α R]
    {rule : R} {source : P} {target : Q}
    (decomposition :
      ∃ (Post : Type y) (postPattern : PatternMod theory α Post)
          (post : Post),
        @mapsIntoMod T theory α P Post R state sourcePattern postPattern
            rulesSemantics rule source post ∧
        @SubsumesMod T theory α Post Q state postPattern targetPattern
            post target) :
    mapsIntoMod theory rule source target := by
  rcases decomposition with
    ⟨Post, postPattern, post, narrowing, subsumption⟩
  exact @mapsInto_of_mapsInto_of_subsumes_mod T theory α P Post Q R
    state sourcePattern postPattern targetPattern rulesSemantics
    rule source post target narrowing subsumption

end Rules

export Patterns (APattMod PatternMod SubsumesMod disjunction_subsumes_mod)
export Rules (RuleMod RulesMod postImageMod MapsInAndOnto mapsIntoMod
  mapsInto_of_mapsInAndOnto_of_subsumes_mod
  mapsInto_of_mapsInto_of_subsumes_mod
  mapsInto_via_narrowing_mod)

end framework
