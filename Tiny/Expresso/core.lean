/-!
Pure semantics: constructor theories, patterns and conditional transitions.
No imports of the old libraries, registration commands or tactic machinery.
Equations are parameters; supported unification algorithms are a separate concern.
-/
namespace Tiny

universe u v w x y

/-! ## Constructor presentation and generated structural equality -/

structure Signature (Sorts : Type u) where
  Symbol : List Sorts → Sorts → Type v

variable {Sorts : Type u} {sig : Signature.{u, v} Sorts}

mutual
  inductive Tree (sig : Signature.{u, v} Sorts) : Sorts → Type (max u v) where
    | app {ss s} (head : sig.Symbol ss s) (args : Trees sig ss) : Tree sig s
  inductive Trees (sig : Signature.{u, v} Sorts) : List Sorts → Type (max u v) where
    | nil : Trees sig []
    | cons {s ss} (first : Tree sig s) (rest : Trees sig ss) : Trees sig (s :: ss)
end

/-- Instances of the declared equations. For example, all ground instances of
commutativity for a chosen symbol. Different symbols may have different laws. -/
abbrev Theory (sig : Signature.{u, v} Sorts) :=
  {s : Sorts} → Tree sig s → Tree sig s → Prop

mutual
  /-- The LEAST equivalence closed under the declared equations and constructors. -/
  inductive EqMod (laws : Theory sig) :
      {s : Sorts} → Tree sig s → Tree sig s → Prop where
    | refl {s} (a : Tree sig s) : EqMod laws a a
    | symm {s} {a b : Tree sig s} : EqMod laws a b → EqMod laws b a
    | trans {s} {a b c : Tree sig s} :
        EqMod laws a b → EqMod laws b c → EqMod laws a c
    | law {s} {a b : Tree sig s} : laws a b → EqMod laws a b
    | congr {ss s} (head : sig.Symbol ss s) {a b : Trees sig ss} :
        EqsMod laws a b → EqMod laws (.app head a) (.app head b)
  inductive EqsMod (laws : Theory sig) :
      {ss : List Sorts} → Trees sig ss → Trees sig ss → Prop where
    | nil : EqsMod laws .nil .nil
    | cons {s ss} {a b : Tree sig s} {as bs : Trees sig ss} :
        EqMod laws a b → EqsMod laws as bs → EqsMod laws (.cons a as) (.cons b bs)
end

theorem EqMod.equivalence (laws : Theory sig) (s : Sorts) :
    Equivalence (EqMod laws (s := s)) :=
  ⟨EqMod.refl, EqMod.symm, EqMod.trans⟩

/-! ## Faithful interpretation using ordinary user-defined constructors
The two registration equations concern syntax, NOT literal commutativity of
Lean constructors. A generator may supply them later, outside this file.
-/

def Args (Carrier : Sorts → Type w) : List Sorts → Type w
  | [] => PUnit
  | s :: ss => Carrier s × Args Carrier ss

structure Algebra (sig : Signature.{u, v} Sorts) where
  Carrier : Sorts → Type w
  apply : ∀ {ss s}, sig.Symbol ss s → Args Carrier ss → Carrier s

mutual
  def Tree.eval (A : Algebra sig) : {s : Sorts} → Tree sig s → A.Carrier s
    | _, .app head args => A.apply head (args.eval A)
  def Trees.eval (A : Algebra sig) : {ss : List Sorts} → Trees sig ss → Args A.Carrier ss
    | _, .nil => PUnit.unit
    | _, .cons a as => (a.eval A, as.eval A)
end

def Args.quote {Carrier : Sorts → Type w} (quote : ∀ s, Carrier s → Tree sig s) :
    (ss : List Sorts) → Args Carrier ss → Trees sig ss
  | [], _ => .nil
  | s :: ss, (a, as) => .cons (quote s a) (Args.quote quote ss as)

structure Registration (sig : Signature.{u, v} Sorts) extends Algebra.{u, v, w} sig where
  quote : ∀ s, Carrier s → Tree sig s
  eval_quote : ∀ s a, (quote s a).eval toAlgebra = a
  quote_apply : ∀ {ss s} (head : sig.Symbol ss s) (args : Args Carrier ss),
    quote s (apply head args) = .app head (Args.quote quote ss args)

mutual
  /-- Constructor compatibility also gives the other round trip. -/
  theorem Registration.quote_eval (reg : Registration sig) {s : Sorts} (a : Tree sig s) :
      reg.quote s (a.eval reg.toAlgebra) = a :=
    match a with
    | .app head args =>
      (reg.quote_apply head (args.eval reg.toAlgebra)).trans
        (congrArg (Tree.app head) (reg.quote_eval_args args))
  theorem Registration.quote_eval_args (reg : Registration sig) {ss : List Sorts}
      (args : Trees sig ss) : Args.quote reg.quote ss (args.eval reg.toAlgebra) = args :=
    match args with
    | .nil => rfl
    | .cons a as => congr (congrArg Trees.cons (reg.quote_eval a)) (reg.quote_eval_args as)
end

/-- One structural equality on native values; no legacy representation/bridge. -/
def NativeEq (laws : Theory sig) (reg : Registration sig) {s : Sorts}
    (a b : reg.Carrier s) : Prop :=
  EqMod laws (reg.quote s a) (reg.quote s b)

theorem NativeEq.equivalence (laws : Theory sig) (reg : Registration sig) (s : Sorts) :
    Equivalence (NativeEq laws reg (s := s)) :=
  ⟨fun a => .refl (reg.quote s a), fun h => .symm h, fun h k => .trans h k⟩

/-! ## Pattern and rule representations
B is the chosen equality on the state type: NativeEq above, or ordinary Eq.
There is only ONE interpretation interface for each kind of representation.
Conditions remain predicates on the original assignments, not on quotient values.
-/

variable {α : Type u} {B : α → α → Prop}

structure Atom (α : Type u) where
  term : α
  requires : Prop := True

structure RuleBody (α : Type u) where
  lhs : α
  rhs : α
  requires : Prop := True

/-- Shared data for heterogeneous pattern disjunction and rule choice. -/
structure Choice (P : Type v) (Q : Type w) where
  left : P
  right : Q

inductive EmptyPattern where
  | empty

class Pattern (B : α → α → Prop) (P : Type v) where
  holds : P → α → Prop

instance : Pattern B α := ⟨fun term state => B term state⟩
instance : Pattern B (Atom α) := ⟨fun atom state => B atom.term state ∧ atom.requires⟩
instance {A : Type v} {P : Type w} [Pattern B P] : Pattern B (A → P) :=
  ⟨fun pattern state => ∃ a, Pattern.holds B (pattern a) state⟩
instance {P : Type v} {Q : Type w} [Pattern B P] [Pattern B Q] :
    Pattern B (Choice P Q) :=
  ⟨fun choice state => Pattern.holds B choice.left state ∨ Pattern.holds B choice.right state⟩
instance : Pattern B EmptyPattern := ⟨fun _ _ => False⟩

class Rules (B : α → α → Prop) (R : Type v) where
  step : R → α → α → Prop

instance : Rules B (RuleBody α) :=
  ⟨fun rule before after => B rule.lhs before ∧ B rule.rhs after ∧ rule.requires⟩
instance {A : Type v} {R : Type w} [Rules B R] : Rules B (A → R) :=
  ⟨fun rule before after => ∃ a, Rules.step B (rule a) before after⟩
instance {R : Type v} {S : Type w} [Rules B R] [Rules B S] : Rules B (Choice R S) :=
  ⟨fun choice before after => Rules.step B choice.left before after ∨
    Rules.step B choice.right before after⟩

/-! ## Semantic judgments and universal/existential decomposition
These describe ONE-STEP transitions. Choice is nondeterminism, not sequencing.
None of these definitions computes unifiers or post-images.
-/

variable {P : Type v} {Q : Type w} {Post : Type x} {R : Type y}

def Subsumes (B : α → α → Prop) [Pattern B P] [Pattern B Q]
    (source : P) (target : Q) : Prop :=
  ∀ state, Pattern.holds B source state → Pattern.holds B target state

def Overlaps (B : α → α → Prop) [Pattern B P] [Pattern B Q]
    (left : P) (right : Q) : Prop :=
  ∃ state, Pattern.holds B left state ∧ Pattern.holds B right state

def postImage (B : α → α → Prop) [Pattern B P] [Rules B R]
    (rule : R) (source : P) (after : α) : Prop :=
  ∃ before, Pattern.holds B source before ∧ Rules.step B rule before after

def MapsInto (B : α → α → Prop) [Pattern B P] [Pattern B Q] [Rules B R]
    (rule : R) (source : P) (target : Q) : Prop :=
  ∀ before after, Pattern.holds B source before → Rules.step B rule before after →
    Pattern.holds B target after

/-- No missing states: the candidate contains every actual successor.
This is the SAME universal mapping judgment, not a second semantics. -/
abbrev Over (B : α → α → Prop) [Pattern B P] [Pattern B Post] [Rules B R]
    (rule : R) (source : P) (post : Post) : Prop := MapsInto B rule source post

/-- No junk states: every candidate state is an actual successor. -/
def Under (B : α → α → Prop) [Pattern B P] [Pattern B Post] [Rules B R]
    (rule : R) (source : P) (post : Post) : Prop :=
  ∀ after, Pattern.holds B post after → postImage B rule source after

def Exact (B : α → α → Prop) [Pattern B P] [Pattern B Post] [Rules B R]
    (rule : R) (source : P) (post : Post) : Prop :=
  Over B rule source post ∧ Under B rule source post

def Reaches (B : α → α → Prop) [Pattern B P] [Pattern B Q] [Rules B R]
    (rule : R) (source : P) (target : Q) : Prop :=
  ∃ before after, Pattern.holds B source before ∧ Rules.step B rule before after ∧
    Pattern.holds B target after

theorem mapsInto_of_over_subsumes [Pattern B P] [Pattern B Post] [Pattern B Q] [Rules B R]
    {rule : R} {source : P} {post : Post} {target : Q}
    (over : Over B rule source post) (subsumes : Subsumes B post target) :
    MapsInto B rule source target :=
  fun before after hsource hstep => subsumes after (over before after hsource hstep)

theorem reaches_of_under_overlaps [Pattern B P] [Pattern B Post] [Pattern B Q] [Rules B R]
    {rule : R} {source : P} {post : Post} {target : Q}
    (under : Under B rule source post) (overlap : Overlaps B post target) :
    Reaches B rule source target :=
  match overlap with
  | ⟨after, hpost, htarget⟩ =>
    match under after hpost with
    | ⟨before, hsource, hstep⟩ => ⟨before, after, hsource, hstep, htarget⟩

end Tiny
