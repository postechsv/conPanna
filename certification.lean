import conPanna.Structural
import examples.bakery

/-!
# A model-independent proof system for unification certification

Part 1: semantic interfaces, inference rules, and adequacy, parameterized by
the user's types and Structural.Theory. No Bakery declarations occur here.
Part 2: once-per-model registrations for the actual imported Bakery definitions.
Part 3: inline certification proofs using Bakery's Conf.

The proof system uses Lean and Structural.EqMod; no Mathlib facts or tactics.
The example import brings Bakery's existing dependencies transitively.
Generic completeness proofs and two registration proofs remain admitted.

Inspiration: ACU-certification.pdf, Figure 1 and Lemma 5.5: transformations of
disjunctions of conjunctions preserve the entire solution set. Our adequacy
theorem composes such transformations. The paper's Theorem 5.9 assumes a
complete unsorted unifier; the ACU rules here address that additional layer.
-/

namespace Certification

open Structural
universe u

/-! ## Part 1. General interfaces and proof system -/

/--
A faithful bag interpretation of one user-defined ACU sort.
This is model-wide evidence, not the answer to a unification problem.

Structural registration supplies the four law witnesses. The interpretation
additionally justifies freeness: EqMod is EXACTLY permutation of encoded atoms,
and every finite bag is representable. Cancellation and complete splitting
cannot be inferred from ACU laws alone in an arbitrary algebra.

Atoms may themselves encode other structural theories (for example by using
quotient-valued atoms). No inductive term grammar is fixed by this interface.
-/
structure ACUView (B : Structural.Theory.{u}) {α : Type u}
    (op : α → α → α) (zero : α) where
  Atom : Type u
  atom : Atom → α
  encode : α → List Atom
  decode : List Atom → α
  encode_zero : encode zero = []
  encode_op : ∀ a b, encode (op a b) = encode a ++ encode b
  encode_atom : ∀ a, encode (atom a) = [a]
  encode_decode : ∀ xs, encode (decode xs) = xs
  reflects : ∀ a b, (a =[B] b) ↔ (encode a).Perm (encode b)
  symbol : HasSymbol B op
  associative : HasAssoc B op
  commutative : HasComm B op
  identity : HasIdentity B op zero

/-- Heterogeneous fields of a constructor, without an arity limit. -/
inductive Fields : Type (u + 1) where
  | unit
  | field (α : Type u)
  | product (left right : Fields)

def Fields.Values : Fields.{u} → Type u
  | .unit => PUnit
  | .field α => α
  | .product left right => left.Values × right.Values

/-- Componentwise EqMod, using the appropriate type for every field. -/
def Fields.Equal (B : Structural.Theory.{u}) :
    (fields : Fields.{u}) → fields.Values → fields.Values → Prop
  | .unit, _, _ => True
  | .field _, a, b => a =[B] b
  | .product left right, a, b =>
      left.Equal B a.1 b.1 ∧ right.Equal B a.2 b.2

/--
Faithful decomposition of a user-defined free constructor.
The signature registration must justify this for all arguments, once.
It is not assumed for a symbol carrying C, AC, or ACU equations.
-/
structure ConstructorView (B : Structural.Theory.{u})
    (fields : Fields.{u}) (α : Type u) where
  build : fields.Values → α
  reflects : ∀ a b, (build a =[B] build b) ↔ fields.Equal B a b

/-- General ACU refinement: four fresh pieces give one complete unifier. -/
theorem acu_split_iff {B : Structural.Theory.{u}} {α : Type u}
    {op : α → α → α} {zero : α}
    (view : ACUView B op zero) (a b c d : α) :
    op a b =[B] op c d ↔
      ∃ p q r s : α,
        a =[B] op p q ∧ b =[B] op r s ∧
        c =[B] op p r ∧ d =[B] op q s := by
  letI := view.symbol
  letI := view.associative
  letI := view.commutative
  constructor
  · -- General metatheorem TODO: partition equal bag sums into four pieces;
    -- use view.decode to realize them and view.reflects to return to EqMod.
    sorry
  · intro h
    obtain ⟨p, q, r, s, ha, hb, hc, hd⟩ := h
    have exchange :
        op (op p q) (op r s) =[B] op (op p r) (op q s) :=
      .trans (.assoc op p q (op r s)) <|
      .trans (.congr op (.ofEq rfl) (.symm (.assoc op q r s))) <|
      .trans (.congr op (.ofEq rfl)
        (.congr op (.comm op q r) (.ofEq rfl))) <|
      .trans (.congr op (.ofEq rfl) (.assoc op r q s))
        (.symm (.assoc op p r (op q s)))
    exact .trans (.congr op ha hb) <|
      .trans exchange (.symm (.congr op hc hd))

theorem acu_cancel_iff {B : Structural.Theory.{u}} {α : Type u}
    {op : α → α → α} {zero : α}
    (view : ACUView B op zero) (a b common : α) :
    op a common =[B] op b common ↔ a =[B] b := by
  letI := view.symbol
  constructor
  · -- General metatheorem TODO: cancel the common encoded bag.
    sorry
  · intro h
    exact .congr op h (.ofEq rfl)

theorem acu_atom_iff {B : Structural.Theory.{u}} {α : Type u}
    {op : α → α → α} {zero : α}
    (view : ACUView B op zero) (a b : α) (k : view.Atom) :
    op a b =[B] view.atom k ↔
      (a =[B] zero ∧ b =[B] view.atom k) ∨
      (a =[B] view.atom k ∧ b =[B] zero) := by
  letI := view.symbol
  letI := view.identity
  constructor
  · -- General metatheorem TODO: partition the singleton encoded bag.
    sorry
  · intro h
    cases h with
    | inl h =>
        exact .trans (.congr op h.1 h.2) (.identityLeft op zero (view.atom k))
    | inr h =>
        exact .trans (.congr op h.1 h.2) (.identityRight op zero (view.atom k))

/-!
### Inference rules

Write P ==>[B] Q for Derives B P Q, and a ~ b for a =[B] b.
In the algebra rules, +, 0, and atom come from an ACUView; they are not
constructors of a fixed term type. EΓ is Fields.Equal for a field layout Γ.

                      P ==> Q    Q ==> R
  -------- [Done]     -------------------- [Compose]
  P ==> P                  P ==> R

  P ==> P'    Q ==> Q'       P ==> P'    Q ==> Q'
  --------------------      --------------------
  P ∧ Q ==> P' ∧ Q' [And]    P ∨ Q ==> P' ∨ Q' [Or]

         for every u, P(u) ==> Q(u)
  -------------------------------------- [Exists]
       (∃ u, P(u)) ==> (∃ u, Q(u))

  a ~ a'    b ~ b'    (a' ~ b') ==> Q
  ---------------------------------- [Rewrite]
                (a ~ b) ==> Q

  ----------------------------------------------------- [ACU split]
  (a+b ~ c+d) ==> ∃ p q r s,
    a ~ p+q ∧ b ~ r+s ∧ c ~ p+r ∧ d ~ q+s

  ----------------------------- [Cancel]
  (a+c ~ b+c) ==> (a ~ b)

  ----------------------------------------------------- [Atom]
  (a+b ~ atom k) ==> (a ~ 0 ∧ b ~ atom k) ∨
                    (a ~ atom k ∧ b ~ 0)

  --------------------------------------------- [Decompose]
  build(args) ~ build(args') ==> EΓ(args,args')

  ----------------------------------------------------- [Distribute]
  (P∨Q) ∧ (R∨S) ==> (P∧R) ∨ (P∧S) ∨ (Q∧R) ∨ (Q∧S)

  ---------------- [Reflexive]     ---------------- [TrueLeft]
  (a ~ a) ==> True                True ∧ P ==> P

Read upwards to construct a derivation. Algebra/decomposition rules require
model-wide views; their semantic assumptions are not added as per-problem goals.

### From the proof system to the semantic certificate

For each assignment to the original variables, P is the equation and Q is
the proposed disjunction of substitution factorizations:
  (∃ fresh variables, x₁ ~ σ₁ ∧ ... ∧ xₙ ~ σₙ) ∨ ...

P and Q are ordinary Lean propositions using the existing EqMod semantics.
Derives.adequate interprets the derivation and produces P ↔ Q:
  P → Q is completeness; Q → P is soundness.
The top-level examples apply this theorem once, then use only general rules.
Proof search and completeness of this collection of proof rules are not claimed.
-/

inductive Derives (B : Structural.Theory.{u}) : Prop → Prop → Prop where
  | done {P : Prop} : Derives B P P
  | trans {P Q R : Prop} :
      Derives B P Q → Derives B Q R → Derives B P R
  | conj {P P' Q Q' : Prop} :
      Derives B P P' → Derives B Q Q' → Derives B (P ∧ Q) (P' ∧ Q')
  | disj {P P' Q Q' : Prop} :
      Derives B P P' → Derives B Q Q' → Derives B (P ∨ Q) (P' ∨ Q')
  | existsCongr {α : Type u} {P Q : α → Prop} :
      (∀ x, Derives B (P x) (Q x)) →
      Derives B (∃ x, P x) (∃ x, Q x)
  | distribute {P Q R S : Prop} :
      Derives B ((P ∨ Q) ∧ (R ∨ S))
        ((P ∧ R) ∨ (P ∧ S) ∨ (Q ∧ R) ∨ (Q ∧ S))
  | eqRefl {α : Type u} (a : α) : Derives B (a =[B] a) True
  | trueLeft {P : Prop} : Derives B (True ∧ P) P
  | rewrite {α : Type u} {a a' b b' : α} {Q : Prop} :
      a =[B] a' → b =[B] b' →
      Derives B (a' =[B] b') Q → Derives B (a =[B] b) Q
  | acu_split {α : Type u} {op : α → α → α} {zero : α}
      (view : ACUView B op zero) (a b c d : α) :
      Derives B (op a b =[B] op c d)
        (∃ p q r s : α,
          a =[B] op p q ∧ b =[B] op r s ∧
          c =[B] op p r ∧ d =[B] op q s)
  | acu_cancel {α : Type u} {op : α → α → α} {zero : α}
      (view : ACUView B op zero) (a b common : α) :
      Derives B (op a common =[B] op b common) (a =[B] b)
  | acu_atom {α : Type u} {op : α → α → α} {zero : α}
      (view : ACUView B op zero) (a b : α) (k : view.Atom) :
      Derives B (op a b =[B] view.atom k)
        ((a =[B] zero ∧ b =[B] view.atom k) ∨
          (a =[B] view.atom k ∧ b =[B] zero))
  | decompose {fields : Fields.{u}} {α : Type u}
      (view : ConstructorView B fields α) (a b : fields.Values) :
      Derives B (view.build a =[B] view.build b) (fields.Equal B a b)

/-- Model-independent interpretation of every derivation as an exact equivalence. -/
theorem Derives.adequate {B : Structural.Theory.{u}} {P Q : Prop}
    (proof : Derives B P Q) : P ↔ Q := by
  induction proof with
  | done => exact Iff.rfl
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | conj _ _ ih₁ ih₂ =>
      constructor
      · intro h
        exact ⟨ih₁.mp h.1, ih₂.mp h.2⟩
      · intro h
        exact ⟨ih₁.mpr h.1, ih₂.mpr h.2⟩
  | disj _ _ ih₁ ih₂ =>
      constructor
      · intro h
        cases h with
        | inl h => exact Or.inl (ih₁.mp h)
        | inr h => exact Or.inr (ih₂.mp h)
      · intro h
        cases h with
        | inl h => exact Or.inl (ih₁.mpr h)
        | inr h => exact Or.inr (ih₂.mpr h)
  | existsCongr _ ih =>
      constructor
      · intro h
        obtain ⟨x, hx⟩ := h
        exact ⟨x, (ih x).mp hx⟩
      · intro h
        obtain ⟨x, hx⟩ := h
        exact ⟨x, (ih x).mpr hx⟩
  | distribute =>
      constructor
      · intro h
        cases h.1 with
        | inl hp =>
            cases h.2 with
            | inl hr => exact Or.inl ⟨hp, hr⟩
            | inr hs => exact Or.inr (Or.inl ⟨hp, hs⟩)
        | inr hq =>
            cases h.2 with
            | inl hr => exact Or.inr (Or.inr (Or.inl ⟨hq, hr⟩))
            | inr hs => exact Or.inr (Or.inr (Or.inr ⟨hq, hs⟩))
      · intro h
        cases h with
        | inl h => exact ⟨Or.inl h.1, Or.inl h.2⟩
        | inr h =>
            cases h with
            | inl h => exact ⟨Or.inl h.1, Or.inr h.2⟩
            | inr h =>
                cases h with
                | inl h => exact ⟨Or.inr h.1, Or.inl h.2⟩
                | inr h => exact ⟨Or.inr h.1, Or.inr h.2⟩
  | eqRefl a => exact ⟨fun _ => True.intro, fun _ => EqMod.ofEq rfl⟩
  | trueLeft => exact ⟨fun h => h.2, fun h => ⟨True.intro, h⟩⟩
  | rewrite left right _ ih =>
      constructor
      · intro h
        exact ih.mp (.trans left.symm (.trans h right))
      · intro h
        exact .trans left (.trans (ih.mpr h) right.symm)
  | acu_split view a b c d => exact acu_split_iff view a b c d
  | acu_cancel view a b common => exact acu_cancel_iff view a b common
  | acu_atom view a b k => exact acu_atom_iff view a b k
  | decompose view a b => exact view.reflects a b

theorem Derives.complete {B : Structural.Theory.{u}} {P Q : Prop}
    (proof : Derives B P Q) : P → Q := proof.adequate.mp

theorem Derives.sound {B : Structural.Theory.{u}} {P Q : Prop}
    (proof : Derives B P Q) : Q → P := proof.adequate.mpr

/-! ## Part 2. Bakery registration, reusable for every certification

Only from this point does the file mention Bakery types. These declarations
describe the model, never a particular unification problem. A future structural
registration generator could produce this data and the required faithfulness
proofs from the inductive signature. That generation is not implemented here.
-/

namespace BakeryRegistration

def elements : ProcSet → List Mode
  | .empty => []
  | .singleton mode => [mode]
  | .union left right => elements left ++ elements right

def rebuild : List Mode → ProcSet
  | [] => .empty
  | mode :: rest => .union (.singleton mode) (rebuild rest)

def procs : ACUView BakeryTheory ProcSet.union ProcSet.empty where
  Atom := Mode
  atom := ProcSet.singleton
  encode := elements
  decode := rebuild
  encode_zero := rfl
  encode_op := fun _ _ => rfl
  encode_atom := fun _ => rfl
  encode_decode := by
    intro modes
    induction modes with
    | nil => rfl
    | cons mode rest ih =>
        change [mode] ++ elements (rebuild rest) = mode :: rest
        rw [ih]
        rfl
  reflects := by
    -- MODEL-WIDE TODO: EqMod on ProcSet is exactly permutation of modes.
    -- This is required for every use of procs, not separately per certificate.
    sorry
  symbol := inferInstance
  associative := inferInstance
  commutative := inferInstance
  identity := inferInstance

def confFields : Fields :=
  .product (.field Nat) (.product (.field Nat) (.field ProcSet))

def conf : ConstructorView BakeryTheory confFields Conf where
  build := fun args => Conf.mk args.1 args.2.1 args.2.2
  reflects := by
    intro a b
    constructor
    · -- MODEL-WIDE TODO: invert EqMod through the free Conf.mk constructor.
      sorry
    · intro h
      exact EqMod.constructor
        (ConstructorCongruence.app
          (ConstructorCongruence.app
            (ConstructorCongruence.app (ConstructorCongruence.head Conf.mk) h.1)
            h.2.1)
          h.2.2)

end BakeryRegistration

/-! ## Part 3. One atomic Bakery problem, two unifiers

Uses the actual Conf, ProcSet, and BakeryTheory imported from examples/bakery.
The counters are shared rigid parameters. The unification variables are X, Y.

Problem:
  Conf(next, serving, (X union empty) union Y)
    =[BakeryTheory] Conf(next, serving, singleton idle)

Proposed substitutions:
  σ₁: X ↦ empty,          Y ↦ singleton idle
  σ₂: X ↦ singleton idle, Y ↦ empty

No fresh variables are needed. The disjunction below is precisely the
factorization formula for these two substitutions, modulo BakeryTheory.

The semantic certificate is one iff: completeness forwards, soundness backwards.
The single proof uses only general rules and the model-wide registration.
It inherits the explicitly admitted generic and registration metatheory.
-/

example (next serving : Nat) :
    ∀ X Y : ProcSet,
      Conf.mk next serving (ProcSet.union (ProcSet.union X ProcSet.empty) Y)
        =[BakeryTheory] Conf.mk next serving (ProcSet.singleton Mode.idle) ↔
      (X =[BakeryTheory] ProcSet.empty ∧
        Y =[BakeryTheory] ProcSet.singleton Mode.idle) ∨
      (X =[BakeryTheory] ProcSet.singleton Mode.idle ∧
        Y =[BakeryTheory] ProcSet.empty) := by
  intro X Y
  -- Interpret a derivation as the requested semantic soundness/completeness iff.
  apply Derives.adequate
  -- The free constructor rule generates three heterogeneous equations:
  -- next ~ next, serving ~ serving, and an ACU equation over ProcSet.
  refine Derives.trans (Derives.decompose BakeryRegistration.conf
    (next, serving, ProcSet.union (ProcSet.union X ProcSet.empty) Y)
    (next, serving, ProcSet.singleton Mode.idle)) ?_
  -- Discharge the rigid counter equations by general reflexivity rules.
  refine Derives.trans
    (Derives.conj (Derives.eqRefl next)
      (Derives.conj (Derives.eqRefl serving) Derives.done)) ?_
  refine Derives.trans Derives.trueLeft ?_
  refine Derives.trans Derives.trueLeft ?_
  -- Normalize the unit, leaving X union Y ~ singleton idle.
  apply Derives.rewrite
    (EqMod.congr ProcSet.union
      (EqMod.identityRight ProcSet.union ProcSet.empty X) (EqMod.ofEq rfl))
    (EqMod.ofEq rfl)
  -- General Atom rule yields exactly the two proposed alternatives.
  exact Derives.acu_atom BakeryRegistration.procs X Y Mode.idle

end Certification
