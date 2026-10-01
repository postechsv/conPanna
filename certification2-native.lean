import certification2
import conPanna.Structural

open scoped Structural

/-!
# Native bridge experiment: one free ACU sort

This file connects the portable proof checker to the EXISTING Structural.EqMod.
It does not introduce an alternative native equality or modify the library.

Scope is intentionally small: an ACU operation and nullary atoms. Its theory
needs no ordinary constructor congruence: ACU's own congruence already handles
the only constructor with arguments. We register the laws before introducing a
State instance, so `structural` does not collect that instance's constructors.
The check `NativeTheory.constructors = []` below makes this restriction explicit.
This is not yet the bridge for Bakery's mixed-sort constructor applications.

General bridge lemmas are separate from the native model and its certificate.

On a fresh checkout, first build the standalone imported experiment:
  lake env lean -o .lake/build/lib/lean/certification2.olean certification2.lean
Then open this file with Lean LSP, or run `lake env lean certification2-native.lean`.
-/

namespace Certification2.NativeBridge

open Structural

variable {Sorts : Type} {s : Sorts}

/-- An interpretation of a law-only native theory in the portable ACU algebra.
These are model-wide registration obligations, never per-problem certificates.
The uniqueness fields are homogeneous: no injectivity of Lean arrow TYPES is
assumed. Empty ordinary-constructor registration excludes that separate case. -/
structure Model (B : Theory) (α : Type) (s : Sorts) where
  encode : α → Value s
  op : α → α → α
  unit : α
  encode_op : ∀ a b, encode (op a b) = .add (encode a) (encode b)
  encode_unit : encode unit = .zero
  symbols : ∀ (f : α → α → α), [HasSymbol B f] → f = op
  comms : ∀ (f : α → α → α), [HasComm B f] → f = op
  assocs : ∀ (f : α → α → α), [HasAssoc B f] → f = op
  identities : ∀ (f : α → α → α) (e : α), [HasIdentity B f e] → f = op ∧ e = unit

/-- Native EqMod reflects into ACU, accounting for EVERY EqMod constructor.
The induction ranges over arbitrary Lean types, rather than assuming that the
datatype used in the final goal is also the type of every intermediate step. -/
theorem reflect {B : Theory} (noConstructors : B.constructors = [])
    {α : Type} (model : Model B α s) {a b : α} (h : EqMod B a b) :
    ACU (model.encode a) (model.encode b) := by
  refine EqMod.rec
    (motive_1 := fun {β : Type} left right _ =>
      ∀ m : Model B β s, ACU (m.encode left) (m.encode right))
    (motive_2 := fun {_ : Type} _ _ _ => False)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h model
  · intro β left right equality m
    cases equality
    exact .refl _
  · intro β left right equation ih m
    exact (ih m).symm
  · intro β first second third h₁ h₂ ih₁ ih₂ m
    exact (ih₁ m).trans (ih₂ m)
  · intro β f hf left left' right right' h₁ h₂ ih₁ ih₂ m
    rw [m.symbols f, m.encode_op, m.encode_op]
    exact .congr (ih₁ m) (ih₂ m)
  · intro β left right constructorProof impossible
    exact impossible.elim
  · intro β f hf left right m
    rw [m.comms f, m.encode_op, m.encode_op]
    exact .comm _ _
  · intro β f hf a b c m
    rw [m.assocs f]
    simp only [m.encode_op]
    exact .assoc _ _ _
  · intro β f e v hf m
    obtain ⟨hop, he⟩ := m.identities f e
    rw [hop, he, m.encode_op, m.encode_unit]
    exact .unit _
  · intro β f e v hf m
    obtain ⟨hop, he⟩ := m.identities f e
    rw [hop, he, m.encode_op, m.encode_unit]
    exact .unitRight _
  · intro β constructor hc
    have hm := hc.member
    rw [noConstructors] at hm
    exact List.not_mem_nil hm
  · intro β γ left right arg arg' functionProof argumentProof impossible ih
    exact impossible

/-- Decoding requires only the registered ACU laws; atoms may be interpreted
arbitrarily. This direction does NOT by itself establish native completeness. -/
def decode {α : Type} (op : α → α → α) (unit : α) (atom : Nat → α) : Value s → α
  | .zero => unit
  | .atom n => atom n
  | .add a b => op (decode op unit atom a) (decode op unit atom b)

theorem decode_preserves {B : Theory} {α : Type} (op : α → α → α) (unit : α)
    (atom : Nat → α) [HasSymbol B op] [HasComm B op] [HasAssoc B op]
    [HasIdentity B op unit] {a b : Value s} (h : ACU a b) :
    EqMod B (decode op unit atom a) (decode op unit atom b) := by
  induction h with
  | refl => exact .ofEq rfl
  | symm _ ih => exact .symm ih
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂
  | congr _ _ ih₁ ih₂ => exact .congr op ih₁ ih₂
  | «assoc» => exact .assoc op _ _ _
  | «comm» => exact .comm op _ _
  | unit => exact .identityLeft op unit _

end Certification2.NativeBridge

namespace Certification2

variable {Sorts : Type} {s : Sorts}

/-! ## Generic certificate transport (independent of the example)

Formulas are positive/existential, so a homomorphism preserving the relation
transports satisfaction forwards. Use encode and decode in opposite directions
to lift a checked iff. `allowed` restricts literal symbols in the PROBLEM and
ANSWER; existential witnesses need not already be encoded native values.
Decoding them supplies native witnesses. No feasibility decision is involved.
-/

structure Semantics (α : Type) where
  zero : α
  atom : Nat → α
  add : α → α → α
  rel : α → α → Prop

def portable (s : Sorts) : Semantics (Value s) :=
  ⟨.zero, .atom, .add, ACU⟩

def Term.denote {α : Type} (m : Semantics α) (ρ : Nat → α) : Term s → α
  | .var n => ρ n
  | .atom n => m.atom n
  | .zero => m.zero
  | .add a b => m.add (a.denote m ρ) (b.denote m ρ)

def Formula.sat {α : Type} (m : Semantics α) (ρ : Nat → α) : Formula s → Prop
  | .truth => True
  | .falsity => False
  | .eqn a b => m.rel (a.denote m ρ) (b.denote m ρ)
  | .conj p q => p.sat m ρ ∧ q.sat m ρ
  | .disj p q => p.sat m ρ ∨ q.sat m ρ
  | .ex p => ∃ v, p.sat m (fun n => match n with | 0 => v | n+1 => ρ n)

def Term.uses (allowed : Nat → Prop) : Term s → Prop
  | .var _ | .zero => True
  | .atom n => allowed n
  | .add a b => a.uses allowed ∧ b.uses allowed

def Formula.uses (allowed : Nat → Prop) : Formula s → Prop
  | .truth | .falsity => True
  | .eqn a b => a.uses allowed ∧ b.uses allowed
  | .conj p q | .disj p q => p.uses allowed ∧ q.uses allowed
  | .ex p => p.uses allowed

structure Hom {α β : Type} (m : Semantics α) (n : Semantics β)
    (f : α → β) (allowed : Nat → Prop) : Prop where
  zero : f m.zero = n.zero
  atom : ∀ k, allowed k → f (m.atom k) = n.atom k
  add : ∀ a b, f (m.add a b) = n.add (f a) (f b)
  rel : ∀ {a b}, m.rel a b → n.rel (f a) (f b)

theorem Term.map_denote {α β : Type} {m : Semantics α} {n : Semantics β}
    {f : α → β} {allowed : Nat → Prop} (hom : Hom m n f allowed)
    (t : Term s) (ht : t.uses allowed) (ρ : Nat → α) :
    f (t.denote m ρ) = t.denote n (fun i => f (ρ i)) := by
  induction t with
  | var => rfl
  | zero => exact hom.zero
  | atom k => exact hom.atom k ht
  | add a b ha hb =>
      change f (m.add _ _) = n.add _ _
      rw [hom.add, ha ht.1, hb ht.2]

theorem Formula.map_sat {α β : Type} {m : Semantics α} {n : Semantics β}
    {f : α → β} {allowed : Nat → Prop} (hom : Hom m n f allowed)
    (p : Formula s) (hp : p.uses allowed) (ρ : Nat → α) :
    p.sat m ρ → p.sat n (fun i => f (ρ i)) := by
  induction p generalizing ρ with
  | truth => exact fun _ => trivial
  | falsity => exact False.elim
  | eqn a b =>
      intro h
      have h' := hom.rel h
      rwa [a.map_denote hom hp.1 ρ, b.map_denote hom hp.2 ρ] at h'
  | conj p q ihp ihq => exact fun ⟨h₁, h₂⟩ => ⟨ihp hp.1 ρ h₁, ihq hp.2 ρ h₂⟩
  | disj p q ihp ihq =>
      intro h
      exact h.elim (fun h => Or.inl (ihp hp.1 ρ h)) (fun h => Or.inr (ihq hp.2 ρ h))
  | ex p ih =>
      rintro ⟨v, hv⟩
      refine ⟨f v, ?_⟩
      have mapped := ih hp _ hv
      have he : (fun i => f (match i with | 0 => v | n+1 => ρ n)) =
          (fun i => match i with | 0 => f v | n+1 => f (ρ n)) := by
        funext i
        cases i <;> rfl
      rw [he] at mapped
      exact mapped

theorem Term.uses_all (t : Term s) : t.uses (fun _ => True) := by
  induction t <;> simp_all [uses]

theorem Formula.uses_all (p : Formula s) : p.uses (fun _ => True) := by
  induction p <;> simp_all [uses, Term.uses_all]

theorem Term.denote_portable (t : Term s) (ρ : Assignment s) :
    t.denote (portable s) ρ = t.eval ρ := by
  induction t <;> simp_all [denote, eval, portable]

theorem Formula.sat_portable (p : Formula s) (ρ : Assignment s) :
    p.sat (portable s) ρ ↔ p.Holds ρ := by
  induction p generalizing ρ with
  | truth => rfl
  | falsity => rfl
  | eqn a b =>
      change ACU (a.denote (portable s) ρ) (b.denote (portable s) ρ) ↔ _
      rw [a.denote_portable, b.denote_portable]
      rfl
  | conj p q hp hq => exact and_congr (hp ρ) (hq ρ)
  | disj p q hp hq => exact or_congr (hp ρ) (hq ρ)
  | ex p hp => exact exists_congr (fun v => hp (push v ρ))

/-- A reusable boundary for lifting every checked certificate, not a new
per-problem proof rule. encode/decode need only form a retraction: unused raw
atom codes may collapse under decoding, since source/answer syntax is checked. -/
structure Bridge {α : Type} (m : Semantics α) (s : Sorts) where
  allowed : Nat → Prop
  encode : α → Value s
  decode : Value s → α
  roundtrip : ∀ a, decode (encode a) = a
  forward : Hom m (portable s) encode allowed
  backward : Hom (portable s) m decode (fun _ => True)

theorem Bridge.transport {α : Type} {m : Semantics α} (b : Bridge m s)
    {p q : Formula s} (hp : p.uses b.allowed) (equiv : Equivalent p q)
    (ρ : Nat → α) : p.sat m ρ → q.sat m ρ := by
  intro h
  have rawP := (p.sat_portable _).mp (p.map_sat b.forward hp ρ h)
  have rawQ := (equiv _).mp rawP
  have nativeQ := q.map_sat b.backward q.uses_all _ ((q.sat_portable _).mpr rawQ)
  simpa only [b.roundtrip] using nativeQ

/-- A checked portable certificate lifts BOTH directions to native semantics.
The ONLY per-problem obligations are finite syntax/checker computations. -/
theorem Bridge.check_exact [DecidableEq Sorts] {α : Type} {m : Semantics α}
    (b : Bridge m s) (p q : Formula s) (cert : Certificate)
    (accepted : check p q cert = true)
    (hp : p.uses b.allowed) (hq : q.uses b.allowed) (ρ : Nat → α) :
    p.sat m ρ ↔ q.sat m ρ :=
  let equiv := Certification2.check_exact p q cert accepted
  ⟨b.transport hp equiv ρ, b.transport hq (fun σ => (equiv σ).symm) ρ⟩

end Certification2

namespace Certification2.NativeExample

inductive Bag where
  | empty | red | blue
  | union : Bag → Bag → Bag
  deriving Repr, DecidableEq

structural NativeTheory where
  assoc Bag.union
  comm Bag.union
  id Bag.union Bag.empty

-- Nullary atoms need no congruence rule; union already has EqMod.congr.
example : NativeTheory.constructors = [] := rfl

-- Deliberate experiment-only ordering, not a proposed replacement registration UI.
-- With State already present, the current command also registers ordinary
-- constructors. Extending reflection to that case is still the next milestone.
instance : framework.State Bag := ⟨⟩

inductive SortTag where
  | bag
  deriving DecidableEq

abbrev Raw := Value SortTag.bag

def encode : Bag → Raw
  | .empty => .zero
  | .red => .atom 0
  | .blue => .atom 1
  | .union a b => .add (encode a) (encode b)

open Structural NativeBridge

def model : Model NativeTheory Bag SortTag.bag where
  encode := encode
  op := Bag.union
  unit := Bag.empty
  encode_op := fun _ _ => rfl
  encode_unit := rfl
  symbols := by
    intro f hf
    have hd : hf.declaration = Symbol.declare Bag.union
        [.associative, .commutative, .identity Bag.empty] := by
      simpa [NativeTheory] using hf.member
    have he := hf.operation_eq
    rw [hd] at he
    exact (eq_of_heq he).symm
  comms := by
    intro f hf
    have hd : hf.declaration = CommutativeDeclaration.declare Bag.union := by
      simpa [NativeTheory] using hf.member
    have he := hf.operation_eq
    rw [hd] at he
    exact (eq_of_heq he).symm
  assocs := by
    intro f hf
    have hd : hf.declaration = AssociativeDeclaration.declare Bag.union := by
      simpa [NativeTheory] using hf.member
    have he := hf.operation_eq
    rw [hd] at he
    exact (eq_of_heq he).symm
  identities := by
    intro f e hf
    have hd : hf.declaration = IdentityDeclaration.declare Bag.union Bag.empty := by
      simpa [NativeTheory] using hf.member
    have hop := hf.operation_eq
    have he := hf.element_eq
    rw [hd] at hop he
    exact ⟨(eq_of_heq hop).symm, (eq_of_heq he).symm⟩

/-- Total decoding is convenient; only codes 0 and 1 belong to this signature.
Unused codes are mapped to blue. They are rejected in problems/answers below. -/
def atom : Nat → Bag
  | 0 => .red
  | _ + 1 => .blue

def decode : Raw → Bag := NativeBridge.decode Bag.union Bag.empty atom

theorem decode_encode (a : Bag) : decode (encode a) = a := by
  induction a <;> simp_all [encode, decode, NativeBridge.decode, atom]

/-- This is the actual native reflection/preservation theorem, not an assumption. -/
theorem eqMod_iff (a b : Bag) :
    a =[NativeTheory] b ↔ ACU (encode a) (encode b) := by
  constructor
  · exact reflect rfl model
  · intro h
    have h' : decode (encode a) =[NativeTheory] decode (encode b) :=
      decode_preserves (B := NativeTheory) Bag.union Bag.empty atom h
    simpa only [decode_encode] using h'

def native : Semantics Bag := ⟨.empty, atom, .union, EqMod NativeTheory⟩

def bridge : Bridge native SortTag.bag where
  allowed := fun n => n = 0 ∨ n = 1
  encode := encode
  decode := decode
  roundtrip := decode_encode
  forward := {
    zero := rfl
    atom := by intro k hk; rcases hk with rfl | rfl <;> rfl
    add := fun _ _ => rfl
    rel := fun h => (eqMod_iff _ _).mp h }
  backward := {
    zero := rfl
    atom := fun _ _ => rfl
    add := fun _ _ => rfl
    rel := fun h => decode_preserves Bag.union Bag.empty atom h }

/-! ## The problem certificate: one proof, no problem-specific lemmas

The native terms below are the user's constructors; there are no encodings in
the theorem statement. The certificate is the SAME rule data used by the Maude
experiment. Only the atom identifier changes, from 7 to this signature's 0.
-/

def problem : Formula SortTag.bag :=
  .eqn (.add (.var 0) (.var 1)) (.add (.atom 0) (.var 2))

def answer : Formula SortTag.bag := peel (.var 0) (.var 1) (.var 2) 0

theorem native_two_unifiers (X Y Z : Bag) :
    Bag.union X Y =[NativeTheory] Bag.union .red Z ↔
      (∃ p q : Bag, X =[NativeTheory] Bag.union .red p ∧
        Y =[NativeTheory] q ∧ Z =[NativeTheory] Bag.union p q) ∨
      (∃ p q : Bag, X =[NativeTheory] p ∧
        Y =[NativeTheory] Bag.union .red q ∧ Z =[NativeTheory] Bag.union p q) := by
  have certified := bridge.check_exact problem answer Examples.overlapPrimitiveTrace
    (by decide)
    (by simp [problem, Formula.uses, Term.uses, bridge])
    (by simp [answer, peel, Formula.uses, Term.uses, Term.lift, bridge])
    (fun n => match n with | 0 => X | 1 => Y | _ => Z)
  simpa only [problem, answer, peel, Formula.sat, Term.denote, Term.lift,
    native, atom] using certified

/-! Boundary/regression checks, not additional lemmas used by the certificate. -/

-- Code 2 decodes to blue but is NOT a native symbol, so it must not be allowed
-- in a problem/answer merely because the decoder is total.
example : ¬ (Formula.eqn (.var 0) (.atom 2) : Formula SortTag.bag).uses
    bridge.allowed := by simp [Formula.uses, Term.uses, bridge]

-- A branch omitted from the claimed answer is still rejected at native use.
example : check problem
    (.ex (.ex (.conj (.eqn (.var 2) (.add (.atom 0) (.var 1)))
      (.conj (.eqn (.var 3) (.var 0)) (.eqn (.var 4) (.add (.var 1) (.var 0)))))))
    Examples.overlapPrimitiveTrace = false := by decide

-- Reflection really distinguishes the native atom constructors.
example : ¬ (Bag.red =[NativeTheory] Bag.blue) := by
  intro h
  have h' := ((eqMod_iff _ _).mp h).flatten_perm
  simp [encode, Value.flatten] at h'

#print axioms eqMod_iff
#print axioms native_two_unifiers

end Certification2.NativeExample
