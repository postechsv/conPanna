import conPanna.Certification.Syntax

/-!
# The surface ACU certification calculus
Read this file alongside certifier/certification.maude (CERTIFICATION-PRODUCER).
The rules have the SAME names and premises as its completed evidence nodes.
No search, registration metaprogramming, parsing, IO or semantic induction lives here.

Three proof levels:
  Equality         t =B u              structural equality, without assumptions
  Derives       E ⊢ t =B u              equality under the current equations
  Complete      ⟨α ; E⟩ ⇒ Σ             every E-solution is covered by fixed Σ

Soundness separately checks each proposed substitution against each original
equation. Semantics.lean proves the rules valid once; its public exact_system
combines completeness and soundness into the registered semantic certificate.
Python emits only these rules, typed DATA and checked side-condition witnesses.
Names are preserved so existing generated and handwritten proofs use ONE calculus.

The live context Γ lists variable sorts. α records one image per ORIGINAL input;
a rule may change Γ without changing the original inputs or supplied answers Σ.
The typed data operations used below are implemented in Syntax.lean.
-/

namespace DirectCertification

open Structural.Indexed

variable {Sorts : Type} {sig : Signature Sorts}

namespace Substitution

/-! ## 1. Structural equality premises (Maude EQUALITY)
REFL / SYMM / TRANS / CONGR / COMM / ASSOC / UNIT.
These constructors justify unconditional equality. Equalities is the vector form.
-/
mutual
  inductive Equality (sig : Signature Sorts) (Γ : List Sorts) :
      {s : Sorts} → Term sig Γ s → Term sig Γ s → Type where
    | refl {s} (a : Term sig Γ s) : Equality sig Γ a a
    | symm {s} {a b : Term sig Γ s} : Equality sig Γ a b → Equality sig Γ b a
    | trans {s} {a b c : Term sig Γ s} :
        Equality sig Γ a b → Equality sig Γ b c → Equality sig Γ a c
    | congr {ss s} (f : sig.Symbol ss s) {a b : Terms sig Γ ss} :
        Equalities sig Γ a b → Equality sig Γ (.app f a) (.app f b)
    | comm {s} (op : sig.ACUOp s) (a b : Term sig Γ s) :
        Equality sig Γ (add op a b) (add op b a)
    | assoc {s} (op : sig.ACUOp s) (a b c : Term sig Γ s) :
        Equality sig Γ (add op (add op a b) c) (add op a (add op b c))
    | unit {s} (op : sig.ACUOp s) (a : Term sig Γ s) :
        Equality sig Γ (add op (zero op) a) a
  inductive Equalities (sig : Signature Sorts) (Γ : List Sorts) :
      {ss : List Sorts} → Terms sig Γ ss → Terms sig Γ ss → Type where
    | nil : Equalities sig Γ .nil .nil
    | cons {s ss} {a b : Term sig Γ s} {as bs : Terms sig Γ ss} :
        Equality sig Γ a b → Equalities sig Γ as bs →
        Equalities sig Γ (.cons a as) (.cons b bs)
end

/-! ## 2. Proposed-answer soundness (Maude answersProof)
A cons node checks lhsσ =B rhsσ for ONE answer; nil ends the list.
The producer emits these equality rows. The sharing/binding constructors are
general derived presentations also available to handwritten certificates.
-/
inductive Soundness {inputs : List Sorts} : Problem sig inputs → List (Answer sig inputs) → Type where
  | nil {problem} : Soundness problem []
  | cons {problem answer rest}
      (proof : Equality sig answer.parameters
        (problem.left.subst answer.images) (problem.right.subst answer.images))
      (tail : Soundness problem rest) : Soundness problem (answer :: rest)
  | sharing {s n rows cols rest} (profile : Profile sig) (op : sig.ACUOp s)
      (slots : Sharing.Slots s inputs n) (left right : FiniteSharing.Vector n)
      (rowLabels : Fin rows → Fin n) (colLabels : Fin cols → Fin n)
      (rowCounts : ∀ i, FiniteSharing.labelCount rowLabels i = left i)
      (colCounts : ∀ i, FiniteSharing.labelCount colLabels i = right i)
      (disjoint : FiniteSharing.Disjoint left right)
      (tail : Soundness (Sharing.problem op slots left right) rest) :
      Soundness (Sharing.problem op slots left right)
        (Sharing.answer op slots left right (FiniteSharing.supportGenerators rowLabels colLabels) :: rest)
  | binding {s Δ rest} (remove : Binding.Removal s inputs Δ) (term : Term sig Δ s)
      (tail : Soundness (Binding.problem remove term) rest) :
      Soundness (Binding.problem remove term) (Binding.answer remove term :: rest)

namespace Worklist

/-! ## 3. Equality premises under E (Maude choose / selectBag / selectCoverage)
HYP selects a current equation; AXIOM embeds unconditional Equality.
DECOMPOSE is restricted to FREE heads; CANCEL removes a common bag prefix;
MULTIPLICITY requires a positive count. These justify premises, not new states.
-/
mutual
  inductive Derives (profile : Profile sig) {Γ} (eqs : List (Problem sig Γ)) :
      {s : Sorts} → Term sig Γ s → Term sig Γ s → Type where
    | axiom {s a b} : Equality sig Γ (s := s) a b → Derives profile eqs a b
    | hyp (index : Fin eqs.length) : Derives profile eqs (eqs.get index).left (eqs.get index).right
    | symm {s a b} : Derives profile eqs (s := s) a b → Derives profile eqs b a
    | trans {s a b c} : Derives profile eqs (s := s) a b → Derives profile eqs b c → Derives profile eqs a c
    | congr {ss s} (f : sig.Symbol ss s) {a b : Terms sig Γ ss} :
        DerivesArgs profile eqs a b → Derives profile eqs (.app f a) (.app f b)
    | cancel {s} (op : sig.ACUOp s) (common a b : Term sig Γ s) :
        Derives profile eqs (add op common a) (add op common b) →
        Derives profile eqs a b
    | multiplicity {s} (op : sig.ACUOp s) (k : Nat) (positive : 0 < k)
        (a b : Term sig Γ s) :
        Derives profile eqs (copies op k a) (copies op k b) →
        Derives profile eqs a b
    | decompose {ss s t} (f : sig.Symbol ss s) (free : profile.view f = .atom f)
        (a b : Terms sig Γ ss) (field : Variable ss t) :
        Derives profile eqs (.app f a) (.app f b) →
        Derives profile eqs (a.get field) (b.get field)
  inductive DerivesArgs (profile : Profile sig) {Γ} (eqs : List (Problem sig Γ)) :
      {ss : List Sorts} → Terms sig Γ ss → Terms sig Γ ss → Type where
    | nil : DerivesArgs profile eqs .nil .nil
    | cons {s ss a b as bs} : Derives profile eqs (s := s) a b →
        DerivesArgs profile eqs (ss := ss) as bs → DerivesArgs profile eqs (.cons a as) (.cons b bs)
end

/-! ## 4. State proof rules (Maude CERTIFICATION-PRODUCER)
Each constructor proves ⟨α ; E⟩ ⇒ Σ from its selected equation and child evidence.
The proposed answers stay fixed. ATOM requires ALL admissible children;
FINITE-SHARING introduces parameters in ONE child, not alternative branches.
-/
inductive Complete (profile : Profile sig) {inputs} (proposed : List (Answer sig inputs)) :
    {Γ : List Sorts} → Terms sig Γ inputs → List (Problem sig Γ) → Type where
  /-- COVER / EARLY-COVER [cover-and-emit]: choose ONE supplied answer and ONE β for ALL input images. -/
  | cover {Γ images eqs} (index : Fin proposed.length)
      (bindings : Terms sig Γ (proposed.get index).parameters)
      (derived : DerivesArgs profile eqs images ((proposed.get index).images.subst bindings)) :
      Complete profile proposed images eqs
  /-- BIND [bind]: remove one variable; substitute in ALL input images and current equations. -/
  | bind {Γ Δ images eqs s} (remove : Binding.Removal s Γ Δ) (term : Term sig Δ s)
      (selected : Derives profile eqs (Binding.problem remove term).left
        (Binding.problem remove term).right)
      (child : Complete profile proposed (images.subst (remove.substitution term))
        (substituteEquations (remove.substitution term) eqs)) :
      Complete profile proposed images eqs
  /-- FREE-OCCURS [occurs-and-emit]: a proper FREE-constructor path closes a contradiction. -/
  | occurs {Γ images eqs s} (v : Variable Γ s) (rhs : Term sig Γ s)
      (path : FreeOccurs.Proper profile v rhs)
      (selected : Derives profile eqs (.var v) rhs) : Complete profile proposed images eqs
  /-- PURIFY [purify]: name a term with one fresh variable and retain its defining equation. -/
  | purify {Γ images s} (term : Term sig Γ s) (template : Problem sig (s :: Γ))
      (before after : List (Problem sig Γ))
      (child : Complete profile proposed (images.subst Purification.embedding)
        (Purification.state term template (before ++ after))) :
      Complete profile proposed images (before ++ Purification.source term template :: after)
  /-- ATOM [atom-split]: prove EVERY coefficient-one supplier child; others cannot supply a singleton. -/
  | atom {Γ images eqs s n ss} (op : sig.ACUOp s) (coeff : FiniteSharing.Vector n)
      (terms : Fin n → Term sig Γ s) (f : sig.Symbol ss s)
      (free : profile.view f = .atom f) (args : Terms sig Γ ss)
      (selected : Derives profile eqs (Sharing.sum op coeff terms) (.app f args))
      (children : ∀ j, coeff j = 1 → Complete profile proposed images
        (atomRequirements op coeff terms (.app f args) j ++ eqs)) :
      Complete profile proposed images eqs
  /-- ZERO [zero-split]: ONE child requires every positive-coefficient summand to be empty. -/
  | zero {Γ images eqs s n} (op : sig.ACUOp s) (coeff : FiniteSharing.Vector n)
      (terms : Fin n → Term sig Γ s)
      (selected : Derives profile eqs (Sharing.sum op coeff terms) (zero op))
      (child : Complete profile proposed images (zeroRequirements op coeff terms ++ eqs)) :
      Complete profile proposed images eqs
  /-- NONEMPTY [nonempty-close]: a FREE bag atom cannot equal the unit. -/
  | nonempty {Γ images eqs s ss} (op : sig.ACUOp s) (f : sig.Symbol ss s)
      (free : profile.view f = .atom f) (args : Terms sig Γ ss)
      (selected : Derives profile eqs (.app f args) (zero op)) :
      Complete profile proposed images eqs
  /-- FINITE-SHARING [finite-sharing]: ALL balanced supports generate ONE correlated substitution. -/
  | sharing {Γ images eqs s n rows cols} (op : sig.ACUOp s) (slots : Sharing.Slots s Γ n)
      (left right : FiniteSharing.Vector n)
      (rowLabels : Fin rows → Fin n) (colLabels : Fin cols → Fin n)
      (rowCounts : ∀ i, FiniteSharing.labelCount rowLabels i = left i)
      (colCounts : ∀ i, FiniteSharing.labelCount colLabels i = right i)
      (disjoint : FiniteSharing.Disjoint left right)
      (selected : Derives profile eqs (Sharing.problem op slots left right).left
        (Sharing.problem op slots left right).right)
      (child : Complete profile proposed
        (images.subst (Sharing.substitution op slots left right (FiniteSharing.supportGenerators rowLabels colLabels)))
        (substituteEquations (Sharing.substitution op slots left right
          (FiniteSharing.supportGenerators rowLabels colLabels)) eqs)) :
      Complete profile proposed images eqs
  /-- MUTATE [witness-cover-and-emit / tryWitness]: introduce four fresh sharing pieces, then certify the child. -/
  | mutate {Γ images eqs s} (op : sig.ACUOp s) (a b c d : Term sig Γ s)
      (selected : Derives profile eqs (add op a b) (add op c d))
      (child : Complete profile proposed (images.subst lift4) (mutated op a b c d eqs)) :
      Complete profile proposed images eqs
  /-- Derived binary ATOM: BOTH children are required; the producer emits atom instead. -/
  | split {Γ images eqs ss s} (op : sig.ACUOp s) (x y : Term sig Γ s)
      (f : sig.Symbol ss s) (free : profile.view f = .atom f) (args : Terms sig Γ ss)
      (selected : Derives profile eqs (add op x y) (.app f args))
      (left : Complete profile proposed images
        (equation x (zero op) :: equation y (.app f args) :: eqs))
      (right : Complete profile proposed images
        (equation x (.app f args) :: equation y (zero op) :: eqs)) :
      Complete profile proposed images eqs
  /-- CLASH [clash-and-emit]: different FREE heads cannot be equal. -/
  | clash {Γ images eqs ss tt s} (f : sig.Symbol ss s) (g : sig.Symbol tt s)
      (hf : profile.view f = .atom f) (hg : profile.view g = .atom g)
      (different : (⟨ss, f⟩ : Σ us, sig.Symbol us s) ≠ ⟨tt, g⟩)
      (a : Terms sig Γ ss) (b : Terms sig Γ tt)
      (selected : Derives profile eqs (.app f a) (.app g b)) :
      Complete profile proposed images eqs

namespace ReplayState

/-! ## 5. Checked explicit state snapshots
Certified is the SAME Complete judgment. accept checks that the supplied child
snapshot equals the rule-computed successor; it does not trust an external dump.
-/
abbrev Certified {inputs Γ} (profile : Profile sig) (proposed : List (Answer sig inputs))
    (state : ReplayState sig inputs Γ) : Type :=
  Complete profile proposed state.images state.equations

def accept {inputs Γ} {profile : Profile sig} {proposed : List (Answer sig inputs)}
    (expected actual : ReplayState sig inputs Γ) (checked : expected = actual)
    (child : Certified profile proposed actual) : Certified profile proposed expected :=
  Eq.mpr (congrArg (Certified profile proposed) checked) child

end ReplayState

/-- FINITE-SHARING with an explicit exhaustive support table.
The checked equality is a side-condition witness, not a claim made by Maude.
This is a derived presentation of sharing, not a new proof rule. -/
def Complete.sharingTable {profile : Profile sig} {inputs proposed Γ images eqs s n rows cols}
    (op : sig.ACUOp s) (slots : Sharing.Slots s Γ n)
    (left right : FiniteSharing.Vector n)
    (rowLabels : Fin rows → Fin n) (colLabels : Fin cols → Fin n)
    (rowCounts : ∀ i, FiniteSharing.labelCount rowLabels i = left i)
    (colCounts : ∀ i, FiniteSharing.labelCount colLabels i = right i)
    (disjoint : FiniteSharing.Disjoint left right)
    (selected : Derives profile eqs (Sharing.problem op slots left right).left
      (Sharing.problem op slots left right).right)
    (table : List (FiniteSharing.Vector n))
    (checked : FiniteSharing.supportGenerators rowLabels colLabels = table)
    (child : Complete profile proposed (inputs := inputs)
      (images.subst (Sharing.substitution op slots left right table))
      (substituteEquations (Sharing.substitution op slots left right table) eqs)) :
    Complete profile proposed (Γ := Γ) images eqs := by
  let motive := fun gs => Complete profile proposed
    (images.subst (Sharing.substitution op slots left right gs))
    (substituteEquations (Sharing.substitution op slots left right gs) eqs)
  exact .sharing op slots left right rowLabels colLabels rowCounts colCounts disjoint selected
    (Eq.mpr (congrArg motive checked) child)

/-! ## 6. Soundness for the original equation system
One Soundness row per original equation, preserving the SAME proposed vectors.
Final public aggregation: Worklist.exact_system, implemented in Semantics.lean.
-/
inductive SystemSoundness {inputs} (proposed : List (Answer sig inputs)) :
    List (Problem sig inputs) → Type where
  | nil : SystemSoundness proposed []
  | cons {problem rest} (head : Soundness problem proposed)
      (tail : SystemSoundness proposed rest) : SystemSoundness proposed (problem :: rest)

end Worklist

/-! ## Derived structural rules
Fixed expansions in the primitive equality language, not tactics or semantic
search. swap_right mirrors Maude's swapProof; the remaining operations support
readable handwritten certificates over repeated sums.
-/
/-- Maude rightUnitProof: COMM followed by UNIT. This is fixed structural
evidence, not a semantic assumption or problem-specific normalization lemma. -/
def Equality.right_unit {Γ s} (op : sig.ACUOp s) (a : Term sig Γ s) :
    Equality sig Γ (add op a (zero op)) a :=
  .trans (.comm op a (zero op)) (.unit op a)

def Equality.swap_right {Γ s} (op : sig.ACUOp s) (a b rest : Term sig Γ s) :
    Equality sig Γ (add op a (add op b rest)) (add op b (add op a rest)) :=
  .trans (.symm (.assoc op a b rest))
    (.trans (.congr (sig.add op) (.cons (.comm op a b) (.cons (.refl rest) .nil)))
      (.assoc op b a rest))

def Equality.exchange_tail {Γ s} (op : sig.ACUOp s) (a b rest : Term sig Γ s) :
    Equality sig Γ (add op a (add op rest b)) (add op b (add op rest a)) :=
  .trans (.congr (sig.add op) (.cons (.refl a) (.cons (.comm op rest b) .nil)))
    (.trans
      (.swap_right op a b rest)
      (.congr (sig.add op) (.cons (.refl b) (.cons (.comm op a rest) .nil))))

def Equality.matrix {Γ s} (op : sig.ACUOp s) (a b c d : Term sig Γ s) :
    Equality sig Γ (add op (add op a b) (add op c d)) (add op (add op a c) (add op b d)) :=
  .trans (.assoc op a b (add op c d))
    (.trans (.congr (sig.add op) (.cons (.refl a) (.cons (.swap_right op b c d) .nil)))
      (.symm (.assoc op a c (add op b d))))

def Equalities.refl {Γ ss} (terms : Terms sig Γ ss) : Equalities sig Γ terms terms :=
  match terms with
  | .nil => .nil
  | .cons a rest => .cons (.refl a) (.refl rest)

def Equality.copies {Γ s} (op : sig.ACUOp s) (k : Nat) {a b : Term sig Γ s}
    (proof : Equality sig Γ a b) : Equality sig Γ (copies op k a) (copies op k b) :=
  match k with
  | 0 => .refl (zero op)
  | k + 1 => .congr (sig.add op) (.cons proof (.cons (.copies op k proof) .nil))

def Equality.copies_zero {Γ s} (op : sig.ACUOp s) : (k : Nat) →
    Equality sig Γ (Substitution.copies op k (zero op)) (zero op)
  | 0 => .refl _
  | k + 1 => .trans (.unit op _) (.copies_zero op k)

def Equality.sum_zero {Γ s} (op : sig.ACUOp s) : {n : Nat} → (coeff : FiniteSharing.Vector n) →
    Equality sig Γ (Sharing.sum op coeff (fun _ => zero op)) (zero op)
  | 0, _ => .refl _
  | _ + 1, coeff => .trans (.congr (sig.add op)
      (.cons (.copies_zero op (coeff 0))
        (.cons (.sum_zero op (fun i => coeff i.succ)) .nil))) (.unit op _)

def Equality.sum_choice {Γ s} (op : sig.ACUOp s) (target : Term sig Γ s) :
    {n : Nat} → (coeff : FiniteSharing.Vector n) → (j : Fin n) → coeff j = 1 →
    Equality sig Γ (Sharing.sum op coeff (fun i => if i = j then target else zero op)) target
  | 0, _, j, _ => Fin.elim0 j
  | _ + 1, coeff, j, degree =>
      Fin.cases (motive := fun j => coeff j = 1 →
        Equality sig Γ (Sharing.sum op coeff (fun i => if i = j then target else zero op)) target)
        (fun degree => by
          simp only [Sharing.sum, if_true, Fin.succ_ne_zero, if_false, degree, Substitution.copies]
          exact .trans (.congr (sig.add op)
            (.cons (.trans (.comm op target _) (.unit op target))
              (.cons (.sum_zero op (fun i => coeff i.succ)) .nil)))
            (.trans (.comm op target _) (.unit op target)))
        (fun j degree => by
          simp only [Sharing.sum, Ne.symm (Fin.succ_ne_zero j), if_false, Fin.succ_inj]
          exact .trans (.congr (sig.add op)
            (.cons (.copies_zero op (coeff 0))
              (.cons (.sum_choice op target (fun i => coeff i.succ) j degree) .nil)))
            (.unit op target)) j degree

def Equality.copies_substitution {Γ Δ s} (op : sig.ACUOp s) (k : Nat)
    (a b : Term sig Γ s) (images : Terms sig Δ Γ)
    (proof : Equality sig Δ (a.subst images) (b.subst images)) :
    Equality sig Δ ((Substitution.copies op k a).subst images)
      ((Substitution.copies op k b).subst images) := by
  rw [copies_subst, copies_subst]
  exact .copies op k proof

/-! ## Optional explicit-family factoring
These declarations support handwritten reference-family certificates. The
maintained producer uses Complete.cover directly instead of enumerating a
reference family in Lean. This is not a second production certification path.
-/
structure Factor {inputs} (source target : Answer sig inputs) where
  parameters : Terms sig source.parameters target.parameters
  images : Equalities sig source.parameters source.images (target.images.subst parameters)

inductive Coverage {inputs : List Sorts} (proposed : List (Answer sig inputs)) : List (Answer sig inputs) → Type where
  | nil : Coverage proposed []
  | cons {source rest} (index : Fin proposed.length)
      (factor : Factor source (proposed.get index)) (tail : Coverage proposed rest) :
      Coverage proposed (source :: rest)


/-! ## Checked side-condition witnesses
These are proof constructors for finite DATA checks, not additional unification
rules. They only package the same elementary proofs used by handwritten terms.
In particular, tableCons proves equality with the EXHAUSTIVE support table, not
merely that its supplied rows are balanced; finCons requires every finite slot.
-/
namespace SideCondition

universe u

/-- Exhaustive finite proof vector: first slot, then ALL remaining slots.
For ATOM, P i is `coeff i = 1 → Complete ...`; no slot may be silently omitted. -/
def finCons {n : Nat} {P : Fin (n + 1) → Sort u}
    (first : P 0) (rest : ∀ i : Fin n, P i.succ) : ∀ i, P i :=
  Fin.cases first rest

/-- A non-one coefficient has no singleton-supplier child. The numerical
inequality is still supplied as a kernel-checked proof, not trusted metadata. -/
def noSupplier {k : Nat} {P : Sort u} (checked : k ≠ 1) : k = 1 → P :=
  fun degree => False.elim (checked degree)

/-- Check one support row componentwise and ALL remaining rows. Function
extensionality is hidden here; the producer still supplies every component check. -/
theorem tableCons {n : Nat} {a b : FiniteSharing.Vector n}
    {as bs : List (FiniteSharing.Vector n)}
    (row : ∀ i, a i = b i) (tail : as = bs) : a :: as = b :: bs :=
  congr (congrArg List.cons (funext row)) tail

/-- Different constructor codes imply different sorted heads. No injectivity
assumption is needed: equal heads would necessarily have equal codes. -/
theorem headsDiffer (profile : Profile sig) {ss tt s}
    (f : sig.Symbol ss s) (g : sig.Symbol tt s)
    (checked : profile.code f ≠ profile.code g) :
    (⟨ss, f⟩ : Σ us, sig.Symbol us s) ≠ ⟨tt, g⟩ :=
  fun same => checked (congrArg (fun x => profile.code x.2) same)

end SideCondition

end Substitution

end DirectCertification
