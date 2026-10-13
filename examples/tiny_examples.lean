import Tiny.Expresso.core
import Tiny.conPanna.Unification.Problem
import Mathlib.Data.Multiset.UnionInter

/-!
A generic ACU template first, then two independent examples: Bakery and a
commutative pair. Bakery includes a single-process semantics slice and ACU
process-bag unification examples, not a proof of the full Bakery protocol.
There are no custom tactics or external calls.
-/

/-! ## Generic ACU template (proof-of-concept certification calculus)
Every ACU annotation generates the SAME shape: empty, singleton and an ACU union.
Its normal-form theorem `Bag E ≅ Multiset E` is proved ONCE here, for every
element type `E`; no user model is involved. The calculus rules below are
consequences of that isomorphism. A certificate only selects rules and supplies
witnesses; it never recomputes unifiers.
-/
namespace ACU

universe u

variable {E : Type u}

inductive Raw (E : Type u) where
  | empty
  | singleton (element : E)
  | union (left right : Raw E) -- ACU, with empty as unit

-- The LEAST equivalence closed under union and the ACU axioms.
-- Element equality remains ordinary equality; only union has equations.
inductive B : Raw E → Raw E → Prop where
  | refl (a : Raw E) : B a a
  | symm {a b} : B a b → B b a
  | trans {a b c} : B a b → B b c → B a c
  | congr {a a' b b'} : B a a' → B b b' → B (.union a b) (.union a' b')
  | assoc (a b c) : B (.union (.union a b) c) (.union a (.union b c))
  | comm (a b) : B (.union a b) (.union b a)
  | unit_left (a) : B (.union .empty a) a
  | unit_right (a) : B (.union a .empty) a

def setoid (E : Type u) : Setoid (Raw E) where
  r := B
  iseqv := ⟨B.refl, B.symm, B.trans⟩

abbrev Bag (E : Type u) := Quotient (setoid E)

-- Native operations are precisely the template constructors lifted to the quotient.
def Bag.empty : Bag E := Quotient.mk _ .empty

def Bag.singleton (element : E) : Bag E := Quotient.mk _ (.singleton element)

def Bag.union (left right : Bag E) : Bag E :=
  Quotient.liftOn₂ left right
    (fun a b => Quotient.mk _ (.union a b))
    (fun _ _ _ _ ha hb => Quotient.sound (B.congr ha hb))

/-! ### Normal form, proved once: `Bag E ≅ Multiset E` -/

-- Flattening: the element list of a raw constructor tree.
def Raw.contents : Raw E → List E
  | .empty => []
  | .singleton a => [a]
  | .union a b => a.contents ++ b.contents

-- Rebuilding: a right-nested union of singletons.
def Raw.ofList : List E → Raw E
  | [] => .empty
  | a :: as => .union (.singleton a) (ofList as)

-- (⇒) Every generated ACU step preserves contents up to permutation.
theorem B.perm {a b : Raw E} (h : B a b) : a.contents.Perm b.contents := by
  induction h with
  | refl => exact .refl _
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | congr _ _ ih₁ ih₂ => exact ih₁.append ih₂
  | assoc => exact .of_eq (List.append_assoc _ _ _)
  | comm => exact List.perm_append_comm
  | unit_left => exact .refl _
  | unit_right => exact .of_eq (List.append_nil _)

theorem Raw.contents_ofList (l : List E) : (Raw.ofList l).contents = l := by
  induction l with
  | nil => rfl
  | cons a as ih => simp [Raw.ofList, Raw.contents, ih]

theorem B.ofList_append (l₁ l₂ : List E) :
    B (.ofList (l₁ ++ l₂)) (.union (.ofList l₁) (.ofList l₂)) := by
  induction l₁ with
  | nil => exact B.symm (B.unit_left _)
  | cons a as ih => exact B.trans (B.congr (B.refl _) ih) (B.symm (B.assoc _ _ _))

theorem B.ofList_perm {l₁ l₂ : List E} (h : l₁.Perm l₂) : B (.ofList l₁) (.ofList l₂) := by
  induction h with
  | nil => exact B.refl _
  | cons _ _ ih => exact B.congr (B.refl _) ih
  | swap =>
    exact B.trans (B.symm (B.assoc _ _ _))
      (B.trans (B.congr (B.comm _ _) (B.refl _)) (B.assoc _ _ _))
  | trans _ _ ih₁ ih₂ => exact B.trans ih₁ ih₂

-- Every raw tree is equivalent to the rebuild of its own contents.
theorem B.ofList_contents (a : Raw E) : B a (.ofList a.contents) := by
  induction a with
  | empty => exact B.refl _
  | singleton => exact B.symm (B.unit_right _)
  | union a b iha ihb => exact B.trans (B.congr iha ihb) (B.symm (B.ofList_append _ _))

-- (⇐) Equal contents up to permutation means ACU-equal.
theorem B.of_perm {a b : Raw E} (h : a.contents.Perm b.contents) : B a b :=
  B.trans (B.ofList_contents a) (B.trans (B.ofList_perm h) (B.symm (B.ofList_contents b)))

def Bag.toMultiset (bag : Bag E) : Multiset E :=
  Quotient.liftOn bag (fun a => (a.contents : Multiset E))
    (fun _ _ h => Multiset.coe_eq_coe.mpr (B.perm h))

def Bag.ofMultiset (m : Multiset E) : Bag E :=
  Quotient.liftOn m (fun l => Quotient.mk _ (Raw.ofList l))
    (fun _ _ h => Quotient.sound (B.ofList_perm h))

namespace Bag

@[simp] theorem toMultiset_empty : (empty : Bag E).toMultiset = 0 := rfl

@[simp] theorem toMultiset_singleton (a : E) : (singleton a).toMultiset = {a} := rfl

@[simp] theorem toMultiset_union (X Y : Bag E) :
    (union X Y).toMultiset = X.toMultiset + Y.toMultiset := by
  induction X using Quotient.inductionOn
  induction Y using Quotient.inductionOn
  rfl

@[simp] theorem toMultiset_ofMultiset (m : Multiset E) : (ofMultiset m).toMultiset = m := by
  induction m using Quotient.inductionOn
  exact congrArg _ (Raw.contents_ofList _)

theorem toMultiset_injective : Function.Injective (toMultiset : Bag E → Multiset E) := by
  intro X Y h
  induction X using Quotient.inductionOn
  induction Y using Quotient.inductionOn
  exact Quotient.sound (B.of_perm (Multiset.coe_eq_coe.mp h))

theorem eq_iff {X Y : Bag E} : X = Y ↔ X.toMultiset = Y.toMultiset :=
  toMultiset_injective.eq_iff.symm

/-! ### Calculus rules
Each rule is ONE generic theorem: a structural equality step a certificate may cite.
- ZERO:   a union equals empty only when both parts are empty.
- ATOM:   a union equals a singleton only when one part is it and the other is empty.
- INJ:    singleton is injective; this hands element equations to the element sort.
- CLASH:  a singleton is never empty.
- REFINE: two binary unions are equal only through a 2×2 sharing grid
          (the refinement property of free commutative monoids).
Only REFINE introduces fresh bag variables; a certificate decides which cells to
split further by ZERO/ATOM. These rules cover LINEAR bag equations; nonlinear
ones (a variable occurring twice) are outside this proof of concept.
-/

theorem union_eq_empty {X Y : Bag E} : union X Y = empty ↔ X = empty ∧ Y = empty := by
  simp only [eq_iff, toMultiset_union, toMultiset_empty]
  constructor
  · intro h
    have hc := congrArg Multiset.card h
    simp only [Multiset.card_add, Multiset.card_zero] at hc
    exact ⟨Multiset.card_eq_zero.mp (by omega), Multiset.card_eq_zero.mp (by omega)⟩
  · rintro ⟨h₁, h₂⟩
    simp [h₁, h₂]

theorem union_eq_singleton {X Y : Bag E} {a : E} :
    union X Y = singleton a ↔
      (X = empty ∧ Y = singleton a) ∨ (X = singleton a ∧ Y = empty) := by
  simp only [eq_iff, toMultiset_union, toMultiset_empty, toMultiset_singleton]
  constructor
  · intro h
    have hc := congrArg Multiset.card h
    simp only [Multiset.card_add, Multiset.card_singleton] at hc
    rcases Nat.add_eq_one_iff.mp hc with ⟨h0, _⟩ | ⟨_, h0⟩
    · rw [Multiset.card_eq_zero.mp h0, Multiset.zero_add] at h
      exact Or.inl ⟨Multiset.card_eq_zero.mp h0, h⟩
    · rw [Multiset.card_eq_zero.mp h0, Multiset.add_zero] at h
      exact Or.inr ⟨h, Multiset.card_eq_zero.mp h0⟩
  · rintro (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩) <;> simp [h₁, h₂]

theorem singleton_inj {a b : E} : singleton a = singleton b ↔ a = b := by
  simp [eq_iff]

theorem singleton_ne_empty (a : E) : singleton a ≠ empty := by
  simp [eq_iff]

theorem refine {X Y Z W : Bag E} (h : union X Y = union Z W) :
    ∃ A B C D, X = union A B ∧ Y = union C D ∧ Z = union A C ∧ W = union B D := by
  classical
  have hm := congrArg toMultiset h
  simp only [toMultiset_union] at hm
  let x := X.toMultiset; let y := Y.toMultiset; let z := Z.toMultiset
  -- Fresh grid cells, read off from multiplicities.
  refine ⟨ofMultiset (x ∩ z), ofMultiset (x - z), ofMultiset (z - x),
    ofMultiset (y - (z - x)), ?_, ?_, ?_, ?_⟩ <;>
  · rw [eq_iff]
    ext e
    have he := congrArg (Multiset.count e) hm
    simp only [toMultiset_union, toMultiset_ofMultiset, Multiset.count_add,
      Multiset.count_inter, Multiset.count_sub, x, y, z] at he ⊢
    omega

/-! ### Laws used when checking a cover witness -/

theorem empty_union (X : Bag E) : union empty X = X := by simp [eq_iff]

theorem union_empty (X : Bag E) : union X empty = X := by simp [eq_iff]

theorem union_comm (X Y : Bag E) : union X Y = union Y X := by simp [eq_iff, Multiset.add_comm]

theorem union_assoc (X Y Z : Bag E) : union (union X Y) Z = union X (union Y Z) := by
  simp [eq_iff, Multiset.add_assoc]

end Bag
end ACU

namespace TinyBakery

open Expresso

inductive Mode where
  | idle
  | wait (ticket : Nat)
  | crit (ticket : Nat)

/-! ## Process-bag model
The user's declaration would be
  `inductive RawProcSet | empty | singleton (process : Mode) | union (ACU)`.
That is exactly the generic template at `E := Mode`, so its relation, quotient
and normal form are instances of `ACU`, not rewritten for this model.
There is no idempotence or extra equation on process contents.
-/
abbrev ProcSet := ACU.Bag Mode

abbrev ProcSet.empty : ProcSet := ACU.Bag.empty

abbrev ProcSet.singleton (process : Mode) : ProcSet := ACU.Bag.singleton process

abbrev ProcSet.union (left right : ProcSet) : ProcSet := ACU.Bag.union left right

structure Conf where
  next : Nat
  serving : Nat
  procs : ProcSet

/-! ## Symbolic patterns
`bind` means existential membership, not a concrete choice of ticket.
The condition in an atom belongs to that same ticket assignment.
-/

def initial : Patt Conf :=
  .bind (fun n : Nat => .atom ⟨n, n, ProcSet.singleton .idle⟩)

def waiting : Patt Conf :=
  .bind (fun n : Nat => .atom ⟨n + 1, n, ProcSet.singleton (.wait n)⟩ (n < n + 1))

def critical : Patt Conf :=
  .bind (fun n : Nat => .atom ⟨n + 1, n, ProcSet.singleton (.crit n)⟩ (n < n + 1))

def bakeryInv : Patt Conf :=
  .disj initial (.disj waiting critical)

--#reduce bakeryInv

/-! ## Parameterized rules and their one-step choice
The same bound ticket occurs on both sides and in the rule condition.
`bakerySystem` permits one of the three steps, not their sequential execution.
-/

def wake : System Conf :=
  .bind (fun n : Nat =>
    .rule ⟨n, n, ProcSet.singleton .idle⟩ ⟨n + 1, n, ProcSet.singleton (.wait n)⟩)

def enter : System Conf :=
  .bind (fun n : Nat =>
    .rule ⟨n + 1, n, ProcSet.singleton (.wait n)⟩
      ⟨n + 1, n, ProcSet.singleton (.crit n)⟩ (n < n + 1))

def exit : System Conf :=
  .bind (fun n : Nat =>
    .rule ⟨n + 1, n, ProcSet.singleton (.crit n)⟩ ⟨n + 1, n + 1, ProcSet.singleton .idle⟩)

def bakerySystem : System Conf :=
  .choice wake (.choice enter exit)

/-! ## ACU unification: provided answers and certified completeness
Each proof below is a short certificate in the generic calculus:
  DECOMP (free constructor fields) → REFINE / ATOM / ZERO (ACU) → COVER.
COVER names the provided unifier and its fresh-variable witness, then checks the
remaining equality by ACU laws. No list or multiset reasoning appears here.
-/
open Unification

open ProcSet

-- The original variables are (n, P, Q); n is a free ticket, P and Q are ACU bags.
-- ⟨n + 1, n, union P Q⟩ = ⟨n + 1, n, singleton (wait n)⟩
-- The equation is on native configurations, whose process field is an ACU quotient.
def problem : Problem Conf (Nat × ProcSet × ProcSet) :=
  .bind fun (N?, P?, Q?) =>
    (⟨N? + 1, N?, union P? Q?⟩, ⟨N? + 1, N?, singleton (.wait N?)⟩)

-- Provided answers, not computed by this proof:
-- σ₁: n ↦ u, P ↦ empty, Q ↦ singleton (wait u)
-- σ₂: n ↦ u, P ↦ singleton (wait u), Q ↦ empty
def unifier1 : Unifier (Nat × ProcSet × ProcSet) :=
  .bind (fun u : Nat => .subst ⟨u, empty, singleton (.wait u)⟩)

def unifier2 : Unifier (Nat × ProcSet × ProcSet) :=
  .bind (fun u : Nat => .subst ⟨u, singleton (.wait u), empty⟩)

def solutions : UnifierSet (Nat × ProcSet × ProcSet) := [unifier1, unifier2]

-- Completeness only: every concrete solution is covered by a provided answer.
example : UnifierSet.Complete problem solutions := by
  rintro ⟨N?, P?, Q?⟩ h
  -- DECOMP: `Conf` is free, so its process fields are equal.
  have hprocs : union P? Q? = ProcSet.singleton (.wait N?) := congrArg Conf.procs h
  -- ATOM: one side holds the process, the other is empty.
  rcases ACU.Bag.union_eq_singleton.mp hprocs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  -- COVER: (answer, fresh witness u := N).
  · exact ⟨unifier1, List.Mem.head _, N?, rfl⟩
  · exact ⟨unifier2, List.Mem.tail _ (List.Mem.head _), N?, rfl⟩

/-! ### A problem needing REFINE: unknown bags on both sides
`union P Q = union (singleton (wait n)) R`, original variables (n, P, Q, R).
Provided answers, each with fresh bags B and D:
  σ₁: P ↦ B,                       Q ↦ union (singleton (wait n)) D, R ↦ union B D
  σ₂: P ↦ union (singleton (wait n)) B, Q ↦ D,                       R ↦ union B D
-/
def problem2 : Problem ProcSet (Nat × ProcSet × ProcSet × ProcSet) :=
  .bind fun (N, P, Q, R) => (union P Q, union (singleton (.wait N)) R)

def unifier2_1 : Unifier (Nat × ProcSet × ProcSet × ProcSet) :=
  .bind (fun (u, B, D) => .subst ⟨u, B, union (singleton (.wait u)) D, union B D⟩)

def unifier2_2 : Unifier (Nat × ProcSet × ProcSet × ProcSet) :=
  .bind (fun (u, B, D) => .subst ⟨u, union (singleton (.wait u)) B, D, union B D⟩)

def solutions2 : UnifierSet (Nat × ProcSet × ProcSet × ProcSet) := [unifier2_1, unifier2_2]

example : UnifierSet.Complete problem2 solutions2 := by
  rintro ⟨N, P, Q, R⟩ h
  have h : union P Q = union (ProcSet.singleton (.wait N)) R := h
  -- REFINE: a 2×2 grid A B / C D with P = A∪B, Q = C∪D, {wait N} = A∪C, R = B∪D.
  obtain ⟨A, B, C, D, rfl, rfl, hw, rfl⟩ := ACU.Bag.refine h
  -- ATOM on the only ground cell column.
  rcases ACU.Bag.union_eq_singleton.mp hw.symm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  -- COVER: (answer, fresh witness (u, B, D)), then an ACU unit law.
  · exact ⟨unifier2_1, List.Mem.head _, (N, B, D), by simp [Unifier.Covers, ACU.Bag.empty_union]⟩
  · exact ⟨unifier2_2, List.Mem.tail _ (List.Mem.head _), (N, B, D),
      by simp [Unifier.Covers, ACU.Bag.empty_union]⟩

end TinyBakery
