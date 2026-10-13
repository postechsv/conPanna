import Tiny.Expresso.ACU
import Mathlib.Data.Multiset.UnionInter

/-!
The bridge `ACU E ≅ Multiset E` and the structural bag facts proved through it.
Certification works on element counts; this file is where ACU values meet
Mathlib's multisets. Here `+` on `ACU E` corresponds to `+` on `Multiset E`
(counts add); Mathlib's `∪` (maximum of counts) plays no role.
-/

namespace ACU

universe u

variable {E : Type u}

def toMultiset (X : ACU E) : Multiset E :=
  Quotient.liftOn X (fun a => (a.contents : Multiset E))
    (fun _ _ h => Multiset.coe_eq_coe.mpr (Equiv.perm h))

def ofMultiset (m : Multiset E) : ACU E :=
  Quotient.liftOn m (fun l => Quotient.mk _ (Ctor.ofList l))
    (fun _ _ h => Quotient.sound (Equiv.ofList_perm h))

@[simp] theorem toMultiset_unit : (∅ : ACU E).toMultiset = 0 := rfl

@[simp] theorem toMultiset_elem (a : E) : ({a} : ACU E).toMultiset = {a} := rfl

@[simp] theorem toMultiset_plus (X Y : ACU E) :
    (X + Y).toMultiset = X.toMultiset + Y.toMultiset := by
  induction X using Quotient.inductionOn
  induction Y using Quotient.inductionOn
  rfl

@[simp] theorem toMultiset_ofMultiset (m : Multiset E) : (ofMultiset m).toMultiset = m := by
  induction m using Quotient.inductionOn
  exact congrArg _ (Ctor.contents_ofList _)

theorem toMultiset_injective : Function.Injective (toMultiset : ACU E → Multiset E) := by
  intro X Y h
  induction X using Quotient.inductionOn
  induction Y using Quotient.inductionOn
  exact Quotient.sound (Equiv.of_perm (Multiset.coe_eq_coe.mp h))

theorem eq_iff {X Y : ACU E} : X = Y ↔ X.toMultiset = Y.toMultiset :=
  toMultiset_injective.eq_iff.symm

/-! ## Structural bag facts
These are the special cases of SOLVE used by the current examples.
-/

theorem plus_eq_unit {X Y : ACU E} : X + Y = ∅ ↔ X = ∅ ∧ Y = ∅ := by
  simp only [eq_iff, toMultiset_plus, toMultiset_unit]
  constructor
  · intro h
    have hc := congrArg Multiset.card h
    simp only [Multiset.card_add, Multiset.card_zero] at hc
    exact ⟨Multiset.card_eq_zero.mp (by omega), Multiset.card_eq_zero.mp (by omega)⟩
  · rintro ⟨h₁, h₂⟩
    simp [h₁, h₂]

theorem plus_eq_elem {X Y : ACU E} {a : E} :
    X + Y = {a} ↔ (X = ∅ ∧ Y = {a}) ∨ (X = {a} ∧ Y = ∅) := by
  simp only [eq_iff, toMultiset_plus, toMultiset_unit, toMultiset_elem]
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

theorem elem_inj {a b : E} : ({a} : ACU E) = {b} ↔ a = b := by
  simp [eq_iff]

theorem elem_ne_unit (a : E) : ({a} : ACU E) ≠ ∅ := by
  simp [eq_iff]

/-- Refinement: two equal sums split into a common 2×2 grid of pieces. -/
theorem refine {X Y Z W : ACU E} (h : X + Y = Z + W) :
    ∃ A B C D, X = A + B ∧ Y = C + D ∧ Z = A + C ∧ W = B + D := by
  classical
  have hm := congrArg toMultiset h
  simp only [toMultiset_plus] at hm
  let x := X.toMultiset; let y := Y.toMultiset; let z := Z.toMultiset
  -- The grid cells are read off from element counts.
  refine ⟨ofMultiset (x ∩ z), ofMultiset (x - z), ofMultiset (z - x),
    ofMultiset (y - (z - x)), ?_, ?_, ?_, ?_⟩ <;>
  · rw [eq_iff]
    ext e
    have he := congrArg (Multiset.count e) hm
    simp only [toMultiset_plus, toMultiset_ofMultiset, Multiset.count_add,
      Multiset.count_inter, Multiset.count_sub, x, y, z] at he ⊢
    omega

end ACU
