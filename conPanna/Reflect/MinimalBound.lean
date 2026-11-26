import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Data.Int.Interval
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# A bound on minimal solutions of a linear Diophantine equation

The equation of an ACU step is `r₁ v₁ + ⋯ + r_k v_k = 0` over `ℕ`, with nonzero integer
coefficients: the multiplicity of a left argument, or minus the multiplicity of a right one.
A solution is *minimal* if it is nonzero and no other nonzero solution lies below it.

`sum_le_of_minimal`: a minimal solution has `v₁ + ⋯ + v_k ≤ 2M`, with `M` the largest
`|rᵢ|`. So the minimal solutions are among the finitely many vectors of total at most `2M`.

Proof. Build `v` one unit at a time from `0`: while the balance `r · w` is `≤ 0`, add a unit
on a positive coordinate, otherwise on a negative one. The balance then stays in `(-M, M]`.
If `v` had more than `2M` units, two steps would start from the same balance, and the units
added between them would be a smaller nonzero solution.
-/

namespace Reflect.MinimalBound

open Finset

variable {k : ℕ}

/-- The balance `r · w`: the left side minus the right side of the equation, at `w`. -/
def balance (r : Fin k → ℤ) (w : Fin k → ℕ) : ℤ := ∑ i, r i * w i

/-- The largest coefficient, in absolute value. -/
def maxCoeff (r : Fin k → ℤ) : ℕ := univ.sup fun i => (r i).natAbs

/-- The total of a vector: its number of units. -/
def total (w : Fin k → ℕ) : ℕ := ∑ i, w i

section

variable {r : Fin k → ℤ}

lemma abs_le_maxCoeff (i : Fin k) : |r i| ≤ maxCoeff r := by
  have : (r i).natAbs ≤ maxCoeff r := le_sup (f := fun i => (r i).natAbs) (mem_univ i)
  rw [Int.abs_eq_natAbs]; exact_mod_cast this

lemma balance_add_unit (w : Fin k → ℕ) (i : Fin k) :
    balance r (w + Pi.single i 1) = balance r w + r i := by
  simp only [balance, Pi.add_apply, Nat.cast_add, mul_add, sum_add_distrib]
  congr 1
  rw [sum_eq_single i (fun j _ hj => by simp [hj]) (by simp)]
  simp

lemma balance_sub {w₁ w₂ : Fin k → ℕ} (h : w₁ ≤ w₂) :
    balance r (w₂ - w₁) = balance r w₂ - balance r w₁ := by
  simp only [balance, Pi.sub_apply, ← sum_sub_distrib, ← mul_sub]
  refine sum_congr rfl fun i _ => ?_
  rw [Nat.cast_sub (h i)]

end

section Walk

variable (r : Fin k → ℤ) (v : Fin k → ℕ)

/-- Coordinate `i` may grow next: it is below `v`, and its coefficient has the sign that
moves the balance back toward `0`. -/
def Candidate (w : Fin k → ℕ) (i : Fin k) : Prop :=
  w i < v i ∧ if balance r w ≤ 0 then 0 < r i else r i < 0

open Classical in
/-- One step of the walk: add a unit on some candidate coordinate, if there is one. -/
noncomputable def step (w : Fin k → ℕ) : Fin k → ℕ :=
  if h : ∃ i, Candidate r v w i then w + Pi.single h.choose 1 else w

/-- The walk from `0`, one unit per step. -/
noncomputable def walk (t : ℕ) : Fin k → ℕ := (step r v)^[t] 0

variable {r v}

lemma walk_zero : walk r v 0 = 0 := rfl

lemma walk_succ (t : ℕ) : walk r v (t + 1) = step r v (walk r v t) :=
  Function.iterate_succ_apply' _ _ _

/-- A step either adds a unit on a candidate coordinate or, if there is none, does nothing. -/
lemma step_cases (w : Fin k → ℕ) :
    (∃ i, Candidate r v w i ∧ step r v w = w + Pi.single i 1) ∨
      ((¬ ∃ i, Candidate r v w i) ∧ step r v w = w) := by
  classical
  by_cases h : ∃ i, Candidate r v w i
  · exact .inl ⟨h.choose, h.choose_spec, by simp [step, h]⟩
  · exact .inr ⟨h, by simp [step, h]⟩

/-- Below a solution `v`, every vector other than `v` has a candidate coordinate: if all
coordinates on the side that should grow were full, the balance would have the wrong sign. -/
lemma candidate_exists (hr : ∀ i, r i ≠ 0) (hv : balance r v = 0)
    {w : Fin k → ℕ} (hw : w ≤ v) (hne : w ≠ v) : ∃ i, Candidate r v w i := by
  by_contra hno
  push_neg at hno
  have key : balance r w = ∑ i, r i * ((w i : ℤ) - v i) := by
    rw [← sub_zero (balance r w), ← hv]
    simp only [balance, ← sum_sub_distrib, mul_sub]
  obtain ⟨j, hj⟩ : ∃ j, w j < v j := by
    by_contra h
    push_neg at h
    exact hne (funext fun i => le_antisymm (hw i) (h i))
  by_cases hb : balance r w ≤ 0
  · -- every positive coordinate is full, so each term is `≥ 0`, and the one at `j` is `> 0`
    have hneg : ∀ i, w i < v i → r i < 0 := fun i hi => by
      have := hno i
      simp only [Candidate, hb, if_true, not_and, not_lt] at this
      exact lt_of_le_of_ne (this hi) (hr i)
    have hpos : 0 < balance r w := by
      rw [key]
      refine sum_pos' (fun i _ => ?_) ⟨j, mem_univ _, ?_⟩
      · rcases lt_or_eq_of_le (hw i) with h | h
        · have h1 := hneg i h
          have h2 : (w i : ℤ) - v i < 0 := sub_neg.mpr (by exact_mod_cast h)
          nlinarith
        · simp [h]
      · have h1 := hneg j hj
        have h2 : (w j : ℤ) - v j < 0 := sub_neg.mpr (by exact_mod_cast hj)
        nlinarith
    omega
  · -- every negative coordinate is full, so each term is `≤ 0`
    have hpos' : ∀ i, w i < v i → 0 < r i := fun i hi => by
      have := hno i
      simp only [Candidate, hb, if_false, not_and, not_lt] at this
      exact lt_of_le_of_ne (this hi) (hr i).symm
    have : balance r w ≤ 0 := by
      rw [key]
      refine sum_nonpos fun i _ => ?_
      rcases lt_or_eq_of_le (hw i) with h | h
      · have h1 := hpos' i h
        have h2 : (w i : ℤ) - v i < 0 := sub_neg.mpr (by exact_mod_cast h)
        nlinarith
      · simp [h]
    exact hb this

lemma walk_le (t : ℕ) : walk r v t ≤ v := by
  induction t with
  | zero => exact fun i => Nat.zero_le _
  | succ t ih =>
    rw [walk_succ]
    rcases step_cases (r := r) (v := v) (walk r v t) with ⟨i, ⟨hi, _⟩, h⟩ | ⟨_, h⟩
    · rw [h]
      intro j
      by_cases hj : j = i
      · subst hj; simp; omega
      · simp [hj]; exact ih j
    · rw [h]; exact ih

lemma walk_mono {t₁ t₂ : ℕ} (h : t₁ ≤ t₂) : walk r v t₁ ≤ walk r v t₂ := by
  induction h with
  | refl => exact le_rfl
  | step _ ih =>
    refine le_trans ih ?_
    rw [walk_succ]
    rcases step_cases (r := r) (v := v) (walk r v _) with ⟨i, _, h⟩ | ⟨_, h⟩
    · rw [h]; exact fun j => Nat.le_add_right _ _
    · rw [h]

/-- Until it reaches `v`, the walk adds exactly one unit per step. -/
lemma total_walk (hr : ∀ i, r i ≠ 0) (hv : balance r v = 0) :
    ∀ t ≤ total v, total (walk r v t) = t := by
  intro t
  induction t with
  | zero => intro _; simp [walk_zero, total]
  | succ t ih =>
    intro ht
    have hlt := ih (by omega)
    have hne : walk r v t ≠ v := fun h => by rw [h] at hlt; omega
    obtain ⟨i, _, hstep⟩ | ⟨hno, _⟩ := step_cases (r := r) (v := v) (walk r v t)
    · rw [walk_succ, hstep]
      simp only [total, Pi.add_apply, sum_add_distrib] at hlt ⊢
      rw [hlt]
      simp
    · exact absurd (candidate_exists hr hv (walk_le t) hne) hno

/-- The balance along the walk stays in `(-M, M]`. -/
lemma balance_walk (hM : 0 < maxCoeff r) (t : ℕ) :
    -(maxCoeff r : ℤ) < balance r (walk r v t) ∧ balance r (walk r v t) ≤ maxCoeff r := by
  induction t with
  | zero => simp [walk_zero, balance]; exact_mod_cast hM
  | succ t ih =>
    rw [walk_succ]
    rcases step_cases (r := r) (v := v) (walk r v t) with ⟨i, ⟨_, hsign⟩, h⟩ | ⟨_, h⟩
    · rw [h, balance_add_unit]
      have hi := abs_le_maxCoeff (r := r) i
      rw [abs_le] at hi
      split_ifs at hsign with hb <;> constructor <;> omega
    · rw [h]; exact ih

end Walk

/-- **The bound.** A minimal solution has at most `2M` units, `M` the largest `|rᵢ|`. -/
theorem total_le_of_minimal {r : Fin k → ℤ} {v : Fin k → ℕ} (hr : ∀ i, r i ≠ 0)
    (hv : balance r v = 0) (hv0 : v ≠ 0)
    (hmin : ∀ w ≤ v, w ≠ 0 → balance r w = 0 → w = v) :
    total v ≤ 2 * maxCoeff r := by
  by_contra hlt
  push_neg at hlt
  set M := maxCoeff r
  have hM : 0 < M := by
    obtain ⟨i, -⟩ : ∃ i, v i ≠ 0 := by
      by_contra h; push_neg at h; exact hv0 (funext h)
    have : (0 : ℤ) < M := lt_of_lt_of_le (abs_pos.mpr (hr i)) (abs_le_maxCoeff i)
    exact_mod_cast this
  -- the balances before steps `0, …, total v - 1` lie in `(-M, M]`, which has `2M` values
  obtain ⟨t₁, ht₁, t₂, ht₂, hne, heq⟩ := exists_ne_map_eq_of_card_lt_of_maps_to
    (s := range (total v)) (t := Ioc (-(M : ℤ)) M) (f := fun t => balance r (walk r v t))
    (by simp; omega)
    (fun t _ => by simpa using balance_walk (v := v) hM t)
  rw [mem_range] at ht₁ ht₂
  -- the units added between the two times form a smaller nonzero solution
  have key : ∀ {a b : ℕ}, a < b → b < total v →
      balance r (walk r v a) = balance r (walk r v b) → False := by
    intro a b hab hb hbal
    have hle : walk r v a ≤ walk r v b := walk_mono hab.le
    set w := walk r v b - walk r v a
    have hw : w ≤ v := fun i => le_trans (Nat.sub_le _ _) (walk_le b i)
    have htot : total w = b - a := by
      have ha' := total_walk hr hv a (by omega)
      have hb' := total_walk hr hv b (by omega)
      simp only [total, w, Pi.sub_apply] at ha' hb' ⊢
      rw [sum_tsub_distrib _ (fun i _ => hle i), ha', hb']
    have hw0 : w ≠ 0 := fun h => by simp [h, total] at htot; omega
    have hbal0 : balance r w = 0 := by rw [balance_sub hle, hbal, sub_self]
    have := congrArg total (hmin w hw hw0 hbal0)
    omega
  rcases lt_or_gt_of_ne hne with h | h
  · exact key h ht₂ heq
  · exact key h ht₁ heq.symm

end Reflect.MinimalBound
