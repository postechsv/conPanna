import conPanna.Unification.Certification.Multiset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.List.Sublists
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Ring.Basic
import Mathlib.Data.Fin.VecNotation

/-!
Bags as sums with coefficients, and the decomposition of a multiset solution into basis
vectors with fresh multiset coefficients (`decompose`), the core of ACU-SOLVE's soundness
(AcuSolve.lean). One side of a bag equation over bag variables `X : Fin n → ACU El` and
aliens `a : Fin m → El` is `side L X La a = Σᵢ L i • X i + Σ_c La c • {a c}`.
-/

namespace Unification.Certification

open ACU

universe y

variable {El : Type y}

/-! ## Data -/

/-- `k • X`: `k` copies of `X`. -/
def copies : ℕ → ACU El → ACU El
  | 0, _ => ∅
  | k + 1, X => X + copies k X

@[simp] theorem copies_zero (X : ACU El) : copies 0 X = ∅ := rfl

@[simp] theorem copies_one (X : ACU El) : copies 1 X = X := by
  simp [copies, ACU.plus_unit]

/-- `Σ_j f j`. -/
def sum {k : ℕ} (f : Fin k → ACU El) : ACU El :=
  (List.ofFn f).foldr (· + ·) ∅

/-- One side of a bag equation: `Σᵢ L i • X i + Σ_c La c • {a c}`. -/
def side {n m : ℕ} (L : Fin n → ℕ) (X : Fin n → ACU El)
    (La : Fin m → ℕ) (a : Fin m → El) : ACU El :=
  sum (fun i => copies (L i) (X i)) + sum (fun c => copies (La c) {a c})

/-- `L · v`. -/
def dot {n : ℕ} (L v : Fin n → ℕ) : ℕ := (List.ofFn fun i => L i * v i).sum

/-- Component-wise `p ≤ v`. -/
def Below {n : ℕ} (p v : Fin n → ℕ) : Prop := ∀ i, p i ≤ v i

/-! ## Basic facts -/

variable {n m k : ℕ}

theorem sum_succ (f : Fin (k + 1) → ACU El) : sum f = f 0 + sum (fun j => f j.succ) := by
  simp [sum, List.ofFn_succ]

@[simp] theorem toMultiset_copies (j : ℕ) (X : ACU El) :
    (copies j X).toMultiset = j • X.toMultiset := by
  induction j with
  | zero => simp [copies]
  | succ j ih => simp [copies, ih, succ_nsmul, add_comm]

@[simp] theorem toMultiset_sum (f : Fin k → ACU El) :
    (sum f).toMultiset = ∑ j, (f j).toMultiset := by
  induction k with
  | zero => simp [sum]
  | succ k ih => rw [sum_succ, toMultiset_plus, ih, Fin.sum_univ_succ]

theorem dot_eq (L v : Fin n → ℕ) : dot L v = ∑ i, L i * v i := by
  simp [dot, List.sum_ofFn]

theorem dot_add (L u v : Fin n → ℕ) : dot L (u + v) = dot L u + dot L v := by
  simp [dot_eq, mul_add, Finset.sum_add_distrib]

theorem dot_le (L : Fin n → ℕ) {u v : Fin n → ℕ} (h : Below u v) : dot L u ≤ dot L v := by
  simp only [dot_eq]
  exact Finset.sum_le_sum fun i _ => Nat.mul_le_mul_left _ (h i)

theorem dot_sub (L : Fin n → ℕ) {u v : Fin n → ℕ} (h : Below u v) :
    dot L (v - u) = dot L v - dot L u := by
  have : v = (v - u) + u := funext fun i => by simp [Nat.sub_add_cancel (h i)]
  conv_rhs => rw [this, dot_add]
  omega

theorem dot_listSum {α : Type} (L : Fin n → ℕ) (G : List α) (f : α → Fin n → ℕ) :
    dot L (fun i => (G.map fun c => f c i).sum) = (G.map fun c => dot L (f c)).sum := by
  induction G with
  | nil => simp [dot_eq]
  | cons c G ih =>
    have : (fun i => ((c :: G).map fun c => f c i).sum) = f c + fun i => (G.map fun c => f c i).sum := by
      funext i; simp
    rw [this, dot_add, ih]; simp

theorem listSum_ite {α : Type} (l : List α) (p : α → Prop) [DecidablePred p] (f : α → ℕ) :
    (l.map fun c => if p c then f c else 0).sum = ((l.filter p).map f).sum := by
  induction l with
  | nil => rfl
  | cons c l ih => by_cases h : p c <;> simp [List.filter_cons, h, ih]

theorem finSum_eq_list (f : Fin m → ℕ) : ∑ c, f c = ((List.finRange m).map f).sum := by
  rw [← List.sum_ofFn, List.ofFn_eq_map]

/-! ## Peeling basis vectors (BASIS) -/

section Peel

variable [DecidableEq El]

/-- The count vector of one element across the bag variables. -/
def counts (x : Fin n → Multiset El) (e : El) : Fin n → ℕ := fun i => (x i).count e

/-- Every multiset solution of a homogeneous system is a combination of basis
vectors with fresh multiset coefficients, if every nonzero solution dominates a
nonzero basis vector and stays a solution after subtracting it. -/
theorem decompose (H : (Fin n → ℕ) → Prop) (B : Fin k → Fin n → ℕ)
    (nonzero : ∀ j, B j ≠ 0)
    (dom : ∀ v, H v → v ≠ 0 → ∃ j, B j ≤ v ∧ H (v - B j))
    (x : Fin n → Multiset El) (hx : ∀ e, H (counts x e)) :
    ∃ U : Fin k → Multiset El, ∀ i, x i = ∑ j, B j i • U j := by
  induction h : ∑ i, Multiset.card (x i) using Nat.strong_induction_on generalizing x with
  | _ N ih =>
  by_cases hz : ∀ i, x i = 0
  · exact ⟨0, fun i => by simp [hz i]⟩
  push_neg at hz
  obtain ⟨i₀, hi₀⟩ := hz
  obtain ⟨e, he⟩ := Multiset.exists_mem_of_ne_zero hi₀
  have hv : counts x e ≠ 0 := fun h0 => by
    have := congrFun h0 i₀
    simp only [counts, Pi.zero_apply, Multiset.count_eq_zero] at this
    exact this he
  obtain ⟨j, hle, hH⟩ := dom _ (hx e) hv
  let x' : Fin n → Multiset El := fun i => x i - Multiset.replicate (B j i) e
  have hrep : ∀ i, Multiset.replicate (B j i) e ≤ x i :=
    fun i => Multiset.le_count_iff_replicate_le.mp (hle i)
  have hx' : ∀ e', H (counts x' e') := by
    intro e'
    by_cases he' : e' = e
    · subst he'
      convert hH using 1
      funext i
      simp [counts, x', Multiset.count_sub]
    · convert hx e' using 1
      funext i
      simp [counts, x', Multiset.count_sub, Multiset.count_replicate, Ne.symm he']
  have hlt : ∑ i, Multiset.card (x' i) < N := by
    rw [← h]
    obtain ⟨i₁, hi₁⟩ := Function.ne_iff.mp (nonzero j)
    apply Finset.sum_lt_sum
    · intro i _
      simp [x', Multiset.card_sub (hrep i)]
    · refine ⟨i₁, Finset.mem_univ _, ?_⟩
      have hc := Multiset.card_le_card (hrep i₁)
      simp only [Multiset.card_replicate] at hc
      simp only [x', Multiset.card_sub (hrep i₁), Multiset.card_replicate]
      simp only [Pi.zero_apply] at hi₁
      omega
  obtain ⟨U', hU'⟩ := ih _ hlt x' hx' rfl
  refine ⟨fun j' => U' j' + if j' = j then {e} else 0, fun i => ?_⟩
  simp only [nsmul_add, Finset.sum_add_distrib, smul_ite, nsmul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, ← hU' i, Multiset.nsmul_singleton, x']
  exact (tsub_add_cancel_of_le (hrep i)).symm

end Peel

end Unification.Certification
