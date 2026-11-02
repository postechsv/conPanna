import Reflect.Eval
import conPanna.Unification.Certification.AcuSolve
import Mathlib.Tactic.Ring

/-!
Soundness of the ACU step (documentation/reflection-design.md, §3), part A: arithmetic on
the row and the basis. Vectors are functions `Fin N → ℕ` over the unknowns.
-/

namespace Reflect

open Term

section Arith

variable (unk : List Term) (alien : List Bool) (row : List Int) (basis : List (List Nat))

/-- The row coefficient of unknown `j`. -/
def rc (j : Nat) : Int := nthD row j 0

/-- The admissible count vectors: they solve the row, hold each alien at most once, and
never two clashing aliens. -/
def Adm (v : Fin unk.length → ℕ) : Prop :=
  (∑ j : Fin unk.length, rc row j.1 * (v j : Int)) = 0 ∧ (∀ j : Fin unk.length, isAlien alien j = true → v j ≤ 1) ∧
    ∀ j k : Fin unk.length, clashes unk alien j k = true → v j + v k ≤ 1

/-- Basis vector `k` as a function. -/
def bf (k : Nat) (j : Fin unk.length) : ℕ := entry basis k j

theorem nth_eq_getElem? {β} : ∀ (l : List β) (n : Nat), nth l n = l[n]?
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: l, n + 1 => by simp [nth, nth_eq_getElem? l n]

theorem nthD_eq {β} (l : List β) (n : Nat) (d : β) : nthD l n d = l.getD n d := by
  simp [nthD, nth_eq_getElem?, List.getD_eq_getElem?_getD]

theorem nthD_of_lt {β} {l : List β} {n : Nat} (d : β) (h : n < l.length) : nthD l n d = l[n] := by
  simp [nthD, nth_eq_getElem?, List.getElem?_eq_getElem h]

theorem dot_eq_sum : ∀ (r : List Int) (v : List Nat) (n : Nat), r.length = n → v.length = n →
    dot r v = ∑ j : Fin n, nthD r j 0 * ((nthD v j 0 : Nat) : Int)
  | [], [], 0, _, _ => by simp [dot]
  | c :: r, x :: v, n + 1, hr, hv => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hr hv
    rw [Fin.sum_univ_succ, dot, dot_eq_sum r v n hr hv]
    simp [nthD, nth]
  | [], _ :: _, _, hr, hv | _ :: _, [], _, hr, hv => by simp at hr hv; omega
  | [], [], _ + 1, hr, _ | _ :: _, _ :: _, 0, hr, _ => by simp at hr

theorem leV_iff : ∀ (b v : List Nat), b.length = v.length →
    (leV b v = true ↔ ∀ j < b.length, nthD b j 0 ≤ nthD v j 0)
  | [], [], _ => by simp [leV]
  | a :: b, x :: v, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    simp only [leV, Bool.and_eq_true, Nat.ble_eq, leV_iff b v h, List.length_cons]
    constructor
    · rintro ⟨h1, h2⟩ j hj
      cases j with
      | zero => simpa [nthD, nth] using h1
      | succ j => simpa [nthD, nth] using h2 j (by omega)
    · intro h'
      exact ⟨by simpa [nthD, nth] using h' 0 (by omega),
        fun j hj => by simpa [nthD, nth] using h' (j + 1) (by omega)⟩
  | [], _ :: _, h | _ :: _, [], h => by simp at h

theorem nthD_unit2 (m j k i : Nat) (hi : i < m) :
    nthD (unit2 m j k) i 0 = (if i = j then 1 else 0) + (if i = k then 1 else 0) := by
  simp [unit2, nthD_eq, List.getD_eq_getElem?_getD, hi]

end Arith

section Dom

variable {unk : List Term} {alien : List Bool} {row : List Int} {basis : List (List Nat)}

theorem basis_facts (hb : basisOk unk alien row basis = true) (hr : row.length = unk.length) :
    ∀ k < basis.length, (nthD basis k []).length = unk.length ∧ (∃ j : Fin unk.length, bf unk basis k j ≠ 0) ∧
      (∑ j : Fin unk.length, rc row j.1 * (bf unk basis k j : Int)) = 0 ∧
      ∀ j : Fin unk.length, isAlien alien j = true → bf unk basis k j ≤ 1 := by
  intro k hk
  simp only [basisOk, List.all_eq_true, Bool.and_eq_true, beq_iff_eq, List.any_eq_true,
    bne_iff_ne, ne_eq, List.mem_range, Bool.or_eq_true, Bool.not_eq_true', Nat.ble_eq] at hb
  have hbk : nthD basis k [] = basis[k] := nthD_of_lt _ hk
  have hmem : nthD basis k [] ∈ basis := by rw [hbk]; exact List.getElem_mem hk
  obtain ⟨⟨⟨hlen, x, hx, hx0⟩, hdot⟩, hal⟩ := hb _ hmem
  refine ⟨hlen, ?_, ?_, ?_⟩
  · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    refine ⟨⟨i, by omega⟩, ?_⟩
    simp only [bf, entry, bvec]
    rw [nthD_of_lt _ hi]
    exact hx0
  · rw [dot_eq_sum _ _ unk.length hr hlen] at hdot
    simpa [rc, bf, entry, bvec] using hdot
  · intro j hj
    rcases hal j j.2 with h | h
    · simp [hj] at h
    · simpa [bf, entry, bvec] using h

theorem adm_sub (hb : basisOk unk alien row basis = true) (hr : row.length = unk.length)
    {k : Nat} (hk : k < basis.length) {v : Fin unk.length → ℕ} (hv : Adm unk alien row v)
    (hle : bf unk basis k ≤ v) : Adm unk alien row (v - bf unk basis k) := by
  obtain ⟨-, -, hdot, -⟩ := basis_facts hb hr k hk
  obtain ⟨h1, h2, h3⟩ := hv
  refine ⟨?_, fun j hj => le_trans (Nat.sub_le _ _) (h2 j hj),
    fun j j' hjj => le_trans (Nat.add_le_add (Nat.sub_le _ _) (Nat.sub_le _ _)) (h3 j j' hjj)⟩
  simp only [Pi.sub_apply]
  have : ∀ j : Fin unk.length, rc row j.1 * ((v j - bf unk basis k j : ℕ) : Int) =
      rc row j.1 * (v j : Int) - rc row j.1 * (bf unk basis k j : Int) := fun j => by
    rw [Nat.cast_sub (hle j), mul_sub]
  rw [Finset.sum_congr rfl fun j _ => this j, Finset.sum_sub_distrib, h1, hdot, sub_zero]

/-- The single-row argument: a nonzero admissible vector is above a basis vector. -/
theorem dom (hb : basisOk unk alien row basis = true) (hc : completeOk unk alien row basis = true)
    (hr : row.length = unk.length) :
    ∀ v : Fin unk.length → ℕ, Adm unk alien row v → v ≠ 0 →
      ∃ k : Fin basis.length, bf unk basis k ≤ v ∧ Adm unk alien row (v - bf unk basis k) := by
  intro v hv hne
  -- a basis vector below `e_j + e_k` (`k ≠ j`; `k = N` for `e_j` alone) is below `v`
  have hbelow : ∀ (j : Fin unk.length) (k : Nat), k ≠ j.1 → 1 ≤ v j →
      (∀ hk : k < unk.length, 1 ≤ v ⟨k, hk⟩) →
      (∃ b ∈ basis, leV b (unit2 unk.length j k) = true) →
      ∃ k' : Fin basis.length, bf unk basis k' ≤ v ∧ Adm unk alien row (v - bf unk basis k') := by
    intro j k hkj hj hk ⟨b, hbm, hle⟩
    obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hbm
    obtain ⟨hlen, -, -, -⟩ := basis_facts hb hr t ht
    have hbt : nthD basis t [] = basis[t] := nthD_of_lt _ ht
    rw [hbt] at hlen
    have hle' := (leV_iff _ _ (by simp [unit2, hlen])).1 hle
    have hbv : bf unk basis t ≤ v := fun i => by
      have := hle' i (by rw [hlen]; exact i.2)
      rw [nthD_unit2 _ _ _ _ i.2] at this
      simp only [bf, entry, bvec, hbt]
      by_cases hij : i.1 = j.1
      · have : i = j := Fin.ext hij
        subst this
        simp only [ite_true, show ¬ i.1 = k from fun h => hkj (h ▸ rfl), ite_false] at this
        omega
      · by_cases hik : i.1 = k
        · obtain ⟨i, hi⟩ := i
          simp only at hik hij
          subst hik
          simp only [hij, ite_false, ite_true] at this
          have := hk hi
          dsimp only
          omega
        · simp only [hij, hik, ite_false] at this
          omega
    exact ⟨⟨t, ht⟩, hbv, adm_sub hb hr ht hv hbv⟩
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hne
  simp only [Pi.zero_apply] at hj
  simp only [completeOk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hc
  obtain ⟨⟨hcoef, hzero⟩, hpair⟩ := hc
  have hrc : ∀ i : Fin unk.length, rc row i = 0 ∨ rc row i = 1 ∨ rc row i = -1 := fun i => by
    have h := hcoef i i.2
    simp only [Bool.or_eq_true, beq_iff_eq] at h
    rcases h with (h | h) | h <;> simp [rc, h]
  obtain ⟨hsum, -, hcl⟩ := hv
  -- a coefficient `c = ±1` with `v ≥ 1` has a partner of the other sign
  have partner : ∀ c : Int, (c = 1 ∨ c = -1) → rc row j = c →
      ∃ k : Fin unk.length, rc row k = -c ∧ 1 ≤ v k := by
    intro c hc hjc
    by_contra hno
    push_neg at hno
    have hnn : ∀ i ∈ Finset.univ, 0 ≤ c * (rc row i.1 * (v i : Int)) := by
      intro i _
      rcases hrc i with h | h | h <;> rcases hc with rfl | rfl
      · simp [h]
      · simp [h]
      · simp [h]
      · have := hno i (by simp [h]); simp [h, show v i = 0 by omega]
      · have := hno i (by simp [h]); simp [h, show v i = 0 by omega]
      · simp [h]
    have hle := Finset.single_le_sum hnn (Finset.mem_univ j)
    rw [← Finset.mul_sum, hsum, mul_zero, hjc] at hle
    rcases hc with rfl | rfl <;> simp at hle <;> omega
  have above (j' : Fin unk.length) (k : Nat) (h : (basis.any fun b => leV b (unit2 unk.length j' k)) = true) :
      ∃ b ∈ basis, leV b (unit2 unk.length j' k) = true := List.any_eq_true.1 h
  rcases hrc j with h0 | h1 | hm
  · have h := hzero j j.2
    simp only [Bool.or_eq_true, bne_iff_ne, ne_eq] at h
    rcases h with h | h
    · exact absurd (by simpa [rc] using h0) h
    · exact hbelow j unk.length (by omega) (by omega) (fun hk => absurd hk (by omega)) (above _ _ h)
  · obtain ⟨k, hk, hvk⟩ := partner 1 (Or.inl rfl) h1
    have hcl' : clashes unk alien j k = false := by
      cases h : clashes unk alien j k
      · rfl
      · have := hcl j k h; omega
    have h := hpair j j.2 k k.2
    rw [Bool.or_eq_true, Bool.or_eq_true] at h
    rcases h with (h | h) | h
    · simp only [Bool.not_eq_true', Bool.and_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at h
      simp only [rc] at h1 hk
      rcases h with h | h
      · exact absurd h1 h
      · exact absurd hk h
    · rw [hcl'] at h; exact absurd h (by simp)
    · exact hbelow j k (fun h' => by have := Fin.ext h'; subst this; rw [hk] at h1; omega) (by omega)
        (fun _ => hvk) (above _ _ h)
  · obtain ⟨k, hk, hvk⟩ := partner (-1) (Or.inr rfl) hm
    have hcl' : clashes unk alien k j = false := by
      cases h : clashes unk alien k j
      · rfl
      · have := hcl k j h; omega
    have h := hpair k k.2 j j.2
    rw [Bool.or_eq_true, Bool.or_eq_true] at h
    rcases h with (h | h) | h
    · simp only [Bool.not_eq_true', Bool.and_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at h
      simp only [rc] at hm hk
      rcases h with h | h
      · exact absurd (by simpa using hk) h
      · exact absurd hm h
    · rw [hcl'] at h; exact absurd h (by simp)
    · exact hbelow k j (fun h' => by have := Fin.ext h'; subst this; rw [hk] at hm; omega) hvk
        (fun hk' => by rw [Fin.eta]; omega) (above _ _ h)

end Dom

section Row

theorem count_eq (t : Term) : ∀ l : List Term, count t l = l.count t
  | [] => rfl
  | u :: l => by
    simp only [count, count_eq t l, List.count_cons, beq_iff]
    by_cases h : t = u
    · subst h; simp; omega
    · simp [h, Ne.symm h]

theorem foldl_ite_sum (N : Nat) (p : Nat → Prop) [DecidablePred p] (f : Nat → Int) (a : Int) :
    (List.range N).foldl (fun acc j => if p j then acc + f j else acc) a =
      a + ∑ j ∈ (Finset.range N).filter p, f j := by
  induction N generalizing a with
  | zero => simp
  | succ N ih =>
    rw [List.range_succ, List.foldl_append, ih, Finset.range_add_one, Finset.filter_insert]
    simp only [List.foldl_cons, List.foldl_nil]
    by_cases h : p N
    · rw [if_pos h, if_pos h, Finset.sum_insert (by simp)]; ring
    · rw [if_neg h, if_neg h]

/-- The row read at the summands: `Σ_j r_j g(u_j) = Σ_{t ∈ L} g t − Σ_{t ∈ R} g t`. -/
theorem row_identity {f : Nat} {unk : List Term} {row : List Int} {l r : Term}
    (hro : rowOk f unk row l r = true) (g : Term → Int) :
    ∑ j : Fin unk.length, rc row j * g (nthD unk j (var 0)) =
      ((summands f l).map g).sum - ((summands f r).map g).sum := by
  set L := summands f l
  set R := summands f r
  set u : Fin unk.length → Term := fun j => nthD unk j (var 0)
  simp only [rowOk, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at hro
  obtain ⟨hmem, hcnt⟩ := hro
  set D := (L ++ R).toFinset
  have hmaps : ∀ j ∈ (Finset.univ : Finset (Fin unk.length)), u j ∈ D := fun j _ => by
    have := hmem j j.2
    simp only [memT, List.any_eq_true, beq_iff] at this
    obtain ⟨t, ht, he⟩ := this
    simp only [D, List.mem_toFinset]; rw [show u j = t from he]; exact ht
  -- group the unknowns by their term
  have hcoef : ∀ t ∈ D, ∑ j ∈ Finset.univ.filter (fun j : Fin unk.length => u j = t), rc row j =
      (L.count t : Int) - (R.count t : Int) := by
    intro t ht
    have h := hcnt t (by simpa [D] using ht)
    rw [foldl_ite_sum unk.length (fun j => beq (nthD unk j (var 0)) t = true), zero_add,
      count_eq, count_eq] at h
    rw [← h]
    rw [Finset.sum_filter, Finset.sum_filter, ← Fin.sum_univ_eq_sum_range
      (fun j => if beq (nthD unk j (var 0)) t = true then nthD row j 0 else 0)]
    simp only [beq_iff, rc, u]
  calc ∑ j : Fin unk.length, rc row j * g (u j)
      = ∑ t ∈ D, ∑ j ∈ Finset.univ.filter (fun j => u j = t), rc row j * g (u j) :=
        (Finset.sum_fiberwise_of_maps_to hmaps _).symm
    _ = ∑ t ∈ D, ((L.count t : Int) - (R.count t : Int)) * g t := by
        refine Finset.sum_congr rfl fun t ht => ?_
        rw [← hcoef t ht, Finset.sum_mul]
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [(Finset.mem_filter.1 hj).2]
    _ = ∑ t ∈ D, (L.count t : Int) * g t - ∑ t ∈ D, (R.count t : Int) * g t := by
        rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun t _ => by ring
    _ = (L.map g).sum - (R.map g).sum := by
        have key : ∀ K : List Term, K.toFinset ⊆ D →
            ∑ t ∈ D, (K.count t : Int) * g t = (K.map g).sum := by
          intro K hK
          rw [Finset.sum_list_map_count, ← Finset.sum_subset hK (fun t _ ht => by
            simp [List.count_eq_zero_of_not_mem (by simpa using ht)])]
          exact Finset.sum_congr rfl fun t _ => by simp [nsmul_eq_mul]
        rw [key L (fun t ht => by simp only [D, List.mem_toFinset, List.mem_append] at ht ⊢; exact Or.inl ht),
          key R (fun t ht => by simp only [D, List.mem_toFinset, List.mem_append] at ht ⊢; exact Or.inr ht)]

end Row

end Reflect
