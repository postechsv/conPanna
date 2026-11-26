import conPanna.Reflect.Eval
import conPanna.Reflect.MinimalBound
import conPanna.Unification.Certification.Solve
import Mathlib.Tactic.Ring

/-!
Soundness of the ACU step, part A: the arithmetic of the computed basis and selections
(`Dio` in `Check.lean`). Vectors are functions `Fin N → ℕ` over the arguments.
-/

namespace Reflect

open Term

section Arith

variable (sh : Dio)

/-- The multiplicity of argument `j`. -/
def rc (j : Nat) : Int := nthD sh.mults j 0

/-- The admissible count vectors (`Adm(s,t)` without its bound): they solve the equation,
hold a non-variable argument at most once, and never two clashing ones. -/
def Adm (n : Nat) (v : Fin n → ℕ) : Prop :=
  (∑ j : Fin n, rc sh j * (v j : Int)) = 0 ∧
  (∀ j : Fin n, nthD sh.nonVar j false = true → v j ≤ 1) ∧
  ∀ i j : Fin n, nthD sh.nonVar i false = true → nthD sh.nonVar j false = true →
    sh.clash i j = true → v i = 0 ∨ v j = 0

/-- Basis element `k` as a function. -/
def bf (n k : Nat) (j : Fin n) : ℕ := nthD (nthD sh.basis k []) j 0

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

theorem mem_vectorsUpTo : ∀ (n b : Nat) (v : List Nat),
    v ∈ Dio.vectorsUpTo n b ↔ v.length = n ∧ v.sum ≤ b
  | 0, b, v => by cases v <;> simp [Dio.vectorsUpTo]
  | n + 1, b, v => by
    cases v with
    | nil => simp [Dio.vectorsUpTo]
    | cons x v =>
      simp only [Dio.vectorsUpTo, List.mem_flatMap, List.mem_range, List.mem_map,
        List.length_cons, List.sum_cons, Nat.add_right_cancel_iff]
      constructor
      · rintro ⟨y, hy, w, hw, h⟩
        injection h with h1 h2
        subst h1 h2
        rw [mem_vectorsUpTo n (b - y) w] at hw
        omega
      · rintro ⟨hl, hs⟩
        exact ⟨x, by omega, v, (mem_vectorsUpTo n (b - x) v).2 ⟨hl, by omega⟩, rfl⟩

end Arith

section Basis

variable {sh : Dio}

theorem nthD_ofFn {n : Nat} (w : Fin n → ℕ) (j : Fin n) : nthD (List.ofFn w) j 0 = w j := by
  rw [nthD_of_lt _ (by simp)]; simp

/-- A basis element is a nonzero solution, at most 1 at non-variable arguments. -/
theorem basis_facts {n : Nat} (hn : sh.size = n) : ∀ k < sh.basis.length,
    (nthD sh.basis k []).length = n ∧ (∃ j, bf sh n k j ≠ 0) ∧
      (∑ j : Fin n, rc sh j * (bf sh n k j : Int)) = 0 ∧
      ∀ j : Fin n, nthD sh.nonVar j false = true → bf sh n k j ≤ 1 := by
  subst hn
  intro k hk
  have hz : nthD sh.basis k [] ∈ sh.adm := by
    rw [nthD_of_lt _ hk]
    exact (List.mem_filter.1 (List.getElem_mem hk)).1
  simp only [Dio.adm, List.mem_filter, Bool.and_eq_true, List.any_eq_true, bne_iff_ne] at hz
  obtain ⟨hvec, ⟨x, hx, hx0⟩, hadm⟩ := hz
  obtain ⟨hlen, -⟩ := (mem_vectorsUpTo _ _ _).1 hvec
  simp only [Dio.admissible, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hadm
  obtain ⟨⟨hdot, hone⟩, -⟩ := hadm
  refine ⟨hlen, ?_, ?_, ?_⟩
  · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    exact ⟨⟨i, by omega⟩, by simpa [bf, nthD_of_lt _ hi] using hx0⟩
  · rw [dot_eq_sum _ _ sh.size rfl hlen] at hdot
    simpa [rc, bf] using hdot
  · intro j hj
    by_cases h0 : bf sh sh.size k j = 0
    · omega
    · have hm : (j : Nat) ∈ sh.marked (nthD sh.basis k []) := by
        simp only [Dio.marked, List.mem_filter, List.mem_range, Bool.and_eq_true, bne_iff_ne]
        exact ⟨j.2, hj, h0⟩
      have := hone j hm
      simp only [bf] at this ⊢; omega

theorem adm_sub {n : Nat} (hn : sh.size = n) {k : Nat} (hk : k < sh.basis.length)
    {v : Fin n → ℕ} (hv : Adm sh n v) (hle : bf sh n k ≤ v) : Adm sh n (v - bf sh n k) := by
  obtain ⟨-, -, hdot, -⟩ := basis_facts hn k hk
  obtain ⟨h1, h2, h3⟩ := hv
  refine ⟨?_, fun j hj => le_trans (Nat.sub_le _ _) (h2 j hj), fun i j hi hj hc => ?_⟩
  · simp only [Pi.sub_apply]
    have : ∀ j : Fin n, rc sh j * ((v j - bf sh n k j : ℕ) : Int) =
        rc sh j * (v j : Int) - rc sh j * (bf sh n k j : Int) := fun j => by
      rw [Nat.cast_sub (hle j), mul_sub]
    rw [Finset.sum_congr rfl fun j _ => this j, Finset.sum_sub_distrib, h1, hdot, sub_zero]
  · rcases h3 i j hi hj hc with h | h
    · left; simp [h]
    · right; simp [h]

/-- Below any `P`-vector lies a minimal one. -/
theorem exists_minimal_below {n : Nat} (P : (Fin n → ℕ) → Prop) :
    ∀ v, P v → ∃ w ≤ v, P w ∧ ∀ u ≤ w, P u → u = w := by
  intro v
  induction h : MinimalBound.total v using Nat.strong_induction_on generalizing v with
  | _ t ih =>
    intro hv
    by_cases hmin : ∀ u ≤ v, P u → u = v
    · exact ⟨v, le_rfl, hv, hmin⟩
    · push_neg at hmin
      obtain ⟨u, hu, hPu, hne⟩ := hmin
      have hlt : MinimalBound.total u < t := by
        rw [← h]
        obtain ⟨j, hj⟩ : ∃ j, u j ≠ v j := Function.ne_iff.1 hne
        exact Finset.sum_lt_sum (fun i _ => hu i) ⟨j, Finset.mem_univ _, lt_of_le_of_ne (hu j) hj⟩
      obtain ⟨w, hw, hPw, hmw⟩ := ih _ hlt u rfl hPu
      exact ⟨w, le_trans hw hu, hPw, hmw⟩

theorem natAbs_le_maxMult (sh : Dio) (j : Fin sh.size) : (rc sh j).natAbs ≤ sh.maxMult := by
  have key : ∀ (l : List Int) (m : Nat), m ≤ l.foldl (fun m a => max m a.natAbs) m ∧
      ∀ a ∈ l, a.natAbs ≤ l.foldl (fun m a => max m a.natAbs) m := by
    intro l
    induction l with
    | nil => intro m; simp
    | cons a l ih =>
      intro m
      obtain ⟨h1, h2⟩ := ih (max m a.natAbs)
      refine ⟨le_trans (le_max_left _ _) h1, fun b hb => ?_⟩
      rcases List.mem_cons.1 hb with rfl | hb
      · exact le_trans (le_max_right _ _) h1
      · exact h2 b hb
  have hj : nthD sh.mults j 0 ∈ sh.mults := by rw [nthD_of_lt _ j.2]; exact List.getElem_mem _
  exact (key sh.mults 0).2 _ hj

/-- **The basis is complete**: every nonzero admissible vector lies above a basis element.
Below it lies a minimal nonzero solution, which is admissible, within the bound
(`MinimalBound.total_le_of_minimal`), hence in `Adm(s,t)` and minimal there. -/
theorem dom {n : Nat} (hn : sh.size = n) (hr : ∀ j : Fin n, rc sh j ≠ 0) :
    ∀ v : Fin n → ℕ, Adm sh n v → v ≠ 0 → ∃ k : Fin sh.basis.length, bf sh n k ≤ v := by
  subst hn
  intro v hv hv0
  let r : Fin sh.size → ℤ := fun j => rc sh j
  let P : (Fin sh.size → ℕ) → Prop := fun u => u ≠ 0 ∧ MinimalBound.balance r u = 0
  obtain ⟨w, hwv, ⟨hw0, hwbal⟩, hwmin⟩ := exists_minimal_below P v ⟨hv0, hv.1⟩
  -- `w` is admissible, as it lies below `v`
  have hwadm : Adm sh sh.size w := ⟨hwbal, fun j hj => le_trans (hwv j) (hv.2.1 j hj),
    fun i j hi hj hc => by
      rcases hv.2.2 i j hi hj hc with h | h
      · left; have h1 : w i ≤ v i := hwv i; rw [h] at h1; exact Nat.le_zero.mp h1
      · right; have h1 : w j ≤ v j := hwv j; rw [h] at h1; exact Nat.le_zero.mp h1⟩
  -- `w` is within the bound
  have hbound : MinimalBound.total w ≤ 2 * sh.maxMult := by
    have := MinimalBound.total_le_of_minimal (r := r) hr hwbal hw0
      (fun u hu hu0 hub => hwmin u hu ⟨hu0, hub⟩)
    have hM : MinimalBound.maxCoeff r ≤ sh.maxMult :=
      Finset.sup_le fun j _ => natAbs_le_maxMult sh j
    omega
  -- so `w`, as a list, is in `Adm(s,t)`
  set l := List.ofFn w with hl
  have hlen : l.length = sh.size := by simp [l]
  have hdot : dot sh.mults l = 0 := by
    rw [dot_eq_sum _ _ sh.size rfl hlen]
    simpa [l, nthD_ofFn, rc] using hwbal
  have hmarked : ∀ j ∈ sh.marked l, j < sh.size ∧ nthD sh.nonVar j false = true ∧
      nthD l j 0 ≠ 0 := by
    intro j hj
    simpa [Dio.marked, List.mem_filter, List.mem_range] using hj
  have hadm : sh.admissible l = true := by
    simp only [Dio.admissible, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, hdot,
      Bool.not_eq_true', true_and]
    refine ⟨fun j hj => ?_, fun i hi j hj => ?_⟩
    · obtain ⟨hjN, hjv, hj0⟩ := hmarked j hj
      have := hwadm.2.1 ⟨j, hjN⟩ hjv
      rw [hl, nthD_ofFn w ⟨j, hjN⟩] at hj0 ⊢
      omega
    · obtain ⟨hiN, hiv, hi0⟩ := hmarked i hi
      obtain ⟨hjN, hjv, hj0⟩ := hmarked j hj
      cases hc : sh.clash i j
      · rfl
      · rw [hl, nthD_ofFn w ⟨i, hiN⟩] at hi0
        rw [hl, nthD_ofFn w ⟨j, hjN⟩] at hj0
        rcases hwadm.2.2 ⟨i, hiN⟩ ⟨j, hjN⟩ hiv hjv hc with h | h <;> contradiction
  have hladm : l ∈ sh.adm := by
    simp only [Dio.adm, List.mem_filter, Bool.and_eq_true, List.any_eq_true, bne_iff_ne]
    refine ⟨(mem_vectorsUpTo _ _ _).2 ⟨hlen, ?_⟩, ?_, hadm⟩
    · simpa [l, List.sum_ofFn, MinimalBound.total] using hbound
    · obtain ⟨j, hj⟩ := Function.ne_iff.1 hw0
      exact ⟨w j, by simp [l], hj⟩
  -- and minimal there: a smaller element would be a smaller nonzero solution
  have hlmin : l ∈ sh.basis := by
    refine List.mem_filter.2 ⟨hladm, ?_⟩
    simp only [Bool.not_eq_true', List.any_eq_false, Bool.and_eq_true, not_and, bne_iff_ne,
      ne_eq, Decidable.not_not]
    intro u hu hle
    simp only [Dio.adm, List.mem_filter, Bool.and_eq_true, List.any_eq_true, bne_iff_ne] at hu
    obtain ⟨hvec, ⟨x, hx, hx0⟩, hua⟩ := hu
    obtain ⟨hulen, -⟩ := (mem_vectorsUpTo _ _ _).1 hvec
    simp only [Dio.admissible, Bool.and_eq_true, beq_iff_eq] at hua
    let u' : Fin sh.size → ℕ := fun j => nthD u j 0
    have hu'le : u' ≤ w := fun j => by
      have := (leV_iff u l (by rw [hulen, hlen])).1 hle j (by rw [hulen]; exact j.2)
      simpa [u', l, nthD_ofFn] using this
    have hu'0 : u' ≠ 0 := fun h => by
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
      have := congrFun h ⟨i, by omega⟩
      simp [u', nthD_of_lt _ hi] at this
      exact hx0 this
    have hu'bal : MinimalBound.balance r u' = 0 := by
      have := hua.1.1
      rw [dot_eq_sum _ _ sh.size rfl hulen] at this
      simpa [MinimalBound.balance, r, u', rc] using this
    have heq := hwmin u' hu'le ⟨hu'0, hu'bal⟩
    apply List.ext_getElem (by rw [hulen, hlen])
    intro j h1 h2
    have := congrFun heq ⟨j, by omega⟩
    simpa [u', l, nthD_of_lt _ h1] using this
  obtain ⟨k, hk, hkl⟩ := List.getElem_of_mem hlmin
  refine ⟨⟨k, hk⟩, fun j => ?_⟩
  have : bf sh sh.size k j = w j := by simp [bf, nthD_of_lt _ hk, hkl, l, nthD_ofFn]
  rw [this]; exact hwv j

/-! ### Selections: every exact cover is enumerated -/

theorem covers_complete (cands : List Nat) (marks : Nat → List Nat) :
    ∀ (fuel : Nat) (todo C : List Nat), todo.length ≤ fuel → C ⊆ cands → C.Nodup →
      (∀ k ∈ C, marks k ≠ [] ∧ ∀ q ∈ marks k, q ∈ todo) →
      (∀ p ∈ todo, C.countP (fun k => (marks k).contains p) = 1) →
      ∃ L ∈ Dio.covers cands marks fuel todo, L.Perm C := by
  intro fuel
  induction fuel with
  | zero =>
    intro todo C hlen _ _ hmk _
    cases todo with
    | cons => simp at hlen
    | nil =>
      cases C with
      | nil => exact ⟨[], by simp [Dio.covers], .refl _⟩
      | cons k _ =>
        obtain ⟨hne, hsub⟩ := hmk k (by simp)
        obtain ⟨q, hq⟩ := List.exists_mem_of_ne_nil _ hne
        exact absurd (hsub q hq) (by simp)
  | succ fuel ih =>
    intro todo C hlen hC hnd hmk hcount
    cases todo with
    | nil =>
      cases C with
      | nil => exact ⟨[], by simp [Dio.covers], .refl _⟩
      | cons k _ =>
        obtain ⟨hne, hsub⟩ := hmk k (by simp)
        obtain ⟨q, hq⟩ := List.exists_mem_of_ne_nil _ hne
        exact absurd (hsub q hq) (by simp)
    | cons p rest =>
      -- the element `c` of `C` covering `p`
      obtain ⟨c, hcC, hcp⟩ : ∃ c ∈ C, (marks c).contains p := by
        have := hcount p (by simp)
        by_contra h
        push_neg at h
        rw [List.countP_eq_zero.2 (by simpa using h)] at this
        simp at this
      have hperm : C.Perm (c :: C.erase c) := List.perm_cons_erase hcC
      have hsplit : ∀ q, C.countP (fun k => (marks k).contains q) =
          (if (marks c).contains q then 1 else 0) +
            (C.erase c).countP (fun k => (marks k).contains q) :=
        fun q => by rw [hperm.countP_eq, List.countP_cons]; split <;> simp_all <;> omega
      -- no other element of `C` marks a position that `c` marks
      have hdisj : ∀ k ∈ C.erase c, ∀ q ∈ marks k, ¬ (marks c).contains q := by
        intro k hk q hq hcq
        have h1 := hcount q ((hmk k (List.mem_of_mem_erase hk)).2 q hq)
        have h2 : 0 < (C.erase c).countP (fun k => (marks k).contains q) :=
          List.countP_pos_iff.2 ⟨k, hk, by simpa using hq⟩
        rw [hsplit q, if_pos hcq] at h1
        omega
      -- cover the remaining positions with the remaining elements
      set todo' := (p :: rest).filter (!(marks c).contains ·)
      obtain ⟨L', hL', hperm'⟩ := ih todo' (C.erase c)
        (by
          have : todo'.length ≤ rest.length := by
            simp only [todo', List.filter_cons, hcp, Bool.not_true, Bool.false_eq_true, ite_false]
            exact List.length_filter_le _ _
          simp at hlen; omega)
        (fun k hk => hC (List.mem_of_mem_erase hk))
        (hnd.erase c)
        (fun k hk => ⟨(hmk k (List.mem_of_mem_erase hk)).1, fun q hq =>
          List.mem_filter.2 ⟨(hmk k (List.mem_of_mem_erase hk)).2 q hq,
            by simpa using hdisj k hk q hq⟩⟩)
        (fun q hq => by
          obtain ⟨hq1, hq2⟩ := List.mem_filter.1 hq
          have := hcount q hq1
          rw [hsplit q, if_neg (by simpa using hq2)] at this
          omega)
      refine ⟨c :: L', ?_, (hperm'.cons c).trans hperm.symm⟩
      simp only [Dio.covers, List.mem_flatMap, List.mem_filter, List.mem_map]
      refine ⟨c, ⟨hC hcC, ?_⟩, L', hL', rfl⟩
      simp only [Bool.and_eq_true, hcp, true_and, List.all_eq_true]
      exact fun q hq => by simpa using (hmk c hcC).2 q hq

theorem countP_eq_sum {β} (P : β → Bool) : ∀ l : List β,
    l.countP P = (l.map fun x => if P x then 1 else 0).sum
  | [] => rfl
  | x :: l => by rw [List.countP_cons, countP_eq_sum P l]; simp [Nat.add_comm]

/-- Basis element `k` marks the non-variable arguments where it is nonzero. -/
theorem mem_marked {k j : Nat} :
    j ∈ sh.marked (nthD sh.basis k []) ↔
      j < sh.size ∧ nthD sh.nonVar j false = true ∧ nthD (nthD sh.basis k []) j 0 ≠ 0 := by
  simp [Dio.marked]

/-- **Every selection is enumerated**: the elements marking no non-variable argument, plus
any choice `T` of the others in which each non-variable argument is marked exactly once. -/
theorem selections_complete {T : List Nat} (hT : T.Nodup)
    (hTk : ∀ k ∈ T, k < sh.basis.length ∧ sh.marked (nthD sh.basis k []) ≠ [])
    (hcov : ∀ j < sh.size, nthD sh.nonVar j false = true →
      (T.map fun k => nthD (nthD sh.basis k []) j 0).sum = 1) :
    ∃ S ∈ sh.selections, S.Perm
      ((List.range sh.basis.length).filter (fun k => (sh.marked (nthD sh.basis k [])).isEmpty)
        ++ T) := by
  set marks := fun k => sh.marked (nthD sh.basis k [])
  obtain ⟨L, hL, hperm⟩ := covers_complete
    ((List.range sh.basis.length).filter fun k => !(marks k).isEmpty) marks
    sh.nonVarPositions.length sh.nonVarPositions T le_rfl
    (fun k hk => List.mem_filter.2 ⟨List.mem_range.2 (hTk k hk).1,
      by simpa [marks] using (hTk k hk).2⟩)
    hT
    (fun k hk => ⟨(hTk k hk).2, fun q hq => by
      obtain ⟨hqN, hqv, -⟩ := mem_marked.1 hq
      simp [Dio.nonVarPositions, hqN, hqv]⟩)
    (fun p hp => by
      simp only [Dio.nonVarPositions, List.mem_filter, List.mem_range] at hp
      obtain ⟨hpN, hpv⟩ := hp
      rw [← hcov p hpN hpv, countP_eq_sum]
      congr 1
      refine List.map_congr_left fun k hk => ?_
      have h1 := (basis_facts rfl k (hTk k hk).1).2.2.2 ⟨p, hpN⟩ hpv
      simp only [bf] at h1
      by_cases h0 : nthD (nthD sh.basis k []) p 0 = 0
      · simp [marks, Dio.marked, h0]
      · have : nthD (nthD sh.basis k []) p 0 = 1 := by omega
        simp [marks, Dio.marked, hpN, hpv, this])
  exact ⟨_ ++ L, List.mem_map.2 ⟨L, hL, rfl⟩, hperm.append_left _⟩

end Basis

section Row

theorem count_eq (t : Term) : ∀ l : List Term, count t l = l.count t
  | [] => rfl
  | u :: l => by
    simp only [count, count_eq t l, List.count_cons, beq_iff]
    by_cases h : t = u
    · subst h; simp; omega
    · simp [h, Ne.symm h]

/-- The row read at the summands: `Σ_j r_j g(u_j) = Σ_{t ∈ L} g t − Σ_{t ∈ R} g t`, given that
every unknown is a summand and the coefficients of each summand add up to its occurrences on
the left minus those on the right. -/
theorem row_identity {f : Nat} {unk : List Term} {row : List Int} {l r : Term}
    (hmem : ∀ j < unk.length, nthD unk j (var 0) ∈ summands f l ++ summands f r)
    (hcnt : ∀ t ∈ summands f l ++ summands f r,
      ∑ j ∈ Finset.univ.filter (fun j : Fin unk.length => nthD unk j (var 0) = t), nthD row j 0 =
        ((summands f l).count t : Int) - ((summands f r).count t : Int))
    (g : Term → Int) :
    ∑ j : Fin unk.length, nthD row j 0 * g (nthD unk j (var 0)) =
      ((summands f l).map g).sum - ((summands f r).map g).sum := by
  set L := summands f l
  set R := summands f r
  set u : Fin unk.length → Term := fun j => nthD unk j (var 0)
  set D := (L ++ R).toFinset
  have hmaps : ∀ j ∈ (Finset.univ : Finset (Fin unk.length)), u j ∈ D := fun j _ => by
    simpa [D] using hmem j j.2
  calc ∑ j : Fin unk.length, nthD row j 0 * g (u j)
      = ∑ t ∈ D, ∑ j ∈ Finset.univ.filter (fun j => u j = t), nthD row j 0 * g (u j) :=
        (Finset.sum_fiberwise_of_maps_to hmaps _).symm
    _ = ∑ t ∈ D, ((L.count t : Int) - (R.count t : Int)) * g t := by
        refine Finset.sum_congr rfl fun t ht => ?_
        rw [← hcnt t (by simpa [D] using ht), Finset.sum_mul]
        refine Finset.sum_congr rfl fun j hj => ?_
        simp only [u, (Finset.mem_filter.1 hj).2]
    _ = ∑ t ∈ D, (L.count t : Int) * g t - ∑ t ∈ D, (R.count t : Int) * g t := by
        rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun t _ => by ring
    _ = (L.map g).sum - (R.map g).sum := by
        have key : ∀ K : List Term, K.toFinset ⊆ D →
            ∑ t ∈ D, (K.count t : Int) * g t = (K.map g).sum := by
          intro K hK
          rw [Finset.sum_list_map_count, ← Finset.sum_subset hK (fun t _ ht => by
            simp [List.count_eq_zero_of_not_mem (by simpa using ht)])]
          exact Finset.sum_congr rfl fun t _ => by simp
        rw [key L (fun t ht => by simp only [D, List.mem_toFinset, List.mem_append] at ht ⊢; exact Or.inl ht),
          key R (fun t ht => by simp only [D, List.mem_toFinset, List.mem_append] at ht ⊢; exact Or.inr ht)]

/-! ### The arguments of an equation -/

theorem memT_iff {t : Term} {l : List Term} : memT t l = true ↔ t ∈ l := by
  simp only [memT, List.any_eq_true, beq_iff]
  exact ⟨fun ⟨u, hu, h⟩ => h ▸ hu, fun h => ⟨t, h, rfl⟩⟩

section Arguments

variable {f : Nat} {l r : Term} {us : List Term} {ms : List Int}

theorem net_eq (t : Term) :
    net f l r t = ((summands f l).count t : Int) - ((summands f r).count t : Int) := by
  simp only [net, count_eq]

theorem weight_eq_sum (t : Term) : ∀ (us : List Term) (ms : List Int), us.length = ms.length →
    weight t us ms = ∑ j : Fin us.length, if nthD us j (var 0) = t then nthD ms j 0 else 0
  | [], [], _ => by simp [weight]
  | u :: us, m :: ms, h => by
    simp only [weight]
    rw [weight_eq_sum t us ms (by simpa using h), List.length_cons, Fin.sum_univ_succ]
    congr 1
    · by_cases hu : u = t
      · subst hu; simp [nthD, nth, (beq_iff (a := u) (b := u)).2 rfl]
      · have hb : beq t u = false := Bool.eq_false_iff.2 fun hb => hu (beq_iff.1 hb).symm
        simp [nthD, nth, hu, hb]
  | [], _ :: _, h | _ :: _, [], h => by simp at h

/-- A correct listing gives what `row_identity` needs: each argument is a summand, with a
nonzero multiplicity, and the multiplicities of each summand add up to its net count. -/
theorem arguments_row (h : argumentsOk f l r us ms = true) :
    us.length = ms.length ∧
    (∀ j < us.length, nthD us j (var 0) ∈ summands f l ++ summands f r) ∧
    (∀ j < us.length, nthD ms j 0 ≠ 0) ∧
    ∀ t ∈ summands f l ++ summands f r,
      ∑ j ∈ Finset.univ.filter (fun j : Fin us.length => nthD us j (var 0) = t), nthD ms j 0 =
        ((summands f l).count t : Int) - ((summands f r).count t : Int) := by
  simp only [argumentsOk, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, bne_iff_ne, ne_eq,
    memT_iff] at h
  obtain ⟨⟨⟨hlen, hne⟩, hmem⟩, hw⟩ := h
  refine ⟨hlen, fun j hj => ?_, fun j hj => ?_, fun t ht => ?_⟩
  · rw [nthD_of_lt _ hj]; exact hmem _ (List.getElem_mem hj)
  · rw [nthD_of_lt _ (hlen ▸ hj)]; exact hne _ (List.getElem_mem _)
  · rw [Finset.sum_filter, ← weight_eq_sum t us ms hlen, hw t ht, net_eq]

end Arguments

end Row

/-! ## Part B: the semantic step -/

/-- A singleton written as a sum: each summand with a nonzero coefficient is empty or the
singleton, and the coefficients of the nonempty summands add up to one. -/
theorem singleton_eq_sum {El : Type*} [DecidableEq El] {k : ℕ} (e : El) (w : Fin k → ℕ)
    (M : Fin k → Multiset El) (h : ({e} : Multiset El) = ∑ t, w t • M t) :
    (∀ t, w t ≠ 0 → M t = 0 ∨ M t = {e}) ∧ ∑ t, (if M t ≠ 0 then w t else 0) = 1 := by
  have hle : ∀ t, w t ≠ 0 → M t ≤ {e} := by
    intro t ht
    calc M t ≤ w t • M t := Multiset.le_iff_count.mpr fun x => by
            rw [Multiset.count_nsmul]; exact Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero ht)
      _ ≤ ∑ t, w t • M t := Finset.single_le_sum (f := fun t => w t • M t)
            (fun _ _ => zero_le _) (Finset.mem_univ t)
      _ = {e} := h.symm
  have h1 : ∀ t, w t ≠ 0 → M t = 0 ∨ M t = {e} := fun t ht => Multiset.le_singleton.mp (hle t ht)
  refine ⟨h1, ?_⟩
  have hc := congrArg Multiset.card h
  rw [Multiset.card_singleton, Multiset.card_sum] at hc
  rw [hc]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Multiset.card_nsmul]
  by_cases hw : w t = 0
  · simp [hw]
  · rcases h1 t hw with h0 | h0 <;> simp [h0]

namespace Model

variable {M : Model}

theorem msum_summands (hM : M.Lawful) {f : Nat} {A : AcuOp M.T} (hA : M.acu? f = some A)
    {ρ : M.Valuation} {t : Term} {y : M.T A.bag} (h : M.eval ρ t = some ⟨A.bag, y⟩) :
    msum A ρ (summands f t) = some (ACU.toMultiset (A.toBag y)) := by
  obtain ⟨h1, -, h3⟩ := acu_law hM hA
  have hc : M.contrib A ⟨A.bag, y⟩ = some (A.toBag y) := by
    simp [contrib, M.get?_ne (s := A.elem) (v := ⟨A.bag, y⟩) (Ne.symm h3)]
  have single : msum A ρ [t] = some (ACU.toMultiset (A.toBag y)) := by
    simp [msum, cval, h, hc]
  cases t with
  | acu g ts =>
    simp only [summands]
    split
    · next hfg =>
      simp only [beq_iff_eq] at hfg; subst hfg
      simp only [eval, hA] at h
      rw [← sumL_msum]
      cases hs : M.sumL ρ A ts with
      | none => simp [hs] at h
      | some Y =>
        simp only [hs, Option.map_some, Option.some.injEq, Sigma.mk.inj_iff, heq_eq_eq, true_and] at h
        simp [← h, h1]
    · exact single
  | var x => exact single
  | app g ts => exact single

theorem msum_mem {A : AcuOp M.T} {ρ : M.Valuation} :
    ∀ {ts : List Term} {m}, msum A ρ ts = some m → ∀ t ∈ ts, ∃ a, cval A ρ t = some a
  | [], _, _, t, ht => by simp at ht
  | s :: ts, m, h, t, ht => by
    simp only [msum] at h
    cases hc : cval A ρ s with
    | none => simp [hc] at h
    | some a =>
      cases hs : msum A ρ ts with
      | none => simp [hc, hs] at h
      | some b =>
        rcases List.mem_cons.1 ht with rfl | ht
        · exact ⟨a, hc⟩
        · exact msum_mem hs t ht

theorem msum_count {A : AcuOp M.T} [DecidableEq (M.T A.elem)] {ρ : M.Valuation} (e : M.T A.elem) :
    ∀ {ts : List Term} {m}, msum A ρ ts = some m →
      (ts.map fun t => (((cval A ρ t).getD 0).count e : Int)).sum = (m.count e : Int)
  | [], m, h => by simp only [msum, Option.some.injEq] at h; subst h; simp
  | s :: ts, m, h => by
    simp only [msum] at h
    cases hc : cval A ρ s with
    | none => simp [hc] at h
    | some a =>
      cases hs : msum A ρ ts with
      | none => simp [hc, hs] at h
      | some b =>
        simp only [hc, hs, Option.bind_some, Option.map_some, Option.some.injEq] at h
        subst h
        simp [hc, msum_count e hs, Multiset.count_add]

theorem msum_replicate {A : AcuOp M.T} {ρ : M.Valuation} {t : Term} {a} (h : cval A ρ t = some a) :
    ∀ n, msum A ρ (List.replicate n t) = some (n • a)
  | 0 => by simp [msum]
  | n + 1 => by
    simp only [List.replicate_succ, msum, h, msum_replicate h n, Option.bind_some, Option.map_some,
      succ_nsmul, add_comm]

theorem msum_flatMap {A : AcuOp M.T} {ρ : M.Valuation} (g : Nat → List Term) (W : Nat → Multiset (M.T A.elem)) :
    ∀ S : List Nat, (∀ k ∈ S, msum A ρ (g k) = some (W k)) →
      msum A ρ (S.flatMap g) = some ((S.map W).sum)
  | [], _ => by simp [msum]
  | k :: S, h => by
    rw [List.flatMap_cons, msum_append, h k (by simp),
      msum_flatMap g W S (fun k hk => h k (by simp [hk]))]
    simp

end Model

theorem natEqL_iff : ∀ {a b : List Nat}, natEqL a b = true ↔ a = b
  | [], [] => by simp [natEqL]
  | x :: a, y :: b => by simp [natEqL, natEqL_iff]
  | [], _ :: _ => by simp [natEqL]
  | _ :: _, [] => by simp [natEqL]

end Reflect
