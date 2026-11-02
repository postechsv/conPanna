import Reflect.AcuStep

/-!
Soundness of the ACU step (documentation/reflection-design.md, §3): every solution of the
conclusion reaches one of the premises, through a valuation that agrees on the state.
-/

namespace Reflect

open Term Unification.Certification

namespace Model

variable {M : Model}

/-- `ρ` respects the sorts and solves the equations. -/
def Sol (M : Model) (vs : List Nat) (ρ : M.Valuation) (E : List Eqn) : Prop :=
  M.WS vs ρ ∧ ∀ e ∈ E, ∃ v, M.eval ρ e.1 = some v ∧ M.eval ρ e.2 = some v

theorem memT_iff {t : Term} {l : List Term} : memT t l = true ↔ t ∈ l := by
  simp only [memT, List.any_eq_true, beq_iff]
  exact ⟨fun ⟨u, hu, h⟩ => h ▸ hu, fun h => ⟨t, h, rfl⟩⟩

theorem foldl_add_eq_sum (g : Nat → Nat) : ∀ (S : List Nat) (a : Nat),
    S.foldl (fun a k => a + g k) a = a + (S.map g).sum
  | [], a => by simp
  | k :: S, a => by rw [List.foldl_cons, foldl_add_eq_sum g S]; simp [Nat.add_assoc]

theorem legal_of {unk : List Term} {alien : List Bool} {basis : List (List Nat)} {S : List Nat}
    (h1 : ∀ k < basis.length, alienFree unk alien basis k = true → k ∈ S)
    (h2 : ∀ j < unk.length, isAlien alien j = true → (S.map fun k => entry basis k j).sum = 1) :
    legal unk alien basis S = true := by
  simp only [legal, Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    Bool.not_eq_true', List.contains_iff_mem, beq_iff_eq]
  refine ⟨fun k hk => ?_, fun j hj => ?_⟩
  · cases h : alienFree unk alien basis k
    · exact Or.inl rfl
    · exact Or.inr (h1 k hk h)
  · cases h : isAlien alien j
    · exact Or.inl rfl
    · exact Or.inr (by rw [foldl_add_eq_sum, Nat.zero_add]; exact h2 j hj h)

/-- An alien-free vector has no alien. -/
theorem alienFree_entry {unk : List Term} {alien : List Bool} {basis : List (List Nat)} {k j : Nat}
    (h : alienFree unk alien basis k = true) (hj : j < unk.length) (ha : isAlien alien j = true) :
    entry basis k j = 0 := by
  simp only [alienFree, List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true',
    beq_iff_eq] at h
  rcases h j hj with h | h
  · simp [ha] at h
  · exact h

/-- An alien vector has an alien. -/
theorem aliensOf_ne_nil {unk : List Term} {alien : List Bool} {basis : List (List Nat)} {k : Nat}
    (h : alienFree unk alien basis k = false) : aliensOf unk alien basis k ≠ [] := by
  have : ∃ j < unk.length, isAlien alien j = true ∧ entry basis k j ≠ 0 := by
    by_contra hno
    push_neg at hno
    have : alienFree unk alien basis k = true := by
      simp only [alienFree, List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true',
        beq_iff_eq]
      intro j hj
      cases ha : isAlien alien j
      · exact Or.inl rfl
      · exact Or.inr (hno j hj ha)
    rw [this] at h; exact absurd h (by simp)
  obtain ⟨j, hj, ha, he⟩ := this
  intro hnil
  have : j ∈ aliensOf unk alien basis k := by simp [aliensOf, hj, ha, he]
  rw [hnil] at this
  simp at this

theorem mem_aliensOf {unk : List Term} {alien : List Bool} {basis : List (List Nat)} {k j : Nat} :
    j ∈ aliensOf unk alien basis k ↔ j < unk.length ∧ isAlien alien j = true ∧ entry basis k j ≠ 0 := by
  simp [aliensOf]

theorem sum_filter_range {β : Type*} [AddCommMonoid β] (P : Nat → Bool) (g : Nat → β) :
    ∀ K, (((List.range K).filter P).map g).sum = ∑ k ∈ Finset.range K, if P k then g k else 0
  | 0 => by simp
  | K + 1 => by
    rw [List.range_succ, List.filter_append, List.map_append, List.sum_append, sum_filter_range P g K,
      Finset.sum_range_succ]
    cases h : P K <;> simp [h]

theorem occursTL_of_mem {z : Nat} : ∀ {ts : List Term} {t : Term}, t ∈ ts → occursT z t = true →
    occursTL z ts = true
  | [], _, h, _ => by simp at h
  | u :: ts, t, h, ht => by
    rcases List.mem_cons.1 h with rfl | h
    · simp [occursTL, ht]
    · simp [occursTL, occursTL_of_mem h ht]

theorem occurs_summand {z f : Nat} {l t : Term} (ht : t ∈ summands f l) (hz : occursT z t = true) :
    occursT z l = true := by
  cases l with
  | acu g ts =>
    simp only [summands] at ht
    split at ht
    · next h => simp only [beq_iff_eq] at h; subst h; simp [occursT, occursTL_of_mem ht hz]
    · simp only [List.mem_singleton] at ht; subst ht; exact hz
  | var x => simp only [summands, List.mem_singleton] at ht; subst ht; exact hz
  | app g ts => simp only [summands, List.mem_singleton] at ht; subst ht; exact hz

theorem acu_sound (hM : M.Lawful) {vs : List Nat} {ρ : M.Valuation} {α : List Term} {E : List Eqn}
    {f i : Nat} {unk : List Term} {alien : List Bool} {row : List Int} {basis : List (List Nat)}
    {sels : List (List Nat × List Nat)} {states : List (List Term × List Eqn)}
    (h : acuPremises M vs α E f i unk alien row basis sels = some states)
    (hsol : M.Sol vs ρ E) (hα : ∀ t ∈ α, (M.eval ρ t).isSome) :
    ∃ j, ∃ hj : j < states.length, ∃ ρ', M.Sol vs ρ' states[j].2 ∧
      states[j].1.map (M.eval ρ') = α.map (M.eval ρ) := by
  classical
  unfold acuPremises at h
  cases hE : nth E i with
  | none => simp [hE] at h
  | some lr =>
  obtain ⟨l, r⟩ := lr
  cases hA : M.acu? f with
  | none => simp [hE, hA] at h
  | some A =>
  simp only [hE, hA] at h
  split at h
  case isFalse => simp at h
  case isTrue hc =>
  simp only [Option.some.injEq] at h
  subst h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨hsl, hsr⟩, hun⟩, hro⟩, hbas⟩, hcom⟩, hsel⟩, hfr⟩ := hc
  -- the equation and its value
  have hlr : (l, r) ∈ E := by
    rw [nth_eq_getElem?] at hE; exact List.mem_of_getElem? hE
  obtain ⟨v, hvl, hvr⟩ := hsol.2 _ hlr
  have hvs := M.tsort_eval hsol.1 hvl
  rw [hsl, Option.some.injEq] at hvs
  obtain ⟨s0, y⟩ := v
  simp only at hvs
  subst hvs
  have hL := msum_summands hM hA hvl
  have hR := msum_summands hM hA hvr
  -- the unknowns
  simp only [unknownsOk, hA, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at hun
  obtain ⟨⟨_, hrl⟩, hun⟩ := hun
  have hmemLR : ∀ j < unk.length, nthD unk j (var 0) ∈ summands f l ++ summands f r := by
    have h' := hro
    simp only [rowOk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h'
    exact fun j hj => memT_iff.1 (h'.1 j hj)
  have hcval : ∀ j < unk.length, ∃ a, cval A ρ (nthD unk j (var 0)) = some a := fun j hj => by
    rcases List.mem_append.1 (hmemLR j hj) with h | h
    · exact msum_mem hL _ h
    · exact msum_mem hR _ h
  let xv : Fin unk.length → Multiset (M.T A.elem) := fun j => (cval A ρ (nthD unk j (var 0))).getD 0
  have hxv : ∀ j : Fin unk.length, cval A ρ (nthD unk j (var 0)) = some (xv j) := fun j => by
    obtain ⟨a, ha⟩ := hcval j j.2; simp [xv, ha]
  -- every element's counts solve the row
  have hrow : ∀ e, (∑ j : Fin unk.length, rc row j * ((xv j).count e : Int)) = 0 := by
    intro e
    have := row_identity hro (fun t => (((cval A ρ t).getD 0).count e : Int))
    rw [msum_count e hL, msum_count e hR, sub_self] at this
    exact this
  -- aliens are single elements
  have halien : ∀ j : Fin unk.length, isAlien alien j = true →
      ∃ a, M.eval ρ (nthD unk j (var 0)) = some ⟨A.elem, a⟩ ∧ xv j = {a} := by
    intro j hj
    have hu := hun j j.2
    rw [if_pos hj, beq_iff_eq] at hu
    have hc := hxv j
    simp only [cval] at hc
    cases he : M.eval ρ (nthD unk j (var 0)) with
    | none => simp [he] at hc
    | some w =>
      have hw := M.tsort_eval hsol.1 he
      rw [hu, Option.some.injEq] at hw
      obtain ⟨s1, a⟩ := w
      simp only at hw
      subst hw
      refine ⟨a, rfl, ?_⟩
      simp only [he, Option.bind_some, contrib, get?_mk, Option.map_some, Option.some.injEq] at hc
      rw [← hc]; rfl
  -- admissible
  have hadm : ∀ e, Adm unk alien row (counts xv e) := by
    intro e
    refine ⟨hrow e, fun j hj => ?_, fun j k hjk => ?_⟩
    · obtain ⟨a, -, hx⟩ := halien j hj
      simp only [counts, hx, Multiset.count_singleton]; split <;> omega
    · simp only [clashes, Bool.and_eq_true] at hjk
      obtain ⟨⟨hja, hka⟩, hh⟩ := hjk
      obtain ⟨a, hea, hxa⟩ := halien j hja
      obtain ⟨b, heb, hxb⟩ := halien k hka
      simp only [counts, hxa, hxb]
      rw [Multiset.count_singleton, Multiset.count_singleton]
      split_ifs with h1 h2 <;> try omega
      subst h1; subst h2
      exfalso
      revert hh
      cases hj' : nthD unk j (var 0) <;> cases hk' : nthD unk k (var 0) <;> simp [head?]
      next g1 ts1 g2 ts2 =>
        rw [hj'] at hea; rw [hk'] at heb
        obtain ⟨xs, -, hx⟩ := M.eval_app_some hea
        obtain ⟨ys, -, hy⟩ := M.eval_app_some heb
        exact (app_inj hM hx hy).1
  -- decompose into basis vectors
  obtain ⟨U, hU⟩ := decompose (Adm unk alien row) (fun k : Fin basis.length => bf unk basis k)
    (fun k hk => by
      obtain ⟨-, ⟨j, hj⟩, -, -⟩ := basis_facts hbas hrl k k.2
      exact hj (congrFun hk j))
    (fun v hv hne => dom hbas hcom hrl v hv hne) xv hadm
  let U' : Nat → Multiset (M.T A.elem) := fun k => if hk : k < basis.length then U ⟨k, hk⟩ else 0
  have hU' : ∀ k : Fin basis.length, U' k = U k := fun k => by simp [U', k.2]
  -- aliens: the selected alien vectors hold the alien's element
  have hsing : ∀ j : Fin unk.length, isAlien alien j = true → ∃ a,
      M.eval ρ (nthD unk j (var 0)) = some ⟨A.elem, a⟩ ∧ xv j = {a} ∧
      (∀ k : Fin basis.length, bf unk basis k j ≠ 0 → U k = 0 ∨ U k = {a}) ∧
      ∑ k : Fin basis.length, (if U k ≠ 0 then bf unk basis k j else 0) = 1 := by
    intro j hj
    obtain ⟨a, he, hx⟩ := halien j hj
    obtain ⟨h1, h2⟩ := singleton_eq_sum a (fun k => bf unk basis k j) U (by rw [← hx, hU j])
    exact ⟨a, he, hx, h1, h2⟩
  -- the selection: every alien-free vector, and the alien vectors used
  let free := (List.range basis.length).filter (alienFree unk alien basis)
  let al := (List.range basis.length).filter (fun k => !alienFree unk alien basis k)
  let T := al.filter (fun k => decide (U' k ≠ 0))
  have hT : T = (List.range basis.length).filter
      (fun k => !alienFree unk alien basis k && decide (U' k ≠ 0)) := by
    simp only [T, al, List.filter_filter, Bool.and_comm]
  have hlegal : legal unk alien basis (free ++ T) = true := by
    refine legal_of (fun k hk hf => List.mem_append_left _ (by simp [free, hk, hf])) ?_
    intro j hj ha
    obtain ⟨a, -, -, -, hsum⟩ := hsing ⟨j, hj⟩ ha
    rw [List.map_append, List.sum_append, hT, sum_filter_range, sum_filter_range]
    have h0 : ∑ k ∈ Finset.range basis.length,
        (if alienFree unk alien basis k = true then entry basis k j else 0) = 0 :=
      Finset.sum_eq_zero fun k _ => by
        split
        · next h => exact alienFree_entry h hj ha
        · rfl
    have hfin : ∑ k : Fin basis.length, (if U k ≠ 0 then bf unk basis k ⟨j, hj⟩ else 0) =
        ∑ k ∈ Finset.range basis.length, (if U' k ≠ 0 then entry basis k j else 0) := by
      rw [← Fin.sum_univ_eq_sum_range (fun k => if U' k ≠ 0 then entry basis k j else 0)]
      exact Finset.sum_congr rfl fun k _ => by simp [hU', bf]
    rw [h0, zero_add, ← hsum, hfin]
    refine Finset.sum_congr rfl fun k hk => ?_
    cases hf : alienFree unk alien basis k
    · simp
    · simp [alienFree_entry hf hj ha]
  -- it is listed
  have hsel' := hsel
  simp only [selsOk, List.all_eq_true] at hsel'
  have hs := hsel' T (mem_powerset (List.filter_sublist))
  rw [hlegal, Bool.not_true, Bool.false_or] at hs
  obtain ⟨⟨S', fresh⟩, hmem, heq⟩ := List.any_eq_true.1 hs
  have hperm : S'.Perm (free ++ T) :=
    (perm_sortN S').symm.trans ((natEqL_iff.1 heq) ▸ perm_sortN (free ++ T))
  sorry

end Model

end Reflect
