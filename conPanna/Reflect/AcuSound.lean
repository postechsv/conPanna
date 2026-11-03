import conPanna.Reflect.AcuStep

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
  have hnodup : S'.Nodup := by
    refine hperm.nodup_iff.2 (List.Nodup.append ((List.nodup_range).filter _) ?_ ?_)
    · rw [hT]; exact (List.nodup_range).filter _
    · intro a ha hb
      simp only [free, hT, List.mem_filter, Bool.and_eq_true, Bool.not_eq_true'] at ha hb
      rw [ha.2] at hb; exact absurd hb.2.1 (by simp)
  have hmemS : ∀ k, k ∈ S' ↔ k < basis.length ∧
      (alienFree unk alien basis k = true ∨ (alienFree unk alien basis k = false ∧ U' k ≠ 0)) := by
    intro k
    rw [hperm.mem_iff, List.mem_append, hT]
    simp only [free, List.mem_filter, List.mem_range, Bool.and_eq_true, Bool.not_eq_true',
      decide_eq_true_eq]
    tauto
  -- the premise
  obtain ⟨jj, hjj, hget⟩ := List.getElem_of_mem hmem
  obtain ⟨⟨hfresh, hflen⟩, -⟩ := hfr _ hmem
  simp only [freshOk, List.all_eq_true, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true',
    List.any_eq_false, Bool.or_eq_false_iff] at hfresh
  have hfnodup : fresh.Nodup := List.nodup_iff_count_le_one.2 fun z => by
    by_cases hz : z ∈ fresh
    · exact (hfresh z hz).1.1.2.le
    · rw [List.count_eq_zero_of_not_mem hz]; omega
  let FS := S'.filter (alienFree unk alien basis)
  let ρ' : M.Valuation := fun z => if z ∈ fresh then
    some ⟨A.bag, A.ofBag (ACU.ofMultiset (U' (FS.getD (fresh.idxOf z) 0)))⟩ else ρ z
  refine ⟨jj, by simpa using hjj, ρ', ?_⟩
  have hfvs : ∀ z ∈ fresh, vs[z]? = some A.bag := fun z hz => (hfresh z hz).1.1.1
  have hfα : ∀ z ∈ fresh, ∀ t ∈ α, occursT z t = false := fun z hz t ht => by
    simpa using (hfresh z hz).1.2 t ht
  have hfE : ∀ z ∈ fresh, ∀ e ∈ E, occursT z e.1 = false ∧ occursT z e.2 = false :=
    fun z hz e he => by simpa [Bool.or_eq_true, not_or] using (hfresh z hz).2 e he
  have hρ'out : ∀ z, z ∉ fresh → ρ' z = ρ z := fun z hz => by simp [ρ', hz]
  have hWS' : M.WS vs ρ' := by
    intro z w hz
    by_cases hzf : z ∈ fresh
    · simp only [ρ', hzf, ite_true, Option.some.injEq] at hz
      subst hz; exact hfvs z hzf
    · rw [hρ'out z hzf] at hz; exact hsol.1 z w hz
  -- the unknowns hold no fresh variable
  have hunk : ∀ j < unk.length, ∀ z ∈ fresh, occursT z (nthD unk j (var 0)) = false := by
    intro j hj z hz
    cases h : occursT z (nthD unk j (var 0))
    · rfl
    · exfalso
      rcases List.mem_append.1 (hmemLR j hj) with hm | hm
      · have := occurs_summand hm h; rw [(hfE z hz _ hlr).1] at this; exact absurd this (by simp)
      · have := occurs_summand hm h; rw [(hfE z hz _ hlr).2] at this; exact absurd this (by simp)
  have hunkEval : ∀ j < unk.length, M.eval ρ' (nthD unk j (var 0)) = M.eval ρ (nthD unk j (var 0)) :=
    fun j hj => eval_congr _ fun z hz => hρ'out z fun hzf => by rw [hunk j hj z hzf] at hz; simp at hz
  -- representatives: an alien vector's first alien
  have hrepA : ∀ k ∈ S', alienFree unk alien basis k = false → ∃ a,
      M.eval ρ' (rep unk alien basis S' fresh k) = some ⟨A.elem, a⟩ ∧ U' k = {a} ∧
      ∀ j ∈ aliensOf unk alien basis k, M.eval ρ (nthD unk j (var 0)) = some ⟨A.elem, a⟩ := by
    intro k hk hf
    have hkK := ((hmemS k).1 hk).1
    have hU0 : U' k ≠ 0 := by
      rcases ((hmemS k).1 hk).2 with h | h
      · rw [hf] at h; exact absurd h (by simp)
      · exact h.2
    -- every alien of `k` holds the element of `U' k`
    have hall : ∀ j ∈ aliensOf unk alien basis k, ∃ a,
        M.eval ρ (nthD unk j (var 0)) = some ⟨A.elem, a⟩ ∧ U' k = {a} := by
      intro j hj
      obtain ⟨hjN, hja, hjk⟩ := mem_aliensOf.1 hj
      obtain ⟨a, he, -, hU1, -⟩ := hsing ⟨j, hjN⟩ hja
      refine ⟨a, he, ?_⟩
      have := hU1 ⟨k, hkK⟩ (by simpa [bf] using hjk)
      rw [← hU' ⟨k, hkK⟩] at this
      exact this.resolve_left hU0
    have hne := aliensOf_ne_nil hf
    obtain ⟨j0, rest, h0⟩ := List.exists_cons_of_ne_nil hne
    obtain ⟨a, he, hUa⟩ := hall j0 (by rw [h0]; simp)
    refine ⟨a, ?_, hUa, fun j hj => ?_⟩
    · simp only [rep, hf, Bool.false_eq_true, ite_false, h0, List.headD_cons]
      rw [hunkEval j0 (mem_aliensOf.1 (by rw [h0]; simp)).1, he]
    · obtain ⟨b, hb, hUb⟩ := hall j hj
      rw [hUa, Multiset.singleton_inj] at hUb
      rw [hb, hUb]
  have hrep : ∀ k ∈ S', cval A ρ' (rep unk alien basis S' fresh k) = some (U' k) := by
    intro k hk
    cases hf : alienFree unk alien basis k
    · obtain ⟨a, he, hUa, -⟩ := hrepA k hk hf
      simp [cval, he, contrib, hUa]
    · have hkFS : k ∈ FS := List.mem_filter.2 ⟨hk, hf⟩
      have hm := List.idxOf_lt_length_of_mem hkFS
      have hmf : FS.idxOf k < fresh.length := by rw [hflen]; exact hm
      have hz : nthD fresh (FS.idxOf k) 0 = fresh[FS.idxOf k] := nthD_of_lt _ hmf
      have hzf : fresh[FS.idxOf k] ∈ fresh := List.getElem_mem hmf
      have hidx : fresh.idxOf fresh[FS.idxOf k] = FS.idxOf k := List.idxOf_getElem hfnodup _ hmf
      have hFS : FS.getD (FS.idxOf k) 0 = k := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hm, Option.getD_some]
        exact List.getElem_idxOf hm
      simp only [rep, hf, ite_true]
      rw [show S'.filter (alienFree unk alien basis) = FS from rfl, hz]
      simp only [cval, eval, ρ', hzf, ite_true, hidx, hFS, Option.bind_some,
        contrib_bag hM hA, Option.map_some, ACU.toMultiset_ofMultiset]
  -- the bag variables: `θ x` evaluates to `x`'s value
  obtain ⟨law1, law2, -⟩ := acu_law hM hA
  have htheta : ∀ x t, theta f unk alien basis S' fresh x = some t → M.eval ρ' t = ρ x := by
    intro x t ht
    simp only [theta, Option.map_eq_some_iff] at ht
    obtain ⟨j, hfind, rfl⟩ := ht
    have hp := List.find?_some hfind
    have hjN := List.mem_range.1 (List.mem_of_find?_eq_some hfind)
    simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff] at hp
    obtain ⟨hja, hjx⟩ := hp
    -- the sum of the selected vectors' shares
    have hsum : msum A ρ' (S'.flatMap fun k =>
        List.replicate (entry basis k j) (rep unk alien basis S' fresh k)) = some (xv ⟨j, hjN⟩) := by
      rw [msum_flatMap _ (fun k => entry basis k j • U' k) S'
        (fun k hk => msum_replicate (hrep k hk) _), hU ⟨j, hjN⟩]
      congr 1
      rw [(hperm.map _).sum_eq, List.map_append, List.sum_append, hT, sum_filter_range,
        sum_filter_range, ← Finset.sum_add_distrib,
        ← Fin.sum_univ_eq_sum_range (fun k => (if alienFree unk alien basis k = true then
          entry basis k j • U' k else 0) + (if (!alienFree unk alien basis k && decide (U' k ≠ 0)) = true
          then entry basis k j • U' k else 0))]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hU' k]
      cases hf : alienFree unk alien basis k <;> by_cases hU0 : U k = 0 <;> simp [hf, hU0, bf]
    have hux := hun j hjN
    rw [if_neg (by simpa using hja), hjx] at hux
    simp only [beq_iff_eq] at hux
    have hcx := hxv ⟨j, hjN⟩
    simp only [hjx, cval, eval] at hcx
    cases hρx : ρ x with
    | none => simp [hρx] at hcx
    | some w =>
      have hw := hsol.1 x w hρx
      rw [hux, Option.some.injEq] at hw
      obtain ⟨s2, yw⟩ := w
      simp only at hw
      subst hw
      simp only [hρx, Option.bind_some, contrib, M.get?_ne (s := A.elem) (v := ⟨A.bag, yw⟩)
        (Ne.symm (acu_law hM hA).2.2), get?_mk, Option.map_some, Option.some.injEq] at hcx
      simp only [eval, hA]
      rw [← sumL_msum] at hsum
      cases hsL : M.sumL ρ' A (S'.flatMap fun k =>
          List.replicate (entry basis k j) (rep unk alien basis S' fresh k)) with
      | none => simp [hsL] at hsum
      | some Y =>
        simp only [hsL, Option.map_some, Option.some.injEq] at hsum
        rw [← hcx] at hsum
        rw [ACU.toMultiset_injective hsum]; simp [law2]
  -- the state, read through `θ` and normalized, keeps its values
  have hkeep : ∀ t, (∀ z ∈ fresh, occursT z t = false) →
      M.eval ρ' (norm M vs (subst (theta f unk alien basis S' fresh) t)) = M.eval ρ t := by
    intro t ht
    rw [eval_norm hM hWS', eval_subst]
    refine eval_congr t fun x hx => ?_
    simp only [substV]
    cases hθ : theta f unk alien basis S' fresh x with
    | some u => exact htheta x u hθ
    | none => exact hρ'out x fun hxf => by rw [ht x hxf] at hx; exact absurd hx (by simp)
  have hkeep' : ∀ (bv : List Nat) t, (∀ z ∈ fresh, occursT z t = false) →
      M.eval ρ' (acuUpd M vs bv (theta f unk alien basis S' fresh) t) = M.eval ρ t := by
    intro bv t ht
    unfold acuUpd
    split
    · exact hkeep t ht
    · exact eval_congr t fun z hz => hρ'out z fun hzf => by rw [ht z hzf] at hz; exact absurd hz (by simp)
  simp only [List.getElem_map, hget]
  refine ⟨⟨hWS', fun e he => ?_⟩, ?_⟩
  · rcases List.mem_append.1 he with he | he
    · simp only [pendingOf, List.mem_flatMap, List.mem_map] at he
      obtain ⟨k, hk, j, hj, rfl⟩ := he
      have hj' := List.mem_of_mem_drop hj
      obtain ⟨hjN, hja, hjk⟩ := mem_aliensOf.1 hj'
      have hf : alienFree unk alien basis k = false := by
        cases h : alienFree unk alien basis k
        · rfl
        · exact absurd (alienFree_entry h hjN hja) hjk
      obtain ⟨a, hea, -, hall⟩ := hrepA k hk hf
      exact ⟨⟨A.elem, a⟩, by rw [hunkEval j hjN]; exact hall j hj', hea⟩
    · obtain ⟨e0, he0, rfl⟩ := List.mem_map.1 he
      have he0' := List.mem_of_mem_eraseIdx he0
      obtain ⟨w, h1, h2⟩ := hsol.2 e0 he0'
      exact ⟨w, by simp only; rw [hkeep' _ _ fun z hz => (hfE z hz e0 he0').1]; exact h1,
        by simp only; rw [hkeep' _ _ fun z hz => (hfE z hz e0 he0').2]; exact h2⟩
  · rw [List.map_map]
    exact List.map_congr_left fun t ht => hkeep' _ t fun z hz => hfα z hz t ht

end Model

end Reflect
