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

theorem acu_sound (hM : M.Lawful) {vs : List Nat} {ρ : M.Valuation} {α : List Term}
    {E : List Eqn} {f i : Nat} {freshs : List (List Nat)} {states : List (List Term × List Eqn)}
    (h : acuSolve M vs α E f i freshs = some states)
    (hsol : M.Sol vs ρ E) (hα : ∀ t ∈ α, (M.eval ρ t).isSome) :
    ∃ j, ∃ hj : j < states.length, ∃ ρ', M.Sol vs ρ' states[j].2 ∧
      states[j].1.map (M.eval ρ') = α.map (M.eval ρ) := by
  classical
  unfold acuSolve at h
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
  set args := arguments f l r
  set unk := args.map (·.term)
  set sh := dioOf M vs A args
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at hc
  obtain ⟨⟨⟨⟨hsl, hsr⟩, hun⟩, hlen⟩, hfr⟩ := hc
  replace hfr : ∀ p ∈ sh.selections.zip freshs, p.2.length =
      (p.1.filter (alienFree unk sh.nonVar sh.basis)).length ∧
      (freshOk vs A.bag α E p.2 = true) := fun p hp => by
    simpa [Bool.and_eq_true, beq_iff_eq] using hfr p hp
  have hsz : sh.size = unk.length := by simp [sh, dioOf, Dio.size, unk]
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
  -- the arguments: each a summand, with nonzero multiplicity
  obtain ⟨hmemLR, hcnt⟩ := arguments_row (f := f) (l := l) (r := r)
  have hrc : ∀ j : Fin unk.length, rc sh j ≠ 0 := fun j => by
    have hj : (j : Nat) < args.length := by simpa [unk] using j.2
    simp only [rc, sh, dioOf]
    rw [nthD_of_lt _ (by simpa using hj)]
    simpa using (arg_mult (List.getElem_mem hj)).2
  have hcval : ∀ j < unk.length, ∃ a, cval A ρ (nthD unk j (var 0)) = some a := fun j hj => by
    rcases List.mem_append.1 (hmemLR j hj) with h | h
    · exact msum_mem hL _ h
    · exact msum_mem hR _ h
  let xv : Fin unk.length → Multiset (M.T A.elem) := fun j => (cval A ρ (nthD unk j (var 0))).getD 0
  have hxv : ∀ j : Fin unk.length, cval A ρ (nthD unk j (var 0)) = some (xv j) := fun j => by
    obtain ⟨a, ha⟩ := hcval j j.2; simp [xv, ha]
  -- every element's counts solve the equation
  have hrow : ∀ e, (∑ j : Fin unk.length, rc sh j * ((xv j).count e : Int)) = 0 := by
    intro e
    have := row_identity hmemLR hcnt (fun t => (((cval A ρ t).getD 0).count e : Int))
    rw [msum_count e hL, msum_count e hR, sub_self] at this
    exact this
  -- non-variable arguments are single elements
  have halien : ∀ j : Fin unk.length, isAlien sh.nonVar j = true →
      ∃ a, M.eval ρ (nthD unk j (var 0)) = some ⟨A.elem, a⟩ ∧ xv j = {a} := by
    intro j hj
    have hu : tsort M vs (nthD unk j (var 0)) = some A.elem := by
      have hj' := hj
      simp only [isAlien, sh, dioOf] at hj'
      rw [nthD_of_lt _ (by simpa [unk] using j.2)] at hj'
      rw [nthD_of_lt _ j.2]
      simpa [unk] using hj'
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
  have hadm : ∀ e, Adm sh unk.length (counts xv e) := by
    intro e
    refine ⟨hrow e, fun j hj => ?_, fun j k hja hka hjk => ?_⟩
    · obtain ⟨a, -, hx⟩ := halien j hj
      simp only [counts, hx, Multiset.count_singleton]; split <;> omega
    · obtain ⟨a, hea, hxa⟩ := halien j hja
      obtain ⟨b, heb, hxb⟩ := halien k hka
      simp only [counts, hxa, hxb]
      rw [Multiset.count_singleton, Multiset.count_singleton]
      by_cases h1 : e = a
      · by_cases h2 : e = b
        · subst h1; subst h2
          exfalso
          simp only [sh, dioOf, clashT] at hjk
          revert hjk
          cases hj' : nthD unk j (var 0) <;> cases hk' : nthD unk k (var 0) <;> simp [head?]
          next g1 ts1 g2 ts2 =>
            rw [hj'] at hea; rw [hk'] at heb
            obtain ⟨xs, -, hx⟩ := M.eval_app_some hea
            obtain ⟨ys, -, hy⟩ := M.eval_app_some heb
            exact (app_inj hM hx hy).1
        · right; simp [h2]
      · left; simp [h1]
  -- the free elements of a selection: as enumerated, the alien-free ones
  have hfreeEq : ∀ k, (sh.marked (nthD sh.basis k [])).isEmpty = alienFree unk sh.nonVar sh.basis k := by
    intro k
    rw [Bool.eq_iff_iff, List.isEmpty_iff, List.eq_nil_iff_forall_not_mem]
    simp only [alienFree, List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true',
      beq_iff_eq, mem_marked, isAlien, entry, bvec, ← hsz]
    constructor
    · intro h j hj
      by_cases ha : nthD sh.nonVar j false = true
      · exact Or.inr (by by_contra h0; exact h j ⟨hj, ha, h0⟩)
      · exact Or.inl (by simpa using ha)
    · rintro h j ⟨hj, ha, h0⟩
      rcases h j hj with h | h
      · simp [ha] at h
      · exact h0 h
  let free := (List.range sh.basis.length).filter (alienFree unk sh.nonVar sh.basis)
  have hfreeL : (List.range sh.basis.length).filter (fun k => (sh.marked (nthD sh.basis k [])).isEmpty) = free :=
    List.filter_congr fun k _ => hfreeEq k
  -- decompose into basis vectors
  obtain ⟨U, hU⟩ := decompose (Adm sh unk.length) (fun k : Fin sh.basis.length => bf sh unk.length k)
    (fun k hk => by
      obtain ⟨-, ⟨j, hj⟩, -, -⟩ := basis_facts hsz k k.2
      exact hj (congrFun hk j))
    (fun v hv hne => by
      obtain ⟨k, hk⟩ := dom hsz hrc v hv hne
      exact ⟨k, hk, adm_sub hsz k.2 hv hk⟩) xv hadm
  let U' : Nat → Multiset (M.T A.elem) := fun k => if hk : k < sh.basis.length then U ⟨k, hk⟩ else 0
  have hU' : ∀ k : Fin sh.basis.length, U' k = U k := fun k => by simp [U', k.2]
  -- aliens: the selected alien vectors hold the alien's element
  have hsing : ∀ j : Fin unk.length, isAlien sh.nonVar j = true → ∃ a,
      M.eval ρ (nthD unk j (var 0)) = some ⟨A.elem, a⟩ ∧ xv j = {a} ∧
      (∀ k : Fin sh.basis.length, bf sh unk.length k j ≠ 0 → U k = 0 ∨ U k = {a}) ∧
      ∑ k : Fin sh.basis.length, (if U k ≠ 0 then bf sh unk.length k j else 0) = 1 := by
    intro j hj
    obtain ⟨a, he, hx⟩ := halien j hj
    obtain ⟨h1, h2⟩ := singleton_eq_sum a (fun k => bf sh unk.length k j) U (by rw [← hx, hU j])
    exact ⟨a, he, hx, h1, h2⟩
  -- the selection: every alien-free vector, and the alien vectors used
  let al := (List.range sh.basis.length).filter (fun k => !alienFree unk sh.nonVar sh.basis k)
  let T := al.filter (fun k => decide (U' k ≠ 0))
  have hT : T = (List.range sh.basis.length).filter
      (fun k => !alienFree unk sh.nonVar sh.basis k && decide (U' k ≠ 0)) := by
    simp only [T, al, List.filter_filter, Bool.and_comm]
  -- the alien vectors used cover each non-variable argument exactly once
  have hcov : ∀ j < sh.size, nthD sh.nonVar j false = true →
      (T.map fun k => nthD (nthD sh.basis k []) j 0).sum = 1 := by
    intro j hj ha
    have hj' : j < unk.length := hsz ▸ hj
    obtain ⟨a, -, -, -, hsum⟩ := hsing ⟨j, hj'⟩ ha
    rw [hT, sum_filter_range]
    have hfin : ∑ k : Fin sh.basis.length, (if U k ≠ 0 then bf sh unk.length k ⟨j, hj'⟩ else 0) =
        ∑ k ∈ Finset.range sh.basis.length, (if U' k ≠ 0 then entry sh.basis k j else 0) := by
      rw [← Fin.sum_univ_eq_sum_range (fun k => if U' k ≠ 0 then entry sh.basis k j else 0)]
      exact Finset.sum_congr rfl fun k _ => by simp [hU', bf, entry, bvec]
    rw [← hsum, hfin]
    refine Finset.sum_congr rfl fun k hk => ?_
    cases hf : alienFree unk sh.nonVar sh.basis k
    · simp [entry, bvec]
    · simp [alienFree_entry hf hj' ha]
  -- so the selection is listed
  obtain ⟨S', hmem, hperm⟩ := selections_complete (T := T)
    (by rw [hT]; exact (List.nodup_range).filter _)
    (fun k hk => by
      rw [hT] at hk
      simp only [List.mem_filter, List.mem_range, Bool.and_eq_true, Bool.not_eq_true'] at hk
      refine ⟨hk.1, fun h => ?_⟩
      have := (hfreeEq k).symm.trans (by rw [h])
      simp [hk.2.1] at this)
    hcov
  rw [hfreeL] at hperm
  have hnodup : S'.Nodup := by
    refine hperm.nodup_iff.2 (List.Nodup.append ((List.nodup_range).filter _) ?_ ?_)
    · rw [hT]; exact (List.nodup_range).filter _
    · intro a ha hb
      simp only [free, hT, List.mem_filter, Bool.and_eq_true, Bool.not_eq_true'] at ha hb
      rw [ha.2] at hb; exact absurd hb.2.1 (by simp)
  have hmemS : ∀ k, k ∈ S' ↔ k < sh.basis.length ∧
      (alienFree unk sh.nonVar sh.basis k = true ∨ (alienFree unk sh.nonVar sh.basis k = false ∧ U' k ≠ 0)) := by
    intro k
    rw [hperm.mem_iff, List.mem_append, hT]
    simp only [free, List.mem_filter, List.mem_range, Bool.and_eq_true, Bool.not_eq_true',
      decide_eq_true_eq]
    exact and_or_left.symm
  -- the premise
  obtain ⟨jj, hjj, hget⟩ := List.getElem_of_mem hmem
  have hjjz : jj < (sh.selections.zip freshs).length := by
    rw [List.length_zip, ← hlen, Nat.min_self]; exact hjj
  set fresh := freshs[jj]'(by rw [← hlen]; exact hjj)
  have hzip : (sh.selections.zip freshs)[jj]'hjjz = (S', fresh) := by simp [hget, fresh]
  obtain ⟨hflen, hfresh⟩ := hfr _ (hzip ▸ List.getElem_mem hjjz)
  simp only [freshOk, List.all_eq_true, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true',
    List.any_eq_false] at hfresh
  have hfnodup : fresh.Nodup := List.nodup_iff_count_le_one.2 fun z => by
    by_cases hz : z ∈ fresh
    · exact (hfresh z hz).1.1.2.le
    · rw [List.count_eq_zero_of_not_mem hz]; omega
  let FS := S'.filter (alienFree unk sh.nonVar sh.basis)
  let ρ' : M.Valuation := fun z => if z ∈ fresh then
    some ⟨A.bag, A.ofBag (ACU.ofMultiset (U' (FS.getD (fresh.idxOf z) 0)))⟩ else ρ z
  refine ⟨jj, by simpa using hjjz, ρ', ?_⟩
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
  have hrepA : ∀ k ∈ S', alienFree unk sh.nonVar sh.basis k = false → ∃ a,
      M.eval ρ' (rep unk sh.nonVar sh.basis S' fresh k) = some ⟨A.elem, a⟩ ∧ U' k = {a} ∧
      ∀ j ∈ aliensOf unk sh.nonVar sh.basis k, M.eval ρ (nthD unk j (var 0)) = some ⟨A.elem, a⟩ := by
    intro k hk hf
    have hkK := ((hmemS k).1 hk).1
    have hU0 : U' k ≠ 0 := by
      rcases ((hmemS k).1 hk).2 with h | h
      · rw [hf] at h; exact absurd h (by simp)
      · exact h.2
    -- every alien of `k` holds the element of `U' k`
    have hall : ∀ j ∈ aliensOf unk sh.nonVar sh.basis k, ∃ a,
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
  have hrep : ∀ k ∈ S', cval A ρ' (rep unk sh.nonVar sh.basis S' fresh k) = some (U' k) := by
    intro k hk
    cases hf : alienFree unk sh.nonVar sh.basis k
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
      rw [show S'.filter (alienFree unk sh.nonVar sh.basis) = FS from rfl, hz]
      simp only [cval, eval, ρ', hzf, ite_true, hidx, hFS, Option.bind_some,
        contrib_bag hM hA, Option.map_some, ACU.toMultiset_ofMultiset]
  -- the bag variables: `θ x` evaluates to `x`'s value
  obtain ⟨law1, law2, -⟩ := acu_law hM hA
  have htheta : ∀ x t, theta f unk sh.nonVar sh.basis S' fresh x = some t → M.eval ρ' t = ρ x := by
    intro x t ht
    simp only [theta, Option.map_eq_some_iff] at ht
    obtain ⟨j, hfind, rfl⟩ := ht
    have hp := List.find?_some hfind
    have hjN := List.mem_range.1 (List.mem_of_find?_eq_some hfind)
    simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff] at hp
    obtain ⟨hja, hjx⟩ := hp
    -- the sum of the selected vectors' shares
    have hsum : msum A ρ' (S'.flatMap fun k =>
        List.replicate (entry sh.basis k j) (rep unk sh.nonVar sh.basis S' fresh k)) = some (xv ⟨j, hjN⟩) := by
      rw [msum_flatMap _ (fun k => entry sh.basis k j • U' k) S'
        (fun k hk => msum_replicate (hrep k hk) _), hU ⟨j, hjN⟩]
      congr 1
      rw [(hperm.map _).sum_eq, List.map_append, List.sum_append, hT, sum_filter_range,
        sum_filter_range, ← Finset.sum_add_distrib,
        ← Fin.sum_univ_eq_sum_range (fun k => (if alienFree unk sh.nonVar sh.basis k = true then
          entry sh.basis k j • U' k else 0) + (if (!alienFree unk sh.nonVar sh.basis k && decide (U' k ≠ 0)) = true
          then entry sh.basis k j • U' k else 0))]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hU' k]
      cases hf : alienFree unk sh.nonVar sh.basis k <;> by_cases hU0 : U k = 0 <;> simp [hf, hU0, bf, entry, bvec]
    have hux := hun j hjN
    simp only [isAlien] at hja
    simp only [hja, hjx, Bool.false_or, beq_iff_eq] at hux
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
          List.replicate (entry sh.basis k j) (rep unk sh.nonVar sh.basis S' fresh k)) with
      | none => simp [hsL] at hsum
      | some Y =>
        simp only [hsL, Option.map_some, Option.some.injEq] at hsum
        rw [← hcx] at hsum
        rw [ACU.toMultiset_injective hsum]; simp [law2]
  -- the state, read through `θ` and normalized, keeps its values
  have hkeep : ∀ t, (∀ z ∈ fresh, occursT z t = false) →
      M.eval ρ' (norm M vs (subst (theta f unk sh.nonVar sh.basis S' fresh) t)) = M.eval ρ t := by
    intro t ht
    rw [eval_norm hM hWS', eval_subst]
    refine eval_congr t fun x hx => ?_
    simp only [substV]
    cases hθ : theta f unk sh.nonVar sh.basis S' fresh x with
    | some u => exact htheta x u hθ
    | none => exact hρ'out x fun hxf => by rw [ht x hxf] at hx; exact absurd hx (by simp)
  have hkeep' : ∀ (bv : List Nat) t, (∀ z ∈ fresh, occursT z t = false) →
      M.eval ρ' (acuUpd M vs bv (theta f unk sh.nonVar sh.basis S' fresh) t) = M.eval ρ t := by
    intro bv t ht
    unfold acuUpd
    split
    · exact hkeep t ht
    · exact eval_congr t fun z hz => hρ'out z fun hzf => by rw [ht z hzf] at hz; exact absurd hz (by simp)
  simp only [List.getElem_map, hzip]
  refine ⟨⟨hWS', fun e he => ?_⟩, ?_⟩
  · rcases List.mem_append.1 he with he | he
    · simp only [pendingOf, List.mem_flatMap, List.mem_map] at he
      obtain ⟨k, hk, j, hj, rfl⟩ := he
      have hj' := List.mem_of_mem_drop hj
      obtain ⟨hjN, hja, hjk⟩ := mem_aliensOf.1 hj'
      have hf : alienFree unk sh.nonVar sh.basis k = false := by
        cases h : alienFree unk sh.nonVar sh.basis k
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
