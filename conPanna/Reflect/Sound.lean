import conPanna.Reflect.AcuSound
import conPanna.Unification.Unification

/-!
Soundness of the checker: `check M c = true` gives `complete P U` for the problem and
unifiers the data `c` mirrors (documentation/reflection-design.md, §2 and §4).
-/

namespace Reflect

open Term Unification

/-- An answer with its Lean unifier body. -/
structure LAns (M : Model) (sh : Shp) where
  bsh : Shp
  img : List Term
  body : bsh.Ty M.T → sh.Ty M.T

namespace Model

variable {M : Model}

mutual
theorem varsBelow_occurs {n x : Nat} : ∀ {t : Term}, varsBelow n t = true → occursT x t = true → x < n
  | .var y, h1, h2 => by
    simp only [varsBelow, Nat.blt_eq] at h1; simp only [occursT, beq_iff_eq] at h2; omega
  | .app _ ts, h1, h2 => varsBelowL_occurs (by simpa [varsBelow] using h1) (by simpa [occursT] using h2)
  | .acu _ ts, h1, h2 => varsBelowL_occurs (by simpa [varsBelow] using h1) (by simpa [occursT] using h2)
theorem varsBelowL_occurs {n x : Nat} : ∀ {ts : List Term}, varsBelowL n ts = true →
    occursTL x ts = true → x < n
  | [], _, h2 => by simp [occursTL] at h2
  | t :: ts, h1, h2 => by
    simp only [varsBelowL, Bool.and_eq_true] at h1
    simp only [occursTL, Bool.or_eq_true] at h2
    rcases h2 with h2 | h2
    · exact varsBelow_occurs h1.1 h2
    · exact varsBelowL_occurs h1.2 h2
end

theorem sol_sub {vs : List Nat} {ρ : M.Valuation} {E E' : List Eqn} (h : M.Sol vs ρ E)
    (hsub : ∀ e ∈ E', e ∈ E) : M.Sol vs ρ E' :=
  ⟨h.1, fun e he => h.2 e (hsub e he)⟩

theorem mem_of_nth {E : List Eqn} {i : Nat} {e : Eqn} (h : nth E i = some e) : e ∈ E := by
  rw [nth_eq_getElem?] at h; exact List.mem_of_getElem? h

theorem run_sound (hM : M.Lawful) (c : Cert) (as : List (LAns M c.sh))
    (has : c.answers = as.map fun a => ⟨a.bsh, a.img⟩)
    (hU : AllL (fun a : LAns M c.sh => ∀ x,
      a.img.map (M.eval (M.enc a.bsh x)) = (M.encL c.sh (a.body x)).map some) as) :
    ∀ n id α E, run M c n id α E = true → ∀ (ρ : M.Valuation) (γ : c.sh.Ty M.T),
      M.Sol c.sorts ρ E → α.map (M.eval ρ) = (M.encL c.sh γ).map some →
      ∃ σ ∈ as.map (fun a => Unifier.bind a.body), covers σ γ := by
  intro n
  induction n with
  | zero => intro id α E h; simp [run] at h
  | succ n ih =>
  intro id α E h ρ γ hsol hα
  have hαlen : α.length = (M.encL c.sh γ).length := by
    have := congrArg List.length hα; simpa using this
  have hαy : ∀ y (hy : y < α.length), M.eval ρ α[y] = some ((M.encL c.sh γ)[y]'(hαlen ▸ hy)) := by
    intro y hy
    have := congrArg (·[y]?) hα
    simp only [List.getElem?_map, List.getElem?_eq_getElem hy, Option.map_some,
      List.getElem?_eq_getElem (hαlen ▸ hy)] at this
    exact Option.some.inj this
  have hdef : ∀ t ∈ α, (M.eval ρ t).isSome := fun t ht => by
    obtain ⟨y, hy, rfl⟩ := List.getElem_of_mem ht
    simp [hαy y hy]
  simp only [run] at h
  cases hst : nth c.steps id with
  | none => simp [hst] at h
  | some rule =>
  rw [hst] at h
  cases rule with
  | delete i p =>
    cases hE : nth E i with
    | none => simp [hE] at h
    | some lr =>
      simp only [hE, Bool.and_eq_true] at h
      exact ih p α _ h.2 ρ γ (sol_sub hsol fun e he => List.mem_of_mem_eraseIdx he) hα
  | decomp i p =>
    cases hE : nth E i with
    | none => simp [hE] at h
    | some lr =>
      obtain ⟨l, r⟩ := lr
      cases l <;> cases r <;> simp only [hE, Bool.false_eq_true] at h
      next f as g bs =>
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨⟨rfl, -⟩, h⟩ := h
      obtain ⟨v, hv1, hv2⟩ := hsol.2 _ (mem_of_nth hE)
      obtain ⟨xs, hxs, hfx⟩ := M.eval_app_some hv1
      obtain ⟨ys, hys, hfy⟩ := M.eval_app_some hv2
      obtain ⟨-, rfl⟩ := app_inj hM hfx hfy
      refine ih p α _ h ρ γ ⟨hsol.1, fun e he => ?_⟩ hα
      rcases List.mem_append.1 he with he | he
      · exact evalL_zip hxs hys e he
      · exact hsol.2 e (List.mem_of_mem_eraseIdx he)
  | clash i =>
    cases hE : nth E i with
    | none => simp [hE] at h
    | some lr =>
      obtain ⟨l, r⟩ := lr
      cases l <;> cases r <;> simp only [hE, Bool.false_eq_true] at h
      next f as g bs =>
      obtain ⟨v, hv1, hv2⟩ := hsol.2 _ (mem_of_nth hE)
      obtain ⟨xs, -, hfx⟩ := M.eval_app_some hv1
      obtain ⟨ys, -, hfy⟩ := M.eval_app_some hv2
      simp only [bne_iff_ne, ne_eq] at h
      exact absurd (app_inj hM hfx hfy).1 h
  | ground i =>
    cases hE : nth E i with
    | none => simp [hE] at h
    | some lr =>
      obtain ⟨l, r⟩ := lr
      simp only [hE] at h
      obtain ⟨v, hv1, hv2⟩ := hsol.2 _ (mem_of_nth hE)
      exact (refute_sound hM h v hv1 hv2).elim
  | elim i x p =>
    cases hE : nth E i with
    | none => simp [hE] at h
    | some lr =>
      obtain ⟨l, r⟩ := lr
      simp only [hE] at h
      obtain ⟨v, hv1, hv2⟩ := hsol.2 _ (mem_of_nth hE)
      -- the eliminated variable's value is the other side's
      have key : ∀ t, (beq l (var x) = true ∧ t = r) ∨ (beq r (var x) = true ∧ t = l) →
          run M c n p (α.map (elimUpd M c.sorts x t))
            ((E.eraseIdx i).map fun e => (elimUpd M c.sorts x t e.1, elimUpd M c.sorts x t e.2)) = true →
          ∃ σ ∈ as.map (fun a => Unifier.bind a.body), covers σ γ := by
        intro t ht hrun
        have hxt : ρ x = M.eval ρ t := by
          rcases ht with ⟨hb, rfl⟩ | ⟨hb, rfl⟩
          · rw [beq_iff] at hb; subst hb; simp only [eval] at hv1; rw [hv1, hv2]
          · rw [beq_iff] at hb; subst hb; simp only [eval] at hv2; rw [hv1, hv2]
        have hθ : substV ρ (fun y => if y == x then some t else none) = ρ := funext fun y => by
          simp only [substV]
          by_cases hy : y = x
          · subst hy; simp [hxt]
          · simp [hy]
        have hkeep : ∀ u, M.eval ρ (elimUpd M c.sorts x t u) = M.eval ρ u := fun u => by
          unfold elimUpd
          split
          · rw [eval_norm hM hsol.1, eval_subst, hθ]
          · rfl
        refine ih p _ _ hrun ρ γ ⟨hsol.1, fun e he => ?_⟩ ?_
        · obtain ⟨e0, he0, rfl⟩ := List.mem_map.1 he
          obtain ⟨w, h1, h2⟩ := hsol.2 e0 (List.mem_of_mem_eraseIdx he0)
          exact ⟨w, by simp only; rw [hkeep]; exact h1, by simp only; rw [hkeep]; exact h2⟩
        · rw [List.map_map, ← hα]; exact List.map_congr_left fun u _ => hkeep u
      by_cases hl : beq l (var x) = true
      · simp only [hl, ite_true, Bool.and_eq_true] at h
        exact key r (Or.inl ⟨hl, rfl⟩) h.2
      · by_cases hr : beq r (var x) = true
        · simp only [hl, hr, ite_true, Bool.false_eq_true, ite_false, Bool.and_eq_true] at h
          exact key l (Or.inr ⟨hr, rfl⟩) h.2
        · simp [hl, hr] at h
  | cover a w =>
    simp only [Bool.and_eq_true, List.isEmpty_iff] at h
    obtain ⟨-, h⟩ := h
    cases hA : nth c.answers a with
    | none => simp [hA] at h
    | some A =>
    simp only [hA, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
      List.any_eq_true] at h
    obtain ⟨⟨⟨⟨⟨hlen, hwlen⟩, hbelow⟩, hocc⟩, hsorts⟩, hzip⟩ := h
    rw [has, nth_eq_getElem?, List.getElem?_map] at hA
    cases hla : as[a]? with
    | none => simp [hla] at hA
    | some la =>
    simp only [hla, Option.map_some, Option.some.injEq] at hA
    subst hA
    simp only at hlen hwlen hbelow hocc hsorts hzip
    let ν : M.Valuation := substV ρ (nth w)
    -- each term of `α` is its answer's image, read through the witness
    have himg : ∀ y (hy : y < la.img.length),
        M.eval ν la.img[y] = some ((M.encL c.sh γ)[y]'(hαlen ▸ hlen ▸ hy)) := by
      intro y hy
      have hy' : y < α.length := hlen ▸ hy
      have hz := hzip (α[y], la.img[y]) (List.mem_iff_getElem.2 ⟨y, by simp [hy, hy'], by simp⟩)
      rw [beq_iff] at hz
      simp only at hz
      rw [← hαy y hy', hz, eval_norm hM hsol.1, eval_subst]
    -- the witness values decode to a binder tuple
    have hν : ∀ j < la.bsh.size, ∃ v, ν (0 + j) = some v ∧ la.bsh.sorts[j]? = some v.1 := by
      intro j hj
      obtain ⟨u, hu, hju⟩ := hocc j hj
      obtain ⟨y, hy', rfl⟩ := List.getElem_of_mem hu
      have hd := eval_def (himg y hy') j hju
      obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hd
      refine ⟨v, by simpa using hv, ?_⟩
      have hjw : j < w.length := hwlen ▸ hj
      have hνj : ν j = M.eval ρ (nthD w j (var 0)) := by
        simp only [ν, substV, nth_eq_getElem?, List.getElem?_eq_getElem hjw, nthD_of_lt _ hjw]
      rw [hνj] at hv
      have := hsorts j hjw
      rw [M.tsort_eval hsol.1 hv, nth_eq_getElem?] at this
      exact this.symm
    obtain ⟨b, hb⟩ := decode la.bsh ν 0 hν
    have hU' := allL_mem hU la (List.mem_of_getElem? hla) b
    refine ⟨Unifier.bind la.body, List.mem_map.2 ⟨la, List.mem_of_getElem? hla, rfl⟩, b, ?_⟩
    apply encL_inj c.sh
    apply List.ext_getElem
    · rw [encL_length, encL_length]
    · intro y h1 h2
      have hy : y < la.img.length := by
        have := congrArg List.length hU'; simp only [List.length_map, encL_length] at this
        rw [encL_length] at h2; omega
      have e2 := congrArg (·[y]?) hU'
      simp only [List.getElem?_map, List.getElem?_eq_getElem hy, Option.map_some,
        List.getElem?_eq_getElem h2] at e2
      rw [← eval_congr (ρ := ν) la.img[y] (fun x hx => by
        have hxb := varsBelow_occurs (hbelow _ (List.getElem_mem hy)) hx
        have := hb x hxb
        simp only [Nat.zero_add] at this
        rw [this]; rfl), himg y hy] at e2
      exact Option.some.inj (Option.some.inj e2)
  | acu f i unk alien row basis sels ps =>
    cases hp : acuPremises M c.sorts α E f i unk alien row basis sels with
    | none => simp [hp] at h
    | some states =>
    simp only [hp, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
    obtain ⟨hlen, hall⟩ := h
    obtain ⟨j, hj, ρ', hsol', hα'⟩ := acu_sound hM hp hsol hdef
    have hjp : j < ps.length := hlen ▸ hj
    exact ih ps[j] states[j].1 states[j].2
      (hall (states[j], ps[j]) (List.mem_iff_getElem.2 ⟨j, by simp [hj, hjp], by simp⟩))
      ρ' γ hsol' (hα'.trans hα)

end Model

theorem complete_of_check (M : Model) (hM : M.Lawful) (c : Cert) (hc : check M c = true)
    (s : Nat) (body : c.sh.Ty M.T → M.T s × M.T s)
    (hl : ∀ γ, M.eval (M.enc c.sh γ) c.lhs = some ⟨s, (body γ).1⟩)
    (hr : ∀ γ, M.eval (M.enc c.sh γ) c.rhs = some ⟨s, (body γ).2⟩)
    (as : List (LAns M c.sh)) (has : c.answers = as.map fun a => ⟨a.bsh, a.img⟩)
    (hU : AllL (fun a : LAns M c.sh => ∀ x,
      a.img.map (M.eval (M.enc a.bsh x)) = (M.encL c.sh (a.body x)).map some) as) :
    complete (Problem.bind body) (as.map fun a => Unifier.bind a.body) := by
  intro γ hγ
  simp only [unifiedBy] at hγ
  simp only [check, Bool.and_eq_true, ge_iff_le, decide_eq_true_eq] at hc
  obtain ⟨⟨hsorts, hsize⟩, hrun⟩ := hc
  rw [natEqL_iff] at hsorts
  have hWS : M.WS c.sorts (M.enc c.sh γ) := by
    intro x v hx
    simp only [Model.enc] at hx
    have hxs : x < c.sh.size := by
      have := (List.getElem?_eq_some_iff.1 hx).1; rwa [Model.encL_length] at this
    have h1 : c.sorts[x]? = (c.sorts.take c.sh.size)[x]? := by rw [List.getElem?_take_of_lt hxs]
    rw [h1, hsorts, ← Model.encL_sorts c.sh γ, List.getElem?_map, hx, Option.map_some]
  refine Model.run_sound hM c as has hU _ _ _ _ hrun (M.enc c.sh γ) γ ⟨hWS, fun e he => ?_⟩ ?_
  · simp only [List.mem_singleton] at he
    subst he
    refine ⟨⟨s, (body γ).1⟩, ?_, ?_⟩
    · rw [Model.eval_norm hM hWS, hl]
    · rw [Model.eval_norm hM hWS, hr, hγ]
  · apply List.ext_getElem
    · simp [Model.encL_length]
    · intro y h1 h2
      simp only [List.getElem_map, List.getElem_range, Model.eval, Model.enc]
      rw [List.getElem?_eq_getElem (by simpa using h2)]

end Reflect
