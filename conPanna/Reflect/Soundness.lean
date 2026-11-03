import conPanna.Reflect.Bridge

/-!
Soundness by reflection: `checkSound M c = true` gives `sound P U` for the problem and
unifiers the claim `c` mirrors. Each answer `σ`, substituted into both sides, normalizes to
the same term; evaluation turns that into `σ(lhs) = σ(rhs)` for every instance.
-/

namespace Reflect

open Term Unification

theorem sound_of_check (M : Model) (hM : M.Lawful) (c : Claim) (hc : checkSound M c = true)
    (b : Bridge M c) : sound b.problem b.unifiers := by
  intro σ hσ γ hcov
  obtain ⟨la, hla, rfl⟩ := List.mem_map.1 hσ
  obtain ⟨x, rfl⟩ := hcov
  simp only [checkSound, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at hc
  obtain ⟨⟨hbl, hbr⟩, hall⟩ := hc
  obtain ⟨hlen, heq⟩ := hall ⟨la.bsh, la.img⟩ (by rw [b.has]; exact List.mem_map_of_mem hla)
  simp only at hlen heq
  have hU := Model.allL_mem b.hU la hla x
  let ν := M.enc la.bsh x
  have hWS : M.WS la.bsh.sorts ν := Model.enc_ws la.bsh x
  -- a side, read at the instance, is the side with the answer substituted
  have side : ∀ t, varsBelow c.sh.size t = true →
      M.eval (M.enc c.sh (la.body x)) t = M.eval ν (norm M la.bsh.sorts (subst (nth la.img) t)) := by
    intro t ht
    rw [Model.eval_norm hM hWS, Model.eval_subst]
    refine Model.eval_congr t fun y hy => ?_
    have hys := Model.varsBelow_occurs ht hy
    have hyi : y < la.img.length := hlen ▸ hys
    have hyb : y < (M.encL c.sh (la.body x)).length := by rw [Model.encL_length]; exact hys
    have e := congrArg (·[y]?) hU
    simp only [List.getElem?_map, List.getElem?_eq_getElem hyi, Option.map_some,
      List.getElem?_eq_getElem hyb] at e
    simp only [Model.substV, nth_eq_getElem?, List.getElem?_eq_getElem hyi, Model.enc]
    rw [List.getElem?_eq_getElem hyb]; exact (Option.some.inj e).symm
  have h := (b.hl (la.body x)).symm.trans ((side _ hbl).trans ((congrArg _ (beq_iff.1 heq)).trans
    ((side _ hbr).symm.trans (b.hr (la.body x)))))
  simp only [Option.some.injEq, Sigma.mk.inj_iff, heq_eq_eq, true_and] at h
  exact h

end Reflect
