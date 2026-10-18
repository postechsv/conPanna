import examples.Bakery.bakery_pf_uncertain
import conPanna.Unification.Tactics.maudeCertifyComp

/-!
Bakery: the obligations of `enter_preserves_inv`, printed by `#obligations` and
pasted verbatim. Completeness is certified by Maude (`maude_certify_comp`);
soundness is checked directly.
-/

namespace Bakery

open Expresso Unification Narrowing

-- the statements below are `#obligations`' output, pasted verbatim
set_option linter.style.longLine false

#obligations enter_preserves_inv

theorem enter_preserves_inv.obligation_1 :
    complete (mayFire enterR initialP)
      [Unifier.bind fun (x : ℕ) => ((x, x, ∅), x, {Mode.wait x}),
        Unifier.bind fun (x : ProcSet × ℕ) => ((x.2, x.2, x.1), x.2, x.1 + {Mode.wait x.2})] := by
  maude_certify_comp

theorem enter_preserves_inv.obligation_2 :
    sound (mayFire enterR initialP)
      [Unifier.bind fun (x : ℕ) => ((x, x, ∅), x, {Mode.wait x}),
        Unifier.bind fun (x : ProcSet × ℕ) => ((x.2, x.2, x.1), x.2, x.1 + {Mode.wait x.2})] := by
  intro u hu γ hγ
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl <;> obtain ⟨x, rfl⟩ := hγ <;>
    simp [unifiedBy, mayFire, enterR, initialP] <;> ac_rfl

theorem enter_preserves_inv.obligation_3 :
    complete (mayFire enterR waitingP)
      [Unifier.bind fun (x : ℕ × ℕ) => ((x.1, x.2, ∅), x.1, x.2, {Mode.wait x.2}),
        Unifier.bind fun (x : ProcSet × ℕ × ℕ) => ((x.2.1, x.2.2, x.1), x.2.1, x.2.2, x.1 + {Mode.wait x.2.2})] := by
  maude_certify_comp

theorem enter_preserves_inv.obligation_4 :
    sound (mayFire enterR waitingP)
      [Unifier.bind fun (x : ℕ × ℕ) => ((x.1, x.2, ∅), x.1, x.2, {Mode.wait x.2}),
        Unifier.bind fun (x : ProcSet × ℕ × ℕ) => ((x.2.1, x.2.2, x.1), x.2.1, x.2.2, x.1 + {Mode.wait x.2.2})] := by
  intro u hu γ hγ
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl <;> obtain ⟨x, rfl⟩ := hγ <;>
    simp [unifiedBy, mayFire, enterR, waitingP] <;> ac_rfl

theorem enter_preserves_inv.obligation_5 :
    complete (mayFire enterR criticalP)
      [Unifier.bind fun (x : ℕ × ℕ) => ((x.1, x.2, {Mode.crit x.2}), x.1, x.2, {Mode.wait x.2}),
        Unifier.bind fun (x : ℕ × ℕ × ProcSet) =>
          ((x.1, x.2.1, x.2.2 + {Mode.crit x.2.1}), x.1, x.2.1, x.2.2 + {Mode.wait x.2.1})] := by
  maude_certify_comp

theorem enter_preserves_inv.obligation_6 :
    sound (mayFire enterR criticalP)
      [Unifier.bind fun (x : ℕ × ℕ) => ((x.1, x.2, {Mode.crit x.2}), x.1, x.2, {Mode.wait x.2}),
        Unifier.bind fun (x : ℕ × ℕ × ProcSet) =>
          ((x.1, x.2.1, x.2.2 + {Mode.crit x.2.1}), x.1, x.2.1, x.2.2 + {Mode.wait x.2.1})] := by
  intro u hu γ hγ
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl <;> obtain ⟨x, rfl⟩ := hγ <;>
    simp [unifiedBy, mayFire, enterR, criticalP] <;> ac_rfl

end Bakery
