import examples.Bakery.bakery_pf_draft
import conPanna.Unification.Tactics.maudeCertifyComp

/-!
Bakery: the obligations of `bakery_preserves_inv` (the whole system narrowed at once),
printed by `#obligations` and pasted verbatim. Completeness is certified by Maude
(`maude_certify_comp`); soundness is left open for now.
-/

namespace Bakery

open Expresso Unification Narrowing

-- the statements below are `#obligations`' output, pasted verbatim
set_option linter.style.longLine false

#obligations bakery_preserves_inv

theorem bakery_preserves_inv.obligation_1 :
    complete (mayFire wakeR initialP)
      [Unifier.bind fun (x : ℕ) => ((x, x, ∅), x, {Mode.idle}),
        Unifier.bind fun (x : ProcSet × ℕ) => ((x.2, x.2, x.1), x.2, {Mode.idle} + x.1)] := by
  maude_certify_comp

theorem bakery_preserves_inv.obligation_2 :
    sound (mayFire wakeR initialP)
      [Unifier.bind fun (x : ℕ) => ((x, x, ∅), x, {Mode.idle}),
        Unifier.bind fun (x : ProcSet × ℕ) => ((x.2, x.2, x.1), x.2, {Mode.idle} + x.1)] := by
  sorry

theorem bakery_preserves_inv.obligation_3 :
    complete (mayFire wakeR waitingP)
      [Unifier.bind fun (x : ℕ × ℕ) => ((x.1, x.2, ∅), x.1, x.2, {Mode.idle}),
        Unifier.bind fun (x : ProcSet × ℕ × ℕ) => ((x.2.1, x.2.2, x.1), x.2.1, x.2.2, {Mode.idle} + x.1)] := by
  maude_certify_comp

theorem bakery_preserves_inv.obligation_4 :
    sound (mayFire wakeR waitingP)
      [Unifier.bind fun (x : ℕ × ℕ) => ((x.1, x.2, ∅), x.1, x.2, {Mode.idle}),
        Unifier.bind fun (x : ProcSet × ℕ × ℕ) => ((x.2.1, x.2.2, x.1), x.2.1, x.2.2, {Mode.idle} + x.1)] := by
  sorry

theorem bakery_preserves_inv.obligation_5 :
    complete (mayFire wakeR criticalP)
      [Unifier.bind fun (x : ℕ × ℕ) => ((x.1, x.2, {Mode.crit x.2}), x.1, x.2, {Mode.idle}),
        Unifier.bind fun (x : ℕ × ℕ × ProcSet) =>
          ((x.1, x.2.1, x.2.2 + {Mode.crit x.2.1}), x.1, x.2.1, {Mode.idle} + x.2.2)] := by
  maude_certify_comp

theorem bakery_preserves_inv.obligation_6 :
    sound (mayFire wakeR criticalP)
      [Unifier.bind fun (x : ℕ × ℕ) => ((x.1, x.2, {Mode.crit x.2}), x.1, x.2, {Mode.idle}),
        Unifier.bind fun (x : ℕ × ℕ × ProcSet) =>
          ((x.1, x.2.1, x.2.2 + {Mode.crit x.2.1}), x.1, x.2.1, {Mode.idle} + x.2.2)] := by
  sorry

theorem bakery_preserves_inv.obligation_7 :
    complete (mayFire enterR initialP)
      [Unifier.bind fun (x : ℕ) => ((x, x, ∅), x, {Mode.wait x}),
        Unifier.bind fun (x : ProcSet × ℕ) => ((x.2, x.2, x.1), x.2, x.1 + {Mode.wait x.2})] := by
  maude_certify_comp

theorem bakery_preserves_inv.obligation_8 :
    sound (mayFire enterR initialP)
      [Unifier.bind fun (x : ℕ) => ((x, x, ∅), x, {Mode.wait x}),
        Unifier.bind fun (x : ProcSet × ℕ) => ((x.2, x.2, x.1), x.2, x.1 + {Mode.wait x.2})] := by
  sorry

theorem bakery_preserves_inv.obligation_9 :
    complete (mayFire enterR waitingP)
      [Unifier.bind fun (x : ℕ × ℕ) => ((x.1, x.2, ∅), x.1, x.2, {Mode.wait x.2}),
        Unifier.bind fun (x : ProcSet × ℕ × ℕ) => ((x.2.1, x.2.2, x.1), x.2.1, x.2.2, x.1 + {Mode.wait x.2.2})] := by
  maude_certify_comp

theorem bakery_preserves_inv.obligation_10 :
    sound (mayFire enterR waitingP)
      [Unifier.bind fun (x : ℕ × ℕ) => ((x.1, x.2, ∅), x.1, x.2, {Mode.wait x.2}),
        Unifier.bind fun (x : ProcSet × ℕ × ℕ) => ((x.2.1, x.2.2, x.1), x.2.1, x.2.2, x.1 + {Mode.wait x.2.2})] := by
  sorry

theorem bakery_preserves_inv.obligation_11 :
    complete (mayFire enterR criticalP)
      [Unifier.bind fun (x : ℕ × ℕ) => ((x.1, x.2, {Mode.crit x.2}), x.1, x.2, {Mode.wait x.2}),
        Unifier.bind fun (x : ℕ × ℕ × ProcSet) =>
          ((x.1, x.2.1, x.2.2 + {Mode.crit x.2.1}), x.1, x.2.1, x.2.2 + {Mode.wait x.2.1})] := by
  maude_certify_comp

theorem bakery_preserves_inv.obligation_12 :
    sound (mayFire enterR criticalP)
      [Unifier.bind fun (x : ℕ × ℕ) => ((x.1, x.2, {Mode.crit x.2}), x.1, x.2, {Mode.wait x.2}),
        Unifier.bind fun (x : ℕ × ℕ × ProcSet) =>
          ((x.1, x.2.1, x.2.2 + {Mode.crit x.2.1}), x.1, x.2.1, x.2.2 + {Mode.wait x.2.1})] := by
  sorry

theorem bakery_preserves_inv.obligation_13 :
    complete (mayFire exitR initialP)
      [Unifier.bind fun (x : ℕ) => ((x, x, ∅), x, {Mode.crit x}),
        Unifier.bind fun (x : ProcSet × ℕ) => ((x.2, x.2, x.1), x.2, x.1 + {Mode.crit x.2})] := by
  maude_certify_comp

theorem bakery_preserves_inv.obligation_14 :
    sound (mayFire exitR initialP)
      [Unifier.bind fun (x : ℕ) => ((x, x, ∅), x, {Mode.crit x}),
        Unifier.bind fun (x : ProcSet × ℕ) => ((x.2, x.2, x.1), x.2, x.1 + {Mode.crit x.2})] := by
  sorry

theorem bakery_preserves_inv.obligation_15 :
    complete (mayFire exitR waitingP)
      [Unifier.bind fun (x : ℕ × ℕ) => ((x.1, x.2, ∅), x.1, x.2, {Mode.crit x.2}),
        Unifier.bind fun (x : ProcSet × ℕ × ℕ) => ((x.2.1, x.2.2, x.1), x.2.1, x.2.2, x.1 + {Mode.crit x.2.2})] := by
  maude_certify_comp

theorem bakery_preserves_inv.obligation_16 :
    sound (mayFire exitR waitingP)
      [Unifier.bind fun (x : ℕ × ℕ) => ((x.1, x.2, ∅), x.1, x.2, {Mode.crit x.2}),
        Unifier.bind fun (x : ProcSet × ℕ × ℕ) => ((x.2.1, x.2.2, x.1), x.2.1, x.2.2, x.1 + {Mode.crit x.2.2})] := by
  sorry

theorem bakery_preserves_inv.obligation_17 :
    complete (mayFire exitR criticalP)
      [Unifier.bind fun (x : ℕ × ℕ) => ((x.1, x.2, {Mode.crit x.2}), x.1, x.2, {Mode.crit x.2}),
        Unifier.bind fun (x : ℕ × ℕ × ProcSet) =>
          ((x.1, x.2.1, x.2.2 + {Mode.crit x.2.1}), x.1, x.2.1, x.2.2 + {Mode.crit x.2.1}),
        Unifier.bind fun (x : ℕ × ℕ) => ((x.1, x.2, ∅), x.1, x.2, ∅),
        Unifier.bind fun (x : ℕ × ℕ × ProcSet) => ((x.1, x.2.1, x.2.2), x.1, x.2.1, x.2.2)] := by
  maude_certify_comp

theorem bakery_preserves_inv.obligation_18 :
    sound (mayFire exitR criticalP)
      [Unifier.bind fun (x : ℕ × ℕ) => ((x.1, x.2, {Mode.crit x.2}), x.1, x.2, {Mode.crit x.2}),
        Unifier.bind fun (x : ℕ × ℕ × ProcSet) =>
          ((x.1, x.2.1, x.2.2 + {Mode.crit x.2.1}), x.1, x.2.1, x.2.2 + {Mode.crit x.2.1}),
        Unifier.bind fun (x : ℕ × ℕ) => ((x.1, x.2, ∅), x.1, x.2, ∅),
        Unifier.bind fun (x : ℕ × ℕ × ProcSet) => ((x.1, x.2.1, x.2.2), x.1, x.2.1, x.2.2)] := by
  sorry

end Bakery
