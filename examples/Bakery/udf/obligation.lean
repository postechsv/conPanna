import examples.Bakery.udf.pf
import conPanna.Unification.Tactics.udfCertify

/-! Test (udf branch): the obligations of `bakery_preserves_inv` as `#obligations` prints
them. Completeness by the certificate narrowing stored (`udf_certify`, no Maude call);
soundness and the post's subsumption are left open. -/

set_option linter.style.longLine false
open Expresso Unification Narrowing

theorem Bakery.bakery_preserves_inv.obligation_1 :
    Expresso.isOverPost Bakery.bakery Bakery.invP Bakery.invP := by
  sorry

theorem Bakery.bakery_preserves_inv.obligation_2 :
    Unification.complete (Narrowing.mayFire Bakery.wakeR Bakery.initialP)
      [Unification.Unifier.bind fun (x : Bakery.ProcSet × ℕ) => ((x.2, x.2, x.1), x.2, {Bakery.Mode.idle} + x.1)] := by
  udf_certify

theorem Bakery.bakery_preserves_inv.obligation_3 :
    Unification.sound (Narrowing.mayFire Bakery.wakeR Bakery.initialP)
      [Unification.Unifier.bind fun (x : Bakery.ProcSet × ℕ) => ((x.2, x.2, x.1), x.2, {Bakery.Mode.idle} + x.1)] := by
  sorry

theorem Bakery.bakery_preserves_inv.obligation_4 :
    Unification.complete (Narrowing.mayFire Bakery.wakeR Bakery.waitingP)
      [Unification.Unifier.bind fun (x : Bakery.ProcSet × ℕ × ℕ) =>
          ((x.2.1, x.2.2, x.1), x.2.1, x.2.2, {Bakery.Mode.idle} + x.1)] := by
  udf_certify

theorem Bakery.bakery_preserves_inv.obligation_5 :
    Unification.sound (Narrowing.mayFire Bakery.wakeR Bakery.waitingP)
      [Unification.Unifier.bind fun (x : Bakery.ProcSet × ℕ × ℕ) =>
          ((x.2.1, x.2.2, x.1), x.2.1, x.2.2, {Bakery.Mode.idle} + x.1)] := by
  sorry

theorem Bakery.bakery_preserves_inv.obligation_6 :
    Unification.complete (Narrowing.mayFire Bakery.wakeR Bakery.criticalP)
      [Unification.Unifier.bind fun (x : ℕ × ℕ × Bakery.ProcSet) =>
          ((x.1, x.2.1, {Bakery.Mode.crit x.2.1} + x.2.2), x.1, x.2.1, {Bakery.Mode.idle} + x.2.2)] := by
  udf_certify

theorem Bakery.bakery_preserves_inv.obligation_7 :
    Unification.sound (Narrowing.mayFire Bakery.wakeR Bakery.criticalP)
      [Unification.Unifier.bind fun (x : ℕ × ℕ × Bakery.ProcSet) =>
          ((x.1, x.2.1, {Bakery.Mode.crit x.2.1} + x.2.2), x.1, x.2.1, {Bakery.Mode.idle} + x.2.2)] := by
  sorry

theorem Bakery.bakery_preserves_inv.obligation_8 :
    Unification.complete (Narrowing.mayFire Bakery.enterR Bakery.initialP)
      [Unification.Unifier.bind fun (x : Bakery.ProcSet × ℕ) =>
          ((x.2, x.2, x.1), x.2, {Bakery.Mode.wait x.2} + x.1)] := by
  udf_certify

theorem Bakery.bakery_preserves_inv.obligation_9 :
    Unification.sound (Narrowing.mayFire Bakery.enterR Bakery.initialP)
      [Unification.Unifier.bind fun (x : Bakery.ProcSet × ℕ) =>
          ((x.2, x.2, x.1), x.2, {Bakery.Mode.wait x.2} + x.1)] := by
  sorry

theorem Bakery.bakery_preserves_inv.obligation_10 :
    Unification.complete (Narrowing.mayFire Bakery.enterR Bakery.waitingP)
      [Unification.Unifier.bind fun (x : Bakery.ProcSet × ℕ × ℕ) =>
          ((x.2.1, x.2.2, x.1), x.2.1, x.2.2, {Bakery.Mode.wait x.2.2} + x.1)] := by
  udf_certify

theorem Bakery.bakery_preserves_inv.obligation_11 :
    Unification.sound (Narrowing.mayFire Bakery.enterR Bakery.waitingP)
      [Unification.Unifier.bind fun (x : Bakery.ProcSet × ℕ × ℕ) =>
          ((x.2.1, x.2.2, x.1), x.2.1, x.2.2, {Bakery.Mode.wait x.2.2} + x.1)] := by
  sorry

theorem Bakery.bakery_preserves_inv.obligation_12 :
    Unification.complete (Narrowing.mayFire Bakery.enterR Bakery.criticalP)
      [Unification.Unifier.bind fun (x : ℕ × ℕ × Bakery.ProcSet) =>
          ((x.1, x.2.1, {Bakery.Mode.crit x.2.1} + x.2.2), x.1, x.2.1, {Bakery.Mode.wait x.2.1} + x.2.2)] := by
  udf_certify

theorem Bakery.bakery_preserves_inv.obligation_13 :
    Unification.sound (Narrowing.mayFire Bakery.enterR Bakery.criticalP)
      [Unification.Unifier.bind fun (x : ℕ × ℕ × Bakery.ProcSet) =>
          ((x.1, x.2.1, {Bakery.Mode.crit x.2.1} + x.2.2), x.1, x.2.1, {Bakery.Mode.wait x.2.1} + x.2.2)] := by
  sorry

theorem Bakery.bakery_preserves_inv.obligation_14 :
    Unification.complete (Narrowing.mayFire Bakery.exitR Bakery.initialP)
      [Unification.Unifier.bind fun (x : Bakery.ProcSet × ℕ) =>
          ((x.2, x.2, x.1), x.2, {Bakery.Mode.crit x.2} + x.1)] := by
  udf_certify

theorem Bakery.bakery_preserves_inv.obligation_15 :
    Unification.sound (Narrowing.mayFire Bakery.exitR Bakery.initialP)
      [Unification.Unifier.bind fun (x : Bakery.ProcSet × ℕ) =>
          ((x.2, x.2, x.1), x.2, {Bakery.Mode.crit x.2} + x.1)] := by
  sorry

theorem Bakery.bakery_preserves_inv.obligation_16 :
    Unification.complete (Narrowing.mayFire Bakery.exitR Bakery.waitingP)
      [Unification.Unifier.bind fun (x : Bakery.ProcSet × ℕ × ℕ) =>
          ((x.2.1, x.2.2, x.1), x.2.1, x.2.2, {Bakery.Mode.crit x.2.2} + x.1)] := by
  udf_certify

theorem Bakery.bakery_preserves_inv.obligation_17 :
    Unification.sound (Narrowing.mayFire Bakery.exitR Bakery.waitingP)
      [Unification.Unifier.bind fun (x : Bakery.ProcSet × ℕ × ℕ) =>
          ((x.2.1, x.2.2, x.1), x.2.1, x.2.2, {Bakery.Mode.crit x.2.2} + x.1)] := by
  sorry

theorem Bakery.bakery_preserves_inv.obligation_18 :
    Unification.complete (Narrowing.mayFire Bakery.exitR Bakery.criticalP)
      [Unification.Unifier.bind fun (x : ℕ × ℕ × Bakery.ProcSet) => ((x.1, x.2.1, x.2.2), x.1, x.2.1, x.2.2)] := by
  udf_certify

theorem Bakery.bakery_preserves_inv.obligation_19 :
    Unification.sound (Narrowing.mayFire Bakery.exitR Bakery.criticalP)
      [Unification.Unifier.bind fun (x : ℕ × ℕ × Bakery.ProcSet) => ((x.1, x.2.1, x.2.2), x.1, x.2.1, x.2.2)] := by
  sorry

#link Bakery.bakery_preserves_inv
#claims Bakery.bakery_preserves_inv.linked
#print axioms Bakery.bakery_preserves_inv.linked
