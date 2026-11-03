import examples.Bakery.proof
import Reflect.Tactic

set_option linter.style.longLine false

#reflect_model Bakery.Conf

theorem R.bakery_preserves_inv.obligation_1 :
    Unification.complete (Narrowing.mayFire Bakery.wakeR Bakery.initialP)
      [Unification.Unifier.bind fun (x : Bakery.ProcSet × ℕ) => ((x.2, x.2, x.1), x.2, {Bakery.Mode.idle} + x.1)] := by
  udf_reflect

theorem R.bakery_preserves_inv.obligation_3 :
    Unification.complete (Narrowing.mayFire Bakery.wakeR Bakery.waitingP)
      [Unification.Unifier.bind fun (x : Bakery.ProcSet × ℕ × ℕ) =>
          ((x.2.1, x.2.2, x.1), x.2.1, x.2.2, {Bakery.Mode.idle} + x.1)] := by
  udf_reflect

theorem R.bakery_preserves_inv.obligation_5 :
    Unification.complete (Narrowing.mayFire Bakery.wakeR Bakery.criticalP)
      [Unification.Unifier.bind fun (x : ℕ × ℕ × Bakery.ProcSet) =>
          ((x.1, x.2.1, {Bakery.Mode.crit x.2.1} + x.2.2), x.1, x.2.1, {Bakery.Mode.idle} + x.2.2)] := by
  udf_reflect

theorem R.bakery_preserves_inv.obligation_7 :
    Unification.complete (Narrowing.mayFire Bakery.enterR Bakery.initialP)
      [Unification.Unifier.bind fun (x : Bakery.ProcSet × ℕ) =>
          ((x.2, x.2, x.1), x.2, {Bakery.Mode.wait x.2} + x.1)] := by
  udf_reflect

theorem R.bakery_preserves_inv.obligation_9 :
    Unification.complete (Narrowing.mayFire Bakery.enterR Bakery.waitingP)
      [Unification.Unifier.bind fun (x : Bakery.ProcSet × ℕ × ℕ) =>
          ((x.2.1, x.2.2, x.1), x.2.1, x.2.2, {Bakery.Mode.wait x.2.2} + x.1)] := by
  udf_reflect

theorem R.bakery_preserves_inv.obligation_11 :
    Unification.complete (Narrowing.mayFire Bakery.enterR Bakery.criticalP)
      [Unification.Unifier.bind fun (x : ℕ × ℕ × Bakery.ProcSet) =>
          ((x.1, x.2.1, {Bakery.Mode.crit x.2.1} + x.2.2), x.1, x.2.1, {Bakery.Mode.wait x.2.1} + x.2.2)] := by
  udf_reflect

theorem R.bakery_preserves_inv.obligation_13 :
    Unification.complete (Narrowing.mayFire Bakery.exitR Bakery.initialP)
      [Unification.Unifier.bind fun (x : Bakery.ProcSet × ℕ) =>
          ((x.2, x.2, x.1), x.2, {Bakery.Mode.crit x.2} + x.1)] := by
  udf_reflect

theorem R.bakery_preserves_inv.obligation_15 :
    Unification.complete (Narrowing.mayFire Bakery.exitR Bakery.waitingP)
      [Unification.Unifier.bind fun (x : Bakery.ProcSet × ℕ × ℕ) =>
          ((x.2.1, x.2.2, x.1), x.2.1, x.2.2, {Bakery.Mode.crit x.2.2} + x.1)] := by
  udf_reflect

theorem R.bakery_preserves_inv.obligation_17 :
    Unification.complete (Narrowing.mayFire Bakery.exitR Bakery.criticalP)
      [Unification.Unifier.bind fun (x : ℕ × ℕ × Bakery.ProcSet) => ((x.1, x.2.1, x.2.2), x.1, x.2.1, x.2.2)] := by
  udf_reflect

theorem R.abortable_preserves_inv.obligation_1 :
    Unification.complete (Narrowing.mayFire Bakery.abortR Bakery.initialP)
      [Unification.Unifier.bind fun (x : Bakery.ProcSet × ℕ × ℕ) =>
          ((x.2.2, x.2.2, x.2.1, x.1), x.2.2, {Bakery.Mode.wait x.2.1} + x.1)] := by
  udf_reflect

theorem R.abortable_preserves_inv.obligation_3 :
    Unification.complete (Narrowing.mayFire Bakery.abortR Bakery.waitingP)
      [Unification.Unifier.bind fun (x : Bakery.ProcSet × ℕ × ℕ × ℕ) =>
          ((x.2.2.1, x.2.2.2, x.2.1, x.1), x.2.2.1, x.2.2.2, {Bakery.Mode.wait x.2.1} + x.1)] := by
  udf_reflect

theorem R.abortable_preserves_inv.obligation_5 :
    Unification.complete (Narrowing.mayFire Bakery.abortR Bakery.criticalP)
      [Unification.Unifier.bind fun (x : ℕ × ℕ × ℕ × Bakery.ProcSet) =>
          ((x.2.1, x.2.2.1, x.1, {Bakery.Mode.crit x.2.2.1} + x.2.2.2), x.2.1, x.2.2.1,
            {Bakery.Mode.wait x.1} + x.2.2.2)] := by
  udf_reflect

theorem R.abortable_preserves_inv.obligation_7 :
    Unification.complete (Narrowing.mayFire Bakery.skipR Bakery.initialP)
      [Unification.Unifier.bind fun (x : ℕ × Bakery.ProcSet) => ((x.1, x.1, x.2), x.1, x.2)] := by
  udf_reflect

theorem R.abortable_preserves_inv.obligation_9 :
    Unification.complete (Narrowing.mayFire Bakery.skipR Bakery.waitingP)
      [Unification.Unifier.bind fun (x : ℕ × ℕ × Bakery.ProcSet) => ((x.1, x.2.1, x.2.2), x.1, x.2.1, x.2.2)] := by
  udf_reflect

theorem R.abortable_preserves_inv.obligation_11 :
    Unification.complete (Narrowing.mayFire Bakery.skipR Bakery.criticalP)
      [Unification.Unifier.bind fun (x : ℕ × ℕ × Bakery.ProcSet) =>
          ((x.1, x.2.1, {Bakery.Mode.crit x.2.1} + x.2.2), x.1, x.2.1, x.2.2)] := by
  udf_reflect


#print axioms R.bakery_preserves_inv.obligation_1
