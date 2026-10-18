import conPanna.Unification.Certification.Tactics

/-!
No unifiers, by a free clash: a successor is never zero. The claim (model,
problem) is written by the user; the compiler appends the (empty) answers and
the proof, from `clash.deriv`.
-/

/- certify
{
  "namespace": "Demo.Clash",
  "context": "Nat × ProcSet × Nat × ProcSet",
  "vars": ["N?", "P?", "M?", "Q?"],
  "ops": {"<_,_,_>": "Conf.mk", "s": "({0} + 1)", "z": "0",
          "wait": "Mode.wait", "idle": "Mode.idle", "crit": "Mode.crit"}
}
-/

open Unification Certification

namespace Demo.Clash

/-! ## Claim -/

inductive Mode where
  | idle
  | wait (ticket : Nat)
  | crit (ticket : Nat)

abbrev ProcSet := ACU Mode

structure Conf where
  next : Nat
  serving : Nat
  procs : ProcSet

def problem : Problem Conf (Nat × ProcSet × Nat × ProcSet) :=
  .bind fun (N?, P?, M?, Q?) => (⟨N? + 1, N?, P?⟩, ⟨0, M?, Q?⟩)

/-! ## Generated from clash.deriv by producer/tools/compile.py -/

def answers : UnifierSet (Nat × ProcSet × Nat × ProcSet) :=
  []

theorem complete : Unification.complete problem answers := by
  rw [← start_iff]
  -- ⊢ - | Conf.mk (N? + 1) N? P? = Conf.mk 0 M? Q? | -
  -- decomp Conf.mk (N? + 1) N? P? = Conf.mk 0 M? Q?
  refine decomp (fun (N?, P?, M?, Q?) => (N? + 1) = 0 ∧ N? = M? ∧ P? = Q?)
      (fun (N?, P?, M?, Q?) h => by acu_free [problem]) ?_
  -- ⊢ - | (N? + 1) = 0; N? = M?; P? = Q? | -
  -- clash
  exact clash fun (N?, P?, M?, Q?) h hD => by acu_free [problem]

end Demo.Clash
