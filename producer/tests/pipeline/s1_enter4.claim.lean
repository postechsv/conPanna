import conPanna.Unification.Certification.Tactics

/-! Rule ENTER against a state with 4 further waiting processes. -/

/- certify
{
  "namespace": "Pipeline.S1Enter4",
  "context": "Nat × ProcSet × Nat × Nat × Nat × Nat × Nat × ProcSet",
  "vars": [
    "K?",
    "P?",
    "N?",
    "M1?",
    "M2?",
    "M3?",
    "M4?",
    "Q?"
  ],
  "ops": {
    "<_,_,_>": "Conf.mk",
    "s": "({0} + 1)",
    "z": "0",
    "wait": "Mode.wait",
    "idle": "Mode.idle",
    "crit": "Mode.crit"
  }
}
-/

open Unification Certification

namespace Pipeline.S1Enter4

inductive Mode where
  | idle
  | wait (ticket : Nat)
  | crit (ticket : Nat)

abbrev ProcSet := ACU Mode

structure Conf where
  next : Nat
  serving : Nat
  procs : ProcSet

def problem : Problem Conf (Nat × ProcSet × Nat × Nat × Nat × Nat × Nat × ProcSet) :=
  .bind fun (K?, P?, N?, M1?, M2?, M3?, M4?, Q?) =>
    (⟨K? + 1, K?, {Mode.wait K?} + P?⟩, ⟨N? + 1, N?, {Mode.wait N?} + {Mode.idle} + {Mode.wait M1?} + {Mode.wait M2?} + {Mode.wait M3?} + {Mode.wait M4?} + Q?⟩)
