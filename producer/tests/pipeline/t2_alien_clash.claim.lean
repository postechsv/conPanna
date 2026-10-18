import conPanna.Unification.Certification.Tactics

/-! A singleton against an incompatible one: P? + {wait(N?)} =? Q? + {idle}. -/

/- certify
{
  "namespace": "Pipeline.T2",
  "context": "Nat × ProcSet × ProcSet",
  "vars": [
    "N?",
    "P?",
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

namespace Pipeline.T2

inductive Mode where
  | idle
  | wait (ticket : Nat)
  | crit (ticket : Nat)

abbrev ProcSet := ACU Mode

structure Conf where
  next : Nat
  serving : Nat
  procs : ProcSet

def problem : Problem ProcSet (Nat × ProcSet × ProcSet) :=
  .bind fun (N?, P?, Q?) => (P? + {Mode.wait N?}, Q? + {Mode.idle})
