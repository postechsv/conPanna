import conPanna.Unification.Certification.Tactics

/-!
Bakery, unknown bags on both sides. The claim (model, problem) is written by the
user; the compiler appends the answers and the proof, from `bakery2.deriv`.
-/

/- certify
{
  "namespace": "Demo.Bakery2",
  "context": "Nat × ProcSet × ProcSet × ProcSet",
  "vars": [
    "N?",
    "P?",
    "Q?",
    "R?"
  ],
  "ops": {
    "wait": "Mode.wait",
    "idle": "Mode.idle",
    "crit": "Mode.crit"
  }
}
-/

open Unification Certification

namespace Demo.Bakery2

/-! ## Claim -/

inductive Mode where
  | idle
  | wait (ticket : Nat)
  | crit (ticket : Nat)

abbrev ProcSet := ACU Mode

def problem : Problem ProcSet (Nat × ProcSet × ProcSet × ProcSet) :=
  .bind fun (N?, P?, Q?, R?) => (P? + Q?, {.wait N?} + R?)
