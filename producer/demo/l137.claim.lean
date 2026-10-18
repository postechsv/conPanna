import conPanna.Unification.Certification.Tactics

/-!
Bakery, the L137 example. The claim (model, problem) is written by the user;
the compiler appends the answers and the proof, from `l137.deriv`.
-/

/- certify
{
  "namespace": "Demo.L137",
  "context": "Nat × ProcSet × ProcSet",
  "vars": [
    "N?",
    "P?",
    "Q?"
  ],
  "ops": {
    "<_,_,_>": "Conf.mk",
    "s": "({0} + 1)",
    "wait": "Mode.wait",
    "idle": "Mode.idle",
    "crit": "Mode.crit"
  }
}
-/

open Unification Certification

namespace Demo.L137

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

def problem : Problem Conf (Nat × ProcSet × ProcSet) :=
  .bind fun (N?, P?, Q?) => (⟨N? + 1, N?, P? + Q?⟩, ⟨N? + 1, N?, {.wait N?}⟩)
