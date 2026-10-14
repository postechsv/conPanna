import Tiny.conPanna.Unification.Certification.Tactics

/-!
Paper §6.2, nonlinear. The claim (model, problem) is written by the user;
the compiler appends the answers and the proof, from `nonlinear.deriv`.
-/

/- certify
{
  "namespace": "Demo.Nonlinear",
  "context": "Bag × Bag × Bag",
  "vars": [
    "X?",
    "Y?",
    "Z?"
  ],
  "ops": {}
}
-/

open Unification Certification

namespace Demo.Nonlinear

/-! ## Claim -/

inductive Elem where
  | a
  | b

abbrev Bag := ACU Elem

def problem : Problem Bag (Bag × Bag × Bag) :=
  .bind fun (X?, Y?, Z?) => (X? + Y?, Z? + Z?)
