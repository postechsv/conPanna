import Tiny.conPanna.Unification.Certification.Tactics

/-! A linear equation with 2 and 2 bag variables. -/

/- certify
{
  "namespace": "Pipeline.S2Linear22",
  "context": "Bag × Bag × Bag × Bag",
  "vars": [
    "X1?",
    "X2?",
    "Y1?",
    "Y2?"
  ],
  "ops": {}
}
-/

open Unification Certification

namespace Pipeline.S2Linear22

inductive Elem where
  | a

abbrev Bag := ACU Elem

def problem : Problem Bag (Bag × Bag × Bag × Bag) :=
  .bind fun (X1?, X2?, Y1?, Y2?) =>
    (X1? + X2?, Y1? + Y2?)
