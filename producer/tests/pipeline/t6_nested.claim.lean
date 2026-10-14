import Tiny.conPanna.Unification.Certification.Tactics

/-! Nested bags: {box X?} + R? =? {box ({a} + Y?)} + {box {b}}. -/

/- certify
{
  "namespace": "Pipeline.T6",
  "context": "Bag × Bag × Boxes",
  "vars": [
    "X?",
    "Y?",
    "R?"
  ],
  "ops": {
    "a": "Elem.a",
    "b": "Elem.b",
    "{_}": "Box.box"
  }
}
-/

open Unification Certification

namespace Pipeline.T6

inductive Elem where
  | a
  | b

abbrev Bag := ACU Elem

inductive Box where
  | box (b : Bag)

abbrev Boxes := ACU Box

def problem : Problem Boxes (Bag × Bag × Boxes) :=
  .bind fun (X?, Y?, R?) =>
    ({Box.box X?} + R?, {Box.box ({Elem.a} + Y?)} + {Box.box {Elem.b}})
