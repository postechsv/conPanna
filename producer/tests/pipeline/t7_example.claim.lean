import conPanna.Unification.Certification.Tactics

/-! The worked example of documentation/worked-example.html:
{box ({a} + X?)} + R? =? {box (Y? + W?)} + {box Z?}. -/

/- certify
{
  "namespace": "Pipeline.T7",
  "context": "Bag × Bag × Bag × Bag × Boxes",
  "vars": [
    "X?",
    "Y?",
    "W?",
    "Z?",
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

namespace Pipeline.T7

inductive Elem where
  | a
  | b

abbrev Bag := ACU Elem

inductive Box where
  | box (b : Bag)

abbrev Boxes := ACU Box

def problem : Problem Boxes (Bag × Bag × Bag × Bag × Boxes) :=
  .bind fun (X?, Y?, W?, Z?, R?) =>
    ({Box.box ({Elem.a} + X?)} + R?, {Box.box (Y? + W?)} + {Box.box Z?})
