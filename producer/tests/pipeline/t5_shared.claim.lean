import Tiny.conPanna.Unification.Certification.Tactics

/-! A system sharing a bag variable: X? + Y? =? Z? + {a} and Y? =? W? + {b}. -/

/- certify
{
  "namespace": "Pipeline.T5",
  "context": "Bag × Bag × Bag × Bag",
  "vars": [
    "X?",
    "Y?",
    "Z?",
    "W?"
  ],
  "ops": {
    "a": "Elem.a",
    "b": "Elem.b"
  }
}
-/

open Unification Certification

namespace Pipeline.T5

inductive Elem where
  | a
  | b

abbrev Bag := ACU Elem

def problem : Problem (Bag × Bag) (Bag × Bag × Bag × Bag) :=
  .bind fun (X?, Y?, Z?, W?) => ((X? + Y?, Y?), (Z? + {Elem.a}, W? + {Elem.b}))
