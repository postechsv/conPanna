import conPanna.Unification.Certification.Tactics

/-! No unifiers: X? + {w(N?)} =? X? + {w(N? + 1)}. -/

/- certify
{
  "namespace": "Pipeline.T3",
  "context": "Bag × Bag × Nat × Nat",
  "vars": [
    "X?",
    "Y?",
    "N?",
    "M?"
  ],
  "ops": {
    "w": "Elem.w",
    "s": "({0} + 1)"
  }
}
-/

open Unification Certification

namespace Pipeline.T3

inductive Elem where
  | w (n : Nat)

abbrev Bag := ACU Elem

def problem : Problem Bag (Bag × Bag × Nat × Nat) :=
  .bind fun (X?, _, N?, _) => (X? + {Elem.w N?}, X? + {Elem.w (N? + 1)})
