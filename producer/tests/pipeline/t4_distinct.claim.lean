import Tiny.conPanna.Unification.Certification.Tactics

/-! A system: X? + {w(N?)} =? Y? + {w(M?)} and N? =? M?. -/

/- certify
{
  "namespace": "Pipeline.T4",
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

namespace Pipeline.T4

inductive Elem where
  | w (n : Nat)

abbrev Bag := ACU Elem

def problem : Problem (Bag × Nat) (Bag × Bag × Nat × Nat) :=
  .bind fun (X?, Y?, N?, M?) => ((X? + {Elem.w N?}, N?), (Y? + {Elem.w M?}, M?))
