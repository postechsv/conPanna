import conPanna.Unification.Certification.Tactics

/-!
Paper §6.1, mixed free and ACU. The claim (model, problem) is written by the user;
the compiler appends the answers and the proof, from `mixed.deriv`.
-/

/- certify
{
  "namespace": "Demo.Mixed",
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

namespace Demo.Mixed

/-! ## Claim -/

inductive Elem where
  | w (n : Nat)

abbrev Bag := ACU Elem

def problem : Problem Bag (Bag × Bag × Nat × Nat) :=
  .bind fun (X?, Y?, N?, M?) => (X? + {.w N?}, Y? + {.w M?})
