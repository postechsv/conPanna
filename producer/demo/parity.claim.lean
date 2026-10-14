import Tiny.conPanna.Unification.Certification.Tactics

/-!
No unifiers, by parity: at the element `a` the counts would satisfy 2x = 2y + 1.
The claim (model, problem) is written by the user; the compiler appends the
(empty) answers and the proof, from `parity.deriv`.
-/

/- certify
{
  "namespace": "Demo.Parity",
  "context": "Bag × Bag",
  "vars": ["X?", "Y?"],
  "ops": {"a": "Elem.a", "b": "Elem.b"}
}
-/

open Unification Certification

namespace Demo.Parity

/-! ## Claim -/

inductive Elem where
  | a
  | b

abbrev Bag := ACU Elem

def problem : Problem Bag (Bag × Bag) :=
  .bind fun (X?, Y?) => (X? + X?, Y? + Y? + {Elem.a})
