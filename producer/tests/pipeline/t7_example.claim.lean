import conPanna.Unification.Certification.Tactics

/-! The worked example of documentation/worked-example.html:
{f ({a} + X?)} + R? =? {f (Y? + W?)} + {f Z?}. -/

/- certify
{
  "namespace": "Pipeline.T7",
  "context": "Fruits × Fruits × Fruits × Fruits × Baskets",
  "vars": [
    "X?",
    "Y?",
    "W?",
    "Z?",
    "R?"
  ],
  "ops": {
    "a": "Fruit.a",
    "b": "Fruit.b",
    "{_}": "Basket.f"
  }
}
-/

open Unification Certification

namespace Pipeline.T7

inductive Fruit where
  | a
  | b

abbrev Fruits := ACU Fruit

inductive Basket where
  | f (x : Fruits)

abbrev Baskets := ACU Basket

def problem : Problem Baskets (Fruits × Fruits × Fruits × Fruits × Baskets) :=
  .bind fun (X?, Y?, W?, Z?, R?) =>
    ({Basket.f ({Fruit.a} + X?)} + R?, {Basket.f (Y? + W?)} + {Basket.f Z?})
