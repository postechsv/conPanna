import conPanna.Unification.Certification.Tactics

/-! The worked example of documentation/worked-example.html:
R? + {f ({a} + X?)} + {f Y?} =? S? + T? + {f ({a} + W?)}. -/

/- certify
{
  "namespace": "Pipeline.T7",
  "context": "Fruits × Fruits × Fruits × Baskets × Baskets × Baskets",
  "vars": ["X?", "Y?", "W?", "R?", "S?", "T?"],
  "ops": {"a": "Fruit.a", "b": "Fruit.b", "{_}": "Basket.f"}
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

def problem : Problem Baskets (Fruits × Fruits × Fruits × Baskets × Baskets × Baskets) :=
  .bind fun (X?, Y?, W?, R?, S?, T?) =>
    (R? + {Basket.f ({Fruit.a} + X?)} + {Basket.f Y?}, S? + T? + {Basket.f ({Fruit.a} + W?)})
