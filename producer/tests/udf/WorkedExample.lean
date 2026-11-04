import conPanna.Reflect.Tactic

open Unification

namespace WorkedExample

inductive Fruit where
  | a | b

abbrev Fruits := ACU Fruit

inductive Basket where
  | f (x : Fruits)

abbrev Baskets := ACU Basket

open Fruit Basket

def problem : Problem Baskets (Fruits × Fruits × Fruits × Baskets × Baskets × Baskets) :=
  .bind fun (X, Y, W, R, S, T) =>
    (R + {f ({a} + X)} + {f Y}, S + T + {f ({a} + W)})

def answers : UnifierSet (Fruits × Fruits × Fruits × Baskets × Baskets × Baskets) :=
  [ -- A, B into S or T; C from R
    .bind fun ((X, Y, W, Z₁, Z₂) : Fruits × Fruits × Fruits × Baskets × Baskets) =>
      (X, Y, W, {f ({a} + W)} + Z₁ + Z₂, {f ({a} + X)} + {f Y} + Z₁, Z₂),
    .bind fun ((X, Y, W, Z₁, Z₂) : Fruits × Fruits × Fruits × Baskets × Baskets) =>
      (X, Y, W, {f ({a} + W)} + Z₁ + Z₂, {f ({a} + X)} + Z₁, {f Y} + Z₂),
    .bind fun ((X, Y, W, Z₁, Z₂) : Fruits × Fruits × Fruits × Baskets × Baskets) =>
      (X, Y, W, {f ({a} + W)} + Z₁ + Z₂, {f Y} + Z₁, {f ({a} + X)} + Z₂),
    .bind fun ((X, Y, W, Z₁, Z₂) : Fruits × Fruits × Fruits × Baskets × Baskets) =>
      (X, Y, W, {f ({a} + W)} + Z₁ + Z₂, Z₁, {f ({a} + X)} + {f Y} + Z₂),
    -- B = C (Y = {a} ∪ W); A into S or T
    .bind fun ((X, W, Z₁, Z₂) : Fruits × Fruits × Baskets × Baskets) =>
      (X, {a} + W, W, Z₁ + Z₂, {f ({a} + X)} + Z₁, Z₂),
    .bind fun ((X, W, Z₁, Z₂) : Fruits × Fruits × Baskets × Baskets) =>
      (X, {a} + W, W, Z₁ + Z₂, Z₁, {f ({a} + X)} + Z₂),
    -- A = C (X = W); B into S or T
    .bind fun ((Y, W, Z₁, Z₂) : Fruits × Fruits × Baskets × Baskets) =>
      (W, Y, W, Z₁ + Z₂, {f Y} + Z₁, Z₂),
    .bind fun ((Y, W, Z₁, Z₂) : Fruits × Fruits × Baskets × Baskets) =>
      (W, Y, W, Z₁ + Z₂, Z₁, {f Y} + Z₂) ]

theorem complete : Unification.complete problem answers := by
  certify_comp

theorem sound : Unification.sound problem answers := by
  certify_sound

end WorkedExample
