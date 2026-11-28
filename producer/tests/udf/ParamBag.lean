import conPanna.Reflect.Tactic

/-! A bag abbreviation with a parameter, used at two element types: `Bag Color` inside the
elements of `Bag Box`. -/

open Unification

namespace UdfTest.ParamBag

inductive Color where
  | red | blue

abbrev Bag (E : Type) := ACU E

inductive Box where
  | box (c : Bag Color)

open Color Box

/-- `{box(Y)} + X ≟ {box({red} + Z)} + W`. -/
def problem : Problem (Bag Box) (Bag Box × Bag Color × Bag Color × Bag Box) :=
  .bind fun (X, Y, Z, W) => ({box Y} + X, {box ({red} + Z)} + W)

/-- The two boxes are different (each side keeps its own), or the same (`Y := {red} + Z`). -/
def answers : UnifierSet (Bag Box × Bag Color × Bag Color × Bag Box) :=
  [ .bind fun ((Y, Z, U) : Bag Color × Bag Color × Bag Box) => ({box ({red} + Z)} + U, Y, Z, {box Y} + U),
    .bind fun ((Z, U) : Bag Color × Bag Box) => (U, {red} + Z, Z, U) ]

theorem complete : Unification.complete problem answers := by
  certify_comp

theorem sound : Unification.sound problem answers := by
  certify_sound

end UdfTest.ParamBag
