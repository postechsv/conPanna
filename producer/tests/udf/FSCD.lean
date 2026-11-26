import conPanna.Reflect.Tactic

/-! The running example of FSCD 2022 (LIPIcs.FSCD.2022.8): `X X Y a b c ≟ b b b c Z`, with
repeated arguments (`X` twice on the left, `b` three times on the right). -/

open Unification

namespace UdfTest.FSCD

inductive Elem where
  | a | b | c

abbrev Bag := ACU Elem

open Elem

def problem : Problem Bag (Bag × Bag × Bag) :=
  .bind fun (X, Y, Z) => (X + X + Y + {a} + {b} + {c}, {b} + {b} + {b} + {c} + Z)

/-- Maude's two unifiers: the extra `b` on the right comes from `X` (once, as `X` is
doubled) or from `Y` (twice). -/
def answers : UnifierSet (Bag × Bag × Bag) :=
  [ .bind fun ((U, V) : Bag × Bag) => ({b} + U, V, {a} + U + U + V),
    .bind fun ((U, V) : Bag × Bag) => (U, {b} + {b} + V, {a} + U + U + V) ]

theorem complete : Unification.complete problem answers := by
  certify_comp

theorem sound : Unification.sound problem answers := by
  certify_sound

end UdfTest.FSCD
