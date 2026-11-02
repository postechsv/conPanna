import conPanna.Unification.Tactics.udfCertify

/-! `X + {w(N)} = Y + {w(M)}`: the aliens are merged (N = M) or kept apart. -/

open Unification

namespace UdfTest.T4

inductive Elem where
  | w (n : Nat)

abbrev Bag := ACU Elem

def problem : Problem Bag (Bag × Bag × Nat × Nat) :=
  .bind fun (X, Y, N, M) => (X + {Elem.w N}, Y + {Elem.w M})

def answers : UnifierSet (Bag × Bag × Nat × Nat) :=
  [.bind fun ((Z, U) : Bag × Nat) => (Z, Z, U, U),
   .bind fun ((Z, N, M) : Bag × Nat × Nat) => (Z + {Elem.w M}, Z + {Elem.w N}, N, M)]


theorem complete : Unification.complete problem answers := by
  udf_certify

end UdfTest.T4
