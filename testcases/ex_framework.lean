import Expresso.Expresso

namespace ex_framework

/-!
These user-level examples exercise free unification independently of rules.
They deliberately appear after all tactic code so the implementation cannot
depend on their particular model, patterns, or names.
-/

open framework

-- User-defined model for the examples.  It is deliberately not part of the
-- generic free-unification implementation, and it needs no `var` constructor.
inductive Conf where
  | c : Conf
  | f : Conf → Conf → Conf
  deriving Repr

instance : State Conf := ⟨⟩



open Conf

-- The examples intentionally live outside the implementation namespace and
-- come after the tactic implementation.

def pat1 (x1 x2 : Conf) : Conf := f x1 x2
def pat2 (y1 : Conf) : Conf := f (f y1 c) c

/- maude outputs the following unifier as a solution
variant unify in EX1 : f(X1, X2) =? f(f(Y1, c), c) .

Unifier 1
rewrites: 0 in 0ms cpu (0ms real) (~ rewrites/second)
X1 --> f(%1:Term, c)
X2 --> c
Y1 --> %1:Term

No more unifiers.
-/

#print pat1 -- λ x1 x2, f x1 x2
#print pat2 -- λ y1, f (f y1 c) c

end ex_framework
