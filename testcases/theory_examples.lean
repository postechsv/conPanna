import conPanna.conPanna

namespace theory_examples

/-!
These declarations demonstrate that theories register symbols uniformly
across arities and sorts. They exercise only the declarative theory interface,
not a particular user model or unification proof.
-/

/-- Representative operations of several arities and sorts. -/
def zeroSymbol : Nat := 0
def increment (value : Nat) : Nat := value + 1
def firstOfThree (first _second _third : Nat) : Nat := first
def select (value : Nat) (enabled : Bool) : Nat :=
  if enabled then value else 0

/--
All arities use the same declaration function.  `select` also demonstrates
that argument sorts need not be homogeneous.
-/
def MixedArityFree : Theory where
  symbols := [
    Theory.Symbol.declare zeroSymbol,
    Theory.Symbol.declare increment,
    Theory.Symbol.declare firstOfThree,
    Theory.Symbol.declare select
  ]

/- `Nat.add` needs no new law proofs: its existing theorems populate the
operator-law list. This declaration does not claim that AC is the full
arithmetic theory; it selects the theory used for unification. -/
def NatAC : Theory where
  symbols := [Theory.Symbol.declare Nat.add [
    .associative Nat.add_assoc,
    .commutative Nat.add_comm
  ]]

end theory_examples
