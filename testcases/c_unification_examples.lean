import conPanna.conPanna

namespace c_unification_examples

/-!
These examples provide a user-defined free-commutative operation and a theory
that registers its structural law. They demonstrate multi-MGU exposure through
the same interface as free unification.
-/

open framework

/-!
`Conf` has the same shape as an ordinary user model: it contains only concrete
configuration constructors and no constructor for logical variables.  The
commutative `f` is a separate function symbol rather than an ordered inductive
constructor.  Its equational laws are part of this example model, not the
tactic, and all tactic code still appears above these declarations.
-/

inductive Conf where
  | atom : Nat → Conf
  | g : Conf → Conf → Conf
  deriving Repr

instance : State Conf := ⟨⟩

-- A function symbol of the model.  It is deliberately not a `Conf`
-- constructor, so its commutativity does not conflict with constructor
-- injectivity.
axiom f : Conf → Conf → Conf

/-- The characteristic equality law of a free commutative constructor. -/
axiom f_eq_iff (a b c d : Conf) :
  f a b = f c d ↔ (a = c ∧ b = d) ∨ (a = d ∧ b = c)

axiom f_comm (a b : Conf) : f a b = f b a

/-- Register `f`; `c_unify` discovers this instance by typeclass synthesis. -/
instance : Unification.C.Operator f where
  comm := f_comm
  eq_iff := f_eq_iff

/-!
`Theory1` registers `f` with the same declaration function used for every arity.
Only the commutative law is binary-specific. The ordinary constructor `g`
is absent and is therefore free.
-/
noncomputable def Theory1 : Theory where
  symbols := [Theory.Symbol.declare f [
    .commutative f_comm
  ]]

noncomputable def combineThree (first second third : Conf) : Conf :=
  Conf.g (Conf.g first second) third

/-- One uniform list containing unary, free binary, C, and ternary symbols. -/
noncomputable def MixedTheory : Theory where
  symbols := [
    Theory.Symbol.declare Conf.atom,
    Theory.Symbol.declare Conf.g,
    Theory.Symbol.declare f [.commutative f_comm],
    Theory.Symbol.declare combineThree
  ]

-- The same registration is visible to standard Lean tooling.
example (a b : Conf) : f a b = f b a := by
  exact Std.Commutative.comm a b

noncomputable def pairLeft (x y : Conf) : Conf := f x y
noncomputable def pairRight (a b : Conf) : Conf := f a b

#print pairLeft
#print pairRight

-- There are two MGUs: the direct pairing and the swapped pairing.  Each is
-- exposed through exactly the same basis-variable/equation interface as the
-- free `unify` tactic, so this proof receives two goals.
example (h : pairLeft ⋈[Theory1] pairRight) : True := by
  unify h in Theory1
  · unify_complete
  · guard_hyp u1 : Conf
    guard_hyp u2 : Conf
    guard_hyp h1 : x = u1
    guard_hyp h2 : y = u2
    guard_hyp h3 : a = u1
    guard_hyp h4 : b = u2
    exact True.intro
  · guard_hyp u1 : Conf
    guard_hyp u2 : Conf
    guard_hyp h1 : x = u1
    guard_hyp h2 : y = u2
    guard_hyp h3 : a = u2
    guard_hyp h4 : b = u1
    exact True.intro

-- The same C dispatch works when unrelated symbols of other arities share the
-- theory. Registration does not partition symbols by arity.
example (h : pairLeft ⋈[MixedTheory] pairRight) : True := by
  unify h in MixedTheory
  · unify_complete
  all_goals exact True.intro

-- Registration is recursive: independently swapping the outer and inner
-- occurrences yields a finite complete set, and every MGU becomes one goal.
example
    (h :
      (fun x y z : Conf => f (f x y) z) ⋈[Theory1]
      (fun a b c : Conf => f c (f a b))) : True := by
  unify h in Theory1
  · unify_complete
  all_goals exact True.intro

-- Free constants can rule out every direct/swapped branch.  The hypothesis is
-- then contradictory and `c_unify` closes an arbitrary target.
open Conf

def red : Conf := atom 0
def blue : Conf := atom 1

@[simp] theorem red_ne_blue : red ≠ blue := by
  simp [red, blue]

example (h : (f red red : Conf) ⋈[Theory1] f red blue) : False := by
  unify h in Theory1
  unify_complete

end c_unification_examples
