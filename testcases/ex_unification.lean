import conPanna.conPanna

namespace ex_unification

open framework

inductive Conf where
  | c : Conf
  | f : Conf → Conf → Conf
  deriving Repr

instance : State Conf := ⟨⟩

open Conf

def pat1 (x1 x2 : Conf) : Conf := f x1 x2
def pat2 (y1 : Conf) : Conf := f (f y1 c) c


#print pat1 -- λ x1 x2, f x1 x2
#print pat2 -- λ y1, f (f y1 c) c

/- maude outputs the following unifier as a solution
variant unify in EX1 : f(X1, X2) =? f(f(Y1, c), c) .

Unifier 1
rewrites: 0 in 0ms cpu (0ms real) (~ rewrites/second)
X1 --> f(%1:Term, c)
X2 --> c
Y1 --> %1:Term

No more unifiers.
-/


-- pat1 ⋈ pat2 means pat1 & pat2 are unifiable
example (h : pat1 ⋈ pat2) : True := by
  unify h
  -- Completeness is an ordinary user-level goal.  It can be proved directly;
  -- `unify_complete` is merely optional automation for proofs like this one.
  · intros <;> simp_all
  · guard_hyp u1 : Conf
    guard_hyp h1 : x1 = f u1 c
    guard_hyp h2 : x2 = c
    guard_hyp h3 : y1 = u1
    exact True.intro


/-- An empty theory: every symbol is free. -/
def FreeTheory : Theory := {}

-- The explicit-theory form has the same public result interface.
example (h : pat1 ⋈[FreeTheory] pat2) : True := by
  unify h in FreeTheory
  · unify_complete
  · guard_hyp u1 : Conf
    guard_hyp h1 : x1 = f u1 c
    guard_hyp h2 : x2 = c
    guard_hyp h3 : y1 = u1
    exact True.intro


-- non-unifiable example
example (h : (fun x : Conf => f x x) ⋈ c) : False := by
  unify h
  unify_complete

-- Failure produces a proof of `False`, so it closes an arbitrary target rather
-- than relying on the target itself being syntactically `False`.
example (h : (c : Conf) ⋈ f c c) : (0 : Nat) = 1 := by
  unify h
  unify_complete


-- A differently named problem with two independent basis variables.  This is
-- below `unify`, so the tactic implementation cannot refer to either pattern.
def pairLeft (x1 x2 : Conf) : Conf := f x1 x2
def pairRight (y1 y2 : Conf) : Conf := f (f y1 y2) (f y2 y1)

-- X1 --> f(%1:Term, %2:Term)
-- X2 --> f(%2:Term, %1:Term)
-- Y1 --> %1:Term
-- Y2 --> %2:Term

#check pairLeft ⋈ pairRight -- : Prop
#unify pairLeft with pairRight

example (h : pairLeft ⋈ pairRight) : True := by
  unify h
  · unify_complete
  · guard_hyp u1 : Conf
    guard_hyp u2 : Conf
    guard_hyp h1 : x1 = f u1 u2
    guard_hyp h2 : x2 = f u2 u1
    guard_hyp h3 : y1 = u1
    guard_hyp h4 : y2 = u2
    exact True.intro


-- Lambda closures work directly; named declarations are not required.
example
    (h : (fun a b : Conf => f a b) ⋈ (fun m : Conf => f m c)) : True := by
  unify h
  · unify_complete
  · guard_hyp u1 : Conf
    guard_hyp h1 : a = u1
    guard_hyp h2 : b = c
    guard_hyp h3 : m = u1
    exact True.intro


-- Pure variables still produce a basis rather than an object-language `var`.
example (h : (fun left : Conf => left) ⋈ (fun right : Conf => right)) : True := by
  unify h
  · unify_complete
  · guard_hyp u1 : Conf
    guard_hyp h1 : left = u1
    guard_hyp h2 : right = u1
    exact True.intro


-- A deeper cascading substitution exercises native unification and certificate
-- reconstruction independently of any declaration names.
example
    (h : (fun a b d : Conf => f a (f b d)) ⋈
      (fun x : Conf => f (f x c) (f c x))) : True := by
  unify h
  · unify_complete
  · guard_hyp u1 : Conf
    guard_hyp h1 : a = f u1 c
    guard_hyp h2 : b = c
    guard_hyp h3 : d = u1
    guard_hyp h4 : x = u1
    exact True.intro


-- A ground unification example
example (h : (f c c : Conf) ⋈ f c c) : True := by
  unify h
  · unify_complete
  · exact True.intro


-- An occurs-check failure: the constructor equations would imply
-- `y = f y c`, which no finite `Conf` can satisfy.
example
    (h : (fun x : Conf => f x x) ⋈
      (fun y : Conf => f (f y c) y)) : False := by
  unify h
  unify_complete


end ex_unification
