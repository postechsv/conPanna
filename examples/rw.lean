import conPanna.conPanna


/-!
These examples define an independent user model, constrained patterns, and
rules to demonstrate exact one-step post generation followed by subsumption.
They are clients of both the semantic framework and unification result format.
-/

open framework


/- https://dmcheck.webs.upv.es/examples/code-viewer.html?file=rw/rw.maude
mod R&W is
  sort Natural .
  op 0 : -> Natural [ctor] .
  op s : Natural -> Natural [ctor] .
  sort Config .
  op <_,_> : Natural Natural -> Config [ctor] .

  vars R W : Natural .

  rl [enter-w] : < 0, 0 > => < 0, s(0) > [narrowing] .
  rl [leave-w] : < R, s(W) > => < R, W > [narrowing] .
  rl [enter-r] : < R, 0 > => < s(R), 0 > [narrowing] .
  rl [leave-r] : < s(R), W > => < R, W > [narrowing] .
endm
-/

inductive Natural where
  | o : Natural
  | s : Natural → Natural
  deriving Repr

structure Conf where
  first : Natural
  second : Natural
  deriving Repr

instance : State Conf := ⟨⟩

open Natural Conf

-- rl [enter-w] : < 0, 0 > => < 0, s(0) > [narrowing] .
def enter_w : RuleBody Conf where
  lhs := ⟨o, o⟩
  rhs := ⟨o, (s o)⟩
  requires := True

-- rl [leave-w] : < R, s(W) > => < R, W > [narrowing] .
def leave_w (R W : Natural) : RuleBody Conf where
  lhs := ⟨R, s W⟩
  rhs := ⟨R, W⟩
  requires := True

-- rl [enter-r] : < R, 0 > => < s(R), 0 > [narrowing] .
def enter_r (R : Natural) : RuleBody Conf where
  lhs := ⟨R, o⟩
  rhs := ⟨s R, o⟩
  requires := True

-- rl [leave-r] : < s(R), W > => < R, W > [narrowing] .
def leave_r (R W : Natural) : RuleBody Conf where
  lhs := ⟨s R, W⟩
  rhs := ⟨R, W⟩
  requires := True

/-- `pair (atom 0) (atom n) where n > 0` -/
def source (n : Nat) : APattBody Conf where
  term := pair (atom 0) (atom n)
  requires := 0 < n

/-- `pair (atom payload) (atom (payload + 1))` where `payload > 0` -/
def target (payload : Nat) : APattBody Conf where
  term := pair (atom payload) (atom (payload + 1))
  requires := 0 < payload
