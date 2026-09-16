import conPanna.conPanna

open framework

/- # Step 1 - Modeling Readers-Writers
--- https://dmcheck.webs.upv.es/examples/code-viewer.html?file=rw/rw.maude
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

/- # Step 2 - Invariant Checking
--- https://dmcheck.webs.upv.es/examples/code-viewer.html?file=rw/rw-dmc.maude
--- Select the module
set module R&W .

--- Check the invariant
check ind-invariant \
     < N:Natural , 0 > | true \
  \/ < 0 , s(0) > | true .

--- Check if the initial state is subsumed by the LHS of the rules (deadlock freedom)
check \
     < N:Natural , 0 > | true \
  \/ < 0 , s(0) > | true \
 subsumed by \
     < 0, 0 > | true \
  \/ < R:Natural, s(W:Natural) > | true \
  \/ < R:Natural, 0 > | true \
  \/ < s(R:Natural), W:Natural > | true .
-/

-- < N, 0 > | true
def p1 (N : Natural) : APattBody Conf where
  term := ⟨N, o⟩
  requires := True

-- < 0, s(0) > | true
def p2 : APattBody Conf where
  term := ⟨o, s o⟩
  requires := True

-- < N, 0 > | true \/ < 0, s(0) > | true
def inv := p1 ⊔ p2
#print inv

-- or alternatively,
def inv' :=
  (fun N => framework.Patterns.APattBody.mk (Conf.mk N o) True) ⊔
  framework.Patterns.APattBody.mk (Conf.mk o (s o)) True

#narrow enter_w from inv

example : enter_w ⊢ inv ↪ inv := by
  apply mapsInto_via_narrowing
  narrow enter_w against inv
  subsume

example : leave_w ⊢ inv ↪ inv := by
  apply mapsInto_via_narrowing
  narrow leave_w against inv
  subsume

example : enter_r ⊢ inv ↪ inv := by
  apply mapsInto_via_narrowing
  narrow enter_r against inv
  subsume

example : leave_r ⊢ inv ↪ inv := by
  apply mapsInto_via_narrowing
  narrow leave_r against inv
  subsume

-- rl [inc-rw] : < R, W > => < s(R), s(W) > [narrowing] .
def inc_rw (R W : Natural) : RuleBody Conf where
  lhs := ⟨R, W⟩
  rhs := ⟨s R, s W⟩
  requires := True

-- < N, 0 > => < s N, s 0 >
-- < 0, s(0) > => < s 0, s s(0) >
#narrow inc_rw from inv
-- (fun u1 ↦ { term := { first := u1.s, second := o.s }, requires := True ∧ True })
-- ⊔ { term := { first := o.s, second := o.s.s }, requires := True ∧ True }
