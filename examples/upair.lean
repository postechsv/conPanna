import conPanna.conPanna

open framework

/- # Step 1 - Modeling UPair (Unordered Pairs)
  idle | waiting | critical
  pair x y = pair y x

  pair is commutative but not associative: nested pairs remain structurally distinct.

  Rules:

  request: pair idle X     → pair waiting X
  enter:   pair waiting idle → pair critical idle
  exit:    pair critical X → pair idle X
-/


/- define constructor symbols -/
inductive Conf where
  | idle
  | wait
  | crit
  | upair : Conf → Conf → Conf -- commutative
  deriving Repr

/- register structural axioms -/
open scoped Structural -- TODO: rename comm to avoid reserved keywords

structural UPairTheory where
  comm Conf.upair

instance : State Conf := ⟨⟩

/- Remark: finite carrier problem
if upair is defined as a usual function
  e.g., axiom upair : Conf → Conf → Conf
where Conf consists of three (idle,wait,crit) constructors only,
we face inconsistency:
there are 3 elements in the set Conf, whereas there are 6 upairs.
-/

-- Activates the law-clause vocabulary without globally reserving names such as
-- `comm`, which may also be ordinary Lean field names.


#reduce UPairTheory
/-!
The declaration above is surface syntax for the following ordinary value:

```
def PairTheory : Structural.Theory where
  symbols := [
    Structural.Symbol.declare Conf.upair [
      Structural.OperatorLaw.commutative
    ]
  ]
```

`comm` records an equation for the future theory-indexed equivalence.  It does
not assert the inconsistent Lean equality
`Conf.upair left right = Conf.upair right left`.
-/

open Conf

-- request: pair idle X → pair waiting X
def request (X : Conf) : RuleBody Conf where
  lhs := upair idle X
  rhs := upair wait X
  requires := True

-- enter: pair waiting idle → pair critical idle
def enter : RuleBody Conf where
  lhs := upair wait idle
  rhs := upair crit idle
  requires := True

-- exit: pair critical X → pair idle X
def exit (X : Conf) : RuleBody Conf where
  lhs := upair crit X
  rhs := upair idle X
  requires := True
