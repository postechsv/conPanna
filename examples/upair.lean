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


/- Define constructor symbols. Separating `Status` from `Conf` ensures that a
symbolic process variable ranges only over process states, while `Conf` remains
a recursive Maude-style term language. -/
inductive Status where
  | idle
  | wait
  | crit
  deriving Repr

inductive Conf where
  | proc : Status → Conf
  | upair : Conf → Conf → Conf -- commutative
  deriving Repr

/- register structural axioms -/
open scoped Structural

structural UPairTheory where
  comm Conf.upair

instance : State Conf := ⟨⟩

#reduce UPairTheory
/-!
The declaration above is surface syntax for the following ordinary value:

```
def UPairTheory : Structural.Theory where
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

open Status Conf

-- i2w: ⟨idle, X⟩ → ⟨wait, X⟩
def i2w (X : Status) : RuleBody Conf where
  lhs := upair (proc idle) (proc X)
  rhs := upair (proc wait) (proc X)
  requires := True

-- w2c: ⟨wait, idle⟩ → ⟨crit, idle⟩
def w2c : RuleBody Conf where
  lhs := upair (proc wait) (proc idle)
  rhs := upair (proc crit) (proc idle)
  requires := True

-- c2i: ⟨crit, X⟩ → ⟨idle, X⟩
def c2i (X : Status) : RuleBody Conf where
  lhs := upair (proc crit) (proc X)
  rhs := upair (proc idle) (proc X)
  requires := True

/- Modulo commutativity, these two symbolic branches describe every unordered
pair except `upair (proc crit) (proc crit)`. -/
def hasIdle (X : Status) : APattBody Conf where
  term := upair (proc idle) (proc X)
  requires := True

def hasWait (X : Status) : APattBody Conf where
  term := upair (proc wait) (proc X)
  requires := True

def mutexInv := hasIdle ⊔ hasWait

#print mutexInv
