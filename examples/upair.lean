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

-- TODO: what if inductive (ctors) deriving/assuming (eqtns)?
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

instance : Structural.HasComm UPairTheory Conf.upair := ⟨True.intro⟩
```

`comm` records an equation for the theory-indexed `Structural.EqMod` relation.
It does not assert the inconsistent Lean equality
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

-- ⟨idle, X⟩ ∨ ⟨wait, X⟩
def mutexInv := hasIdle ⊔ hasWait

#print mutexInv

-- Manual checks of the two C-unifiers needed by `c2i`. Swapping the outer
-- `upair` gives respectively `X = idle, Y = crit` and
-- `X = wait, Y = crit`.
example : Structural.EqMod UPairTheory
    (c2i idle).lhs (hasIdle crit).term := by
  simpa [c2i, hasIdle] using
    (Structural.EqMod.comm Conf.upair (proc crit) (proc idle))

example : Structural.EqMod UPairTheory
    (c2i wait).lhs (hasWait crit).term := by
  simpa [c2i, hasWait] using
    (Structural.EqMod.comm Conf.upair (proc crit) (proc wait))

#narrow i2w against mutexInv -- ⟨wait, X⟩
#narrow w2c against mutexInv -- ⟨crit, idle⟩
#narrow c2i against mutexInv -- ⊥ under free unification

#narrow i2w against mutexInv in UPairTheory -- ⟨wait, X⟩ ∨ ⟨wait, idle⟩ ∨ ⟨wait, wait⟩
#narrow w2c against mutexInv in UPairTheory -- ⟨crit, idle⟩ ∨ ⟨crit, idle⟩
#narrow c2i against mutexInv in UPairTheory -- ⟨idle, idle⟩ ∨ ⟨idle, wait⟩

example : i2w ⊢ mutexInv ↪ mutexInv := by
  apply mapsInto_via_narrowing
  narrow i2w against mutexInv
  subsume

/- This is the first genuine obstruction. Narrowing computes
`upair (proc crit) (proc idle)`, but syntactic subsumption cannot identify it
with the `hasIdle crit` instance `upair (proc idle) (proc crit)`.

example : w2c ⊢ mutexInv ↪ mutexInv := by
  apply mapsInto_via_narrowing
  narrow w2c against mutexInv
  subsume
-/

/- This script currently closes, but only vacuously: syntactic unification
returns an empty post-image because `c2i` starts with `crit`, whereas both
invariant branches start with `idle` or `wait`. C-unification should instead
find the swapped source instances and produce `idle/idle` and `idle/wait`. -/
example : c2i ⊢ mutexInv ↪ mutexInv := by
  apply mapsInto_via_narrowing
  narrow c2i against mutexInv
  subsume
