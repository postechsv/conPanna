import conPanna.conPanna

open framework
open Structural

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
  | upair : Conf → Conf → Conf -- [comm]
  deriving Repr

-- register Conf as top-level sort for rewriting
instance : State Conf := ⟨⟩

-- register structural axioms
structural UPairTheory where
  comm Conf.upair

#reduce UPairTheory
/-

Because `Conf.upair` is an inductive constructor and this theory is C-only,
the command also derives internal solver metadata from constructor injectivity.
That metadata supports the reusable C-equivalence lemmas below without
model-specific freeness assumptions.

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


-- Atomic C-unification problems underlying the three disjunctive narrowings.
#unify (fun X : Status => (i2w X).lhs) with
  (fun Y : Status => (hasIdle Y).term) mod UPairTheory
#unify (fun X : Status => (i2w X).lhs) with
  (fun Y : Status => (hasWait Y).term) mod UPairTheory

#unify w2c.lhs with
  (fun Y : Status => (hasIdle Y).term) mod UPairTheory
#unify w2c.lhs with
  (fun Y : Status => (hasWait Y).term) mod UPairTheory

#unify (fun X : Status => (c2i X).lhs) with
  (fun Y : Status => (hasIdle Y).term) mod UPairTheory
#unify (fun X : Status => (c2i X).lhs) with
  (fun Y : Status => (hasWait Y).term) mod UPairTheory

#narrow i2w from mutexInv -- ⟨wait, X⟩
#narrow w2c from mutexInv -- ⟨crit, idle⟩
#narrow c2i from mutexInv -- ⊥ under free unification

#narrow i2w from mutexInv mod UPairTheory -- ⟨wait, X⟩ ∨ ⟨wait, idle⟩ ∨ ⟨wait, wait⟩
#narrow w2c from mutexInv mod UPairTheory -- ⟨crit, idle⟩ ∨ ⟨crit, idle⟩
#narrow c2i from mutexInv mod UPairTheory -- ⟨idle, idle⟩ ∨ ⟨idle, wait⟩
-- above result is correct but contains redundant patterns (low quality)
-- but this quality is not from narrowing itself
-- quality should be handled in unification & post-processing



/- Complete C-unifiers for `i2w.lhs` against `hasIdle.term`. -/
theorem i2w_hasIdle_complete :
    ∀ X Y,
      upair (proc idle) (proc X) =[UPairTheory] upair (proc idle) (proc Y)
    →
      (∃ U : Status, X = U ∧ Y = U) ∨ (X = idle ∧ Y = idle) := by
  intro X Y overlap
  have cases :=
    (Structural.EqMod.iff_cEquiv Conf.upair).mp overlap
  clear overlap
  cases cases with
  | ofEq equality => simp_all
  | direct first second | swapped first second =>
    have firstEq := Structural.CEquiv.eq_of_left_not_operation
      (equation := first) (by simp)
    have secondEq := Structural.CEquiv.eq_of_left_not_operation
      (equation := second) (by simp)
    simp_all

/- Complete C-unifiers for `i2w.lhs` against `hasWait.term`. -/
theorem i2w_hasWait_complete :
    ∀ X Y,
      upair (proc idle) (proc X) =[UPairTheory] upair (proc wait) (proc Y)
    →
      X = wait ∧ Y = idle := by
  intro X Y overlap
  have cases :=
    (Structural.EqMod.iff_cEquiv Conf.upair).mp overlap
  clear overlap
  cases cases with
  | ofEq equality => simp_all
  | direct first second | swapped first second =>
    have firstEq := Structural.CEquiv.eq_of_left_not_operation
      (equation := first) (by simp)
    have secondEq := Structural.CEquiv.eq_of_left_not_operation
      (equation := second) (by simp)
    simp_all

-- `narrow` suggests a covering post. The nested proof supplies atomic
-- unification completeness; the following proof is subsumption.
example : i2w ⊢ mutexInv ↪[UPairTheory] mutexInv := by
  -- step 1) decompose (pivoting on post)
  apply mapsInto_via_narrowing_mod

  -- step 2) narrowing (i2w ⊢ mutexInv ↪[UPairTheory] ?post)
  narrow i2w from mutexInv mod UPairTheory := by
    exact ⟨i2w_hasIdle_complete, i2w_hasWait_complete⟩

  -- step 3) subsumption (post ⊑[UPairTheory] mutexInv)
  intro after hpost
  rcases hpost with hpost | hpost | hpost
  · rcases hpost with ⟨X, hafter, _⟩
    exact Or.inr ⟨X, hafter, True.intro⟩
  · rcases hpost with ⟨hafter, _⟩
    exact Or.inr ⟨idle, hafter, True.intro⟩
  · rcases hpost with ⟨hafter, _⟩
    exact Or.inr ⟨wait, hafter, True.intro⟩

-- this proof is unusually short because the rule i2w is assumed as hypothesis
-- whose rhs always contains `wait`, trivially proving the invaraint pattern
example : i2w ⊢ mutexInv ↪[UPairTheory] mutexInv := by
  intro before after _ hstep
  rcases hstep with ⟨X, hlhs, hrhs, hcond⟩
  exact Or.inr ⟨X, hrhs, True.intro⟩


example : w2c ⊢ mutexInv ↪[UPairTheory] mutexInv := by
  apply mapsInto_via_narrowing_mod

  narrow w2c from mutexInv mod UPairTheory := by
    sorry

  intro after hpost
  rcases hpost with ⟨hafter, _⟩ | ⟨hafter, _⟩
  all_goals
    exact Or.inl ⟨crit,
      Structural.EqMod.trans
        (Structural.EqMod.comm Conf.upair (proc idle) (proc crit))
        hafter,
      True.intro⟩

example : c2i ⊢ mutexInv ↪[UPairTheory] mutexInv := by
  apply mapsInto_via_narrowing_mod

  narrow c2i from mutexInv mod UPairTheory := by
    sorry

  intro after hpost
  rcases hpost with hpost | hpost
  · rcases hpost with ⟨hafter, _⟩
    exact Or.inl ⟨idle, hafter, True.intro⟩
  · rcases hpost with ⟨hafter, _⟩
    exact Or.inl ⟨wait, hafter, True.intro⟩
