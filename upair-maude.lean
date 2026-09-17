import conPanna.conPanna

set_option conPanna.unification.useMaude true

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

open Status Conf

def i2w (X : Status) : RuleBody Conf where
  lhs := upair (proc idle) (proc X)
  rhs := upair (proc wait) (proc X)
  requires := True

def w2c : RuleBody Conf where
  lhs := upair (proc wait) (proc idle)
  rhs := upair (proc crit) (proc idle)
  requires := True

def c2i (X : Status) : RuleBody Conf where
  lhs := upair (proc crit) (proc X)
  rhs := upair (proc idle) (proc X)
  requires := True

def hasIdle (X : Status) : APattBody Conf where
  term := upair (proc idle) (proc X)
  requires := True

def hasWait (X : Status) : APattBody Conf where
  term := upair (proc wait) (proc X)
  requires := True

def mutexInv := hasIdle ⊔ hasWait

theorem i2w_hasIdle_maude_complete :
    ∀ X Y,
      upair (proc idle) (proc X) =[UPairTheory]
        upair (proc idle) (proc Y) →
      ∃ U : Status, X = U ∧ Y = U := by
  intro X Y overlap
  have cases := (Structural.EqMod.iff_cEquiv Conf.upair).mp overlap
  clear overlap
  cases cases with
  | ofEq equality => simp_all
  | direct first second | swapped first second =>
      have firstEq := Structural.CEquiv.eq_of_left_not_operation
        (equation := first) (by simp)
      have secondEq := Structural.CEquiv.eq_of_left_not_operation
        (equation := second) (by simp)
      simp_all

theorem i2w_hasWait_maude_complete :
    ∀ X Y,
      upair (proc idle) (proc X) =[UPairTheory]
        upair (proc wait) (proc Y) →
      X = wait ∧ Y = idle := by
  intro X Y overlap
  have cases := (Structural.EqMod.iff_cEquiv Conf.upair).mp overlap
  clear overlap
  cases cases with
  | ofEq equality => simp_all
  | direct first second | swapped first second =>
      have firstEq := Structural.CEquiv.eq_of_left_not_operation
        (equation := first) (by simp)
      have secondEq := Structural.CEquiv.eq_of_left_not_operation
        (equation := second) (by simp)
      simp_all

example : i2w ⊢ mutexInv ↪[UPairTheory] mutexInv := by
  apply mapsInto_via_narrowing_mod

  narrow i2w from mutexInv mod UPairTheory := by
    exact ⟨i2w_hasIdle_maude_complete, i2w_hasWait_maude_complete⟩

  intro after hpost
  rcases hpost with hpost | hpost
  · rcases hpost with ⟨X, hafter, _⟩
    exact Or.inr ⟨X, hafter, True.intro⟩
  · rcases hpost with ⟨hafter, _⟩
    exact Or.inr ⟨wait, hafter, True.intro⟩

#dump_maude_model Conf mod UPairTheory
#dump_maude_term
  (fun X : Status => Conf.upair (Conf.proc Status.idle) (Conf.proc X))
  from Conf

-- The six atomic C-unification problems used by narrowing in `upair.lean`.
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

#narrow i2w from mutexInv mod UPairTheory
#narrow w2c from mutexInv mod UPairTheory
#narrow c2i from mutexInv mod UPairTheory
