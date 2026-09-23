import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Multiset.AddSub
import conPanna.conPanna

set_option conPanna.unification.useMaude true

open framework
open Structural

/-!
# Lamport's Bakery algorithm

This is the constrained-narrowing experiment derived from the earlier Lean
model in `../bakery/bakery.lean` and the DM-Check Bakery example.

The process collection is kept as an ACU constructor language for structural
unification.  Constraints, including `Multiset.Nodup`, remain ordinary Lean
propositions so that feasibility can be established with Lean lemmas.
-/

inductive Mode where
  | idle
  | wait : Nat → Mode
  | crit : Nat → Mode
  deriving Repr

inductive ProcSet where
  | empty
  | singleton : Mode → ProcSet
  | union : ProcSet → ProcSet → ProcSet -- ACU
  deriving Repr

structure Conf where
  next : Nat
  serving : Nat
  procs : ProcSet
  deriving Repr

instance : State Conf := ⟨⟩

structural BakeryTheory where
  assoc ProcSet.union
  comm ProcSet.union
  id ProcSet.union ProcSet.empty

open Mode ProcSet
open scoped Multiset

/- One idle process takes the current ticket. -/
def wake (next serving : Nat) (rest : ProcSet) : RuleBody Conf where
  lhs := {
    next
    serving
    procs := union (singleton idle) rest
  }
  rhs := {
    next := next.succ
    serving
    procs := union (singleton (wait next)) rest
  }
  requires := True

/- The process holding the currently served ticket enters. -/
def enter (next serving : Nat) (rest : ProcSet) : RuleBody Conf where
  lhs := {
    next
    serving
    procs := union (singleton (wait serving)) rest
  }
  rhs := {
    next
    serving
    procs := union (singleton (crit serving)) rest
  }
  requires := True

/- The critical process exits and advances the serving counter. -/
def exit (next serving : Nat) (rest : ProcSet) : RuleBody Conf where
  lhs := {
    next
    serving
    procs := union (singleton (crit serving)) rest
  }
  rhs := {
    next
    serving := serving.succ
    procs := union (singleton idle) rest
  }
  requires := True

def bakeryRules := wake ⊔ enter ⊔ exit

/- A multiset view used only by constraints.  ACU process union is translated
to Mathlib multiset addition, allowing constraints to use its library. -/
def tickets : ProcSet → Multiset Nat
  | empty => 0
  | ProcSet.singleton idle => 0
  | ProcSet.singleton (wait ticket) => {ticket}
  | ProcSet.singleton (crit ticket) => {ticket}
  | union left right => tickets left + tickets right

def allIdle : ProcSet → Prop
  | empty => True
  | ProcSet.singleton mode => mode = idle
  | union left right => allIdle left ∧ allIdle right

def outsideCritical : ProcSet → Prop
  | empty => True
  | ProcSet.singleton idle => True
  | ProcSet.singleton (wait _) => True
  | ProcSet.singleton (crit _) => False
  | union left right => outsideCritical left ∧ outsideCritical right

def ticketsInRange (lower upper : Nat) (procs : ProcSet) : Prop :=
  ∀ ticket ∈ tickets procs, lower ≤ ticket ∧ ticket < upper

/- All processes are idle and both counters agree. -/
def initial (counter : Nat) (procs : ProcSet) : APattBody Conf where
  term := { next := counter, serving := counter, procs }
  requires := allIdle procs

/- No process is critical; outstanding tickets are unique and lie between the
serving and next counters. -/
def waiting (next serving : Nat) (procs : ProcSet) : APattBody Conf where
  term := { next, serving, procs }
  requires :=
    serving < next ∧
    outsideCritical procs ∧
    ticketsInRange serving next procs ∧
    (tickets procs).Nodup

/- Exactly the process with the serving ticket is presented as critical.  The
remainder contains only idle/waiting processes with larger unique tickets. -/
def critical (next serving : Nat) (rest : ProcSet) : APattBody Conf where
  term := {
    next
    serving
    procs := union (singleton (crit serving)) rest
  }
  requires :=
    serving < next ∧
    outsideCritical rest ∧
    (∀ ticket ∈ tickets rest, serving < ticket ∧ ticket < next) ∧
    (tickets rest).Nodup

def bakeryInv := initial ⊔ waiting ⊔ critical

/- A deliberately small first constrained-narrowing target.  It isolates the
ACU overlap used by `wake` while retaining a nontrivial Lean constraint. -/
def idleWithUniqueTickets
    (next serving : Nat) (rest : ProcSet) : APattBody Conf where
  term := {
    next
    serving
    procs := union (singleton idle) rest
  }
  requires := (tickets rest).Nodup

-- First experiment for the next step:
-- #narrow wake from idleWithUniqueTickets mod BakeryTheory

-- Full experiments to enable once constrained unification exposes residual
-- constraints cleanly:
-- #narrow wake from bakeryInv mod BakeryTheory
-- #narrow enter from bakeryInv mod BakeryTheory
-- #narrow exit from bakeryInv mod BakeryTheory
-- #narrow bakeryRules from bakeryInv mod BakeryTheory
