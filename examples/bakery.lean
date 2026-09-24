import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Multiset.AddSub
import Mathlib.Data.Multiset.UnionInter
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

/- ⟨N, M, idle; PS⟩ => ⟨N+1, M, wait(N); PS⟩ -/
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

/- ⟨N, M, wait(M); PS⟩ => ⟨N, M, crit(M); PS⟩ -/
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

/- ⟨N, M, crit(M); PS⟩ => ⟨N, M+1, idle; PS⟩ -/
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

/- tickets(PS) = multiset of ticket numbers in PS -/
def tickets : ProcSet → Multiset Nat
  | empty => 0
  | ProcSet.singleton idle => 0
  | ProcSet.singleton (wait ticket) => {ticket}
  | ProcSet.singleton (crit ticket) => {ticket}
  | union left right => tickets left + tickets right

/- all procs in PS are idle -/
def allIdle : ProcSet → Prop
  | empty => True
  | ProcSet.singleton mode => mode = idle
  | union left right => allIdle left ∧ allIdle right

/- no procs in PS is crit -/
def noCrit : ProcSet → Prop
  | empty => True
  | ProcSet.singleton idle => True
  | ProcSet.singleton (wait _) => True
  | ProcSet.singleton (crit _) => False
  | union left right => noCrit left ∧ noCrit right

/- tickets(PS) ⊆ [l,u) -/
def ticketsInRange (lower upper : Nat) (procs : ProcSet) : Prop :=
  ∀ ticket ∈ tickets procs, lower ≤ ticket ∧ ticket < upper

/- ⟨N, M, PS⟩ | allIdle(PS) -/
def initial (counter : Nat) (procs : ProcSet) : APattBody Conf where
  term := { next := counter, serving := counter, procs }
  requires := allIdle procs

/- ⟨N, M, PS⟩ | N > M ∧ noCrit(PS) ∧ tickets(PS) ⊆ [M, N) ∧ tickets(PS).Nodup -/
def waiting (next serving : Nat) (procs : ProcSet) : APattBody Conf where
  term := { next, serving, procs }
  requires :=
    serving < next ∧
    noCrit procs ∧
    ticketsInRange serving next procs ∧
    (tickets procs).Nodup

/- ⟨N, M, crit(M); PS⟩ | N > M ∧ noCrit(PS) ∧ tickets(PS) ⊆ (M, N) ∧ tickets(PS).Nodup -/
def critical (next serving : Nat) (rest : ProcSet) : APattBody Conf where
  term := {
    next
    serving
    procs := union (singleton (crit serving)) rest
  }
  requires :=
    serving < next ∧
    noCrit rest ∧
    (∀ ticket ∈ tickets rest, serving < ticket ∧ ticket < next) ∧
    (tickets rest).Nodup

def bakeryInv := initial ⊔ waiting ⊔ critical


/- useful lemmas -/

lemma noCrit_of_allIdle {procs : ProcSet} (h : allIdle procs) :
    noCrit procs := by
  induction procs with
  | empty => simp [noCrit]
  | singleton mode => cases mode <;> simp_all [allIdle, noCrit]
  | union left right ihLeft ihRight =>
      simp_all [allIdle, noCrit]

lemma tickets_eq_zero_of_allIdle {procs : ProcSet} (h : allIdle procs) :
    tickets procs = 0 := by
  induction procs with
  | empty => simp [tickets]
  | singleton mode => cases mode <;> simp_all [allIdle, tickets]
  | union left right ihLeft ihRight =>
      simp_all [allIdle, tickets]

lemma wake_initial_constraints (next : Nat) (rest : ProcSet)
    (hIdle : allIdle (union rest (singleton idle))) :
    (waiting next.succ next (union (singleton (wait next)) rest)).requires := by
  have hRestIdle : allIdle rest := by
    simpa [allIdle] using hIdle
  have hRestNoCrit := noCrit_of_allIdle hRestIdle
  have hRestTickets := tickets_eq_zero_of_allIdle hRestIdle
  simp [waiting, noCrit, tickets, ticketsInRange, hRestNoCrit,
    hRestTickets]

lemma wake_waiting_constraints (next serving : Nat) (rest : ProcSet)
    (hlt : serving < next)
    (hnoCrit : noCrit (union rest (singleton idle)))
    (hrange : ticketsInRange serving next (union rest (singleton idle)))
    (hnodup : (tickets (union rest (singleton idle))).Nodup) :
    (waiting next.succ serving (union (singleton (wait next)) rest)).requires := by
  have hnoCritRest : noCrit rest := by
    simpa [noCrit] using hnoCrit
  have hrangeRest : ticketsInRange serving next rest := by
    simpa [tickets, ticketsInRange] using hrange
  have hnodupRest : (tickets rest).Nodup := by
    simpa [tickets] using hnodup
  have hfresh : next ∉ tickets rest := by
    intro hmem
    have := hrangeRest next hmem
    omega
  simp only [waiting, noCrit, tickets, ticketsInRange,
    Multiset.nodup_add, Multiset.nodup_singleton]
  refine ⟨by omega, ⟨trivial, hnoCritRest⟩, ?_, ?_⟩
  · intro ticket hmem
    simp only [Multiset.mem_add, Multiset.mem_singleton] at hmem
    rcases hmem with rfl | hmem
    · omega
    · have := hrangeRest ticket hmem
      omega
  · exact ⟨by simp, hnodupRest, by simpa using hfresh⟩

lemma wake_critical_constraints (next serving : Nat) (rest : ProcSet)
    (hlt : serving < next)
    (hnoCrit : noCrit (union rest (singleton idle)))
    (hrange :
      ∀ ticket ∈ tickets (union rest (singleton idle)),
        serving < ticket ∧ ticket < next)
    (hnodup : (tickets (union rest (singleton idle))).Nodup) :
    (critical next.succ serving
      (union (singleton (wait next)) rest)).requires := by
  have hnoCritRest : noCrit rest := by
    simpa [noCrit] using hnoCrit
  have hrangeRest :
      ∀ ticket ∈ tickets rest, serving < ticket ∧ ticket < next := by
    simpa [tickets] using hrange
  have hnodupRest : (tickets rest).Nodup := by
    simpa [tickets] using hnodup
  have hfresh : next ∉ tickets rest := by
    intro hmem
    have := hrangeRest next hmem
    omega
  simp only [critical, noCrit, tickets, Multiset.nodup_add,
    Multiset.nodup_singleton]
  refine ⟨by omega, ⟨trivial, hnoCritRest⟩, ?_, ?_⟩
  · intro ticket hmem
    simp only [Multiset.mem_add, Multiset.mem_singleton] at hmem
    rcases hmem with rfl | hmem
    · omega
    · have := hrangeRest ticket hmem
      exact ⟨this.1, lt_trans this.2 (Nat.lt_succ_self next)⟩
  · exact ⟨by simp, hnodupRest, by simpa using hfresh⟩




/- main proof -/

macro "bakery_subsume" : tactic =>
  `(tactic|
    simp only [framework.Patterns.SubsumesMod,
      framework.Patterns.PatternMod.semantics,
      framework.Patterns.APattMod.semantics,
      bakeryInv, initial, waiting, critical] <;>
    simp_all [allIdle, noCrit, ticketsInRange, tickets,
      noCrit_of_allIdle, tickets_eq_zero_of_allIdle,
      Multiset.nodup_add] <;>
    grind)

example : wake ⊢ bakeryInv ↪[BakeryTheory] bakeryInv := by
  apply mapsInto_via_narrowing_mod
  narrow wake from bakeryInv mod BakeryTheory := by
    sorry
  subsume_cases <;>
    simp only [framework.Patterns.SubsumesMod,
      framework.Patterns.PatternMod.semantics,
      framework.Patterns.APattMod.semantics,
      bakeryInv, initial, waiting, critical]
  · rintro state ⟨next, rest, hstate, _, hIdle⟩
    right
    left
    refine ⟨next.succ, next, union (singleton (wait next)) rest,
      hstate, wake_initial_constraints next rest hIdle⟩
  · rintro state ⟨next, serving, rest, hstate, _, hlt, hnoCrit,
      hrange, hnodup⟩
    right
    left
    refine ⟨next.succ, serving, union (singleton (wait next)) rest,
      hstate, wake_waiting_constraints next serving rest hlt hnoCrit
        hrange hnodup⟩
  · rintro state ⟨next, serving, rest, hstate, _, hlt, hnoCrit,
      hrange, hnodup⟩
    right
    right
    refine ⟨next.succ, serving, union (singleton (wait next)) rest,
      ?_, ?_⟩
    · exact Structural.EqMod.transAt BakeryTheory (by structural_rfl) hstate
    · exact wake_critical_constraints next serving rest hlt hnoCrit
        hrange hnodup

example : enter ⊢ bakeryInv ↪[BakeryTheory] bakeryInv := by
  apply mapsInto_via_narrowing_mod
  narrow enter from bakeryInv mod BakeryTheory := by
    sorry
  subsume_cases
  · bakery_subsume
  · bakery_subsume
  · bakery_subsume



example : exit ⊢ bakeryInv ↪[BakeryTheory] bakeryInv := by
  apply mapsInto_via_narrowing_mod
  narrow exit from bakeryInv mod BakeryTheory := by
    sorry
  subsume_cases
  -- The three infeasible overlaps close automatically.
  · bakery_subsume
  · bakery_subsume
  · bakery_subsume
  -- The feasible overlap requires a successor/equality case split.
  · /- ⟨N,M+1,idle;PS⟩ | N>M ∧ nocrit(PS) ∧ tickets(PS)⊆(M,N) ∧ tickets(PS).Nodup -/
    simp only [framework.Patterns.SubsumesMod,
      framework.Patterns.PatternMod.semantics,
      framework.Patterns.APattMod.semantics,
      bakeryInv, initial, waiting, critical]
    rintro state ⟨next, serving, rest, hstate, _, hlt, hnoCrit,
      hrange, hnodup⟩
    have idle_if_no_tickets :
        ∀ procs, noCrit procs → tickets procs = 0 → allIdle procs := by
      intro procs
      induction procs with
      | empty =>
          simp [allIdle]
      | singleton mode =>
          cases mode <;> simp [noCrit, tickets, allIdle]
      | union left right ihLeft ihRight =>
          simp only [noCrit, tickets, allIdle]
          rintro ⟨hLeft, hRight⟩ hzero
          have hcards := congrArg Multiset.card hzero
          simp only [Multiset.card_add, Multiset.card_zero] at hcards
          have hLeftZero : tickets left = 0 :=
            Multiset.card_eq_zero.mp (by omega)
          have hRightZero : tickets right = 0 :=
            Multiset.card_eq_zero.mp (by omega)
          exact ⟨ihLeft hLeft hLeftZero, ihRight hRight hRightZero⟩
    by_cases hboundary : serving.succ = next
    · left
      have hNoTickets : tickets rest = 0 := by
        apply Multiset.eq_zero_iff_forall_notMem.mpr
        intro ticket hticket
        have bounds := hrange ticket hticket
        omega
      have hRestIdle := idle_if_no_tickets rest hnoCrit hNoTickets
      refine ⟨next, union (singleton idle) rest, ?_, ?_⟩
      · rw [hboundary] at hstate
        exact hstate
      · simpa [allIdle] using hRestIdle
    · right
      left
      refine ⟨next, serving.succ, union (singleton idle) rest, hstate, ?_⟩
      refine ⟨by omega, ?_, ?_, ?_⟩
      · simpa [noCrit] using hnoCrit
      · intro ticket hticket
        have hticketRest : ticket ∈ tickets rest := by
          simpa [tickets] using hticket
        have bounds := hrange ticket hticketRest
        exact ⟨by omega, bounds.2⟩
      · simpa [tickets] using hnodup
