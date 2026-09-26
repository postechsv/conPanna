import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Multiset.AddSub
import Mathlib.Data.Multiset.UnionInter
import conPanna.conPanna
import conPanna.PatternPretty

set_option conPanna.unification.useMaude true

open framework
open Structural

/-!
Prototype symbolic-subsumption infrastructure.  This section is deliberately
model-independent so it can move unchanged into the library after the
interface has been validated here.
-/
namespace SymbolicSubsumptionPrototype

open framework.Patterns

universe u v w x

theorem subsumes_mod_trans
    {theory : Structural.Theory.{u}}
    {α : Type u} {P : Type v} {Q : Type w} {R : Type x}
    [State α] [PatternMod theory α P] [PatternMod theory α Q]
    [PatternMod theory α R]
    {source : P} {middle : Q} {target : R}
    (h₁ : source ⊑[theory] middle)
    (h₂ : middle ⊑[theory] target) :
    source ⊑[theory] target := by
  intro state hsource
  exact h₂ state (h₁ state hsource)

theorem source_family_subsumes_mod
    {theory : Structural.Theory.{u}}
    {α : Type u} {A : Type v} {P : Type w} {Q : Type x}
    [State α] [APattMod theory α P] [PatternMod theory α Q]
    {source : A → P} {target : Q}
    (h : ∀ argument, source argument ⊑[theory] target) :
    source ⊑[theory] target := by
  intro state hsource
  rcases hsource with ⟨argument, hsource⟩
  exact h argument state hsource

theorem target_family_subsumes_mod
    {theory : Structural.Theory.{u}}
    {α : Type u} {A : Type v} {P : Type w} {Q : Type x}
    [State α] [PatternMod theory α P] [APattMod theory α Q]
    {source : P} {target : A → Q}
    (argument : A)
    (h : source ⊑[theory] target argument) :
    source ⊑[theory] target := by
  intro state hsource
  exact ⟨argument, h state hsource⟩

theorem target_left_subsumes_mod
    {theory : Structural.Theory.{u}}
    {α : Type u} {P : Type v} {Q : Type w} {R : Type x}
    [State α] [PatternMod theory α P] [PatternMod theory α Q]
    [PatternMod theory α R]
    {source : P} {left : Q} {right : R}
    (h : source ⊑[theory] left) :
    source ⊑[theory] (left ⊔ right) := by
  intro state hsource
  exact Or.inl (h state hsource)

theorem target_right_subsumes_mod
    {theory : Structural.Theory.{u}}
    {α : Type u} {P : Type v} {Q : Type w} {R : Type x}
    [State α] [PatternMod theory α P] [PatternMod theory α Q]
    [PatternMod theory α R]
    {source : P} {left : Q} {right : R}
    (h : source ⊑[theory] right) :
    source ⊑[theory] (left ⊔ right) := by
  intro state hsource
  exact Or.inr (h state hsource)

theorem subsumes_mod_refl
    {theory : Structural.Theory.{u}}
    {α : Type u} {P : Type v}
    [State α] [PatternMod theory α P]
    {pattern : P} : pattern ⊑[theory] pattern := by
  intro _ h
  exact h

theorem apattBody_subsumes_of_match
    {theory : Structural.Theory.{u}}
    {α : Type u} [State α]
    {source target : APattBody α}
    (hterm : Structural.EqMod theory target.term source.term)
    (hcondition : source.requires → target.requires) :
    source ⊑[theory] target := by
  intro state hsource
  exact ⟨Structural.EqMod.transAt theory hterm hsource.1,
    hcondition hsource.2⟩

theorem apattBody_subsumes_of_infeasible
    {theory : Structural.Theory.{u}}
    {α : Type u} {Q : Type v} [State α]
    [PatternMod theory α Q]
    {source : APattBody α} {target : Q}
    (hfalse : source.requires → False) :
    source ⊑[theory] target := by
  intro _ hsource
  exact False.elim (hfalse hsource.2)

open Lean Meta Elab Tactic

syntax (name := refineSubsumptionPrototype)
  "refine_subsumption " "(" ident* ")" " using " term : tactic

syntax (name := refutePostPrototype)
  "refute_post " "(" ident* ")" : tactic

syntax (name := subsumptionVariablesPrototype)
  "subsumption_variables " "(" ident* ")" : tactic

private def introduceSourceArguments (names : Array (TSyntax `ident)) :
    TacticM Unit := do
  for name in names do
    let goal ← getMainGoal
    let lemmaProof ← mkConstWithFreshMVarLevels ``source_family_subsumes_mod
    let [subgoal] ← goal.apply lemmaProof
      | throwError "could not expose the next source-pattern argument"
    let (_, next) ← subgoal.introN 1 [name.getId]
    replaceMainGoal [next]

private partial def targetPath (target selectedHead : Expr) :
    MetaM (Option (List Bool)) := do
  let reduced ← withTransparency .all <| whnf target
  let arguments := reduced.getAppArgs
  if reduced.getAppFn.isConstOf ``framework.Patterns.Disjunction.mk &&
      arguments.size >= 2 then
    if let some path ← targetPath arguments[arguments.size - 2]! selectedHead then
      return some (false :: path)
    if let some path ← targetPath arguments[arguments.size - 1]! selectedHead then
      return some (true :: path)
    return none
  if ← withoutModifyingState <| isDefEq target.getAppFn selectedHead then
    return some []
  return none

private def includeSelectedAtom (goal : MVarId) : TacticM Unit :=
    goal.withContext do
  let input ← Narrowing.Goal.ofSubsumesType (← goal.getType)
  let selectedHead := input.source.getAppFn
  let some path ← targetPath input.target selectedHead
    | throwError "the selected atom does not occur in the target pattern"
  let mut goal := goal
  for goRight in path do
    let theoremName := if goRight then
      ``target_right_subsumes_mod
    else
      ``target_left_subsumes_mod
    let theoremProof ← mkConstWithFreshMVarLevels theoremName
    let [next] ← goal.apply theoremProof
      | throwError "could not select the requested target disjunct"
    goal := next
  for argument in input.source.getAppArgs do
    setGoals [goal]
    let argumentSyntax ← Term.exprToSyntax argument
    evalTactic (← `(tactic|
      apply target_family_subsumes_mod $argumentSyntax))
    let [next] ← getGoals
      | throwError m!"could not instantiate the selected target atom"
    goal := next
  let theoremProof ← mkConstWithFreshMVarLevels ``subsumes_mod_refl
  let remaining ← goal.apply theoremProof
  unless remaining.isEmpty do
    throwError "the supplied target arguments do not instantiate the selected atom"

private def sourceDefinition? : TacticM (Option Ident) := do
  let goal ← getMainGoal
  let input ← goal.withContext do
    Narrowing.Goal.ofSubsumesType (← goal.getType)
  match input.source.getAppFn with
  | .fvar fvarId =>
      let declaration ← goal.withContext fvarId.getDecl
      return if declaration.isLet then some (mkIdent declaration.userName)
        else none
  | _ => return none

private def unfoldSourceDefinition (definition? : Option Ident) : TacticM Unit := do
  if let some definition := definition? then
    evalTactic (← `(tactic| dsimp only [$definition:ident]))

private def refineSubsumption (target : Term) : TacticM Unit := do
  let sourceDefinition ← sourceDefinition?
  evalTactic (← `(tactic|
    apply subsumes_mod_trans (middle := $target)))
  let [sourceToMiddle, middleToTarget] ← getGoals
    | throwError "unexpected symbolic-subsumption subgoals"

  setGoals [sourceToMiddle]
  evalTactic (← `(tactic|
    apply apattBody_subsumes_of_match))
  let [structuralGoal, conditionGoal] ← getGoals
    | throwError "unexpected atomic-subsumption subgoals"

  setGoals [structuralGoal]
  unfoldSourceDefinition sourceDefinition
  evalTactic (← `(tactic| try simp_all only))
  unless (← getGoals).isEmpty do
    evalTactic (← `(tactic| structural_rfl))
  unless (← getGoals).isEmpty do
    throwError "could not discharge the instantiated structural equality"

  setGoals [middleToTarget]
  includeSelectedAtom middleToTarget

  setGoals [conditionGoal]
  unfoldSourceDefinition sourceDefinition

elab_rules : tactic
  | `(tactic| refine_subsumption ($names:ident*) using $target:term) => do
      introduceSourceArguments names
      refineSubsumption target
  | `(tactic| refute_post ($names:ident*)) => do
      introduceSourceArguments names
      let sourceDefinition ← sourceDefinition?
      evalTactic (← `(tactic|
        apply apattBody_subsumes_of_infeasible))
      unfoldSourceDefinition sourceDefinition
  | `(tactic| subsumption_variables ($names:ident*)) => do
      introduceSourceArguments names

end SymbolicSubsumptionPrototype

open SymbolicSubsumptionPrototype

/-!
Computational narrowing prototype. Each successor is introduced as a named
local definition, and `post` is their disjunction. Certification is separate.
-/
namespace NamedPostPrototype

open Lean Meta Elab Tactic
open framework.Patterns

syntax "narrow " term " from " term " mod " term " as " ident : tactic

elab_rules : tactic
  | `(tactic| narrow $rule:term from $source:term mod $theory:term as $post:ident) => do
      let goal ← getMainGoal
      let (input, alternatives) ← goal.withContext do
        let rule ← Tactic.elabTerm rule.raw none
        let source ← Tactic.elabTerm source.raw none
        let theoryType ← mkConstWithFreshMVarLevels ``Structural.Theory
        let theory ← Tactic.elabTerm theory.raw (some theoryType)
        let input ← Narrowing.Problem.ofRulesAndPattern rule source
        let alternatives ← Narrowing.Backend.solvePattern input (some theory)
        return (input, alternatives)
      let mut goal := goal
      let mut atoms : Array Expr := #[]
      for index in [:alternatives.size] do
        let some alternative := alternatives[index]?
          | throwError "missing narrowing alternative"
        let atom ← goal.withContext do
          Narrowing.Materialization.successor
            alternative.problem alternative.alternative
        let atomType ← goal.withContext <| inferType atom
        let sourceName := match alternative.problem.source.closure.application.getAppFn with
          | .const name _ => name.getString!
          | _ => "source"
        let name ← goal.withContext do
          return (← getLCtx).getUnusedName
            (Name.mkSimple s!"post_{sourceName}")
        let next ← goal.define name atomType atom
        let (atomFVar, next) ← next.intro1P
        atoms := atoms.push (mkFVar atomFVar)
        goal := next
      let postValue ← goal.withContext do
        if atoms.isEmpty then
          return (← Narrowing.Materialization.post input.stateType #[]).value
        let mut value := atoms[atoms.size - 1]!
        for atom in atoms.toList.dropLast.reverse do
          value ← mkAppM ``framework.Patterns.Disjunction.mk #[atom, value]
        return value
      let postType ← goal.withContext <| inferType postValue
      let next ← goal.define post.getId postType postValue
      let (_, next) ← next.intro1P
      replaceMainGoal [next]

end NamedPostPrototype

open NamedPostPrototype

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

open Lean PrettyPrinter.Delaborator PrettyPrinter.Delaborator.SubExpr in
@[app_delab Conf.mk]
def delabConf : Delab := do
  unless (← getOptions).getBool `conPanna.pp.compactPatterns true do
    failure
  let next ← withNaryArg 0 delab
  let serving ← withNaryArg 1 delab
  let procs ← withNaryArg 2 delab
  `(⟨$next, $serving, $procs⟩)

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

lemma enter_waiting_constraints (next serving : Nat) (rest : ProcSet)
    (hlt : serving < next)
    (hnoCrit : noCrit (union rest (singleton (wait serving))))
    (hrange :
      ticketsInRange serving next (union rest (singleton (wait serving))))
    (hnodup :
      (tickets (union rest (singleton (wait serving)))).Nodup) :
    (critical next serving rest).requires := by
  simp only [critical]
  simp_all [noCrit, ticketsInRange, tickets, Multiset.nodup_add]
  grind

lemma allIdle_of_noCrit_of_tickets_eq_zero (procs : ProcSet)
    (hnoCrit : noCrit procs) (hzero : tickets procs = 0) :
    allIdle procs := by
  induction procs with
  | empty => simp [allIdle]
  | singleton mode => cases mode <;> simp_all [noCrit, tickets, allIdle]
  | union left right ihLeft ihRight =>
      simp only [noCrit, tickets, allIdle] at hnoCrit hzero ⊢
      have hcards := congrArg Multiset.card hzero
      simp only [Multiset.card_add, Multiset.card_zero] at hcards
      have hLeftZero : tickets left = 0 :=
        Multiset.card_eq_zero.mp (by omega)
      have hRightZero : tickets right = 0 :=
        Multiset.card_eq_zero.mp (by omega)
      exact ⟨ihLeft hnoCrit.1 hLeftZero, ihRight hnoCrit.2 hRightZero⟩

lemma exit_critical_initial_constraints (next serving : Nat) (rest : ProcSet)
    (hboundary : serving.succ = next)
    (_hlt : serving < next)
    (hnoCrit : noCrit rest)
    (hrange : ∀ ticket ∈ tickets rest,
      serving < ticket ∧ ticket < next)
    (_hnodup : (tickets rest).Nodup) :
    (initial next (union (singleton idle) rest)).requires := by
  have hzero : tickets rest = 0 := by
    apply Multiset.eq_zero_iff_forall_notMem.mpr
    intro ticket hticket
    have bounds := hrange ticket hticket
    omega
  have hRestIdle := allIdle_of_noCrit_of_tickets_eq_zero rest hnoCrit hzero
  simpa [initial, allIdle] using hRestIdle

lemma exit_critical_waiting_constraints (next serving : Nat) (rest : ProcSet)
    (hboundary : serving.succ ≠ next)
    (hlt : serving < next)
    (hnoCrit : noCrit rest)
    (hrange : ∀ ticket ∈ tickets rest,
      serving < ticket ∧ ticket < next)
    (hnodup : (tickets rest).Nodup) :
    (waiting next serving.succ (union (singleton idle) rest)).requires := by
  simp only [waiting]
  refine ⟨by omega, ?_, ?_, ?_⟩
  · simpa [noCrit] using hnoCrit
  · intro ticket hticket
    have hticketRest : ticket ∈ tickets rest := by
      simpa [tickets] using hticket
    have bounds := hrange ticket hticketRest
    exact ⟨by omega, bounds.2⟩
  · simpa [tickets] using hnodup




/- main proof -/

example : wake ⊢ bakeryInv ↪[BakeryTheory] bakeryInv := by
  narrow wake from bakeryInv mod BakeryTheory as post
  have hsub : post ⊑[BakeryTheory] bakeryInv := by
    unfold bakeryInv
    unfold post
    subsume_cases
    · apply target_right_subsumes_mod
      apply target_left_subsumes_mod
      unfold post_initial
      unfold waiting
      refine_subsumption (next rest) using
        waiting next.succ next (union (singleton (wait next)) rest)
      simpa only [true_and, and_imp] using wake_initial_constraints next rest
    · apply target_right_subsumes_mod
      apply target_left_subsumes_mod
      refine_subsumption (next serving rest) using
        waiting next.succ serving (union (singleton (wait next)) rest)
      simpa only [true_and, and_imp] using
        wake_waiting_constraints next serving rest
    · apply target_right_subsumes_mod
      apply target_right_subsumes_mod
      refine_subsumption (next serving rest) using
        critical next.succ serving (union (singleton (wait next)) rest)
      simpa only [true_and, and_imp] using
        wake_critical_constraints next serving rest
  have hcomplete : wake ⊢ bakeryInv ↪[BakeryTheory] post := by
    sorry
  exact mapsInto_of_mapsInto_of_subsumes_mod hcomplete hsub

example : enter ⊢ bakeryInv ↪[BakeryTheory] bakeryInv := by
  narrow enter from bakeryInv mod BakeryTheory as post
  have hsub : post ⊑[BakeryTheory] bakeryInv := by
    unfold bakeryInv
    subsume_cases
    · refute_post (next rest)
      simp [allIdle]
    · refine_subsumption (next serving rest) using
        critical next serving rest
      simpa only [true_and, and_imp] using
        enter_waiting_constraints next serving rest
    · refute_post (next serving rest)
      simp only [tickets, true_and]
      rintro ⟨_, _, hrange, _⟩
      have hmem : serving ∈ tickets rest + {serving} := by simp
      have := hrange serving hmem
      omega
  have hcomplete : enter ⊢ bakeryInv ↪[BakeryTheory] post := by
    sorry
  exact mapsInto_of_mapsInto_of_subsumes_mod hcomplete hsub



example : exit ⊢ bakeryInv ↪[BakeryTheory] bakeryInv := by
  narrow exit from bakeryInv mod BakeryTheory as post
  have hsub : post ⊑[BakeryTheory] bakeryInv := by
    unfold bakeryInv
    subsume_cases
    · refute_post (next rest)
      simp [allIdle]
    · refute_post (next serving rest)
      simp [noCrit]
    · refute_post (next serving rest)
      simp [noCrit]
    · subsumption_variables (next serving rest)
      by_cases hboundary : serving.succ = next
      · refine_subsumption () using
          initial next (union (singleton idle) rest)
        simpa only [true_and, and_imp] using
          exit_critical_initial_constraints next serving rest hboundary
      · refine_subsumption () using
          waiting next serving.succ (union (singleton idle) rest)
        simpa only [true_and, and_imp] using
          exit_critical_waiting_constraints next serving rest hboundary
  have hcomplete : exit ⊢ bakeryInv ↪[BakeryTheory] post := by
    sorry
  exact mapsInto_of_mapsInto_of_subsumes_mod hcomplete hsub
