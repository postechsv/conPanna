import Expresso.core
import Expresso.ACU
import conPanna.Unification.Unification
import conPanna.Unification.Certification.Calculus
import conPanna.Unification.Certification.Multiset
import conPanna.Narrowing.Narrowing
--import conPanna.Dumper
import conPanna.Unification.Tactics.maudeUnify
import conPanna.Unification.Tactics.maudeCertifyComp
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-!
Bakery: a single-process semantics slice and ACU process-bag unification
examples, not a proof of the full Bakery protocol.
There are no custom tactics or external calls.
-/

namespace Bakery

open Expresso

inductive Mode where
  | idle
  | wait (ticket : Nat)
  | crit (ticket : Nat)

/-! ## Process-bag model
Registering an ACU sort, as in Maude's
  `op _+_ : ProcSet ProcSet -> ProcSet [assoc comm id: ∅]`.
Values are written `∅`, `{p}` and `P + Q`; equality is modulo ACU.
There is no idempotence or extra equation on process contents.
-/
abbrev ProcSet := ACU Mode

structure Conf where
  next : Nat
  serving : Nat
  procs : ProcSet

/-! ## Symbolic patterns
`bind` means existential membership, not a concrete choice of ticket.
The condition in a patch belongs to that same ticket assignment.
-/

def initial : Pattern Conf :=
  .patch (.bind fun n : Nat => { state := ⟨n, n, {.idle}⟩ })

def waiting : Pattern Conf :=
  .patch (.bind fun n : Nat => ⟨⟨n + 1, n, {.wait n}⟩, n < n + 1⟩)

def critical : Pattern Conf :=
  .patch (.bind fun n : Nat => ⟨⟨n + 1, n, {.crit n}⟩, n < n + 1⟩)

def invP : Pattern Conf :=
  .disj initial (.disj waiting critical)

--#reduce invP

/-! ## Parameterized rules and their one-step choice
The same bound ticket occurs on both sides and in the rule condition.
`bakerySystem` permits one of the three steps, not their sequential execution.
-/

def wake : System Conf :=
  .rule (.bind fun n : Nat =>
    { lhs := ⟨n, n, {.idle}⟩, rhs := ⟨n + 1, n, {.wait n}⟩ })

def enter : System Conf :=
  .rule (.bind fun n : Nat =>
    ⟨⟨n + 1, n, {.wait n}⟩, ⟨n + 1, n, {.crit n}⟩, n < n + 1⟩)

def exit : System Conf :=
  .rule (.bind fun n : Nat =>
    { lhs := ⟨n + 1, n, {.crit n}⟩, rhs := ⟨n + 1, n + 1, {.idle}⟩ })

def bakerySystem : System Conf :=
  .choice wake (.choice enter exit)

/-! ## N processes: `enter` preserves the invariant
The process bag now has a rest variable, so unification is genuinely modulo ACU.
Conditions follow the legacy `bakery.lean`, stated through `ACU.toMultiset`.
The unifiers are computed by Maude (`maude_unify`) and their completeness is
certified (`maude_certify_comp`); soundness and the containment are left as `sorry`.
-/
namespace NProc

open Unification Narrowing

def Mode.ticket? : Mode → Option Nat
  | .idle => none
  | .wait t => some t
  | .crit t => some t

/-- Tickets of the waiting and critical processes. -/
def tickets (PS : ProcSet) : Multiset Nat := PS.toMultiset.filterMap Mode.ticket?

def allIdle (PS : ProcSet) : Prop := ∀ m ∈ PS.toMultiset, m = .idle

def noCrit (PS : ProcSet) : Prop := ∀ m ∈ PS.toMultiset, ∀ t, m ≠ .crit t

/-- `⟨c, c, PS⟩ | allIdle(PS)` -/
def initialP : Patch Conf := .bind fun ((c, PS) : Nat × ProcSet) =>
  ⟨⟨c, c, PS⟩, allIdle PS⟩

/-- `⟨N, M, PS⟩ | M < N ∧ noCrit(PS) ∧ tickets(PS) ⊆ [M, N) ∧ nodup` -/
def waitingP : Patch Conf := .bind fun ((N, M, PS) : Nat × Nat × ProcSet) =>
  ⟨⟨N, M, PS⟩, M < N ∧ noCrit PS ∧ (∀ t ∈ tickets PS, M ≤ t ∧ t < N) ∧ (tickets PS).Nodup⟩

/-- `⟨N, M, crit(M) + PS⟩ | M < N ∧ noCrit(PS) ∧ tickets(PS) ⊆ (M, N) ∧ nodup` -/
def criticalP : Patch Conf := .bind fun ((N, M, PS) : Nat × Nat × ProcSet) =>
  ⟨⟨N, M, {Mode.crit M} + PS⟩,
    M < N ∧ noCrit PS ∧ (∀ t ∈ tickets PS, M < t ∧ t < N) ∧ (tickets PS).Nodup⟩

-- The constructor model of `Conf`, as the Maude module the producer works in.
-- #dump_model Conf

def invP : Pattern Conf :=
  .disj (.patch initialP) (.disj (.patch waitingP) (.patch criticalP))

/-- `⟨N, M, wait(M) + R⟩ ⇒ ⟨N, M, crit(M) + R⟩` -/
def enterR : Rule Conf := .bind fun ((N, M, R) : Nat × Nat × ProcSet) =>
  { lhs := ⟨N, M, {Mode.wait M} + R⟩, rhs := ⟨N, M, {Mode.crit M} + R⟩ }

/-! Completeness of each cell's unifiers, certified by Maude. The unifiers are
those `maude_unify` computes in `enter_preserves_inv` below; Maude's ACU unification
also returns the special case of an empty rest, an instance of the general one. -/

theorem initial_complete : complete (mayFire enterR initialP)
    [.bind fun (c : Nat) => ((c, c, ∅), c, {Mode.wait c}),
     .bind fun ((R, c) : ProcSet × Nat) => ((c, c, R), c, R + {Mode.wait c})] := by
  maude_certify_comp

theorem waiting_complete : complete (mayFire enterR waitingP)
    [.bind fun ((N, M) : Nat × Nat) => ((N, M, ∅), N, M, {Mode.wait M}),
     .bind fun ((R, N, M) : ProcSet × Nat × Nat) => ((N, M, R), N, M, R + {Mode.wait M})] := by
  maude_certify_comp

theorem critical_complete : complete (mayFire enterR criticalP)
    [.bind fun ((N, M) : Nat × Nat) => ((N, M, {Mode.crit M}), N, M, {Mode.wait M}),
     .bind fun ((N, M, Z) : Nat × Nat × ProcSet) =>
       ((N, M, Z + {Mode.crit M}), N, M, Z + {Mode.wait M})] := by
  maude_certify_comp

/-! ## Recording holes (proof of concept)
`later` is `sorry` whose statement is first made self-contained: the proof's local
`let`s (here `Us`, the Maude unifiers) are unfolded, so the hole states a closed,
literal obligation. `#obligations thm` lists the recorded holes of `thm` as theorem
statements, ready to be proved elsewhere. -/

open Lean Meta Elab Tactic in
/-- Close the goal like `sorry`, recording its self-contained statement. -/
elab "later" : tactic => withMainContext do
  let goal ← getMainGoal
  let P ← zetaReduce (← instantiateMVars (← goal.getType))
  if P.hasFVar then
    throwError "later: the statement depends on local variables{indentExpr P}"
  goal.assign (← mkSorry P false)
  replaceMainGoal []

open Lean Meta Elab Command in
/-- List the holes of a theorem's proof as standalone statements. -/
elab "#obligations " id:ident : command => liftTermElabM do
  let n ← realizeGlobalConstNoOverloadWithInfo id
  let some v := (← getConstInfo n).value? | throwError "{n} has no proof term"
  let holes ← IO.mkRef (#[] : Array Expr)
  v.forEach fun e => do
    if e.isAppOfArity ``sorryAx 2 then holes.modify (·.push e.appFn!.appArg!)
  let mut msg := m!""
  for (P, i) in (← holes.get).zipIdx do
    if P.hasLooseBVars then
      msg := msg ++ m!"-- hole {i + 1}: a plain `sorry`; its statement depends on the proof's context\n\n"
    else
      -- binder types are printed, so the statement parses back (`x.1` needs `x`'s type)
      let stmt ← withOptions (pp.funBinderTypes.set · true) (ppExpr P)
      msg := msg ++ m!"theorem {n}.obligation_{i + 1} :{Format.nest 4 (Format.line ++ stmt)} := by\n  sorry\n\n"
  logInfo msg

/-- The post has three candidates: from `initial` (refuted: `wait(c)` is not idle),
from `waiting` (lands in `critical`), and from `critical`: two processes in the
critical section, refuted by the ticket range. -/
theorem enter_preserves_inv : isOverPost (.rule enterR) invP invP := by
  -- one unifier set per (rule, patch) cell, computed by Maude
  let Us : unifiers_R_P (.rule enterR) invP := by maude_unify
  let post : Pattern Conf := post_R_P (.rule enterR) invP Us
  have hpost : isPost (.rule enterR) invP (post) :=
    certifyPost_R_P _ _ Us
      ⟨⟨by later, by later⟩,     -- initial:  complete, sound
       ⟨by later, by later⟩,     -- waiting:  complete, sound
       ⟨by later, by later⟩⟩    -- critical: complete, sound
  have hsub : subsumes post invP := by
    sorry
  exact over_of_subsumes hpost.1 hsub -- TODO: completeness & soundness instead of 1 & 2

-- TODOs
-- filter bot
-- flatten disjunctions
-- user friendly syntax for patches
-- unfoldable defintions for patches so user can unfold state and cond at will
-- support A/C/AC + free/U 6 combinations as "basic theories" for maude_unify and dump
-- prevent .cache interference
-- certification obligation printing so user coulde copy-paste as lemmas
-- syntax highlighting error due to meta programming
-- check maude producer is deterministic (i.e. no rules, only equations)

#print axioms enter_preserves_inv

#obligations enter_preserves_inv

theorem s_obligation_2 :
    sound (mayFire enterR initialP)
      [Unifier.bind fun (x : ℕ) => ((x, x, ∅), x, {Mode.wait x}),
        Unifier.bind fun (x : ProcSet × ℕ) => ((x.2, x.2, x.1), x.2, x.1 + {Mode.wait x.2})] := by
  intro u hu γ hγ
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl <;> obtain ⟨x, rfl⟩ := hγ <;>
    simp [unifiedBy, mayFire, enterR, initialP, waitingP, criticalP] <;> ac_rfl

theorem s_obligation_4 :
    sound (mayFire enterR waitingP)
      [Unifier.bind fun (x : ℕ × ℕ) => ((x.1, x.2, ∅), x.1, x.2, {Mode.wait x.2}),
        Unifier.bind fun (x : ProcSet × ℕ × ℕ) => ((x.2.1, x.2.2, x.1), x.2.1, x.2.2, x.1 + {Mode.wait x.2.2})] := by
  intro u hu γ hγ
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl <;> obtain ⟨x, rfl⟩ := hγ <;>
    simp [unifiedBy, mayFire, enterR, initialP, waitingP, criticalP] <;> ac_rfl

theorem s_obligation_6 :
    sound (mayFire enterR criticalP)
      [Unifier.bind fun (x : ℕ × ℕ) => ((x.1, x.2, {Mode.crit x.2}), x.1, x.2, {Mode.wait x.2}),
        Unifier.bind fun (x : ℕ × ℕ × ProcSet) =>
          ((x.1, x.2.1, x.2.2 + {Mode.crit x.2.1}), x.1, x.2.1, x.2.2 + {Mode.wait x.2.1})] := by
  intro u hu γ hγ
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl <;> obtain ⟨x, rfl⟩ := hγ <;>
    simp [unifiedBy, mayFire, enterR, initialP, waitingP, criticalP] <;> ac_rfl

end NProc

end Bakery
