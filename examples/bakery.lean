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

/-- The post has three candidates: from `initial` (refuted: `wait(c)` is not idle),
from `waiting` (lands in `critical`), and from `critical`: two processes in the
critical section, refuted by the ticket range. -/
theorem enter_preserves_inv : isOverPost (.rule enterR) invP invP := by
  -- one unifier set per (rule, patch) cell, computed by Maude
  let Us : unifiers_R_P (.rule enterR) invP := by maude_unify
  let post : Pattern Conf := post_R_P (.rule enterR) invP Us
  have hpost : isPost (.rule enterR) invP (post) :=
    certifyPost_R_P _ _ Us
      ⟨⟨initial_complete, sorry⟩,     -- initial:  complete, sound
       ⟨waiting_complete, sorry⟩,     -- waiting:  complete, sound
       ⟨critical_complete, sorry⟩⟩    -- critical: complete, sound
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

end NProc

end Bakery
