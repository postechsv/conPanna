import Tiny.Expresso.core
import Tiny.Expresso.ACU
import Tiny.conPanna.Unification.Unification
import Tiny.conPanna.Unification.Certification.Calculus
import Tiny.conPanna.Unification.Certification.Multiset
import Tiny.conPanna.Narrowing.Narrowing
import Tiny.conPanna.Dumper
import Tiny.conPanna.Unification.Tactics.maudeUnify
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-!
Bakery: a single-process semantics slice and ACU process-bag unification
examples, not a proof of the full Bakery protocol.
There are no custom tactics or external calls.
-/

namespace TinyBakery

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
The unifiers are computed by Maude (`maude_unify`); every certificate and the
containment are left as `sorry`.
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

/-- The post has three candidates: from `initial` (refuted: `wait(c)` is not idle),
from `waiting` (lands in `critical`), and from `critical`: two processes in the
critical section, refuted by the ticket range. -/
theorem enter_preserves_inv : isOverPost (.rule enterR) invP invP := by
  -- one unifier set per (rule, patch) cell, computed by Maude
  let Us : unifiers_R_P (.rule enterR) invP := by maude_unify
  let post : Pattern Conf := post_R_P (.rule enterR) invP Us
  have hpost : isPost (.rule enterR) invP (post) :=
    certifyPost_R_P _ _ Us
      ⟨⟨sorry, sorry⟩,     -- initial:  complete, sound
       ⟨sorry, sorry⟩,     -- waiting:  complete, sound
       ⟨sorry, sorry⟩⟩     -- critical: complete, sound
  have hsub : subsumes post invP := by
    sorry
  exact over_of_subsumes hpost.1 hsub

-- TODOs
-- filter bot
-- flatten disjunctions
-- user friendly syntax for patches
-- unfoldable defintions for patches so user can unfold state and cond at will

end NProc

end TinyBakery
