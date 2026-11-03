import examples.Bakery.ctor
import conPanna.core
import conPanna.Unification.Certification.Multiset

/-!
Bakery, N processes: the rules, one package of type `System`. Each rule acts on one
process of the bag; `R` is the rest.
-/

namespace Bakery

open Expresso

/-- `⟨N, M, idle + R⟩ ⇒ ⟨N + 1, M, wait(N) + R⟩`: take the next ticket. -/
def wakeR : Rule Conf := .bind fun ((N, M, R) : Nat × Nat × ProcSet) =>
  { lhs := ⟨N, M, {Mode.idle} + R⟩, rhs := ⟨N + 1, M, {Mode.wait N} + R⟩ }

/-- `⟨N, M, wait(M) + R⟩ ⇒ ⟨N, M, crit(M) + R⟩`: the ticket being served enters. -/
def enterR : Rule Conf := .bind fun ((N, M, R) : Nat × Nat × ProcSet) =>
  { lhs := ⟨N, M, {Mode.wait M} + R⟩, rhs := ⟨N, M, {Mode.crit M} + R⟩ }

/-- `⟨N, M, crit(M) + R⟩ ⇒ ⟨N, M + 1, idle + R⟩`: leave, serve the next ticket. -/
def exitR : Rule Conf := .bind fun ((N, M, R) : Nat × Nat × ProcSet) =>
  { lhs := ⟨N, M, {Mode.crit M} + R⟩, rhs := ⟨N, M + 1, {Mode.idle} + R⟩ }

/-- One step of any process: a choice, not a sequence. -/
def bakery : System Conf := [wakeR, enterR, exitR]

/-! ## Abortable: a waiting process gives up its ticket, and serving skips tickets nobody
holds. -/

def Mode.ticket? : Mode → Option Nat
  | .idle => none
  | .wait t => some t
  | .crit t => some t

/-- Tickets of the waiting and critical processes. -/
def tickets (PS : ProcSet) : Multiset Nat := PS.toMultiset.filterMap Mode.ticket?

/-- A waiting process gives up its ticket. -/
def abortR : Rule Conf := .bind fun ((N, M, T, R) : Nat × Nat × Nat × ProcSet) =>
  { lhs := ⟨N, M, {Mode.wait T} + R⟩, rhs := ⟨N, M, {Mode.idle} + R⟩ }

/-- Serving skips a ticket nobody holds (without the condition, it could skip past a
waiting process, or start serving a ticket while another process is critical). -/
def skipR : Rule Conf := .bind fun ((N, M, R) : Nat × Nat × ProcSet) =>
  { lhs := ⟨N, M, R⟩, rhs := ⟨N, M + 1, R⟩
    cond := M < N ∧ M ∉ tickets R }

def abortable : System Conf := [abortR, skipR]

end Bakery
