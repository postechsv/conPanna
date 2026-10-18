import examples.Bakery.model.bakery_ctor
import Expresso.core

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
def bakery : System Conf := .choice (.rule wakeR) (.choice (.rule enterR) (.rule exitR))

end Bakery
