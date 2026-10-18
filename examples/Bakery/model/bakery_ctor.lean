import Expresso.ACU
import conPanna.Dumper

/-!
Bakery, N processes: the constructor model of configurations.
A configuration holds the next ticket to hand out, the ticket being served, and the
bag of processes. The bag is an ACU sort: registering it is writing `ACU Mode`.
-/

namespace Bakery

inductive Mode where
  | idle
  | wait (ticket : Nat)
  | crit (ticket : Nat)

/-- A bag of processes: `∅`, `{p}` and `P + Q`, equal modulo ACU. -/
abbrev ProcSet := ACU Mode

structure Conf where
  next : Nat
  serving : Nat
  procs : ProcSet

/-! The model as the Maude module the tools work in (written to `producer/.cache`). -/
#dump_model Conf

end Bakery
