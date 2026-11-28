import conPanna.BaseTheory.ACU
import conPanna.Dumper

/-!
Readers-writers as a Petri net, N processes: the constructor model of markings.
A marking is a multiset of places (Meseguer, "Conditional rewriting logic as a unified
model of concurrency", §5.3.1): the ACU sort `ACU Place`. The resource place `tok` holds
two tokens; a reader takes one, a writer both.
-/

namespace ReadersWriters

inductive Place where
  | idle
  | reading
  | writing
  | tok
  deriving DecidableEq

/-- A marking: `∅`, `{p}` and `M + M'`, equal modulo ACU. -/
abbrev Marking := ACU Place

/-- The state: the marking of the net. -/
structure Conf where
  marking : Marking

/-! The model as the Maude module the tools work in (written to `producer/.cache`). -/
#dump_model Conf

end ReadersWriters
