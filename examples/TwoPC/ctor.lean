import conPanna.BaseTheory.ACU
import conPanna.Dumper

/-!
Two-phase commit: the constructor model of configurations.
-/

namespace TwoPC

abbrev Oid := Nat
abbrev Oids := ACU Oid

inductive PState where
  | working | prepared | committed | aborted
  deriving DecidableEq

inductive CState where
  | collecting | committing | aborting
  deriving DecidableEq

/-- `< P : Participant | state : S >` -/
structure Participant where
  id : Oid
  state : PState

/-- `< C : Coordinator | phase : PH, parts : PS, wait : W >` -/
structure Coordinator where
  id : Oid
  phase : CState
  parts : Oids
  wait : Oids

inductive Msg where
  | vote (yes : Bool) (src dst : Oid)
  | decision (commit : Bool) (src : Oid) (rcv : Oids)

inductive Item where
  | part (o : Participant)
  | coord (o : Coordinator)
  | msg (m : Msg)

abbrev Items := ACU Item

structure Conf where
  cf : Items

#dump_model Conf

end TwoPC
