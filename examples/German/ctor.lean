import Expresso.ACU
import conPanna.Dumper

/-!
German's cache-coherence protocol: the constructor model of configurations.
-/

namespace German

abbrev Oid := Nat
abbrev Oids := ACU Oid

inductive CacheState where
  | invalid | shared | exclusive
  deriving DecidableEq

/-- Channel 1, cache to directory: a request. -/
inductive Req where
  | noReq | reqS | reqE

/-- Channel 2, directory to cache: an invalidation or a grant. -/
inductive Gnt where
  | noGnt | inv | gntS | gntE
  deriving DecidableEq

/-- Channel 3, cache to directory: an invalidation acknowledgement. -/
inductive Ack where
  | noAck | invAck
  deriving DecidableEq

/-- The request the directory is serving. -/
inductive Cmd where
  | idle | cmdS | cmdE
  deriving DecidableEq

/-- `< I : Cache | state, chan1, chan2, chan3 >` -/
structure Cache where
  id : Oid
  state : CacheState
  ch1 : Req
  ch2 : Gnt
  ch3 : Ack

/-- `< Dir | cmd, ptr, exGntd, shr, inv >`: the request served and its requester; whether
an exclusive copy was granted; the sharers; those still to invalidate. -/
structure Dir where
  cmd : Cmd
  ptr : Oid
  exGntd : Bool
  shr : Oids
  inv : Oids

inductive Item where
  | cache (c : Cache)
  | dir (d : Dir)

abbrev Items := ACU Item

structure Conf where
  cf : Items

#dump_model Conf

end German
