import examples.German.ctor
import Expresso.core
import conPanna.Unification.Certification.Multiset

/-!
German's protocol: the rules, one package of type `System`.
-/

namespace German

open Expresso

def sendReqS : Rule Conf := .bind fun ((I, C2, C3, CF) : Oid × Gnt × Ack × Items) =>
  { lhs := ⟨{Item.cache ⟨I, .invalid, .noReq, C2, C3⟩} + CF⟩
    rhs := ⟨{Item.cache ⟨I, .invalid, .reqS, C2, C3⟩} + CF⟩ }

def sendReqEI : Rule Conf := .bind fun ((I, C2, C3, CF) : Oid × Gnt × Ack × Items) =>
  { lhs := ⟨{Item.cache ⟨I, .invalid, .noReq, C2, C3⟩} + CF⟩
    rhs := ⟨{Item.cache ⟨I, .invalid, .reqE, C2, C3⟩} + CF⟩ }

def sendReqES : Rule Conf := .bind fun ((I, C2, C3, CF) : Oid × Gnt × Ack × Items) =>
  { lhs := ⟨{Item.cache ⟨I, .shared, .noReq, C2, C3⟩} + CF⟩
    rhs := ⟨{Item.cache ⟨I, .shared, .reqE, C2, C3⟩} + CF⟩ }

/-- The directory takes a shared request: the sharers are to be invalidated (if needed). -/
def recvReqS : Rule Conf := .bind fun ((P, X, SH, IV, I, S, C2, C3, CF) :
    Oid × Bool × Oids × Oids × Oid × CacheState × Gnt × Ack × Items) =>
  { lhs := ⟨{Item.dir ⟨.idle, P, X, SH, IV⟩} + ({Item.cache ⟨I, S, .reqS, C2, C3⟩} + CF)⟩
    rhs := ⟨{Item.dir ⟨.cmdS, I, X, SH, SH⟩} + ({Item.cache ⟨I, S, .noReq, C2, C3⟩} + CF)⟩ }

def recvReqE : Rule Conf := .bind fun ((P, X, SH, IV, I, S, C2, C3, CF) :
    Oid × Bool × Oids × Oids × Oid × CacheState × Gnt × Ack × Items) =>
  { lhs := ⟨{Item.dir ⟨.idle, P, X, SH, IV⟩} + ({Item.cache ⟨I, S, .reqE, C2, C3⟩} + CF)⟩
    rhs := ⟨{Item.dir ⟨.cmdE, I, X, SH, SH⟩} + ({Item.cache ⟨I, S, .noReq, C2, C3⟩} + CF)⟩ }

/-- Invalidate a sharer: for an exclusive request, or a shared one after an exclusive grant. -/
def sendInvE : Rule Conf := .bind fun ((P, X, SH, I, IV, S, C1, C3, CF) :
    Oid × Bool × Oids × Oid × Oids × CacheState × Req × Ack × Items) =>
  { lhs := ⟨{Item.dir ⟨.cmdE, P, X, SH, {I} + IV⟩} + ({Item.cache ⟨I, S, C1, .noGnt, C3⟩} + CF)⟩
    rhs := ⟨{Item.dir ⟨.cmdE, P, X, SH, IV⟩} + ({Item.cache ⟨I, S, C1, .inv, C3⟩} + CF)⟩ }

def sendInvS : Rule Conf := .bind fun ((P, SH, I, IV, S, C1, C3, CF) :
    Oid × Oids × Oid × Oids × CacheState × Req × Ack × Items) =>
  { lhs := ⟨{Item.dir ⟨.cmdS, P, true, SH, {I} + IV⟩} + ({Item.cache ⟨I, S, C1, .noGnt, C3⟩} + CF)⟩
    rhs := ⟨{Item.dir ⟨.cmdS, P, true, SH, IV⟩} + ({Item.cache ⟨I, S, C1, .inv, C3⟩} + CF)⟩ }

/-- A cache acknowledges an invalidation and drops its copy. -/
def sendInvAck : Rule Conf := .bind fun ((I, S, C1, CF) : Oid × CacheState × Req × Items) =>
  { lhs := ⟨{Item.cache ⟨I, S, C1, .inv, .noAck⟩} + CF⟩
    rhs := ⟨{Item.cache ⟨I, .invalid, C1, .noGnt, .invAck⟩} + CF⟩ }

/-- The directory takes an acknowledgement (while serving a request): `I` is no longer a
sharer, and no exclusive copy remains. Split on whether `I` is a sharer (sets are
multisets kept duplicate-free: membership is a pattern, non-membership a condition). -/
def recvInvAckS : Rule Conf := .bind fun ((K, P, X, I, SH, IV, S, C1, C2, CF) :
    Cmd × Oid × Bool × Oid × Oids × Oids × CacheState × Req × Gnt × Items) =>
  { lhs := ⟨{Item.dir ⟨K, P, X, {I} + SH, IV⟩} + ({Item.cache ⟨I, S, C1, C2, .invAck⟩} + CF)⟩
    rhs := ⟨{Item.dir ⟨K, P, false, SH, IV⟩} + ({Item.cache ⟨I, S, C1, C2, .noAck⟩} + CF)⟩
    cond := K ≠ Cmd.idle }

def recvInvAckN : Rule Conf := .bind fun ((K, P, X, SH, IV, I, S, C1, C2, CF) :
    Cmd × Oid × Bool × Oids × Oids × Oid × CacheState × Req × Gnt × Items) =>
  { lhs := ⟨{Item.dir ⟨K, P, X, SH, IV⟩} + ({Item.cache ⟨I, S, C1, C2, .invAck⟩} + CF)⟩
    rhs := ⟨{Item.dir ⟨K, P, false, SH, IV⟩} + ({Item.cache ⟨I, S, C1, C2, .noAck⟩} + CF)⟩
    cond := K ≠ Cmd.idle ∧ I ∉ SH.toMultiset }

/-- Grant a shared copy to the requester (no exclusive copy out). -/
def sendGntSN : Rule Conf := .bind fun ((I, SH, IV, S, C1, C3, CF) :
    Oid × Oids × Oids × CacheState × Req × Ack × Items) =>
  { lhs := ⟨{Item.dir ⟨.cmdS, I, false, SH, IV⟩} + ({Item.cache ⟨I, S, C1, .noGnt, C3⟩} + CF)⟩
    rhs := ⟨{Item.dir ⟨.idle, I, false, {I} + SH, IV⟩} + ({Item.cache ⟨I, S, C1, .gntS, C3⟩} + CF)⟩
    cond := I ∉ SH.toMultiset }

def sendGntSS : Rule Conf := .bind fun ((I, SH, IV, S, C1, C3, CF) :
    Oid × Oids × Oids × CacheState × Req × Ack × Items) =>
  { lhs := ⟨{Item.dir ⟨.cmdS, I, false, {I} + SH, IV⟩} + ({Item.cache ⟨I, S, C1, .noGnt, C3⟩} + CF)⟩
    rhs := ⟨{Item.dir ⟨.idle, I, false, {I} + SH, IV⟩} + ({Item.cache ⟨I, S, C1, .gntS, C3⟩} + CF)⟩ }

/-- Grant an exclusive copy: only when there are no sharers. -/
def sendGntE : Rule Conf := .bind fun ((I, IV, S, C1, C3, CF) :
    Oid × Oids × CacheState × Req × Ack × Items) =>
  { lhs := ⟨{Item.dir ⟨.cmdE, I, false, ∅, IV⟩} + ({Item.cache ⟨I, S, C1, .noGnt, C3⟩} + CF)⟩
    rhs := ⟨{Item.dir ⟨.idle, I, true, {I}, IV⟩} + ({Item.cache ⟨I, S, C1, .gntE, C3⟩} + CF)⟩ }

def recvGntS : Rule Conf := .bind fun ((I, S, C1, C3, CF) : Oid × CacheState × Req × Ack × Items) =>
  { lhs := ⟨{Item.cache ⟨I, S, C1, .gntS, C3⟩} + CF⟩
    rhs := ⟨{Item.cache ⟨I, .shared, C1, .noGnt, C3⟩} + CF⟩ }

def recvGntE : Rule Conf := .bind fun ((I, S, C1, C3, CF) : Oid × CacheState × Req × Ack × Items) =>
  { lhs := ⟨{Item.cache ⟨I, S, C1, .gntE, C3⟩} + CF⟩
    rhs := ⟨{Item.cache ⟨I, .exclusive, C1, .noGnt, C3⟩} + CF⟩ }

def german : System Conf :=
  [sendReqS, sendReqEI, sendReqES, recvReqS, recvReqE, sendInvE, sendInvS, sendInvAck,
   recvInvAckS, recvInvAckN, sendGntSN, sendGntSS, sendGntE, recvGntS, recvGntE]

end German
