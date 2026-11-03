import examples.TwoPC.ctor
import conPanna.core

/-!
Two-phase commit: the rules, one package of type `System`.
-/

namespace TwoPC

open Expresso

def voteYes : Rule Conf := .bind fun ((P, C, CF) : Oid × Oid × Items) =>
  { lhs := ⟨{Item.part ⟨P, .working⟩} + CF⟩
    rhs := ⟨{Item.part ⟨P, .prepared⟩} + ({Item.msg (.vote true P C)} + CF)⟩ }

def voteNo : Rule Conf := .bind fun ((P, C, CF) : Oid × Oid × Items) =>
  { lhs := ⟨{Item.part ⟨P, .working⟩} + CF⟩
    rhs := ⟨{Item.part ⟨P, .aborted⟩} + ({Item.msg (.vote false P C)} + CF)⟩ }

def recvYes : Rule Conf := .bind fun ((C, PS, P, W, CF) : Oid × Oids × Oid × Oids × Items) =>
  { lhs := ⟨{Item.coord ⟨C, .collecting, PS, {P} + W⟩} + ({Item.msg (.vote true P C)} + CF)⟩
    rhs := ⟨{Item.coord ⟨C, .collecting, PS, W⟩} + CF⟩ }

def decideCommit : Rule Conf := .bind fun ((C, PS, CF) : Oid × Oids × Items) =>
  { lhs := ⟨{Item.coord ⟨C, .collecting, PS, ∅⟩} + CF⟩
    rhs := ⟨{Item.coord ⟨C, .committing, PS, ∅⟩} + ({Item.msg (.decision true C PS)} + CF)⟩ }

def recvNo : Rule Conf := .bind fun ((C, PS, W, P, CF) : Oid × Oids × Oids × Oid × Items) =>
  { lhs := ⟨{Item.coord ⟨C, .collecting, PS, W⟩} + ({Item.msg (.vote false P C)} + CF)⟩
    rhs := ⟨{Item.coord ⟨C, .aborting, PS, W⟩} + ({Item.msg (.decision false C PS)} + CF)⟩ }

def timeout : Rule Conf := .bind fun ((C, PS, W, CF) : Oid × Oids × Oids × Items) =>
  { lhs := ⟨{Item.coord ⟨C, .collecting, PS, W⟩} + CF⟩
    rhs := ⟨{Item.coord ⟨C, .aborting, PS, W⟩} + ({Item.msg (.decision false C PS)} + CF)⟩ }

def deliverCommit : Rule Conf := .bind fun ((C, P, R, S, CF) :
    Oid × Oid × Oids × PState × Items) =>
  { lhs := ⟨{Item.msg (.decision true C ({P} + R))} + ({Item.part ⟨P, S⟩} + CF)⟩
    rhs := ⟨{Item.msg (.decision true C R)} + ({Item.part ⟨P, .committed⟩} + CF)⟩ }

def deliverAbort : Rule Conf := .bind fun ((C, P, R, S, CF) :
    Oid × Oid × Oids × PState × Items) =>
  { lhs := ⟨{Item.msg (.decision false C ({P} + R))} + ({Item.part ⟨P, S⟩} + CF)⟩
    rhs := ⟨{Item.msg (.decision false C R)} + ({Item.part ⟨P, .aborted⟩} + CF)⟩ }

def lossVote : Rule Conf := .bind fun ((V, P, C, CF) : Bool × Oid × Oid × Items) =>
  { lhs := ⟨{Item.msg (.vote V P C)} + CF⟩
    rhs := ⟨CF⟩ }

def twoPC : System Conf :=
  [voteYes, voteNo, recvYes, decideCommit, recvNo, timeout, deliverCommit, deliverAbort,
   lossVote]

end TwoPC
