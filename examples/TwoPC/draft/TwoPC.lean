import conPanna.conPanna
import conPanna.Unification.Certification.Multiset

/-!
# Two-phase commit: a feasibility draft

An object-oriented model (objects and messages in one ACU configuration; identifier
sets as a second ACU sort) and an invariant with one patch per coordinator phase, aimed
at atomic-commit agreement: no participant commits while another aborts.

`twoPC_inv`: narrowing the whole system against the three patches gives 82 cases;
simplification drops 50 (a second coordinator, a phase mismatch, impossible messages);
each of the 32 left lands in its phase's patch by `maude_match`, and its condition
follows by simplification, except the two `recvYes` patches (a short explicit proof).
Obligations: `obligation.lean`; agreement end to end: `agreement.lean`.
-/

namespace TwoPC

open Expresso Unification Narrowing Subsumption

/-! ## Model -/

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

/-! ## Rules -/

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

/-! ## Summaries of a configuration (higher-order, additive over `+`) -/

def partOf : Item → Multiset Participant | .part o => {o} | _ => 0
def coordOf : Item → Multiset Coordinator | .coord o => {o} | _ => 0
def voteOf : Item → Multiset (Bool × Oid) | .msg (.vote b p _) => {(b, p)} | _ => 0
def decOf : Item → Multiset Bool | .msg (.decision b _ _) => {b} | _ => 0

def parts (CF : Items) : Multiset Participant := CF.toMultiset.bind partOf
def coords (CF : Items) : Multiset Coordinator := CF.toMultiset.bind coordOf
def votes (CF : Items) : Multiset (Bool × Oid) := CF.toMultiset.bind voteOf
def decs (CF : Items) : Multiset Bool := CF.toMultiset.bind decOf

theorem parts_plus (X Y : Items) : parts (X + Y) = parts X + parts Y := by simp [parts]
theorem parts_one (a : Item) : parts {a} = partOf a := by simp [parts]
theorem parts_unit : parts ∅ = 0 := by simp [parts]
theorem coords_plus (X Y : Items) : coords (X + Y) = coords X + coords Y := by simp [coords]
theorem coords_one (a : Item) : coords {a} = coordOf a := by simp [coords]
theorem coords_unit : coords ∅ = 0 := by simp [coords]
theorem votes_plus (X Y : Items) : votes (X + Y) = votes X + votes Y := by simp [votes]
theorem votes_one (a : Item) : votes {a} = voteOf a := by simp [votes]
theorem votes_unit : votes ∅ = 0 := by simp [votes]
theorem decs_plus (X Y : Items) : decs (X + Y) = decs X + decs Y := by simp [decs]
theorem decs_one (a : Item) : decs {a} = decOf a := by simp [decs]
theorem decs_unit : decs ∅ = 0 := by simp [decs]

/-! ## Invariant: one patch per coordinator phase -/

/-- In every phase: the coordinator is unique, participants have distinct ids, each
participant has at most one vote in transit, and a working one has none. -/
def common (CF : Items) : Prop :=
  coords CF = 0 ∧ ((parts CF).map (·.id)).Nodup ∧ ((votes CF).map (·.2)).Nodup ∧
  (∀ o ∈ parts CF, o.state = .working → ∀ b, (b, o.id) ∉ votes CF)

/-- Collecting: nothing decided; a participant not waited for, or with a yes in transit,
is prepared; a yes in transit is still awaited. -/
def coll (W : Oids) (CF : Items) : Prop :=
  common CF ∧ decs CF = 0 ∧
  (∀ o ∈ parts CF, o.state ≠ .committed ∧ (o.state = .prepared ∨ o.id ∈ W.toMultiset) ∧
    ((true, o.id) ∈ votes CF → o.state = .prepared)) ∧
  (∀ p, (true, p) ∈ votes CF → p ∈ W.toMultiset)

/-- Committed: every participant prepared or committed; only commit decisions. -/
def comm (CF : Items) : Prop :=
  common CF ∧ (∀ o ∈ parts CF, o.state = .prepared ∨ o.state = .committed) ∧
  (∀ b ∈ decs CF, b = true)

/-- Aborted: nobody committed; only abort decisions. -/
def abrt (CF : Items) : Prop :=
  common CF ∧ (∀ o ∈ parts CF, o.state ≠ .committed) ∧ (∀ b ∈ decs CF, b = false)

def collP : Patch Conf := .bind fun ((C, PS, W, CF) : Oid × Oids × Oids × Items) =>
  ⟨⟨{Item.coord ⟨C, .collecting, PS, W⟩} + CF⟩, coll W CF⟩

def commP : Patch Conf := .bind fun ((C, PS, W, CF) : Oid × Oids × Oids × Items) =>
  ⟨⟨{Item.coord ⟨C, .committing, PS, W⟩} + CF⟩, comm CF⟩

def abrtP : Patch Conf := .bind fun ((C, PS, W, CF) : Oid × Oids × Oids × Items) =>
  ⟨⟨{Item.coord ⟨C, .aborting, PS, W⟩} + CF⟩, abrt CF⟩

def inv : Pattern Conf := [collP, commP, abrtP]

/-! ## Agreement follows from each patch -/

theorem agree_coll {W : Oids} {CF : Items} (h : coll W CF) :
    ∀ o ∈ parts CF, o.state ≠ .committed := fun o ho => (h.2.2.1 o ho).1

theorem agree_comm {CF : Items} (h : comm CF) :
    ∀ o ∈ parts CF, o.state ≠ .aborted := fun o ho => by
  rcases h.2.1 o ho with h' | h' <;> simp [h']

theorem agree_abrt {CF : Items} (h : abrt CF) :
    ∀ o ∈ parts CF, o.state ≠ .committed := h.2.1

/-! ## Narrowing -/

-- narrowing simplifies 82 cases in one declaration
set_option maxHeartbeats 4000000 in
theorem twoPC_inv : isOverPost twoPC inv inv := by
  narrow twoPC from inv
    using [ACU.plus_unit, ACU.unit_plus, coll, comm, abrt, common, parts_plus, parts_one,
      parts_unit, coords_plus, coords_one, coords_unit, votes_plus, votes_one, votes_unit,
      decs_plus, decs_one, decs_unit, partOf, coordOf, voteOf, decOf]
    as post hpost
  refine over_of_subsumes hpost.1 (subsumes_of_cover fun a ha => ?_)
  rw [← post_eq] at ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  repeat' rcases ha with rfl | ha
  all_goals apply subsumes_one
  -- each post patch lands in the patch of its coordinator phase
  all_goals
    first
    | maude_match collP
    | maude_match commP
    | maude_match abrtP
  -- the conditions: 15 of 26 close by simplification alone
  all_goals
    try simp only [coll, comm, abrt, common, parts_plus, parts_one, parts_unit, coords_plus,
      coords_one, coords_unit, votes_plus, votes_one, votes_unit, decs_plus, decs_one,
      decs_unit, partOf, coordOf, voteOf, decOf, ACU.toMultiset_unit, add_zero, zero_add, Multiset.map_add, Multiset.map_singleton,
      Multiset.nodup_add, Multiset.nodup_singleton, Multiset.disjoint_singleton,
      Multiset.mem_add, Multiset.mem_singleton,
      Multiset.mem_map, or_imp, forall_and, forall_eq, Prod.mk.injEq,
      Prod.exists, Bool.exists_bool, Bool.forall_bool] at hc ⊢
    try (simp_all; done)
  -- 11 left, the protocol's relational facts (`aesop`, `grind` fail): a new vote's sender
  -- had none in transit (`vote`, coll/abrt), the counted voter is the prepared one
  -- (`recvYes`), no no-vote at commit (`decideCommit`), and a vote's witness carries over
  -- to the delivered participant (`deliver*`)
  -- the two `recvYes` patches: the voter `P` (`x.2.1`) leaves the waiting set; it is
  -- prepared, and no other yes from it is in transit
  all_goals
    refine ⟨⟨hc.1.1, hc.1.2.1, hc.1.2.2.1.1, hc.1.2.2.2.1⟩, hc.2.1,
      ⟨hc.2.2.1.1, fun o ho => ?_, hc.2.2.1.2.2.1⟩, fun p hp => ?_⟩
    · by_cases hP : o.id = x.2.1
      · exact .inl (hc.2.2.1.2.2.2 o ho hP)
      · simpa [hP] using hc.2.2.1.2.1 o ho
    · have hne : p ≠ x.2.1 := fun e => hc.1.2.2.1.2.2 (.inr ⟨p, hp, e⟩)
      simpa [hne] using hc.2.2.2 p hp

end TwoPC
