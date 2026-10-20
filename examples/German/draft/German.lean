import conPanna.conPanna
import conPanna.Unification.Certification.Multiset

/-!
# German's cache-coherence protocol: a feasibility draft

The control part of German's protocol (no data), object-oriented: cache objects, each
with its three single-slot channels, and one directory object, in one ACU configuration;
the directory's sharer and invalidate sets are a second ACU sort (ids).

Forward: an invariant with one patch per directory situation (`inv`), preserved rule by
rule; coherence by disjointness from the bad patterns (`german_coherent`).
A draft: the condition proofs are `sorry`. The invariant was checked by explicit-state
enumeration outside the framework (inductive for 2 caches; all states reachable with 3
caches satisfy it). Six post patches do not route by matching: a condition fixes a
constructor value the target states literally (e.g. a cache state known to be invalid);
they need a case split, or a narrowing step that solves such conditions.
-/

namespace German

open Expresso Unification Narrowing Subsumption

/-! ## Model -/

abbrev Oid := Nat
abbrev Oids := ACU Oid

inductive CacheState where
  | invalid | shared | exclusive

/-- Channel 1, cache to directory: a request. -/
inductive Req where
  | noReq | reqS | reqE

/-- Channel 2, directory to cache: an invalidation or a grant. -/
inductive Gnt where
  | noGnt | inv | gntS | gntE

/-- Channel 3, cache to directory: an invalidation acknowledgement. -/
inductive Ack where
  | noAck | invAck

/-- The request the directory is serving. -/
inductive Cmd where
  | idle | cmdS | cmdE

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

/-! ## Rules -/

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

/-! ## Bad patterns: coherence fails -/

/-- Two caches: one exclusive, the other exclusive. -/
def badEE : Patch Conf := .bind fun ((I, R1, G1, A1, J, R2, G2, A2, CF) :
    Oid × Req × Gnt × Ack × Oid × Req × Gnt × Ack × Items) =>
  ⟨⟨{Item.cache ⟨I, .exclusive, R1, G1, A1⟩} + ({Item.cache ⟨J, .exclusive, R2, G2, A2⟩} + CF)⟩,
    True⟩

/-- Two caches: one exclusive, the other shared. -/
def badES : Patch Conf := .bind fun ((I, R1, G1, A1, J, R2, G2, A2, CF) :
    Oid × Req × Gnt × Ack × Oid × Req × Gnt × Ack × Items) =>
  ⟨⟨{Item.cache ⟨I, .exclusive, R1, G1, A1⟩} + ({Item.cache ⟨J, .shared, R2, G2, A2⟩} + CF)⟩,
    True⟩

def bad : Pattern Conf := [badEE, badES]

/-! ## The invariant (forward): one patch per directory situation
Constructors carry the directory's situation and, when an exclusive copy is out, its owner
`I`, linked by the shared id to the sharer set `{I}`; conditions say what the rest is. -/

/-- The caches' ids. -/
def cacheIds (CF : Items) : Multiset Oid :=
  CF.toMultiset.bind fun | .cache c => {c.id} | .dir _ => 0

/-- No exclusive copy out: a cache in the rest. A cache is a sharer exactly when it is
shared or a grant, invalidation or acknowledgement of it is in flight; invalidations
happen only while serving an exclusive request, to sharers not yet invalidated. -/
def freeItem (K : Cmd) (SH IV : Oids) : Item → Prop
  | .dir _ => False
  | .cache c => c.state ≠ .exclusive ∧ c.ch2 ≠ .gntE ∧
      (c.ch2 = .inv →
        c.state = .shared ∧ c.ch3 = .noAck ∧ K = .cmdE ∧ c.id ∉ IV.toMultiset) ∧
      (c.ch3 = .invAck →
        c.state = .invalid ∧ c.ch2 = .noGnt ∧ K = .cmdE ∧ c.id ∉ IV.toMultiset) ∧
      (c.id ∈ SH.toMultiset ↔
        c.state = .shared ∨ c.ch2 = .gntS ∨ c.ch2 = .inv ∨ c.ch3 = .invAck)

/-- An exclusive copy out to `I`: any other cache. -/
def otherItem (I : Oid) : Item → Prop
  | .dir _ => False
  | .cache c => c.id ≠ I ∧ c.state = .invalid ∧ c.ch2 = .noGnt ∧ c.ch3 = .noAck

def freeP : Patch Conf := .bind fun ((K, P, SH, IV, CF) : Cmd × Oid × Oids × Oids × Items) =>
  ⟨⟨{Item.dir ⟨K, P, false, SH, IV⟩} + CF⟩,
    (∀ it ∈ CF.toMultiset, freeItem K SH IV it) ∧ (cacheIds CF).Nodup ∧
      SH.toMultiset.Nodup ∧ IV.toMultiset ≤ SH.toMultiset⟩

/-- The owner holds the exclusive copy. -/
def ownE : Patch Conf := .bind fun ((K, P, IV, I, R, CF) : Cmd × Oid × Oids × Oid × Req × Items) =>
  ⟨⟨{Item.dir ⟨K, P, true, {I}, IV⟩} + ({Item.cache ⟨I, .exclusive, R, .noGnt, .noAck⟩} + CF)⟩,
    (∀ it ∈ CF.toMultiset, otherItem I it) ∧ (cacheIds CF).Nodup ∧ IV.toMultiset ≤ {I}⟩

/-- The exclusive grant is on its way to the owner. -/
def ownG : Patch Conf := .bind fun ((K, P, IV, I, R, CF) : Cmd × Oid × Oids × Oid × Req × Items) =>
  ⟨⟨{Item.dir ⟨K, P, true, {I}, IV⟩} + ({Item.cache ⟨I, .invalid, R, .gntE, .noAck⟩} + CF)⟩,
    (∀ it ∈ CF.toMultiset, otherItem I it) ∧ (cacheIds CF).Nodup ∧ IV.toMultiset ≤ {I}⟩

/-- The owner is being invalidated. -/
def ownInv : Patch Conf := .bind fun ((K, P, I, R, CF) : Cmd × Oid × Oid × Req × Items) =>
  ⟨⟨{Item.dir ⟨K, P, true, {I}, ∅⟩} + ({Item.cache ⟨I, .exclusive, R, .inv, .noAck⟩} + CF)⟩,
    K ≠ Cmd.idle ∧ (∀ it ∈ CF.toMultiset, otherItem I it) ∧ (cacheIds CF).Nodup⟩

/-- The owner has given up its copy; the directory has yet to hear it. -/
def ownAck : Patch Conf := .bind fun ((K, P, I, R, CF) : Cmd × Oid × Oid × Req × Items) =>
  ⟨⟨{Item.dir ⟨K, P, true, {I}, ∅⟩} + ({Item.cache ⟨I, .invalid, R, .noGnt, .invAck⟩} + CF)⟩,
    K ≠ Cmd.idle ∧ (∀ it ∈ CF.toMultiset, otherItem I it) ∧ (cacheIds CF).Nodup⟩

def inv : Pattern Conf := [freeP, ownE, ownG, ownInv, ownAck]

/-! ## Domain lemmas: the conditions over sums -/

theorem cacheIds_plus (X Y : Items) : cacheIds (X + Y) = cacheIds X + cacheIds Y := by
  simp [cacheIds]
theorem cacheIds_cache (c : Cache) : cacheIds {Item.cache c} = {c.id} := by simp [cacheIds]
theorem cacheIds_dir (d : Dir) : cacheIds {Item.dir d} = 0 := by simp [cacheIds]
theorem cacheIds_unit : cacheIds ∅ = 0 := by simp [cacheIds]

theorem freeItem_cache (K : Cmd) (SH IV : Oids) (c : Cache) :
    freeItem K SH IV (.cache c) ↔ c.state ≠ .exclusive ∧ c.ch2 ≠ .gntE ∧
      (c.ch2 = .inv →
        c.state = .shared ∧ c.ch3 = .noAck ∧ K = .cmdE ∧ c.id ∉ IV.toMultiset) ∧
      (c.ch3 = .invAck →
        c.state = .invalid ∧ c.ch2 = .noGnt ∧ K = .cmdE ∧ c.id ∉ IV.toMultiset) ∧
      (c.id ∈ SH.toMultiset ↔
        c.state = .shared ∨ c.ch2 = .gntS ∨ c.ch2 = .inv ∨ c.ch3 = .invAck) := Iff.rfl
theorem freeItem_dir (K : Cmd) (SH IV : Oids) (d : Dir) : freeItem K SH IV (.dir d) ↔ False :=
  Iff.rfl
theorem otherItem_cache (I : Oid) (c : Cache) :
    otherItem I (.cache c) ↔
      c.id ≠ I ∧ c.state = .invalid ∧ c.ch2 = .noGnt ∧ c.ch3 = .noAck := Iff.rfl
theorem otherItem_dir (I : Oid) (d : Dir) : otherItem I (.dir d) ↔ False := Iff.rfl

/-! ## Each rule preserves the invariant
One narrowing per rule (small, bounded declarations), combined by `isOverPost_choice`.
Each post patch is routed to the invariant patch of its directory situation. -/

/-- Route a post patch to the invariant patch its state matches. -/
macro "route" : tactic => `(tactic| first
  | maude_match freeP | maude_match ownE | maude_match ownG | maude_match ownInv
  | maude_match ownAck)

-- routing a rule\'s patches takes more than the default budget
set_option maxHeartbeats 4000000 in
theorem sendReqS_inv : isOverPost [sendReqS] inv inv := by
  narrow [sendReqS] from inv
    using [ACU.plus_unit, ACU.unit_plus, ACU.toMultiset_plus, ACU.toMultiset_elem,
      ACU.toMultiset_unit, Multiset.mem_add, Multiset.mem_singleton, Multiset.notMem_zero,
      or_imp, forall_and, forall_eq, freeItem_cache, freeItem_dir, otherItem_cache,
      otherItem_dir, cacheIds_plus, cacheIds_cache,
      cacheIds_dir, cacheIds_unit, Multiset.nodup_add, Multiset.nodup_singleton,
      Multiset.disjoint_singleton]
    as post hpost
  refine over_of_subsumes hpost.1 (subsumes_of_cover fun a ha => ?_)
  rw [← post_eq] at ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  repeat' rcases ha with rfl | ha
  all_goals apply subsumes_one
  all_goals try route
  -- conditions (and the patches whose constructor values only their conditions fix,
  -- see the file header): to be filled
  all_goals sorry

-- routing a rule\'s patches takes more than the default budget
set_option maxHeartbeats 4000000 in
theorem sendReqEI_inv : isOverPost [sendReqEI] inv inv := by
  narrow [sendReqEI] from inv
    using [ACU.plus_unit, ACU.unit_plus, ACU.toMultiset_plus, ACU.toMultiset_elem,
      ACU.toMultiset_unit, Multiset.mem_add, Multiset.mem_singleton, Multiset.notMem_zero,
      or_imp, forall_and, forall_eq, freeItem_cache, freeItem_dir, otherItem_cache,
      otherItem_dir, cacheIds_plus, cacheIds_cache,
      cacheIds_dir, cacheIds_unit, Multiset.nodup_add, Multiset.nodup_singleton,
      Multiset.disjoint_singleton]
    as post hpost
  refine over_of_subsumes hpost.1 (subsumes_of_cover fun a ha => ?_)
  rw [← post_eq] at ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  repeat' rcases ha with rfl | ha
  all_goals apply subsumes_one
  all_goals try route
  -- conditions (and the patches whose constructor values only their conditions fix,
  -- see the file header): to be filled
  all_goals sorry

-- routing a rule\'s patches takes more than the default budget
set_option maxHeartbeats 4000000 in
theorem sendReqES_inv : isOverPost [sendReqES] inv inv := by
  narrow [sendReqES] from inv
    using [ACU.plus_unit, ACU.unit_plus, ACU.toMultiset_plus, ACU.toMultiset_elem,
      ACU.toMultiset_unit, Multiset.mem_add, Multiset.mem_singleton, Multiset.notMem_zero,
      or_imp, forall_and, forall_eq, freeItem_cache, freeItem_dir, otherItem_cache,
      otherItem_dir, cacheIds_plus, cacheIds_cache,
      cacheIds_dir, cacheIds_unit, Multiset.nodup_add, Multiset.nodup_singleton,
      Multiset.disjoint_singleton]
    as post hpost
  refine over_of_subsumes hpost.1 (subsumes_of_cover fun a ha => ?_)
  rw [← post_eq] at ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  repeat' rcases ha with rfl | ha
  all_goals apply subsumes_one
  all_goals try route
  -- conditions (and the patches whose constructor values only their conditions fix,
  -- see the file header): to be filled
  all_goals sorry

-- routing a rule\'s patches takes more than the default budget
set_option maxHeartbeats 4000000 in
theorem recvReqS_inv : isOverPost [recvReqS] inv inv := by
  narrow [recvReqS] from inv
    using [ACU.plus_unit, ACU.unit_plus, ACU.toMultiset_plus, ACU.toMultiset_elem,
      ACU.toMultiset_unit, Multiset.mem_add, Multiset.mem_singleton, Multiset.notMem_zero,
      or_imp, forall_and, forall_eq, freeItem_cache, freeItem_dir, otherItem_cache,
      otherItem_dir, cacheIds_plus, cacheIds_cache,
      cacheIds_dir, cacheIds_unit, Multiset.nodup_add, Multiset.nodup_singleton,
      Multiset.disjoint_singleton]
    as post hpost
  refine over_of_subsumes hpost.1 (subsumes_of_cover fun a ha => ?_)
  rw [← post_eq] at ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  repeat' rcases ha with rfl | ha
  all_goals apply subsumes_one
  all_goals try route
  -- conditions (and the patches whose constructor values only their conditions fix,
  -- see the file header): to be filled
  all_goals sorry

-- routing a rule\'s patches takes more than the default budget
set_option maxHeartbeats 4000000 in
theorem recvReqE_inv : isOverPost [recvReqE] inv inv := by
  narrow [recvReqE] from inv
    using [ACU.plus_unit, ACU.unit_plus, ACU.toMultiset_plus, ACU.toMultiset_elem,
      ACU.toMultiset_unit, Multiset.mem_add, Multiset.mem_singleton, Multiset.notMem_zero,
      or_imp, forall_and, forall_eq, freeItem_cache, freeItem_dir, otherItem_cache,
      otherItem_dir, cacheIds_plus, cacheIds_cache,
      cacheIds_dir, cacheIds_unit, Multiset.nodup_add, Multiset.nodup_singleton,
      Multiset.disjoint_singleton]
    as post hpost
  refine over_of_subsumes hpost.1 (subsumes_of_cover fun a ha => ?_)
  rw [← post_eq] at ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  repeat' rcases ha with rfl | ha
  all_goals apply subsumes_one
  all_goals try route
  -- conditions (and the patches whose constructor values only their conditions fix,
  -- see the file header): to be filled
  all_goals sorry

-- routing a rule\'s patches takes more than the default budget
set_option maxHeartbeats 4000000 in
theorem sendInvE_inv : isOverPost [sendInvE] inv inv := by
  narrow [sendInvE] from inv
    using [ACU.plus_unit, ACU.unit_plus, ACU.toMultiset_plus, ACU.toMultiset_elem,
      ACU.toMultiset_unit, Multiset.mem_add, Multiset.mem_singleton, Multiset.notMem_zero,
      or_imp, forall_and, forall_eq, freeItem_cache, freeItem_dir, otherItem_cache,
      otherItem_dir, cacheIds_plus, cacheIds_cache,
      cacheIds_dir, cacheIds_unit, Multiset.nodup_add, Multiset.nodup_singleton,
      Multiset.disjoint_singleton]
    as post hpost
  refine over_of_subsumes hpost.1 (subsumes_of_cover fun a ha => ?_)
  rw [← post_eq] at ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  repeat' rcases ha with rfl | ha
  all_goals apply subsumes_one
  all_goals try route
  -- conditions (and the patches whose constructor values only their conditions fix,
  -- see the file header): to be filled
  all_goals sorry

-- routing a rule\'s patches takes more than the default budget
set_option maxHeartbeats 4000000 in
theorem sendInvS_inv : isOverPost [sendInvS] inv inv := by
  narrow [sendInvS] from inv
    using [ACU.plus_unit, ACU.unit_plus, ACU.toMultiset_plus, ACU.toMultiset_elem,
      ACU.toMultiset_unit, Multiset.mem_add, Multiset.mem_singleton, Multiset.notMem_zero,
      or_imp, forall_and, forall_eq, freeItem_cache, freeItem_dir, otherItem_cache,
      otherItem_dir, cacheIds_plus, cacheIds_cache,
      cacheIds_dir, cacheIds_unit, Multiset.nodup_add, Multiset.nodup_singleton,
      Multiset.disjoint_singleton]
    as post hpost
  refine over_of_subsumes hpost.1 (subsumes_of_cover fun a ha => ?_)
  rw [← post_eq] at ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  repeat' rcases ha with rfl | ha
  all_goals apply subsumes_one
  all_goals try route
  -- conditions (and the patches whose constructor values only their conditions fix,
  -- see the file header): to be filled
  all_goals sorry

-- routing a rule\'s patches takes more than the default budget
set_option maxHeartbeats 4000000 in
theorem sendInvAck_inv : isOverPost [sendInvAck] inv inv := by
  narrow [sendInvAck] from inv
    using [ACU.plus_unit, ACU.unit_plus, ACU.toMultiset_plus, ACU.toMultiset_elem,
      ACU.toMultiset_unit, Multiset.mem_add, Multiset.mem_singleton, Multiset.notMem_zero,
      or_imp, forall_and, forall_eq, freeItem_cache, freeItem_dir, otherItem_cache,
      otherItem_dir, cacheIds_plus, cacheIds_cache,
      cacheIds_dir, cacheIds_unit, Multiset.nodup_add, Multiset.nodup_singleton,
      Multiset.disjoint_singleton]
    as post hpost
  refine over_of_subsumes hpost.1 (subsumes_of_cover fun a ha => ?_)
  rw [← post_eq] at ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  repeat' rcases ha with rfl | ha
  all_goals apply subsumes_one
  all_goals try route
  -- conditions (and the patches whose constructor values only their conditions fix,
  -- see the file header): to be filled
  all_goals sorry

-- routing a rule\'s patches takes more than the default budget
set_option maxHeartbeats 4000000 in
theorem recvInvAckS_inv : isOverPost [recvInvAckS] inv inv := by
  narrow [recvInvAckS] from inv
    using [ACU.plus_unit, ACU.unit_plus, ACU.toMultiset_plus, ACU.toMultiset_elem,
      ACU.toMultiset_unit, Multiset.mem_add, Multiset.mem_singleton, Multiset.notMem_zero,
      or_imp, forall_and, forall_eq, freeItem_cache, freeItem_dir, otherItem_cache,
      otherItem_dir, cacheIds_plus, cacheIds_cache,
      cacheIds_dir, cacheIds_unit, Multiset.nodup_add, Multiset.nodup_singleton,
      Multiset.disjoint_singleton]
    as post hpost
  refine over_of_subsumes hpost.1 (subsumes_of_cover fun a ha => ?_)
  rw [← post_eq] at ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  repeat' rcases ha with rfl | ha
  all_goals apply subsumes_one
  all_goals try route
  -- conditions (and the patches whose constructor values only their conditions fix,
  -- see the file header): to be filled
  all_goals sorry

-- routing a rule\'s patches takes more than the default budget
set_option maxHeartbeats 4000000 in
theorem recvInvAckN_inv : isOverPost [recvInvAckN] inv inv := by
  narrow [recvInvAckN] from inv
    using [ACU.plus_unit, ACU.unit_plus, ACU.toMultiset_plus, ACU.toMultiset_elem,
      ACU.toMultiset_unit, Multiset.mem_add, Multiset.mem_singleton, Multiset.notMem_zero,
      or_imp, forall_and, forall_eq, freeItem_cache, freeItem_dir, otherItem_cache,
      otherItem_dir, cacheIds_plus, cacheIds_cache,
      cacheIds_dir, cacheIds_unit, Multiset.nodup_add, Multiset.nodup_singleton,
      Multiset.disjoint_singleton]
    as post hpost
  refine over_of_subsumes hpost.1 (subsumes_of_cover fun a ha => ?_)
  rw [← post_eq] at ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  repeat' rcases ha with rfl | ha
  all_goals apply subsumes_one
  all_goals try route
  -- conditions (and the patches whose constructor values only their conditions fix,
  -- see the file header): to be filled
  all_goals sorry

-- routing a rule\'s patches takes more than the default budget
set_option maxHeartbeats 4000000 in
theorem sendGntSN_inv : isOverPost [sendGntSN] inv inv := by
  narrow [sendGntSN] from inv
    using [ACU.plus_unit, ACU.unit_plus, ACU.toMultiset_plus, ACU.toMultiset_elem,
      ACU.toMultiset_unit, Multiset.mem_add, Multiset.mem_singleton, Multiset.notMem_zero,
      or_imp, forall_and, forall_eq, freeItem_cache, freeItem_dir, otherItem_cache,
      otherItem_dir, cacheIds_plus, cacheIds_cache,
      cacheIds_dir, cacheIds_unit, Multiset.nodup_add, Multiset.nodup_singleton,
      Multiset.disjoint_singleton]
    as post hpost
  refine over_of_subsumes hpost.1 (subsumes_of_cover fun a ha => ?_)
  rw [← post_eq] at ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  repeat' rcases ha with rfl | ha
  all_goals apply subsumes_one
  all_goals try route
  -- conditions (and the patches whose constructor values only their conditions fix,
  -- see the file header): to be filled
  all_goals sorry

-- routing a rule\'s patches takes more than the default budget
set_option maxHeartbeats 4000000 in
theorem sendGntSS_inv : isOverPost [sendGntSS] inv inv := by
  narrow [sendGntSS] from inv
    using [ACU.plus_unit, ACU.unit_plus, ACU.toMultiset_plus, ACU.toMultiset_elem,
      ACU.toMultiset_unit, Multiset.mem_add, Multiset.mem_singleton, Multiset.notMem_zero,
      or_imp, forall_and, forall_eq, freeItem_cache, freeItem_dir, otherItem_cache,
      otherItem_dir, cacheIds_plus, cacheIds_cache,
      cacheIds_dir, cacheIds_unit, Multiset.nodup_add, Multiset.nodup_singleton,
      Multiset.disjoint_singleton]
    as post hpost
  refine over_of_subsumes hpost.1 (subsumes_of_cover fun a ha => ?_)
  rw [← post_eq] at ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  repeat' rcases ha with rfl | ha
  all_goals apply subsumes_one
  all_goals try route
  -- conditions (and the patches whose constructor values only their conditions fix,
  -- see the file header): to be filled
  all_goals sorry

-- routing a rule\'s patches takes more than the default budget
set_option maxHeartbeats 4000000 in
theorem sendGntE_inv : isOverPost [sendGntE] inv inv := by
  narrow [sendGntE] from inv
    using [ACU.plus_unit, ACU.unit_plus, ACU.toMultiset_plus, ACU.toMultiset_elem,
      ACU.toMultiset_unit, Multiset.mem_add, Multiset.mem_singleton, Multiset.notMem_zero,
      or_imp, forall_and, forall_eq, freeItem_cache, freeItem_dir, otherItem_cache,
      otherItem_dir, cacheIds_plus, cacheIds_cache,
      cacheIds_dir, cacheIds_unit, Multiset.nodup_add, Multiset.nodup_singleton,
      Multiset.disjoint_singleton]
    as post hpost
  refine over_of_subsumes hpost.1 (subsumes_of_cover fun a ha => ?_)
  rw [← post_eq] at ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  repeat' rcases ha with rfl | ha
  all_goals apply subsumes_one
  all_goals try route
  -- conditions (and the patches whose constructor values only their conditions fix,
  -- see the file header): to be filled
  all_goals sorry

-- routing a rule\'s patches takes more than the default budget
set_option maxHeartbeats 4000000 in
theorem recvGntS_inv : isOverPost [recvGntS] inv inv := by
  narrow [recvGntS] from inv
    using [ACU.plus_unit, ACU.unit_plus, ACU.toMultiset_plus, ACU.toMultiset_elem,
      ACU.toMultiset_unit, Multiset.mem_add, Multiset.mem_singleton, Multiset.notMem_zero,
      or_imp, forall_and, forall_eq, freeItem_cache, freeItem_dir, otherItem_cache,
      otherItem_dir, cacheIds_plus, cacheIds_cache,
      cacheIds_dir, cacheIds_unit, Multiset.nodup_add, Multiset.nodup_singleton,
      Multiset.disjoint_singleton]
    as post hpost
  refine over_of_subsumes hpost.1 (subsumes_of_cover fun a ha => ?_)
  rw [← post_eq] at ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  repeat' rcases ha with rfl | ha
  all_goals apply subsumes_one
  all_goals try route
  -- conditions (and the patches whose constructor values only their conditions fix,
  -- see the file header): to be filled
  all_goals sorry

-- routing a rule\'s patches takes more than the default budget
set_option maxHeartbeats 4000000 in
theorem recvGntE_inv : isOverPost [recvGntE] inv inv := by
  narrow [recvGntE] from inv
    using [ACU.plus_unit, ACU.unit_plus, ACU.toMultiset_plus, ACU.toMultiset_elem,
      ACU.toMultiset_unit, Multiset.mem_add, Multiset.mem_singleton, Multiset.notMem_zero,
      or_imp, forall_and, forall_eq, freeItem_cache, freeItem_dir, otherItem_cache,
      otherItem_dir, cacheIds_plus, cacheIds_cache,
      cacheIds_dir, cacheIds_unit, Multiset.nodup_add, Multiset.nodup_singleton,
      Multiset.disjoint_singleton]
    as post hpost
  refine over_of_subsumes hpost.1 (subsumes_of_cover fun a ha => ?_)
  rw [← post_eq] at ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  repeat' rcases ha with rfl | ha
  all_goals apply subsumes_one
  all_goals try route
  -- conditions (and the patches whose constructor values only their conditions fix,
  -- see the file header): to be filled
  all_goals sorry

/-- The whole protocol preserves the invariant. -/
theorem german_inv : isOverPost german inv inv :=
  isOverPost_choice sendReqS_inv
    (isOverPost_choice sendReqEI_inv
    (isOverPost_choice sendReqES_inv
    (isOverPost_choice recvReqS_inv
    (isOverPost_choice recvReqE_inv
    (isOverPost_choice sendInvE_inv
    (isOverPost_choice sendInvS_inv
    (isOverPost_choice sendInvAck_inv
    (isOverPost_choice recvInvAckS_inv
    (isOverPost_choice recvInvAckN_inv
    (isOverPost_choice sendGntSN_inv
    (isOverPost_choice sendGntSS_inv
    (isOverPost_choice sendGntE_inv
    (isOverPost_choice recvGntS_inv
    (recvGntE_inv))))))))))))))

/-! ## Coherence -/

/-- Initial states: the directory idle, no sharers; every cache invalid with empty
channels, ids distinct. -/
def initP : Patch Conf := .bind fun ((P, CF) : Oid × Items) =>
  ⟨⟨{Item.dir ⟨.idle, P, false, ∅, ∅⟩} + CF⟩,
    (∀ it ∈ CF.toMultiset, ∃ i, it = Item.cache ⟨i, .invalid, .noReq, .noGnt, .noAck⟩) ∧
      (cacheIds CF).Nodup⟩

theorem init_inv : subsumes [initP] inv := by
  sorry

/-- No state of the invariant is incoherent: each bad pattern's two caches cannot both
fit (unification of the patterns, the conditions refuting each unifier). -/
theorem inv_bad : ¬ overlaps inv bad := by
  sorry

/-- Coherence: from an initial state, never an exclusive cache next to an exclusive or a
shared one. -/
theorem german_coherent {x y : Conf} (hx : Pattern.holds [initP] x) (hxy : german.steps x y) :
    ¬ bad.holds y :=
  fun hy => inv_bad ⟨y, invariant init_inv german_inv hx hxy, hy⟩

end German
