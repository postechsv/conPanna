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

/-- A cache's own facts when no exclusive copy is out: an invalidation goes to a shared
cache with no acknowledgement pending, an acknowledgement comes from an invalid one. -/
def freeItem : Item → Prop
  | .dir _ => False
  | .cache c => c.state ≠ .exclusive ∧ c.ch2 ≠ .gntE ∧
      (c.ch2 = .inv → c.state = .shared ∧ c.ch3 = .noAck) ∧
      (c.ch3 = .invAck → c.state = .invalid ∧ c.ch2 = .noGnt)

/-- A cache's id, if it is a sharer: shared, or a grant, invalidation or acknowledgement
of it in flight. -/
def shrOf : Item → Multiset Oid
  | .cache c => if c.state = .shared ∨ c.ch2 = .gntS ∨ c.ch2 = .inv ∨ c.ch3 = .invAck
      then {c.id} else 0
  | .dir _ => 0

/-- A cache's id, if an invalidation or acknowledgement of it is in flight. -/
def invOf : Item → Multiset Oid
  | .cache c => if c.ch2 = .inv ∨ c.ch3 = .invAck then {c.id} else 0
  | .dir _ => 0

/-- The sharers and the caches being invalidated, as summaries of the configuration. -/
def shrIds (CF : Items) : Multiset Oid := CF.toMultiset.bind shrOf
def invIds (CF : Items) : Multiset Oid := CF.toMultiset.bind invOf

/-- An exclusive copy out to `I`: any other cache. -/
def otherItem (I : Oid) : Item → Prop
  | .dir _ => False
  | .cache c => c.id ≠ I ∧ c.state = .invalid ∧ c.ch2 = .noGnt ∧ c.ch3 = .noAck

/-- No exclusive copy out: the sharer set is exactly the sharers; the ones to invalidate
are sharers; invalidations happen only while serving an exclusive request, to caches
no longer in the invalidate set. -/
def freeP : Patch Conf := .bind fun ((K, P, SH, IV, CF) : Cmd × Oid × Oids × Oids × Items) =>
  ⟨⟨{Item.dir ⟨K, P, false, SH, IV⟩} + CF⟩,
    (∀ it ∈ CF.toMultiset, freeItem it) ∧ (cacheIds CF).Nodup ∧
      SH.toMultiset = shrIds CF ∧ IV.toMultiset ≤ SH.toMultiset ∧
      (∀ x ∈ invIds CF, x ∉ IV.toMultiset) ∧ (K = Cmd.cmdE ∨ invIds CF = 0)⟩

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

theorem freeItem_cache (c : Cache) :
    freeItem (.cache c) ↔ c.state ≠ .exclusive ∧ c.ch2 ≠ .gntE ∧
      (c.ch2 = .inv → c.state = .shared ∧ c.ch3 = .noAck) ∧
      (c.ch3 = .invAck → c.state = .invalid ∧ c.ch2 = .noGnt) := Iff.rfl
theorem freeItem_dir (d : Dir) : freeItem (.dir d) ↔ False := Iff.rfl
theorem otherItem_cache (I : Oid) (c : Cache) :
    otherItem I (.cache c) ↔
      c.id ≠ I ∧ c.state = .invalid ∧ c.ch2 = .noGnt ∧ c.ch3 = .noAck := Iff.rfl
theorem otherItem_dir (I : Oid) (d : Dir) : otherItem I (.dir d) ↔ False := Iff.rfl

theorem shrIds_plus (X Y : Items) : shrIds (X + Y) = shrIds X + shrIds Y := by simp [shrIds]
theorem shrIds_one (a : Item) : shrIds {a} = shrOf a := by simp [shrIds]
theorem shrIds_unit : shrIds ∅ = 0 := by simp [shrIds]
theorem invIds_plus (X Y : Items) : invIds (X + Y) = invIds X + invIds Y := by simp [invIds]
theorem invIds_one (a : Item) : invIds {a} = invOf a := by simp [invIds]
theorem invIds_unit : invIds ∅ = 0 := by simp [invIds]

theorem mem_cacheIds {X : Items} {c : Cache} (h : Item.cache c ∈ X.toMultiset) :
    c.id ∈ cacheIds X :=
  Multiset.mem_bind.2 ⟨_, h, Multiset.mem_singleton_self _⟩

/-- Sharers and caches being invalidated are caches: an id not among the caches is
among neither. -/
theorem shrIds_notMem {X : Items} {a : Oid} (h : a ∉ cacheIds X) : a ∉ shrIds X := by
  intro ha
  obtain ⟨it, hit, ha⟩ := Multiset.mem_bind.1 ha
  cases it with
  | dir _ => simp [shrOf] at ha
  | cache c =>
    simp only [shrOf] at ha
    split_ifs at ha
    · exact h ((Multiset.mem_singleton.1 ha) ▸ mem_cacheIds hit)
    · simp at ha

theorem invIds_notMem {X : Items} {a : Oid} (h : a ∉ cacheIds X) : a ∉ invIds X := by
  intro ha
  obtain ⟨it, hit, ha⟩ := Multiset.mem_bind.1 ha
  cases it with
  | dir _ => simp [invOf] at ha
  | cache c =>
    simp only [invOf] at ha
    split_ifs at ha
    · exact h ((Multiset.mem_singleton.1 ha) ▸ mem_cacheIds hit)
    · simp at ha

/-! Transfers between owned and free: the rest is idle exactly when nobody shares. -/

/-- Idle other caches share nothing and invalidate nothing. -/
theorem others_free {I : Oid} {X : Items} (h : ∀ it ∈ X.toMultiset, otherItem I it) :
    (∀ it ∈ X.toMultiset, freeItem it) ∧ shrIds X = 0 ∧ invIds X = 0 := by
  refine ⟨fun it hit => ?_, ?_, ?_⟩
  · cases it with
    | dir _ => exact (h _ hit).elim
    | cache c =>
      obtain ⟨-, h1, h2, h3⟩ := h _ hit
      simp [freeItem, h1, h2, h3]
  · refine Multiset.eq_zero_of_forall_notMem fun x hx => ?_
    obtain ⟨it, hit, hx⟩ := Multiset.mem_bind.1 hx
    cases it with
    | dir _ => exact (h _ hit).elim
    | cache c =>
      obtain ⟨-, h1, h2, h3⟩ := h _ hit
      simp [shrOf, h1, h2, h3] at hx
  · refine Multiset.eq_zero_of_forall_notMem fun x hx => ?_
    obtain ⟨it, hit, hx⟩ := Multiset.mem_bind.1 hx
    cases it with
    | dir _ => exact (h _ hit).elim
    | cache c =>
      obtain ⟨-, -, h2, h3⟩ := h _ hit
      simp [invOf, h2, h3] at hx

/-- The owned → free transfer, rewrite-friendly: idle other caches. -/
theorem others_shrIds {I : Oid} {X : Items} (h : ∀ it ∈ X.toMultiset, otherItem I it) :
    shrIds X = 0 := (others_free h).2.1
theorem others_invIds {I : Oid} {X : Items} (h : ∀ it ∈ X.toMultiset, otherItem I it) :
    invIds X = 0 := (others_free h).2.2
theorem others_freeAll {I : Oid} {X : Items} (h : ∀ it ∈ X.toMultiset, otherItem I it) :
    ∀ it ∈ X.toMultiset, freeItem it := (others_free h).1
theorem others_notMem {I : Oid} {X : Items} (h : ∀ it ∈ X.toMultiset, otherItem I it) :
    I ∉ cacheIds X := fun hI => by
  obtain ⟨it, hit, hI⟩ := Multiset.mem_bind.1 hI
  cases it with
  | dir _ => exact (h _ hit).elim
  | cache c => exact (h _ hit).1 (Multiset.mem_singleton.1 hI).symm

/-! Multiset bookkeeping on the sharer and invalidate sets. -/

theorem cons_eq_add_singleton {a : Oid} {s t : Multiset Oid} : a ::ₘ s = t + {a} ↔ s = t := by
  rw [add_comm, Multiset.singleton_add, Multiset.cons_inj_right]

theorem cons_eq_singleton {a : Oid} {s : Multiset Oid} : a ::ₘ s = {a} ↔ s = 0 := by
  rw [← Multiset.cons_zero, Multiset.cons_inj_right]

theorem le_of_le_add_singleton {a : Oid} {s t : Multiset Oid} (h : s ≤ t + {a}) (ha : a ∉ s) :
    s ≤ t := by
  rw [add_comm, Multiset.singleton_add] at h
  exact (Multiset.le_cons_of_notMem ha).1 h

theorem cons_ne_shrIds {a : Oid} {s : Multiset Oid} {X : Items} (h : a ∉ cacheIds X) :
    a ::ₘ s ≠ shrIds X := fun e => shrIds_notMem h (e ▸ Multiset.mem_cons_self a s)

/-- With no sharers, free caches are idle, so other caches for an owner not among them. -/
theorem free_others {I : Oid} {X : Items} (h : ∀ it ∈ X.toMultiset, freeItem it)
    (hs : shrIds X = 0) (hI : I ∉ cacheIds X) : ∀ it ∈ X.toMultiset, otherItem I it := by
  intro it hit
  cases it with
  | dir _ => exact (h _ hit).elim
  | cache c =>
    obtain ⟨h1, h2, -, -⟩ := h _ hit
    have hsh : shrOf (.cache c) = 0 := Multiset.eq_zero_of_forall_notMem fun y hy => by
      have : y ∈ shrIds X := Multiset.mem_bind.2 ⟨_, hit, hy⟩
      simp [hs] at this
    simp only [shrOf, ite_eq_right_iff, Multiset.singleton_ne_zero, imp_false, not_or] at hsh
    obtain ⟨hs1, hs2, hs3, hs4⟩ := hsh
    refine ⟨fun e => hI (e ▸ mem_cacheIds hit), ?_, ?_, ?_⟩
    · cases hc : c.state <;> simp_all
    · cases hc : c.ch2 <;> simp_all
    · cases hc : c.ch3 <;> simp_all

/-! ## Each rule preserves the invariant
One narrowing per rule (small, bounded declarations), combined by `isOverPost_choice`.
Each post patch is routed to the invariant patch of its directory situation. -/

set_option hygiene false in
/-- Close a routed post patch's condition `hc ⊢ …`: unfold the conditions over sums, then
simplification, case splits on the summaries' `if`s, propositional reasoning. -/
macro "cond_close" : tactic => `(tactic| (
  try simp only [ACU.toMultiset_plus, ACU.toMultiset_elem,
    ACU.toMultiset_unit, Multiset.mem_add, Multiset.mem_singleton, Multiset.notMem_zero,
    or_imp, forall_and, forall_eq, freeItem_cache, freeItem_dir, otherItem_cache,
    otherItem_dir, cacheIds_plus, cacheIds_cache, cacheIds_dir, cacheIds_unit,
    shrIds_plus, shrIds_one, shrIds_unit, invIds_plus, invIds_one, invIds_unit, shrOf, invOf,
    Multiset.nodup_add, Multiset.nodup_singleton, Multiset.disjoint_singleton,
    Multiset.le_singleton, reduceCtorEq, false_or, or_false, ne_eq, not_false_eq_true,
    true_and, and_true, imp_self, implies_true, true_implies, false_implies] at hc ⊢
  first
  | (simp_all; done)
  | (split_ifs at hc ⊢ <;> simp_all <;> done)
  | (tauto; done)
  | (aesop; done)))

set_option hygiene false in
/-- The bookkeeping fallback: destructure the patch variables, split the conjunctions and
the enumerated fields, then simplify with the multiset facts of the sharer sets. -/
macro "cond_close2" : tactic => `(tactic| (
  clear post_eq hpost
  revert hc; revert x; simp only [Prod.forall]; intros
  simp only [ACU.toMultiset_plus, ACU.toMultiset_elem,
    ACU.toMultiset_unit, Multiset.mem_add, Multiset.mem_singleton, Multiset.notMem_zero,
    or_imp, forall_and, forall_eq, freeItem_cache, freeItem_dir, otherItem_cache,
    otherItem_dir, cacheIds_plus, cacheIds_cache, cacheIds_dir, cacheIds_unit,
    shrIds_plus, shrIds_one, shrIds_unit, invIds_plus, invIds_one, invIds_unit, shrOf, invOf,
    Multiset.nodup_add, Multiset.nodup_singleton, Multiset.disjoint_singleton,
    Multiset.le_singleton] at *
  casesm* _ ∧ _
  cases_type* CacheState Gnt Ack Cmd <;>
    simp_all [shrIds_notMem, invIds_notMem, Multiset.singleton_add, Multiset.cons_add,
      Multiset.add_cons, Multiset.mem_cons, le_add_right, le_add_left, Multiset.cons_inj_right,
      add_comm, Multiset.singleton_eq_cons_iff] <;> done))

set_option hygiene false in
/-- The decomposition of a routed condition `hc ⊢ …` over sums (as by `cond_close`), for
the explicit proofs below. -/
macro "cond_decomp" : tactic => `(tactic| (
  simp only [ACU.toMultiset_plus, ACU.toMultiset_elem,
    ACU.toMultiset_unit, Multiset.mem_add, Multiset.mem_singleton, Multiset.notMem_zero,
    or_imp, forall_and, forall_eq, freeItem_cache, freeItem_dir, otherItem_cache,
    otherItem_dir, cacheIds_plus, cacheIds_cache, cacheIds_dir, cacheIds_unit,
    shrIds_plus, shrIds_one, shrIds_unit, invIds_plus, invIds_one, invIds_unit, shrOf, invOf,
    Multiset.nodup_add, Multiset.nodup_singleton, Multiset.disjoint_singleton,
    Multiset.le_singleton, reduceCtorEq, false_or, or_false, ne_eq, not_false_eq_true,
    true_and, and_true, imp_self, implies_true, true_implies, false_implies] at hc ⊢))

/-- Route a post patch to the invariant patch its state matches. -/
macro "route" : tactic => `(tactic| first
  | maude_match freeP | maude_match ownE | maude_match ownG | maude_match ownInv
  | maude_match ownAck)

-- routing a rule's patches takes more than the default budget
set_option maxHeartbeats 4000000 in
theorem sendReqS_inv : isOverPost [sendReqS] inv inv := by
  narrow [sendReqS] from inv
    using [ACU.plus_unit, ACU.unit_plus, ACU.toMultiset_plus, ACU.toMultiset_elem,
      ACU.toMultiset_unit, Multiset.mem_add, Multiset.mem_singleton, Multiset.notMem_zero,
      or_imp, forall_and, forall_eq, freeItem_cache, freeItem_dir, otherItem_cache,
      otherItem_dir, cacheIds_plus, cacheIds_cache, cacheIds_dir, cacheIds_unit,
      shrIds_plus, shrIds_one, shrIds_unit, invIds_plus, invIds_one, invIds_unit, shrOf, invOf,
      Multiset.nodup_add, Multiset.nodup_singleton, Multiset.disjoint_singleton]
    as post hpost
  refine over_of_subsumes hpost.1 (subsumes_of_cover fun a ha => ?_)
  rw [← post_eq] at ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  repeat' rcases ha with rfl | ha
  all_goals apply subsumes_one
  all_goals try route
  all_goals try cond_close
  all_goals try cond_close2

-- routing a rule's patches takes more than the default budget
set_option maxHeartbeats 4000000 in
theorem sendReqEI_inv : isOverPost [sendReqEI] inv inv := by
  narrow [sendReqEI] from inv
    using [ACU.plus_unit, ACU.unit_plus, ACU.toMultiset_plus, ACU.toMultiset_elem,
      ACU.toMultiset_unit, Multiset.mem_add, Multiset.mem_singleton, Multiset.notMem_zero,
      or_imp, forall_and, forall_eq, freeItem_cache, freeItem_dir, otherItem_cache,
      otherItem_dir, cacheIds_plus, cacheIds_cache, cacheIds_dir, cacheIds_unit,
      shrIds_plus, shrIds_one, shrIds_unit, invIds_plus, invIds_one, invIds_unit, shrOf, invOf,
      Multiset.nodup_add, Multiset.nodup_singleton, Multiset.disjoint_singleton]
    as post hpost
  refine over_of_subsumes hpost.1 (subsumes_of_cover fun a ha => ?_)
  rw [← post_eq] at ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  repeat' rcases ha with rfl | ha
  all_goals apply subsumes_one
  all_goals try route
  all_goals try cond_close
  all_goals try cond_close2

-- routing a rule's patches takes more than the default budget
set_option maxHeartbeats 4000000 in
theorem sendReqES_inv : isOverPost [sendReqES] inv inv := by
  narrow [sendReqES] from inv
    using [ACU.plus_unit, ACU.unit_plus, ACU.toMultiset_plus, ACU.toMultiset_elem,
      ACU.toMultiset_unit, Multiset.mem_add, Multiset.mem_singleton, Multiset.notMem_zero,
      or_imp, forall_and, forall_eq, freeItem_cache, freeItem_dir, otherItem_cache,
      otherItem_dir, cacheIds_plus, cacheIds_cache, cacheIds_dir, cacheIds_unit,
      shrIds_plus, shrIds_one, shrIds_unit, invIds_plus, invIds_one, invIds_unit, shrOf, invOf,
      Multiset.nodup_add, Multiset.nodup_singleton, Multiset.disjoint_singleton]
    as post hpost
  refine over_of_subsumes hpost.1 (subsumes_of_cover fun a ha => ?_)
  rw [← post_eq] at ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  repeat' rcases ha with rfl | ha
  all_goals apply subsumes_one
  all_goals try route
  all_goals try cond_close
  all_goals try cond_close2

-- routing a rule's patches takes more than the default budget
set_option maxHeartbeats 4000000 in
theorem recvReqS_inv : isOverPost [recvReqS] inv inv := by
  narrow [recvReqS] from inv
    using [ACU.plus_unit, ACU.unit_plus, ACU.toMultiset_plus, ACU.toMultiset_elem,
      ACU.toMultiset_unit, Multiset.mem_add, Multiset.mem_singleton, Multiset.notMem_zero,
      or_imp, forall_and, forall_eq, freeItem_cache, freeItem_dir, otherItem_cache,
      otherItem_dir, cacheIds_plus, cacheIds_cache, cacheIds_dir, cacheIds_unit,
      shrIds_plus, shrIds_one, shrIds_unit, invIds_plus, invIds_one, invIds_unit, shrOf, invOf,
      Multiset.nodup_add, Multiset.nodup_singleton, Multiset.disjoint_singleton]
    as post hpost
  refine over_of_subsumes hpost.1 (subsumes_of_cover fun a ha => ?_)
  rw [← post_eq] at ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  repeat' rcases ha with rfl | ha
  all_goals apply subsumes_one
  all_goals try route
  all_goals try cond_close
  all_goals try cond_close2

-- routing a rule's patches takes more than the default budget
set_option maxHeartbeats 4000000 in
theorem recvReqE_inv : isOverPost [recvReqE] inv inv := by
  narrow [recvReqE] from inv
    using [ACU.plus_unit, ACU.unit_plus, ACU.toMultiset_plus, ACU.toMultiset_elem,
      ACU.toMultiset_unit, Multiset.mem_add, Multiset.mem_singleton, Multiset.notMem_zero,
      or_imp, forall_and, forall_eq, freeItem_cache, freeItem_dir, otherItem_cache,
      otherItem_dir, cacheIds_plus, cacheIds_cache, cacheIds_dir, cacheIds_unit,
      shrIds_plus, shrIds_one, shrIds_unit, invIds_plus, invIds_one, invIds_unit, shrOf, invOf,
      Multiset.nodup_add, Multiset.nodup_singleton, Multiset.disjoint_singleton]
    as post hpost
  refine over_of_subsumes hpost.1 (subsumes_of_cover fun a ha => ?_)
  rw [← post_eq] at ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  repeat' rcases ha with rfl | ha
  all_goals apply subsumes_one
  all_goals try route
  all_goals try cond_close
  all_goals try cond_close2

-- routing a rule's patches takes more than the default budget
set_option maxHeartbeats 4000000 in
theorem sendInvE_inv : isOverPost [sendInvE] inv inv := by
  narrow [sendInvE] from inv
    using [ACU.plus_unit, ACU.unit_plus, ACU.toMultiset_plus, ACU.toMultiset_elem,
      ACU.toMultiset_unit, Multiset.mem_add, Multiset.mem_singleton, Multiset.notMem_zero,
      or_imp, forall_and, forall_eq, freeItem_cache, freeItem_dir, otherItem_cache,
      otherItem_dir, cacheIds_plus, cacheIds_cache, cacheIds_dir, cacheIds_unit,
      shrIds_plus, shrIds_one, shrIds_unit, invIds_plus, invIds_one, invIds_unit, shrOf, invOf,
      Multiset.nodup_add, Multiset.nodup_singleton, Multiset.disjoint_singleton]
    as post hpost
  refine over_of_subsumes hpost.1 (subsumes_of_cover fun a ha => ?_)
  rw [← post_eq] at ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  repeat' rcases ha with rfl | ha
  all_goals apply subsumes_one
  all_goals try route
  all_goals try cond_close
  all_goals try cond_close2
  -- open: the protocol's remaining facts (multiset bookkeeping on the sharer and
  -- invalidate sets), and the patches whose constructor values only their conditions fix
  -- no copy out: the cache invalidated is a sharer (it is in `IV ⊆ SH`), not one with an
  -- acknowledgement pending (that one is out of `IV`), so it is shared; it leaves `IV`
  · cond_decomp
    obtain ⟨⟨hE, hia⟩, hSH, hle, hA1, hA2⟩ := hc
    have hA : x.2.2.2.1 = .noAck := by
      cases h : x.2.2.2.1
      · rfl
      · simp [h] at hA1
    have hS : x.2.1 = .shared := by
      cases h : x.2.1
      · simp [h, hA] at hSH; rw [hSH] at hle; simp at hle
      · rfl
      · exact absurd h hE
    simp only [hS, true_or, if_true] at hSH
    rw [hSH] at hle ⊢
    have h0 : ACU.toMultiset x.2.2.2.2.1 = 0 := by
      rw [← Multiset.cons_zero, Multiset.cons_le_cons_iff] at hle; exact Multiset.le_zero.1 hle
    simp [hS, hA, h0]
  · cond_decomp
    obtain ⟨⟨hrest, hE, hia⟩, ⟨hnd, hI⟩, hSH, hle, ⟨-, hA1⟩, hinv, hA2⟩ := hc
    have hA : x.2.2.2.2.1 = .noAck := by
      cases h : x.2.2.2.2.1
      · rfl
      · simp [h] at hA1
    have hS : x.2.2.1 = .shared := by
      cases h : x.2.2.1
      · simp only [h, hA, reduceCtorEq, or_self, if_false, add_zero] at hSH
        rw [hSH] at hle
        exact absurd (Multiset.mem_of_le hle (Multiset.mem_cons_self _ _)) (shrIds_notMem hI)
      · rfl
      · exact absurd h hE
    simp only [hS, true_or, if_true] at hSH
    rw [hSH] at hle ⊢
    have hIn : x.2.1 ∉ ACU.toMultiset x.2.2.2.2.2.1 := fun hm => by
      have hc := Multiset.count_le_of_le x.2.1 hle
      rw [Multiset.count_cons_self, Multiset.count_add, Multiset.count_singleton_self,
        Multiset.count_eq_zero.2 (shrIds_notMem hI)] at hc
      have := Multiset.count_pos.2 hm
      omega
    refine ⟨⟨hrest, hE, ⟨hS, hA⟩, fun h => by simp [hA] at h, fun h => by simp [hA] at h⟩,
      ⟨hnd, hI⟩, by simp, le_trans (Multiset.le_cons_self _ _) hle, ⟨hinv, by simp [hIn]⟩,
      .inl trivial⟩
  -- an exclusive copy out: as for `sendInvS`
  all_goals first
    | (cond_decomp; casesm* _ ∧ _
       exact absurd (Multiset.mem_singleton.1 (‹_ ::ₘ _ = {_}› ▸ Multiset.mem_cons_self _ _))
         ‹¬_ = _›)
    | (refine ⟨ownInv, by simp [inv], ?_⟩
       unfold sendInvE_inv.post_10 ownInv
       refine Subsumption.subsumes_of_match
         (fun x => (Cmd.cmdE, x.2.2.2, x.2.1, x.2.2.1, (∅ : Items))) fun x hc => ?_
       have h0 : x.1 = ∅ := ACU.eq_iff.2 (by simpa using cons_eq_singleton.1 hc)
       exact ⟨by simp [h0, ACU.plus_unit], by simp [cacheIds_unit]⟩)
    | (refine ⟨ownInv, by simp [inv], ?_⟩
       unfold sendInvE_inv.post_12 ownInv
       refine Subsumption.subsumes_of_match
         (fun x => (Cmd.cmdE, x.2.2.2.2, x.2.2.1, x.2.2.2.1, x.2.1)) fun x hc => ?_
       obtain ⟨hoth, hnd, hcons⟩ := hc
       have h0 : x.1 = ∅ := ACU.eq_iff.2 (by simpa using cons_eq_singleton.1 hcons)
       exact ⟨by simp [h0], by simp, hoth, hnd⟩)

-- routing a rule's patches takes more than the default budget
set_option maxHeartbeats 4000000 in
theorem sendInvS_inv : isOverPost [sendInvS] inv inv := by
  narrow [sendInvS] from inv
    using [ACU.plus_unit, ACU.unit_plus, ACU.toMultiset_plus, ACU.toMultiset_elem,
      ACU.toMultiset_unit, Multiset.mem_add, Multiset.mem_singleton, Multiset.notMem_zero,
      or_imp, forall_and, forall_eq, freeItem_cache, freeItem_dir, otherItem_cache,
      otherItem_dir, cacheIds_plus, cacheIds_cache, cacheIds_dir, cacheIds_unit,
      shrIds_plus, shrIds_one, shrIds_unit, invIds_plus, invIds_one, invIds_unit, shrOf, invOf,
      Multiset.nodup_add, Multiset.nodup_singleton, Multiset.disjoint_singleton]
    as post hpost
  refine over_of_subsumes hpost.1 (subsumes_of_cover fun a ha => ?_)
  rw [← post_eq] at ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  repeat' rcases ha with rfl | ha
  all_goals apply subsumes_one
  all_goals try route
  all_goals try cond_close
  all_goals try cond_close2
  -- open: the protocol's remaining facts (multiset bookkeeping on the sharer and
  -- invalidate sets), and the patches whose constructor values only their conditions fix
  -- invalidating while an exclusive copy is out: the invalidate set holds at most the
  -- owner, so the cache invalidated is the owner (the patches where it is another cache
  -- are contradictory), and its invalidate set becomes empty
  all_goals first
    | (cond_decomp; casesm* _ ∧ _
       exact absurd (Multiset.mem_singleton.1 (‹_ ::ₘ _ = {_}› ▸ Multiset.mem_cons_self _ _))
         ‹¬_ = _›)
    | (refine ⟨ownInv, by simp [inv], ?_⟩
       unfold sendInvS_inv.post_6 ownInv
       refine Subsumption.subsumes_of_match
         (fun x => (Cmd.cmdS, x.2.2.2, x.2.1, x.2.2.1, (∅ : Items))) fun x hc => ?_
       have h0 : x.1 = ∅ := ACU.eq_iff.2 (by simpa using cons_eq_singleton.1 hc)
       exact ⟨by simp [h0, ACU.plus_unit], by simp [cacheIds_unit]⟩)
    | (refine ⟨ownInv, by simp [inv], ?_⟩
       unfold sendInvS_inv.post_8 ownInv
       refine Subsumption.subsumes_of_match
         (fun x => (Cmd.cmdS, x.2.2.2.2, x.2.2.1, x.2.2.2.1, x.2.1)) fun x hc => ?_
       obtain ⟨hoth, hnd, hcons⟩ := hc
       have h0 : x.1 = ∅ := ACU.eq_iff.2 (by simpa using cons_eq_singleton.1 hcons)
       exact ⟨by simp [h0], by simp, hoth, hnd⟩)

-- routing a rule's patches takes more than the default budget
set_option maxHeartbeats 4000000 in
theorem sendInvAck_inv : isOverPost [sendInvAck] inv inv := by
  narrow [sendInvAck] from inv
    using [ACU.plus_unit, ACU.unit_plus, ACU.toMultiset_plus, ACU.toMultiset_elem,
      ACU.toMultiset_unit, Multiset.mem_add, Multiset.mem_singleton, Multiset.notMem_zero,
      or_imp, forall_and, forall_eq, freeItem_cache, freeItem_dir, otherItem_cache,
      otherItem_dir, cacheIds_plus, cacheIds_cache, cacheIds_dir, cacheIds_unit,
      shrIds_plus, shrIds_one, shrIds_unit, invIds_plus, invIds_one, invIds_unit, shrOf, invOf,
      Multiset.nodup_add, Multiset.nodup_singleton, Multiset.disjoint_singleton]
    as post hpost
  refine over_of_subsumes hpost.1 (subsumes_of_cover fun a ha => ?_)
  rw [← post_eq] at ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  repeat' rcases ha with rfl | ha
  all_goals apply subsumes_one
  all_goals try route
  all_goals try cond_close
  all_goals try cond_close2

-- routing a rule's patches takes more than the default budget
set_option maxHeartbeats 4000000 in
theorem recvInvAckS_inv : isOverPost [recvInvAckS] inv inv := by
  narrow [recvInvAckS] from inv
    using [ACU.plus_unit, ACU.unit_plus, ACU.toMultiset_plus, ACU.toMultiset_elem,
      ACU.toMultiset_unit, Multiset.mem_add, Multiset.mem_singleton, Multiset.notMem_zero,
      or_imp, forall_and, forall_eq, freeItem_cache, freeItem_dir, otherItem_cache,
      otherItem_dir, cacheIds_plus, cacheIds_cache, cacheIds_dir, cacheIds_unit,
      shrIds_plus, shrIds_one, shrIds_unit, invIds_plus, invIds_one, invIds_unit, shrOf, invOf,
      Multiset.nodup_add, Multiset.nodup_singleton, Multiset.disjoint_singleton]
    as post hpost
  refine over_of_subsumes hpost.1 (subsumes_of_cover fun a ha => ?_)
  rw [← post_eq] at ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  repeat' rcases ha with rfl | ha
  all_goals apply subsumes_one
  all_goals try route
  all_goals try cond_close
  all_goals try cond_close2
  -- open: the protocol's remaining facts (multiset bookkeeping on the sharer and
  -- invalidate sets), and the patches whose constructor values only their conditions fix
  -- the acknowledging cache leaves the sharers (and was not to be invalidated again)
  · cond_decomp
    obtain ⟨⟨⟨hE, hG, hInv, hS, hGn⟩, hSH, hIV, hIIV, hK⟩, -⟩ := hc
    have h0 := cons_eq_singleton.1 hSH
    refine ⟨⟨hE, hG, fun h => absurd h hInv⟩, by simp [h0, hS, hGn], ?_, by simp [hGn], .inl hK⟩
    rw [h0] at hIV ⊢
    exact (Multiset.le_cons_of_notMem hIIV).1 hIV
  · cond_decomp
    obtain ⟨⟨⟨hrest, hE, hG, hInv, hS, hGn⟩, ⟨hnd, hI⟩, hSH, hIV, ⟨hinv1, hIIV⟩, hK⟩, -⟩ := hc
    have hM := cons_eq_add_singleton.1 hSH
    refine ⟨⟨hrest, hE, hG, fun h => absurd h hInv⟩, ⟨hnd, hI⟩, by simp [hM, hS, hGn], ?_,
      ⟨hinv1, by simp [hGn]⟩, .inl hK⟩
    rw [hM] at hIV ⊢
    exact (Multiset.le_cons_of_notMem hIIV).1 hIV
  -- the owner's acknowledgement: no copy out any more, and the rest is idle
  · cond_decomp
    obtain ⟨⟨-, hoth, hnd⟩, -⟩ := hc
    obtain ⟨hf, hs, hi⟩ := others_free hoth
    exact ⟨hf, ⟨hnd, others_notMem hoth⟩, by simp [hs], le_refl _, .inr (by simp [hi])⟩

-- routing a rule's patches takes more than the default budget
set_option maxHeartbeats 4000000 in
theorem recvInvAckN_inv : isOverPost [recvInvAckN] inv inv := by
  narrow [recvInvAckN] from inv
    using [ACU.plus_unit, ACU.unit_plus, ACU.toMultiset_plus, ACU.toMultiset_elem,
      ACU.toMultiset_unit, Multiset.mem_add, Multiset.mem_singleton, Multiset.notMem_zero,
      or_imp, forall_and, forall_eq, freeItem_cache, freeItem_dir, otherItem_cache,
      otherItem_dir, cacheIds_plus, cacheIds_cache, cacheIds_dir, cacheIds_unit,
      shrIds_plus, shrIds_one, shrIds_unit, invIds_plus, invIds_one, invIds_unit, shrOf, invOf,
      Multiset.nodup_add, Multiset.nodup_singleton, Multiset.disjoint_singleton]
    as post hpost
  refine over_of_subsumes hpost.1 (subsumes_of_cover fun a ha => ?_)
  rw [← post_eq] at ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  repeat' rcases ha with rfl | ha
  all_goals apply subsumes_one
  all_goals try route
  all_goals try cond_close
  all_goals try cond_close2

-- routing a rule's patches takes more than the default budget
set_option maxHeartbeats 4000000 in
theorem sendGntSN_inv : isOverPost [sendGntSN] inv inv := by
  narrow [sendGntSN] from inv
    using [ACU.plus_unit, ACU.unit_plus, ACU.toMultiset_plus, ACU.toMultiset_elem,
      ACU.toMultiset_unit, Multiset.mem_add, Multiset.mem_singleton, Multiset.notMem_zero,
      or_imp, forall_and, forall_eq, freeItem_cache, freeItem_dir, otherItem_cache,
      otherItem_dir, cacheIds_plus, cacheIds_cache, cacheIds_dir, cacheIds_unit,
      shrIds_plus, shrIds_one, shrIds_unit, invIds_plus, invIds_one, invIds_unit, shrOf, invOf,
      Multiset.nodup_add, Multiset.nodup_singleton, Multiset.disjoint_singleton]
    as post hpost
  refine over_of_subsumes hpost.1 (subsumes_of_cover fun a ha => ?_)
  rw [← post_eq] at ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  repeat' rcases ha with rfl | ha
  all_goals apply subsumes_one
  all_goals try route
  all_goals try cond_close
  all_goals try cond_close2

-- routing a rule's patches takes more than the default budget
set_option maxHeartbeats 4000000 in
theorem sendGntSS_inv : isOverPost [sendGntSS] inv inv := by
  narrow [sendGntSS] from inv
    using [ACU.plus_unit, ACU.unit_plus, ACU.toMultiset_plus, ACU.toMultiset_elem,
      ACU.toMultiset_unit, Multiset.mem_add, Multiset.mem_singleton, Multiset.notMem_zero,
      or_imp, forall_and, forall_eq, freeItem_cache, freeItem_dir, otherItem_cache,
      otherItem_dir, cacheIds_plus, cacheIds_cache, cacheIds_dir, cacheIds_unit,
      shrIds_plus, shrIds_one, shrIds_unit, invIds_plus, invIds_one, invIds_unit, shrOf, invOf,
      Multiset.nodup_add, Multiset.nodup_singleton, Multiset.disjoint_singleton]
    as post hpost
  refine over_of_subsumes hpost.1 (subsumes_of_cover fun a ha => ?_)
  rw [← post_eq] at ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  repeat' rcases ha with rfl | ha
  all_goals apply subsumes_one
  all_goals try route
  all_goals try cond_close
  all_goals try cond_close2
  -- open: the protocol's remaining facts (multiset bookkeeping on the sharer and
  -- invalidate sets), and the patches whose constructor values only their conditions fix
  -- the requester was already a sharer: it is shared (else its id would be among the
  -- rest's sharers, which are caches with other ids), and the sharer set is unchanged
  · cond_decomp
    obtain ⟨⟨hrest, hE, hia⟩, ⟨hnd, hI⟩, hSH, hIV, ⟨hinv1, hinv2⟩, hinv0, hna⟩ := hc
    have h0 : shrIds x.1 = 0 := by
      by_cases hs : x.2.1 = CacheState.shared
      · simpa [hs] using hSH
      · simp only [hs, hna, or_self, if_false, add_zero] at hSH
        exact absurd (hSH ▸ Multiset.mem_singleton_self _) (shrIds_notMem hI)
    exact ⟨⟨hrest, hE, hia, fun h => hna h⟩, ⟨hnd, hI⟩, by simp [h0], hIV, ⟨hinv1, hinv2⟩,
      by simp [hinv0, hna]⟩
  · cond_decomp
    obtain ⟨⟨hrest, hE, hia⟩, ⟨hnd, hI⟩, hSH, hIV, ⟨hinv1, hinv2⟩, hinv0, hna⟩ := hc
    have hM : ACU.toMultiset x.2.2.2.2.1 = shrIds x.1 := by
      by_cases hs : x.2.1 = CacheState.shared
      · simp only [hs, true_or, if_true] at hSH
        exact cons_eq_add_singleton.1 hSH
      · simp only [hs, hna, or_self, if_false, add_zero] at hSH
        exact absurd hSH (cons_ne_shrIds hI)
    refine ⟨⟨hrest, hE, hia, fun h => hna h⟩, ⟨hnd, hI⟩, ?_, by rwa [Multiset.singleton_add],
      ⟨hinv1, hinv2⟩, by simp [hinv0, hna]⟩
    simp [hM, add_comm]

-- routing a rule's patches takes more than the default budget
set_option maxHeartbeats 4000000 in
theorem sendGntE_inv : isOverPost [sendGntE] inv inv := by
  narrow [sendGntE] from inv
    using [ACU.plus_unit, ACU.unit_plus, ACU.toMultiset_plus, ACU.toMultiset_elem,
      ACU.toMultiset_unit, Multiset.mem_add, Multiset.mem_singleton, Multiset.notMem_zero,
      or_imp, forall_and, forall_eq, freeItem_cache, freeItem_dir, otherItem_cache,
      otherItem_dir, cacheIds_plus, cacheIds_cache, cacheIds_dir, cacheIds_unit,
      shrIds_plus, shrIds_one, shrIds_unit, invIds_plus, invIds_one, invIds_unit, shrOf, invOf,
      Multiset.nodup_add, Multiset.nodup_singleton, Multiset.disjoint_singleton]
    as post hpost
  refine over_of_subsumes hpost.1 (subsumes_of_cover fun a ha => ?_)
  rw [← post_eq] at ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  repeat' rcases ha with rfl | ha
  all_goals apply subsumes_one
  all_goals try route
  all_goals try cond_close
  all_goals try cond_close2
  -- open: the protocol's remaining facts (multiset bookkeeping on the sharer and
  -- invalidate sets), and the patches whose constructor values only their conditions fix
  -- the exclusive grant: the requester holds nothing (not exclusive, not a sharer: it is
  -- invalid, with no acknowledgement pending), and nobody else shares, so the rest is idle;
  -- matching cannot see the fields these conditions fix, so the substitution is explicit
  · refine ⟨ownG, by simp [inv], ?_⟩
    unfold sendGntE_inv.post_1 ownG
    refine Subsumption.subsumes_of_match
      (fun x => (Cmd.idle, x.2.2.2.1, x.2.2.2.2, x.2.2.2.1, x.2.1, (∅ : Items))) fun x hc => ?_
    obtain ⟨⟨hE, -⟩, ⟨hS, hA⟩, hIV, -⟩ := hc
    have hS' : x.1 = .invalid := by cases h : x.1 <;> simp_all
    have hA' : x.2.2.1 = .noAck := by cases h : x.2.2.1 <;> simp_all
    refine ⟨by simp [hS', hA', ACU.plus_unit], ?_⟩
    simp [cacheIds_unit, hIV]
  · refine ⟨ownG, by simp [inv], ?_⟩
    unfold sendGntE_inv.post_2 ownG
    refine Subsumption.subsumes_of_match
      (fun x => (Cmd.idle, x.2.2.2.2.1, x.2.2.2.2.2, x.2.2.2.2.1, x.2.2.1, x.1)) fun x hc => ?_
    obtain ⟨⟨hrest, hE, -⟩, ⟨hnd, hI⟩, hSH, hIV, -, -⟩ := hc
    have h0 : shrIds x.1 = 0 ∧ ¬(x.2.1 = .shared ∨ x.2.2.2.1 = .invAck) := by
      split_ifs at hSH with hc'
      · exact absurd hSH.symm (by simp [add_eq_zero])
      · exact ⟨by simpa using hSH.symm, hc'⟩
    have hS' : x.2.1 = .invalid := by cases h : x.2.1 <;> simp_all
    have hA' : x.2.2.2.1 = .noAck := by cases h : x.2.2.2.1 <;> simp_all
    exact ⟨by simp [hS', hA'], free_others hrest h0.1 hI, hnd, by simp [hIV]⟩

-- routing a rule's patches takes more than the default budget
set_option maxHeartbeats 4000000 in
theorem recvGntS_inv : isOverPost [recvGntS] inv inv := by
  narrow [recvGntS] from inv
    using [ACU.plus_unit, ACU.unit_plus, ACU.toMultiset_plus, ACU.toMultiset_elem,
      ACU.toMultiset_unit, Multiset.mem_add, Multiset.mem_singleton, Multiset.notMem_zero,
      or_imp, forall_and, forall_eq, freeItem_cache, freeItem_dir, otherItem_cache,
      otherItem_dir, cacheIds_plus, cacheIds_cache, cacheIds_dir, cacheIds_unit,
      shrIds_plus, shrIds_one, shrIds_unit, invIds_plus, invIds_one, invIds_unit, shrOf, invOf,
      Multiset.nodup_add, Multiset.nodup_singleton, Multiset.disjoint_singleton]
    as post hpost
  refine over_of_subsumes hpost.1 (subsumes_of_cover fun a ha => ?_)
  rw [← post_eq] at ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  repeat' rcases ha with rfl | ha
  all_goals apply subsumes_one
  all_goals try route
  all_goals try cond_close
  all_goals try cond_close2

-- routing a rule's patches takes more than the default budget
set_option maxHeartbeats 4000000 in
theorem recvGntE_inv : isOverPost [recvGntE] inv inv := by
  narrow [recvGntE] from inv
    using [ACU.plus_unit, ACU.unit_plus, ACU.toMultiset_plus, ACU.toMultiset_elem,
      ACU.toMultiset_unit, Multiset.mem_add, Multiset.mem_singleton, Multiset.notMem_zero,
      or_imp, forall_and, forall_eq, freeItem_cache, freeItem_dir, otherItem_cache,
      otherItem_dir, cacheIds_plus, cacheIds_cache, cacheIds_dir, cacheIds_unit,
      shrIds_plus, shrIds_one, shrIds_unit, invIds_plus, invIds_one, invIds_unit, shrOf, invOf,
      Multiset.nodup_add, Multiset.nodup_singleton, Multiset.disjoint_singleton]
    as post hpost
  refine over_of_subsumes hpost.1 (subsumes_of_cover fun a ha => ?_)
  rw [← post_eq] at ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  repeat' rcases ha with rfl | ha
  all_goals apply subsumes_one
  all_goals try route
  all_goals try cond_close
  all_goals try cond_close2

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
  refine subsumes_of_cover fun a ha => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  subst ha
  refine subsumes_one ⟨freeP, by simp [inv], ?_⟩
  unfold initP freeP
  refine Subsumption.subsumes_of_match
    (fun x => (Cmd.idle, x.1, (∅ : Oids), (∅ : Oids), x.2)) fun x hc => ⟨rfl, ?_⟩
  obtain ⟨hCF, hnd⟩ := hc
  -- every cache is idle: free, not a sharer, not being invalidated
  have hs : shrIds x.2 = 0 := Multiset.eq_zero_of_forall_notMem fun y hy => by
    obtain ⟨it, hit, hy⟩ := Multiset.mem_bind.1 hy
    obtain ⟨i, rfl⟩ := hCF it hit
    simp [shrOf] at hy
  have hi : invIds x.2 = 0 := Multiset.eq_zero_of_forall_notMem fun y hy => by
    obtain ⟨it, hit, hy⟩ := Multiset.mem_bind.1 hy
    obtain ⟨i, rfl⟩ := hCF it hit
    simp [invOf] at hy
  refine ⟨fun it hit => ?_, hnd, by simp [hs], by simp, by simp [hi], .inr hi⟩
  obtain ⟨i, rfl⟩ := hCF it hit
  simp [freeItem]

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
