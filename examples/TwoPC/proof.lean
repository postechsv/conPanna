import examples.TwoPC.rule
import conPanna.conPanna
import conPanna.Unification.Certification.Multiset

/-!
# Two-phase commit: the invariant and its top-level proof

An object-oriented model (objects and messages in one ACU configuration; identifier
sets as a second ACU sort) and an invariant with one patch per coordinator phase, aimed
at atomic-commit agreement: no participant commits while another aborts.

`twoPC_inv`: narrowing the whole system against the three patches, with Maude's filtered
unifiers, gives 13 post patches after simplification; each lands in its phase's patch by
`maude_match`, and its condition follows by simplification, except one `recvYes` patch (a
short explicit proof). Certification claims: `cert.lean`; agreement end to end: `main.lean`.
-/

namespace TwoPC

open Expresso Unification Narrowing Subsumption

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

-- narrowing simplifies all cases in one declaration
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
  -- the conditions: all but one close by simplification alone
  all_goals
    try simp only [coll, comm, abrt, common, parts_plus, parts_one, parts_unit, coords_plus,
      coords_one, coords_unit, votes_plus, votes_one, votes_unit, decs_plus, decs_one,
      decs_unit, partOf, coordOf, voteOf, decOf, ACU.toMultiset_unit, add_zero, zero_add, Multiset.map_add, Multiset.map_singleton,
      Multiset.nodup_add, Multiset.nodup_singleton, Multiset.disjoint_singleton,
      Multiset.mem_add, Multiset.mem_singleton,
      Multiset.mem_map, or_imp, forall_and, forall_eq, Prod.mk.injEq,
      Prod.exists, Bool.exists_bool, Bool.forall_bool] at hc ⊢
    try (simp_all; done)
  -- one left, a protocol fact (`aesop`, `grind` fail): `recvYes`, the voter `P` (`x.2.1`)
  -- leaves the waiting set; it is prepared, and no yes from it is in transit
  all_goals
    refine ⟨⟨hc.1.1, hc.1.2.1, hc.1.2.2.1.2, hc.1.2.2.2.2.1, hc.1.2.2.2.2.2⟩, hc.2.1,
      ⟨hc.2.2.1.1, fun o ho => ?_, hc.2.2.1.2.2.2⟩, fun p hp => ?_⟩
    · rcases hc.2.2.1.2.1 o ho with h | h | h
      · exact .inl h
      · exact .inl (hc.2.2.1.2.2.1 o ho h)
      · exact .inr h
    · rcases hc.2.2.2 p hp with h | h
      · exact absurd (h ▸ hp) hc.1.2.2.1.1.2
      · exact h

end TwoPC
