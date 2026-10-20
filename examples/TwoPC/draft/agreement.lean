import examples.TwoPC.draft.obligation

/-!
# Two-phase commit: atomic-commit agreement

`twoPC_inv` with its obligations linked in: `inv` is inductive. Initial states lie in it
(`init_inv`) and it lies in the agreement pattern (`inv_safe`), so every reachable state is
in agreement (`twoPC_agreement`, by `invariant_safe`).
-/

namespace TwoPC

open Expresso

#link twoPC_inv

theorem mem_parts {CF : Items} {o : Participant} (h : Item.part o ∈ CF.toMultiset) :
    o ∈ parts CF :=
  Multiset.mem_bind.2 ⟨_, h, by simp [partOf]⟩

/-- Initially the coordinator collects, waiting for all participants; every participant
works, with distinct ids among the coordinator's; there are no messages. -/
theorem inv_init {C : Oid} {PS : Oids} {CF : Items}
    (hCF : ∀ it ∈ CF.toMultiset, ∃ o, it = .part o ∧ o.state = .working ∧ o.id ∈ PS.toMultiset)
    (hids : ((parts CF).map (·.id)).Nodup) :
    inv.holds ⟨{Item.coord ⟨C, .collecting, PS, PS⟩} + CF⟩ := by
  have hp : ∀ o ∈ parts CF, o.state = .working ∧ o.id ∈ PS.toMultiset := by
    intro o ho
    obtain ⟨it, hit, ho⟩ := Multiset.mem_bind.1 ho
    obtain ⟨o', rfl, h⟩ := hCF it hit
    simp only [partOf, Multiset.mem_singleton] at ho
    exact ho ▸ h
  -- the configuration has participants only, so no coordinator, votes or decisions
  have hz : ∀ {β : Type} (f : Item → Multiset β), (∀ o, f (.part o) = 0) →
      CF.toMultiset.bind f = 0 := fun f hf =>
    Multiset.eq_zero_of_forall_notMem fun b hb => by
      obtain ⟨it, hit, hb⟩ := Multiset.mem_bind.1 hb
      obtain ⟨o, rfl, -⟩ := hCF it hit
      simp [hf] at hb
  have hc : coords CF = 0 := hz _ fun _ => rfl
  have hv : votes CF = 0 := hz _ fun _ => rfl
  have hd : decs CF = 0 := hz _ fun _ => rfl
  simp only [inv, collP, Pattern.holds_cons, Patch.holds, PatchBody.holds]
  refine .inl ⟨(C, PS, PS, CF), rfl, ⟨hc, hids, by simp [hv], by simp [hv]⟩, hd,
    fun o ho => ?_, by simp [hv]⟩
  obtain ⟨hw, hid⟩ := hp o ho
  simp [hw, hid, hv]

/-- Each patch of the invariant: no committed participant next to an aborted one. -/
theorem agree_inv {s : Conf} (h : inv.holds s) {p q : Participant}
    (hp : Item.part p ∈ s.cf.toMultiset) (hq : Item.part q ∈ s.cf.toMultiset)
    (hpc : p.state = .committed) (hqa : q.state = .aborted) : False := by
  simp only [inv, collP, commP, abrtP, Pattern.holds_cons, Pattern.holds_nil, or_false,
    Patch.holds, PatchBody.holds] at h
  rcases h with ⟨⟨C, PS, W, CF⟩, rfl, h⟩ | ⟨⟨C, PS, W, CF⟩, rfl, h⟩ | ⟨⟨C, PS, W, CF⟩, rfl, h⟩ <;>
    simp only [ACU.toMultiset_plus, ACU.toMultiset_elem, Multiset.mem_add,
      Multiset.mem_singleton, reduceCtorEq, false_or] at hp hq
  · exact agree_coll h p (mem_parts hp) hpc
  · exact agree_comm h q (mem_parts hq) hqa
  · exact agree_abrt h p (mem_parts hp) hpc

/-- Initial states: the coordinator collects, waiting for all participants; every
participant works, with distinct ids among the coordinator's; there are no messages. -/
def initP : Patch Conf := .bind fun ((C, PS, CF) : Oid × Oids × Items) =>
  ⟨⟨{Item.coord ⟨C, .collecting, PS, PS⟩} + CF⟩,
    (∀ it : Item, it ∈ CF.toMultiset → ∃ o : Participant, it = Item.part o ∧
      o.state = PState.working ∧ o.id ∈ PS.toMultiset) ∧
      ((parts CF).map fun o : Participant => o.id).Nodup⟩

/-- Agreement: no participant committed while another aborted. -/
def safeP : Pattern Conf := [.bind fun (s : Conf) => ⟨s, ∀ p q : Participant,
  Item.part p ∈ s.cf.toMultiset → Item.part q ∈ s.cf.toMultiset →
    p.state = .committed → q.state ≠ .aborted⟩]

theorem init_inv : subsumes [initP] inv := fun s hs => by
  simp only [initP, Pattern.holds_cons, Pattern.holds_nil, or_false, Patch.holds,
    PatchBody.holds] at hs
  obtain ⟨⟨C, PS, CF⟩, rfl, hCF, hids⟩ := hs
  exact inv_init hCF hids

theorem inv_safe : subsumes inv safeP := fun s hs => by
  simp only [safeP, Pattern.holds_cons, Pattern.holds_nil, or_false, Patch.holds,
    PatchBody.holds]
  exact ⟨s, rfl, fun p q hp hq hpc hqa => agree_inv hs hp hq hpc hqa⟩

/-- Atomic-commit agreement in every state reachable from an initial one. -/
theorem twoPC_agreement {x y : Conf} (hx : Pattern.holds [initP] x) (hxy : twoPC.steps x y) :
    safeP.holds y :=
  invariant_safe init_inv twoPC_inv.linked inv_safe hx hxy

#print axioms twoPC_agreement

end TwoPC
