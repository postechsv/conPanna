import examples.TwoPC.draft.obligation

/-!
# Two-phase commit: atomic-commit agreement

`twoPC_inv` with its obligations linked in: `inv` is inductive. Initial states lie in it
(`inv_init`), and each of its patches excludes a committed participant next to an aborted
one, so no reachable state has both (`twoPC_agreement`).
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

/-- The invariant at every state reachable from one in it. -/
theorem inv_reach {s s' : Conf} (h : inv.holds s)
    (hr : Relation.ReflTransGen (System.step twoPC) s s') : inv.holds s' := by
  induction hr with
  | refl => exact h
  | tail _ hst ih => exact twoPC_inv.linked _ _ ih hst

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

/-- Atomic-commit agreement: in no state reachable from an initial one has a participant
committed while another aborted. -/
theorem twoPC_agreement {C : Oid} {PS : Oids} {CF : Items}
    (hCF : ∀ it ∈ CF.toMultiset, ∃ o, it = .part o ∧ o.state = .working ∧ o.id ∈ PS.toMultiset)
    (hids : ((parts CF).map (·.id)).Nodup) {s : Conf}
    (hr : Relation.ReflTransGen (System.step twoPC) ⟨{Item.coord ⟨C, .collecting, PS, PS⟩} + CF⟩ s)
    {p q : Participant} (hp : Item.part p ∈ s.cf.toMultiset) (hq : Item.part q ∈ s.cf.toMultiset)
    (hpc : p.state = .committed) (hqa : q.state = .aborted) : False :=
  agree_inv (inv_reach (inv_init hCF hids) hr) hp hq hpc hqa

#print axioms twoPC_agreement

end TwoPC
