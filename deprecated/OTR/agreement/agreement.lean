import examples.OTR.agreement.obligation

/-!
# OneThirdRule: agreement

`otr_inv` with its obligations linked in: the invariant is inductive. With `inv_init` and
`agreement` (`model.lean`): from an initial state, every reachable state has the invariant,
so any two decided nodes decided the same value.
-/

namespace OTRA

open Expresso

#link otr_inv

theorem inv_holds {s : Conf} : inv.holds s ↔ InvS s := by
  simp only [inv, invP, Pattern.holds_cons, Pattern.holds_nil, or_false, Patch.holds,
    PatchBody.holds, InvS]
  constructor
  · rintro ⟨⟨TH, IDS, CF, LG⟩, rfl, h⟩; exact h
  · intro h; exact ⟨(s.th, s.ids, s.items, s.log), rfl, h⟩

/-- Every state reachable from one with the invariant has it. -/
theorem inv_reach {s s' : Conf} (h : InvS s) (hr : Relation.ReflTransGen (System.step otr) s s') :
    InvS s' := by
  induction hr with
  | refl => exact h
  | tail _ hst ih => exact inv_holds.1 (otr_inv.linked _ _ (inv_holds.2 ih) hst)

/-- Agreement of OneThirdRule: in every state reachable from an initial one, two decided
nodes decided the same value. -/
theorem otr_agreement {TH : Nat} {IDS : OidSet} {CF : Items}
    (hCF : ∀ it ∈ CF.toMultiset, ∃ n, it = .node n ∧ n.round = 0 ∧ n.step = .init ∧
      n.dec = .undecided ∧ n.vt = 0 ∧ n.vf = 0 ∧ n.va = 0)
    (hids : IDS.toMultiset.Nodup) (hth : 2 * Multiset.card (nodesOf CF.toMultiset) < 3 * TH)
    {s : Conf} (hr : Relation.ReflTransGen (System.step otr) ⟨TH, IDS, CF, ∅⟩ s)
    {n₁ n₂ : Node} (h₁ : Item.node n₁ ∈ s.items.toMultiset) (h₂ : Item.node n₂ ∈ s.items.toMultiset)
    {v w : Bool} (hv : n₁.dec = .decided v) (hw : n₂.dec = .decided w) : v = w :=
  agreement (inv_reach (s := ⟨TH, IDS, CF, ∅⟩) (inv_init hCF hids hth) hr) h₁ h₂ hv hw

#print axioms otr_agreement

end OTRA
