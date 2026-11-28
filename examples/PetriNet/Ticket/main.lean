import examples.PetriNet.Ticket.cert

/-!
The ticket machine: the finished theorem. The invariance proof of `proof.lean` is linked
with its certification obligations (`cert.lean`). From the paper's starting marking (four
quarters and two dollars), every reachable marking is worth 300 cents.
-/

namespace Ticket

open Expresso PetriNet Place

#link net_preserves_inv

/-- The paper's starting marking: four quarters and two dollars. -/
def startP : Pattern (Marking Place) :=
  [.bind fun (_ : Unit) =>
    ⟨{quarter} + {quarter} + {quarter} + {quarter} + {dollar} + {dollar}, True⟩]

theorem init_inv : subsumes startP invP := fun s h => by
  simp only [startP, invP, worthP, Pattern.holds_cons, Pattern.holds_nil, or_false,
    Patch.holds, PatchBody.holds] at h ⊢
  obtain ⟨_, rfl, -⟩ := h
  exact ⟨_, rfl, by simp [value_plus, value_elem, price]⟩

/-- From the starting marking, every step keeps the value at 300 cents. -/
theorem net_value {x y : Marking Place} (hx : startP.holds x) (hxy : net.steps x y) :
    invP.holds y :=
  invariant_safe init_inv net_preserves_inv.linked (fun _ h => h) hx hxy

#claims net_preserves_inv.linked
#print axioms net_value

end Ticket
