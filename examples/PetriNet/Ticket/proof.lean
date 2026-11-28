import examples.PetriNet.Ticket.rule
import conPanna.BaseTheory.Multiset
import conPanna.Narrowing.Narrowing
import conPanna.Unification.Tactics.maudeUnify
import conPanna.Later
import conPanna.Subsumption
import conPanna.Unification.Tactics.maudeMatch
import conPanna.narrow

/-!
The ticket machine: the money in the marking is conserved. Every transition exchanges
tokens of equal value (dollar 100, quarter 25, t1 50, t2 75, in cents). The invariant is
stated for the paper's starting marking, four quarters and two dollars: 300 cents.
-/

namespace Ticket

open Expresso Unification Narrowing Subsumption PetriNet Place

/-- The value of a token, in cents. -/
def price : Place → Nat
  | dollar => 100
  | quarter => 25
  | t1 => 50
  | t2 => 75

/-- The value of a marking: its tokens' prices, added up. -/
def value (M : Marking Place) : Nat :=
  100 * M.toMultiset.count dollar + 25 * M.toMultiset.count quarter +
    50 * M.toMultiset.count t1 + 75 * M.toMultiset.count t2

theorem value_plus (X Y : Marking Place) : value (X + Y) = value X + value Y := by
  simp only [value, ACU.toMultiset_plus, Multiset.count_add]; omega

theorem value_elem (p : Place) : value {p} = price p := by
  cases p <;> simp [value, price, ACU.toMultiset_elem]

/-- The markings worth 300 cents, the value of the paper's starting marking. -/
def worthP : Patch (Marking Place) := .bind fun (M : Marking Place) => ⟨M, value M = 300⟩

def invP : Pattern (Marking Place) := [worthP]

/-- `net(invP) ⊆ invP`: every transition keeps the value. -/
theorem net_preserves_inv : isOverPost net invP invP := by
  narrow net from invP
    using [ACU.plus_unit, ACU.unit_plus]
    as post hpost
  refine over_of_subsumes hpost.1 (subsumes_of_cover fun a ha => ?_)
  rw [← post_eq] at ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  -- one case per transition: the tokens taken and given are worth the same
  rcases ha with rfl | rfl | rfl | rfl | rfl <;>
    (apply subsumes_one; maude_match worthP
     simp only [value_plus, value_elem, price] at hc ⊢; omega)

end Ticket
