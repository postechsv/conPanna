import examples.Bakery.bakery_pf
import examples.Bakery.bakery_abort_obligation

/-!
Bakery, abortable: the original protocol extended with `abort` and `skip` preserves the
same invariant. The two parts are proved separately (`bakery_preserves_inv`,
`abortable_preserves_inv`) and combined: a step of `bakery ++ abortable` is a step of one
of them.
-/

namespace Bakery

open Expresso

#link abortable_preserves_inv

/-- Over-approximations of the post compose over a union of rules. -/
theorem isOverPost_append {α : Type} {R₁ R₂ : System α} {S P : Pattern α}
    (h₁ : isOverPost R₁ S P) (h₂ : isOverPost R₂ S P) : isOverPost (R₁ ++ R₂) S P :=
  fun a b ha hab => ((System.step_append _ _ _ _).1 hab).elim (h₁ a b ha) (h₂ a b ha)

theorem bakery_abort_preserves_inv : isOverPost (bakery ++ abortable) invP invP :=
  isOverPost_append bakery_preserves_inv.linked abortable_preserves_inv.linked

#print axioms bakery_abort_preserves_inv

end Bakery
