import examples.Bakery.bakery_pf
import examples.Bakery.bakery_abort_obligation

/-!
Bakery, abortable: the original protocol extended with `abort` and `skip` preserves the
same invariant. The two parts are proved separately (`bakery_preserves_inv`,
`abortable_preserves_inv`) and combined (`isOverPost_choice`): a step of
`bakery ++ abortable` is a step of one of them. Mutual exclusion follows as before.
-/

namespace Bakery

open Expresso

#link abortable_preserves_inv

theorem bakery_abort_preserves_inv : isOverPost (bakery ++ abortable) invP invP :=
  isOverPost_choice bakery_preserves_inv.linked abortable_preserves_inv.linked

/-- Mutual exclusion still holds with `abort` and `skip`. -/
theorem bakery_abort_mutex {x y : Conf} (hx : Pattern.holds [initialP] x)
    (hxy : (bakery ++ abortable).steps x y) : mutexP.holds y :=
  invariant_safe init_inv bakery_abort_preserves_inv inv_mutex hx hxy

#print axioms bakery_abort_mutex

end Bakery
