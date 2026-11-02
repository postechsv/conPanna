import Reflect.Check
import conPanna.Unification.Unification

/-!
Soundness of the checker: `check M c = true` gives `complete P U` for the problem and
unifiers the data `c` mirrors (documentation/reflection-design.md, §4).
-/

namespace Reflect

open Unification

/-- An answer with its Lean unifier body. -/
structure LAns (M : Model) (sh : Shp) where
  bsh : Shp
  img : List Term
  body : bsh.Ty M.T → sh.Ty M.T

theorem complete_of_check (M : Model) (hM : M.Lawful) (c : Cert) (hc : check M c = true)
    (s : Nat) (body : c.sh.Ty M.T → M.T s × M.T s)
    (hl : ∀ γ, M.eval (M.enc c.sh γ) c.lhs = some ⟨s, (body γ).1⟩)
    (hr : ∀ γ, M.eval (M.enc c.sh γ) c.rhs = some ⟨s, (body γ).2⟩)
    (as : List (LAns M c.sh)) (has : c.answers = as.map fun a => ⟨a.bsh, a.img⟩)
    (hU : AllL (fun a : LAns M c.sh => ∀ x,
      a.img.map (M.eval (M.enc a.bsh x)) = (M.encL c.sh (a.body x)).map some) as) :
    complete (Problem.bind body) (as.map fun a => Unifier.bind a.body) := by
  sorry

end Reflect
