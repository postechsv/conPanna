import conPanna.Unification.Unification

/-!
Deferred certification claims. `narrow` closes each cell's completeness obligation with
`laterAx key P U` and its soundness obligation with `laterSoundAx P U`, instead of `sorry`:
the claims are certified later, as separate obligations (`#obligations`, `#link`).

Unlike `sorryAx`, these axioms state only completeness and soundness claims. So a theorem
whose `#print axioms` shows them (and no `sorryAx`) holds modulo exactly these claims,
which `#claims` lists. `key` names the claim's completeness certificate, stored by the
narrowing step (udfStore.lean); it plays no logical role.
-/

namespace Unification

universe u v x

/-- A completeness claim, deferred to certification. -/
axiom laterAx (key : String) {α : Type u} {Γ : Type v} (P : Problem α Γ)
    (U : UnifierSet.{v, x} Γ) : complete P U

/-- A soundness claim, deferred to certification. -/
axiom laterSoundAx {α : Type u} {Γ : Type v} (P : Problem α Γ)
    (U : UnifierSet.{v, x} Γ) : sound P U

end Unification
