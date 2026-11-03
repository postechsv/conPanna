import conPanna.Reflect.Eval
import conPanna.Unification.Unification

/-!
The bridge between a claim as data and the Lean goal it mirrors
(documentation/reflection-design.md, §4): the problem `P = Problem.bind body` and the
unifiers `U` whose sides and images the data terms evaluate to, by `rfl`.
-/

namespace Reflect

/-- An answer with its Lean unifier body. -/
structure LAns (M : Model) (sh : Shp) where
  bsh : Shp
  img : List Term
  body : bsh.Ty M.T → sh.Ty M.T

/-- The claim `c` mirrors the problem `Problem.bind body` (sides of sort `s`) and the
unifiers `as`: each fact holds by evaluation (`rfl`). -/
structure Bridge (M : Model) (c : Claim) where
  s : Nat
  body : c.sh.Ty M.T → M.T s × M.T s
  as : List (LAns M c.sh)
  hl : ∀ γ, M.eval (M.enc c.sh γ) c.lhs = some ⟨s, (body γ).1⟩
  hr : ∀ γ, M.eval (M.enc c.sh γ) c.rhs = some ⟨s, (body γ).2⟩
  has : c.answers = as.map fun a => ⟨a.bsh, a.img⟩
  hU : AllL (fun a : LAns M c.sh => ∀ x,
    a.img.map (M.eval (M.enc a.bsh x)) = (M.encL c.sh (a.body x)).map some) as

/-- The problem the claim mirrors. -/
abbrev Bridge.problem {M : Model} {c : Claim} (b : Bridge M c) : Unification.Problem (M.T b.s) (c.sh.Ty M.T) :=
  .bind b.body

/-- The unifiers the claim mirrors. -/
abbrev Bridge.unifiers {M : Model} {c : Claim} (b : Bridge M c) : Unification.UnifierSet (c.sh.Ty M.T) :=
  b.as.map fun a => .bind a.body

namespace Model

variable {M : Model}

open Term

mutual
theorem varsBelow_occurs {n x : Nat} : ∀ {t : Term}, varsBelow n t = true → occursT x t = true → x < n
  | .var y, h1, h2 => by
    simp only [varsBelow, Nat.blt_eq] at h1; simp only [occursT, beq_iff_eq] at h2; omega
  | .app _ ts, h1, h2 => varsBelowL_occurs (by simpa [varsBelow] using h1) (by simpa [occursT] using h2)
  | .acu _ ts, h1, h2 => varsBelowL_occurs (by simpa [varsBelow] using h1) (by simpa [occursT] using h2)
theorem varsBelowL_occurs {n x : Nat} : ∀ {ts : List Term}, varsBelowL n ts = true →
    occursTL x ts = true → x < n
  | [], _, h2 => by simp [occursTL] at h2
  | t :: ts, h1, h2 => by
    simp only [varsBelowL, Bool.and_eq_true] at h1
    simp only [occursTL, Bool.or_eq_true] at h2
    rcases h2 with h2 | h2
    · exact varsBelow_occurs h1.1 h2
    · exact varsBelowL_occurs h1.2 h2
end

/-- A tuple's valuation respects the tuple's sorts. -/
theorem enc_ws (sh : Shp) (x : sh.Ty M.T) : M.WS sh.sorts (M.enc sh x) := by
  intro y v hy
  simp only [enc] at hy
  rw [← encL_sorts sh x, List.getElem?_map, hy, Option.map_some]

end Model

end Reflect
