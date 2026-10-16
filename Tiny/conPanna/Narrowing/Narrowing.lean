import Tiny.Expresso.core
import Tiny.conPanna.Unification.Unification

/-!
One-step narrowing, reduced to unification.

The specification is `isPost` from `core.lean`: `isOverPost` (no missing successor) and
`isUnderPost` (no junk successor) play the roles of `complete` and `sound`. For one
patch and one rule, the post is read off the unifiers of their mayFire problem
(`isPost_of_unifiers`); patterns and systems then compose by `disj` and `choice`.
-/

namespace Narrowing

open Expresso Unification

universe u

variable {α : Type u}

/-! ## One patch, one rule -/

-- `mayFire r p` = rule r may fire on patch p if condition holds
-- r.lhs =? p.state (ignoring both constraints)
def mayFire : (r : Rule α) → (p : Patch α) → Problem α (r.Vars × p.Vars)
  | .bind rframe, .bind pframe => .bind fun (b, a) => ((rframe b).lhs, (pframe a).state)

/-- The successor patch of one unifier `σ = ∃x. (b x, a x)`: `∃x. ⟨t (b x) | c (a x) ∧ d (b x)⟩`. -/
-- `post' r p σ` = σ(r.rhs) | σ(p.cond) ∧ σ(r.cond)
def post' : (r : Rule α) → (p : Patch α) → Unifier.{u, u} (r.Vars × p.Vars) → Patch α
  | .bind rframe, .bind pframe, .bind σ => .bind fun x =>
      ⟨(rframe (σ x).1).rhs, (pframe (σ x).2).cond ∧ (rframe (σ x).1).cond⟩

/-- The post: one successor patch per unifier. -/
-- `post r p Σ` = ⊔_σ∈Σ {σ(r.rhs) | σ(p.cond) ∧ σ(r.cond)}
def post (r : Rule α) (p : Patch α) : UnifierSet.{u, u} (r.Vars × p.Vars) → Pattern α
  | [] => .bott
  | σ :: rest => .disj (.patch (post' r p σ)) (post r p rest)

theorem post_holds {r : Rule α} {p : Patch α} {unifiers : UnifierSet.{u, u} (r.Vars × p.Vars)}
    {s : α} : (post r p unifiers).holds s ↔ ∃ σ ∈ unifiers, (post' r p σ).holds s := by
  induction unifiers with
  | nil => simp [post, Pattern.holds]
  | cons σ rest ih => simp [post, Pattern.holds, ih]

/-- Completeness of the unifiers gives `isOverPost`. -/
theorem isOverPost_of_complete {r : Rule α} {p : Patch α} {unifiers : UnifierSet.{u, u} (r.Vars × p.Vars)}
    (h : complete (mayFire r p) unifiers) : isOverPost (.rule r) (.patch p) (post r p unifiers) := by
  obtain ⟨g⟩ := r
  obtain ⟨f⟩ := p
  rintro _ after ⟨a, rfl, hc⟩ ⟨b, hl, rfl, hd⟩
  obtain ⟨⟨σ⟩, hmem, x, hx⟩ := h (b, a) hl
  refine post_holds.2 ⟨.bind σ, hmem, x, ?_⟩
  simp [PatchBody.holds, ← hx, hc, hd]

/-- Soundness of the unifiers gives `isUnderPost`. -/
theorem isUnderPost_of_sound {r : Rule α} {p : Patch α} {unifiers : UnifierSet.{u, u} (r.Vars × p.Vars)}
    (h : sound (mayFire r p) unifiers) : isUnderPost (.rule r) (.patch p) (post r p unifiers) := by
  obtain ⟨g⟩ := r
  obtain ⟨f⟩ := p
  intro after hpost
  obtain ⟨⟨σ⟩, hmem, x, rfl, hc, hd⟩ := post_holds.1 hpost
  exact ⟨_, ⟨_, rfl, hc⟩, _, h _ hmem (σ x) ⟨x, rfl⟩, rfl, hd⟩

theorem isPost_of_unifiers {r : Rule α} {p : Patch α} {unifiers : UnifierSet.{u, u} (r.Vars × p.Vars)}
    (hc : complete (mayFire r p) unifiers) (hs : sound (mayFire r p) unifiers) :
    isPost (.rule r) (.patch p) (post r p unifiers) :=
  ⟨isOverPost_of_complete hc, isUnderPost_of_sound hs⟩


end Narrowing
