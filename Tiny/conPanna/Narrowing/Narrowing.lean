import Tiny.Expresso.core
import Tiny.conPanna.Unification.Unification

/-!
One-step narrowing, reduced to unification.

The specification is `isPost` from `core.lean`: `isOverPost` (no missing successor) and
`isUnderPost` (no junk successor) play the roles of `complete` and `sound`. For one
rule and one patch, the post is read off the unifiers of their `mayFire` problem
(`certifyPost_r_p`); patterns and systems then compose by `disj` and `choice`
(`certifyPost_r_P`, `certifyPost_R_P`).
-/

namespace Narrowing

open Expresso Unification

universe u

variable {α : Type u}

/-! ## One rule, one patch -/

-- `mayFire r p` = rule r may fire on patch p if condition holds
-- r.lhs =? p.state (ignoring both constraints)
def mayFire : (r : Rule α) → (p : Patch α) → Problem α (r.Vars × p.Vars)
  | .bind rframe, .bind pframe => .bind fun (b, a) => ((rframe b).lhs, (pframe a).state)

/-! Naming: `r` a rule, `R` a system, `p` a patch, `P` a pattern, `u` a unifier,
`U` a unifier set, `Us` the unifier sets of a level. A suffix `_r_p`, `_r_P`, `_R_P`
names the level a definition works at. -/

abbrev unifier_r_p (r : Rule α) (p : Patch α) := Unifier.{u, u} (r.Vars × p.Vars)
abbrev unifiers_r_p (r : Rule α) (p : Patch α) := UnifierSet.{u, u} (r.Vars × p.Vars)

/-- `U` is a complete and sound set of unifiers of `mayFire r p`. -/
def certificates_r_p (r : Rule α) (p : Patch α) (U : unifiers_r_p r p) : Prop :=
  complete (mayFire r p) U ∧ sound (mayFire r p) U

/-- The successor patch of one unifier `u = ∃x. (b x, a x)`: `∃x. ⟨t (b x) | c (a x) ∧ d (b x)⟩`. -/
-- `post_r_p_u r p u` = u(r.rhs) | u(p.cond) ∧ u(r.cond)
def post_r_p_u : (r : Rule α) → (p : Patch α) → unifier_r_p r p → Patch α
  | .bind rframe, .bind pframe, .bind u => .bind fun x =>
      ⟨(rframe (u x).1).rhs, (pframe (u x).2).cond ∧ (rframe (u x).1).cond⟩

/-- One successor patch per unifier. -/
-- `post_r_p r p U` = ⊔_u∈U {u(r.rhs) | u(p.cond) ∧ u(r.cond)}
def post_r_p (r : Rule α) (p : Patch α) : unifiers_r_p r p → Pattern α
  | [] => .bott
  | u :: U => .disj (.patch (post_r_p_u r p u)) (post_r_p r p U)

theorem post_r_p_holds {r : Rule α} {p : Patch α} {U : unifiers_r_p r p} {s : α} :
    (post_r_p r p U).holds s ↔ ∃ u ∈ U, (post_r_p_u r p u).holds s := by
  induction U with
  | nil => simp [post_r_p, Pattern.holds]
  | cons u U ih => simp [post_r_p, Pattern.holds, ih]

/-- Completeness of the unifiers gives `isOverPost`. -/
theorem isOverPost_of_complete {r : Rule α} {p : Patch α} {U : unifiers_r_p r p}
    (h : complete (mayFire r p) U) : isOverPost (.rule r) (.patch p) (post_r_p r p U) := by
  obtain ⟨g⟩ := r
  obtain ⟨f⟩ := p
  rintro _ after ⟨a, rfl, hc⟩ ⟨b, hl, rfl, hd⟩
  obtain ⟨⟨u⟩, hmem, x, hx⟩ := h (b, a) hl
  refine post_r_p_holds.2 ⟨.bind u, hmem, x, ?_⟩
  simp [PatchBody.holds, ← hx, hc, hd]

/-- Soundness of the unifiers gives `isUnderPost`. -/
theorem isUnderPost_of_sound {r : Rule α} {p : Patch α} {U : unifiers_r_p r p}
    (h : sound (mayFire r p) U) : isUnderPost (.rule r) (.patch p) (post_r_p r p U) := by
  obtain ⟨g⟩ := r
  obtain ⟨f⟩ := p
  intro after hpost
  obtain ⟨⟨u⟩, hmem, x, rfl, hc, hd⟩ := post_r_p_holds.1 hpost
  exact ⟨_, ⟨_, rfl, hc⟩, _, h _ hmem (u x) ⟨x, rfl⟩, rfl, hd⟩

theorem certifyPost_r_p (r : Rule α) (p : Patch α) (U : unifiers_r_p r p)
    (h : certificates_r_p r p U) : isPost (.rule r) (.patch p) (post_r_p r p U) :=
  ⟨isOverPost_of_complete h.1, isUnderPost_of_sound h.2⟩

/-! ## One rule, a pattern: one unifier set per patch -/

def unifiers_r_P (r : Rule α) : Pattern α → Type (u + 1)
  | .bott => PUnit.{u + 2}
  | .patch p => unifiers_r_p r p
  | .disj P₁ P₂ => unifiers_r_P r P₁ × unifiers_r_P r P₂

def certificates_r_P (r : Rule α) : (P : Pattern α) → unifiers_r_P r P → Prop
  | .bott, _ => True
  | .patch p, U => certificates_r_p r p U
  | .disj P₁ P₂, (Us₁, Us₂) => certificates_r_P r P₁ Us₁ ∧ certificates_r_P r P₂ Us₂

def post_r_P (r : Rule α) : (P : Pattern α) → unifiers_r_P r P → Pattern α
  | .bott, _ => .bott
  | .patch p, U => post_r_p r p U
  | .disj P₁ P₂, (Us₁, Us₂) => .disj (post_r_P r P₁ Us₁) (post_r_P r P₂ Us₂)

theorem certifyPost_r_P (r : Rule α) : (P : Pattern α) → (Us : unifiers_r_P r P) →
    certificates_r_P r P Us → isPost (.rule r) P (post_r_P r P Us)
  | .bott, _, _ => isPost_bott _
  | .patch p, U, h => certifyPost_r_p r p U h
  | .disj P₁ P₂, (Us₁, Us₂), ⟨h₁, h₂⟩ =>
      isPost_disj (certifyPost_r_P r P₁ Us₁ h₁) (certifyPost_r_P r P₂ Us₂ h₂)

/-! ## A system, a pattern: one row per rule -/

def unifiers_R_P : System α → Pattern α → Type (u + 1)
  | .empty, _ => PUnit.{u + 2}
  | .rule r, P => unifiers_r_P r P
  | .choice R₁ R₂, P => unifiers_R_P R₁ P × unifiers_R_P R₂ P

def certificates_R_P : (R : System α) → (P : Pattern α) → unifiers_R_P R P → Prop
  | .empty, _, _ => True
  | .rule r, P, Us => certificates_r_P r P Us
  | .choice R₁ R₂, P, (Us₁, Us₂) => certificates_R_P R₁ P Us₁ ∧ certificates_R_P R₂ P Us₂

def post_R_P : (R : System α) → (P : Pattern α) → unifiers_R_P R P → Pattern α
  | .empty, _, _ => .bott
  | .rule r, P, Us => post_r_P r P Us
  | .choice R₁ R₂, P, (Us₁, Us₂) => .disj (post_R_P R₁ P Us₁) (post_R_P R₂ P Us₂)

/-- One narrowing step: if every (rule, patch) pair has a certified unifier set,
`post_R_P` is exactly the set of successors. -/
theorem certifyPost_R_P : (R : System α) → (P : Pattern α) → (Us : unifiers_R_P R P) →
    certificates_R_P R P Us → isPost R P (post_R_P R P Us)
  | .empty, P, _, _ => isPost_empty P
  | .rule r, P, Us, h => certifyPost_r_P r P Us h
  | .choice R₁ R₂, P, (Us₁, Us₂), ⟨h₁, h₂⟩ =>
      isPost_choice (certifyPost_R_P R₁ P Us₁ h₁) (certifyPost_R_P R₂ P Us₂ h₂)

end Narrowing
