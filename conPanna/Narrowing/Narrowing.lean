import Expresso.core
import conPanna.Unification.Unification

/-!
One-step narrowing, reduced to unification.

The specification is `isPost` from `core.lean`: `isOverPost` (no missing successor) and
`isUnderPost` (no junk successor) play the roles of `complete` and `sound`. For one
rule and one patch, the post is read off the unifiers of their `mayFire` problem
(`certifyPost_r_p`); patterns and systems are lists, and their posts are the
concatenations of the cells' posts (`certifyPost_r_P`, `certifyPost_R_P`).
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
def post_r_p (r : Rule α) (p : Patch α) (U : unifiers_r_p r p) : Pattern α :=
  U.map (post_r_p_u r p)

theorem post_r_p_holds {r : Rule α} {p : Patch α} {U : unifiers_r_p r p} {s : α} :
    (post_r_p r p U).holds s ↔ ∃ u ∈ U, (post_r_p_u r p u).holds s := by
  simp only [post_r_p, Pattern.holds, List.mem_map]
  exact ⟨fun ⟨_, ⟨u, hu, rfl⟩, h⟩ => ⟨u, hu, h⟩, fun ⟨u, hu, h⟩ => ⟨_, ⟨u, hu, rfl⟩, h⟩⟩

/-- Completeness of the unifiers gives `isOverPost`. -/
theorem isOverPost_of_complete {r : Rule α} {p : Patch α} {U : unifiers_r_p r p}
    (h : complete (mayFire r p) U) : isOverPost [r] [p] (post_r_p r p U) := by
  obtain ⟨g⟩ := r
  obtain ⟨f⟩ := p
  intro _ after hs hstep
  simp only [Pattern.holds_cons, Pattern.holds_nil, or_false, System.step_cons,
    System.step_nil] at hs hstep
  obtain ⟨a, rfl, hc⟩ := hs
  obtain ⟨b, hl, rfl, hd⟩ := hstep
  obtain ⟨⟨u⟩, hmem, x, hx⟩ := h (b, a) hl
  refine post_r_p_holds.2 ⟨.bind u, hmem, x, ?_⟩
  simp [PatchBody.holds, ← hx, hc, hd]

/-- Soundness of the unifiers gives `isUnderPost`. -/
theorem isUnderPost_of_sound {r : Rule α} {p : Patch α} {U : unifiers_r_p r p}
    (h : sound (mayFire r p) U) : isUnderPost [r] [p] (post_r_p r p U) := by
  obtain ⟨g⟩ := r
  obtain ⟨f⟩ := p
  intro after hpost
  obtain ⟨⟨u⟩, hmem, x, rfl, hc, hd⟩ := post_r_p_holds.1 hpost
  exact ⟨_, (Pattern.holds_cons ..).2 (.inl ⟨_, rfl, hc⟩),
    (System.step_cons ..).2 (.inl ⟨_, h _ hmem (u x) ⟨x, rfl⟩, rfl, hd⟩)⟩

theorem certifyPost_r_p (r : Rule α) (p : Patch α) (U : unifiers_r_p r p)
    (h : certificates_r_p r p U) : isPost [r] [p] (post_r_p r p U) :=
  ⟨isOverPost_of_complete h.1, isUnderPost_of_sound h.2⟩

/-! ## One rule, a pattern: one unifier set per patch -/

def unifiers_r_P (r : Rule α) : Pattern α → Type (u + 1)
  | [] => PUnit.{u + 2}
  | p :: P => unifiers_r_p r p × unifiers_r_P r P

def certificates_r_P (r : Rule α) : (P : Pattern α) → unifiers_r_P r P → Prop
  | [], _ => True
  | p :: P, (U, Us) => certificates_r_p r p U ∧ certificates_r_P r P Us

def post_r_P (r : Rule α) : (P : Pattern α) → unifiers_r_P r P → Pattern α
  | [], _ => []
  | p :: P, (U, Us) => post_r_p r p U ++ post_r_P r P Us

theorem certifyPost_r_P (r : Rule α) : (P : Pattern α) → (Us : unifiers_r_P r P) →
    certificates_r_P r P Us → isPost [r] P (post_r_P r P Us)
  | [], _, _ => isPost_bott _
  | p :: P, (U, Us), ⟨h₁, h₂⟩ =>
      isPost_disj (S₁ := [p]) (certifyPost_r_p r p U h₁) (certifyPost_r_P r P Us h₂)

/-! ## A system, a pattern: one row per rule -/

def unifiers_R_P : System α → Pattern α → Type (u + 1)
  | [], _ => PUnit.{u + 2}
  | r :: R, P => unifiers_r_P r P × unifiers_R_P R P

def certificates_R_P : (R : System α) → (P : Pattern α) → unifiers_R_P R P → Prop
  | [], _, _ => True
  | r :: R, P, (Us₁, Us₂) => certificates_r_P r P Us₁ ∧ certificates_R_P R P Us₂

def post_R_P : (R : System α) → (P : Pattern α) → unifiers_R_P R P → Pattern α
  | [], _, _ => []
  | r :: R, P, (Us₁, Us₂) => post_r_P r P Us₁ ++ post_R_P R P Us₂

/-- One narrowing step: if every (rule, patch) pair has a certified unifier set,
`post_R_P` is exactly the set of successors. -/
theorem certifyPost_R_P : (R : System α) → (P : Pattern α) → (Us : unifiers_R_P R P) →
    certificates_R_P R P Us → isPost R P (post_R_P R P Us)
  | [], P, _, _ => isPost_empty P
  | r :: R, P, (Us₁, Us₂), ⟨h₁, h₂⟩ =>
      isPost_choice (R₁ := [r]) (certifyPost_r_P r P Us₁ h₁) (certifyPost_R_P R P Us₂ h₂)

end Narrowing
