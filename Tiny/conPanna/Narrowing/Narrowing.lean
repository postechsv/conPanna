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

/-! Naming: `r` a rule, `R` a system, `p` a patch, `P` a pattern, `v` a unifier,
`V` a unifier set, `U` the unifier data of a level. A suffix `_r_p`, `_r_P`, `_R_P`
names the level a definition works at. -/

abbrev unifier_r_p (r : Rule α) (p : Patch α) := Unifier.{u, u} (r.Vars × p.Vars)
abbrev unifiers_r_p (r : Rule α) (p : Patch α) := UnifierSet.{u, u} (r.Vars × p.Vars)

/-- `V` is a complete and sound set of unifiers of `mayFire r p`. -/
def certificates_r_p (r : Rule α) (p : Patch α) (V : unifiers_r_p r p) : Prop :=
  complete (mayFire r p) V ∧ sound (mayFire r p) V

/-- The successor patch of one unifier `v = ∃x. (b x, a x)`: `∃x. ⟨t (b x) | c (a x) ∧ d (b x)⟩`. -/
-- `post_r_p_v r p v` = v(r.rhs) | v(p.cond) ∧ v(r.cond)
def post_r_p_v : (r : Rule α) → (p : Patch α) → unifier_r_p r p → Patch α
  | .bind rframe, .bind pframe, .bind v => .bind fun x =>
      ⟨(rframe (v x).1).rhs, (pframe (v x).2).cond ∧ (rframe (v x).1).cond⟩

/-- One successor patch per unifier. -/
-- `post_r_p r p V` = ⊔_v∈V {v(r.rhs) | v(p.cond) ∧ v(r.cond)}
def post_r_p (r : Rule α) (p : Patch α) : unifiers_r_p r p → Pattern α
  | [] => .bott
  | v :: V => .disj (.patch (post_r_p_v r p v)) (post_r_p r p V)

theorem post_r_p_holds {r : Rule α} {p : Patch α} {V : unifiers_r_p r p} {s : α} :
    (post_r_p r p V).holds s ↔ ∃ v ∈ V, (post_r_p_v r p v).holds s := by
  induction V with
  | nil => simp [post_r_p, Pattern.holds]
  | cons v V ih => simp [post_r_p, Pattern.holds, ih]

/-- Completeness of the unifiers gives `isOverPost`. -/
theorem isOverPost_of_complete {r : Rule α} {p : Patch α} {V : unifiers_r_p r p}
    (h : complete (mayFire r p) V) : isOverPost (.rule r) (.patch p) (post_r_p r p V) := by
  obtain ⟨g⟩ := r
  obtain ⟨f⟩ := p
  rintro _ after ⟨a, rfl, hc⟩ ⟨b, hl, rfl, hd⟩
  obtain ⟨⟨v⟩, hmem, x, hx⟩ := h (b, a) hl
  refine post_r_p_holds.2 ⟨.bind v, hmem, x, ?_⟩
  simp [PatchBody.holds, ← hx, hc, hd]

/-- Soundness of the unifiers gives `isUnderPost`. -/
theorem isUnderPost_of_sound {r : Rule α} {p : Patch α} {V : unifiers_r_p r p}
    (h : sound (mayFire r p) V) : isUnderPost (.rule r) (.patch p) (post_r_p r p V) := by
  obtain ⟨g⟩ := r
  obtain ⟨f⟩ := p
  intro after hpost
  obtain ⟨⟨v⟩, hmem, x, rfl, hc, hd⟩ := post_r_p_holds.1 hpost
  exact ⟨_, ⟨_, rfl, hc⟩, _, h _ hmem (v x) ⟨x, rfl⟩, rfl, hd⟩

theorem certifyPost_r_p (r : Rule α) (p : Patch α) (V : unifiers_r_p r p)
    (h : certificates_r_p r p V) : isPost (.rule r) (.patch p) (post_r_p r p V) :=
  ⟨isOverPost_of_complete h.1, isUnderPost_of_sound h.2⟩

/-! ## One rule, a pattern: one unifier set per patch -/

def unifiers_r_P (r : Rule α) : Pattern α → Type (u + 1)
  | .bott => PUnit.{u + 2}
  | .patch p => unifiers_r_p r p
  | .disj P₁ P₂ => unifiers_r_P r P₁ × unifiers_r_P r P₂

def certificates_r_P (r : Rule α) : (P : Pattern α) → unifiers_r_P r P → Prop
  | .bott, _ => True
  | .patch p, V => certificates_r_p r p V
  | .disj P₁ P₂, (U₁, U₂) => certificates_r_P r P₁ U₁ ∧ certificates_r_P r P₂ U₂

def post_r_P (r : Rule α) : (P : Pattern α) → unifiers_r_P r P → Pattern α
  | .bott, _ => .bott
  | .patch p, V => post_r_p r p V
  | .disj P₁ P₂, (U₁, U₂) => .disj (post_r_P r P₁ U₁) (post_r_P r P₂ U₂)

theorem certifyPost_r_P (r : Rule α) : (P : Pattern α) → (U : unifiers_r_P r P) →
    certificates_r_P r P U → isPost (.rule r) P (post_r_P r P U)
  | .bott, _, _ => isPost_bott _
  | .patch p, V, h => certifyPost_r_p r p V h
  | .disj P₁ P₂, (U₁, U₂), ⟨h₁, h₂⟩ =>
      isPost_disj (certifyPost_r_P r P₁ U₁ h₁) (certifyPost_r_P r P₂ U₂ h₂)

/-! ## A system, a pattern: one row per rule -/

def unifiers_R_P : System α → Pattern α → Type (u + 1)
  | .empty, _ => PUnit.{u + 2}
  | .rule r, P => unifiers_r_P r P
  | .choice R₁ R₂, P => unifiers_R_P R₁ P × unifiers_R_P R₂ P

def certificates_R_P : (R : System α) → (P : Pattern α) → unifiers_R_P R P → Prop
  | .empty, _, _ => True
  | .rule r, P, U => certificates_r_P r P U
  | .choice R₁ R₂, P, (U₁, U₂) => certificates_R_P R₁ P U₁ ∧ certificates_R_P R₂ P U₂

def post_R_P : (R : System α) → (P : Pattern α) → unifiers_R_P R P → Pattern α
  | .empty, _, _ => .bott
  | .rule r, P, U => post_r_P r P U
  | .choice R₁ R₂, P, (U₁, U₂) => .disj (post_R_P R₁ P U₁) (post_R_P R₂ P U₂)

/-- One narrowing step: if every (rule, patch) pair has a certified unifier set,
`post_R_P` is exactly the set of successors. -/
theorem certifyPost_R_P : (R : System α) → (P : Pattern α) → (U : unifiers_R_P R P) →
    certificates_R_P R P U → isPost R P (post_R_P R P U)
  | .empty, P, _, _ => isPost_empty P
  | .rule r, P, U, h => certifyPost_r_P r P U h
  | .choice R₁ R₂, P, (U₁, U₂), ⟨h₁, h₂⟩ =>
      isPost_choice (certifyPost_R_P R₁ P U₁ h₁) (certifyPost_R_P R₂ P U₂ h₂)

end Narrowing
