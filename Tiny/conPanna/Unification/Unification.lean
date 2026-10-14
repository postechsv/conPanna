namespace Unification

universe u v x

/-!
Native unification semantics. Model types account for their structural equality:
use quotient values for sorts with nontrivial axioms, and ordinary values for free sorts.
Consequently, terms and assignment packages are compared using ordinary Lean equality.
There is no constructor encoding, registration, or metaprogramming dependency here.

Same shape as patterns: a unifier binds its variables once, over one type `A`
(several variables go in a tuple), and its body is an assignment `Γ` of the
original variables; a unifier set is a list of unifiers.
-/

/-- The problem `t₁[Γ] =? t₂[Γ]`: one binder returns both sides under the same
assignment `Γ` of the original variables. -/
inductive Problem (α : Type u) (Γ : Type v) where
  | bind (body : Γ → α × α) : Problem α Γ

/-- A unifier `∃ a : A, body a`, e.g. `.bind fun U! => ⟨f U!, U!⟩` for `X ↦ f(U), Y ↦ U`. -/
inductive Unifier (Γ : Type v) : Type (max v (x + 1)) where
  | bind {A : Type x} (body : A → Γ) : Unifier Γ

abbrev UnifierSet (Γ : Type v) := List (Unifier.{v, x} Γ)

variable {α : Type u} {Γ : Type v}

/-- `γ(t₁) = γ(t₂)`. -/
def unifiedBy : Problem α Γ → Γ → Prop
  | .bind body, γ => (body γ).1 = (body γ).2

/-- `γ` is an instance of `σ`. -/
def covers : Unifier.{v, x} Γ → Γ → Prop
  | .bind body, γ => ∃ a, γ = body a

/-- Every solution is an instance of some answer. -/
def complete (problem : Problem α Γ) (answers : UnifierSet.{v, x} Γ) : Prop :=
  ∀ γ, unifiedBy problem γ → ∃ σ ∈ answers, covers σ γ

/-- Every instance of every answer is a solution. -/
def sound (problem : Problem α Γ) (answers : UnifierSet.{v, x} Γ) : Prop :=
  ∀ σ ∈ answers, ∀ γ, covers σ γ → unifiedBy problem γ

end Unification
