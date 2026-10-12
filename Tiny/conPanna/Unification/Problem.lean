namespace Unification

universe u v x y

/-!
Native unification semantics. Model types account for their structural equality:
use quotient values for sorts with nontrivial axioms, and ordinary values for free sorts.
Consequently, terms and assignment packages are compared using ordinary Lean equality.
Theory/presentation recovery and supported-theory validation belong in a separate module.
There is no constructor encoding, registration, or metaprogramming dependency here.
-/

-- meaning `t1[Γ] =B? t2[Γ]` the B-unification problem
-- e.g., { X := x, Y := y } : Γ (user provides x, y from their own context)
-- Γ → α is the type of α-terms with free variables in dom(Γ)
-- The model's quotient types now absorb B; α and Γ are native Lean types.
structure Problem (α : Type u) (Γ : Type v) where
  lhs : Γ → α
  rhs : Γ → α

-- abbrev ProblemSet (α : Type u) (Vars : Type v) := List (Problem α Vars)
-- this cannot encode many sorted problems; all are α
-- This note still applies to a list indexed by a single result type α.

variable {α : Type u} {Γ : Type v}

/- meaning `σ(t1) =[B] σ(t2)` -/
def Problem.unifies (problem : Problem α Γ) (γ : Γ)
    : Prop :=
  problem.lhs γ = problem.rhs γ

-- Note: should i separate out substitution for ceritifcation etc?
inductive Unifier (Γ : Type v) : Type (max v (x + 1)) where
  | subst (γ : Γ) : Unifier Γ
  | bind {A : Type x} (closure : A → Unifier Γ) : Unifier Γ
    -- e.g., `.bind (fun u => .subst { X := f u, Y := u })` for `X ↦ f(U), Y ↦ U`

-- Note: should i eliminate Γ?
abbrev UnifierSet (Γ : Type v) := List (Unifier.{v, x} Γ)




/- σ.Covers γ iff γ ∈ σ -/
def Unifier.Covers : Unifier Γ → Γ → Prop
  | .subst γ', γ => γ = γ'
  | .bind fresh, γ => ∃ u, (fresh u).Covers γ

/- this will be the main judgment for our certification calculus -/
-- Σ covers γ
def UnifierSet.Covers (unifiers : UnifierSet Γ) (γ : Γ) : Prop :=
  ∃ σ, σ ∈ unifiers ∧ σ.Covers γ

/- this will be the main judgment for our certification calculus -/
def UnifierSet.Complete (problem : Problem α Γ) (solutions : UnifierSet Γ) : Prop :=
  ∀ γ, problem.unifies γ → solutions.Covers γ
-- for any γ s.t. `γ(t1) =[B] γ(t2)`, ∃ σ ∈ solutions, σ covers γ modulo R`
-- With quotient-valued sorts, the old B and R comparisons are ordinary equality.

/-- Every instance of this proposed unifier solves the native equation. -/
def Unifier.Sound (problem : Problem α Γ) : Unifier Γ → Prop
  | .subst γ => problem.unifies γ
  | .bind fresh => ∀ value, (fresh value).Sound problem

/-- No proposed unifier produces a nonsolution. -/
def UnifierSet.Sound (problem : Problem α Γ) (solutions : UnifierSet Γ) : Prop :=
  ∀ σ, σ ∈ solutions → σ.Sound problem





-- i don't think this make sense at all;
/-- Apply a native body to every substitution image, preserving fresh binders.
e.g.,
`x1 ↦ f(u), x2 ↦ u` becomes `x1 ↦ f(p(u)), x2 ↦ p(u)` for `p : α → β`.
`σ = .bind (fun u => .subst (f u, u))` becomes `.bind (fun u => .subst (p (f u) u))`.
by `closure = fun (x, y) => p x y`
-/
def Unifier.apply {β : Type y} (σ : Unifier.{v, x} Γ) (closure : Γ → β)
    : Unifier.{y, x} β :=
  match σ with
  | .subst γ => .subst (closure γ)
  | .bind fresh => .bind (fun value => (fresh value).apply closure)
end Unification
