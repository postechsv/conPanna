namespace Unification

universe u v w x

-- meaning `t1[Γ] =B? t2[Γ]` the B-unification problem
-- e.g., { X := x, Y := y } : Γ (user provides x, y from their own context)
-- Γ → α is the type of α-terms with free variables in dom(Γ)
-- TODO: shouldn't it also be parameterized by B?
structure Problem (α : Type u) (Γ : Type v) where
  lhs : Γ → α
  rhs : Γ → α

-- abbrev ProblemSet (α : Type u) (Vars : Type v) := List (Problem α Vars)
-- this cannot encode many sorted problems; all are α

variable {α : Type u} {Γ : Type v}

/- meaning `σ(t1) =[B] σ(t2)` -/
def Problem.unifies (problem : Problem α Γ) (B : α → α → Prop) (γ : Γ)
    : Prop :=
  B (problem.lhs γ) (problem.rhs γ)

-- TODO: should i separate out substitution for ceritifcation etc?
inductive Unifier (Γ : Type v) : Type (max v (w + 1)) where
  | subst (γ : Γ) : Unifier Γ
  | bind {A : Type w} (closure : A → Unifier Γ) : Unifier Γ
    -- e.g., `.bind (fun u => .subst { X := f u, Y := u })` for `X ↦ f(U), Y ↦ U`

-- TODO: should i eliminate Γ?
abbrev UnifierSet (Γ : Type v) := List (Unifier.{v, w} Γ)




/-- `R` compares original assignments variable-by-variable modulo their sort's laws.
It is NOT merely equality of the two problem terms. Bindings are existential here.
-/
def Unifier.Covers (R : Γ → Γ → Prop) : Unifier Γ → Γ → Prop
  | .subst γ, assignment => R assignment γ
  | .bind fresh, assignment => ∃ value, (fresh value).Covers R assignment

/-- At least one proposed unifier covers this original assignment. -/
def UnifierSet.Covers (R : Γ → Γ → Prop)
    (unifiers : UnifierSet Γ) (assignment : Γ) : Prop :=
  ∃ σ, σ ∈ unifiers ∧ σ.Covers R assignment

/-- No original solution is missed.
`B` compares terms; `R` compares assignments.
For a mixed context, define `R` with the appropriate structural relation per field.
Completeness does not assert that the proposed answers are sound.
-/
def UnifierSet.Complete (B : α → α → Prop) (R : Γ → Γ → Prop)
    (problem : Problem α Γ) (solutions : UnifierSet Γ) : Prop :=
  ∀ γ, problem.unifies B γ → solutions.Covers R γ
-- `σ(t1) =[B] σ(t2)` => ∃ σ' ∈ solutions, σ' covers γ modulo R`






-- i don't think this make sense at all;
/-- Apply a native body to every substitution image, preserving fresh binders.
e.g.,
`x1 ↦ f(u), x2 ↦ u` becomes `x1 ↦ f(p(u)), x2 ↦ p(u)` for `p : α → β`.
`σ = .bind (fun u => .subst (f u, u))` becomes `.bind (fun u => .subst (p (f u) u))`.
by `closure = fun (x, y) => p x y`
-/
def Unifier.apply {β : Type x} (σ : Unifier.{v, w} Γ) (closure : Γ → β)
    : Unifier.{x, w} β :=
  match σ with
  | .subst γ => .subst (closure γ)
  | .bind fresh => .bind (fun value => (fresh value).apply closure)
end Unification
