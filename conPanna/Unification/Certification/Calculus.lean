import conPanna.Unification.Certification.Judgment
import conPanna.Unification.Certification.Solve

/-!
The rules of the certification calculus for the free part, one theorem per rule of the
derivation format (documentation/derivation-format.md). Each rule acts on the first pending
equation `e` of a state `⟨α ; e :: E ; D⟩`:

| UDF rule                | Lean                    | first equation `e`, and what replaces it         |
|-------------------------|-------------------------|--------------------------------------------------|
| `delete`                | `delete`                | `t = t`; dropped                                 |
| `decomp`                | `decomp`                | `f(s₁,…,sₙ) = f(t₁,…,tₙ)`; replaced by `sᵢ = tᵢ` |
| `elim`                  | `elim`                  | `V = t`; dropped, `V := t` substituted           |
| `clash`, `occurs`, `ground` | `clash`             | (none) the constraints are contradictory         |
| `cover`                 | `cover` (Judgment.lean) | (none) one unifier covers every solution         |
| `acu-solve`             | `acu_solve` (AcuSolve.lean) | a system of bag equations                    |

Not rules of the format: `rename` (present a state over another context) and the
generic `transfer` and `close` (Judgment.lean) that every rule instantiates; `restate`
(AcuSolve.lean) states the pending equations in another form.

Variables are the components of the context tuple `Γ`. ELIM and ACU-SOLVE change the
context: ELIM removes a variable, ACU-SOLVE replaces bag variables by fresh ones; the
state is carried over by `State.subst`. `Split` names the bag variables of a system.
-/

namespace Unification.Certification

universe v w w' x y

variable {Γ₀ : Type v} {Γ : Type w} {unifiers : UnifierSet.{v, x} Γ₀}
  {α : Γ → Γ₀} {e : Γ → Prop} {E : List (Γ → Prop)} {D : Γ → Prop}

/-! ## Free part -/

/-- DELETE `t = t`. Dropping an equation only adds solutions to cover, so the rule needs
no proof that `e` is trivial. -/
theorem delete (next : ⟨α, E, D⟩ ⊩ unifiers) : ⟨α, e :: E, D⟩ ⊩ unifiers :=
  fun ρ hE hD => next ρ hE.2 hD

/-- DECOMP `f(s₁,…,sₙ) = f(t₁,…,tₙ)` into `s₁ = t₁, …, sₙ = tₙ`, the equations `es`. -/
theorem decomp (es : List (Γ → Prop)) (h : ∀ ρ, e ρ → Eqs es ρ)
    (next : ⟨α, es ++ E, D⟩ ⊩ unifiers) : ⟨α, e :: E, D⟩ ⊩ unifiers :=
  fun ρ hE hD => next ρ ((eqs_append es E ρ).2 ⟨h ρ hE.1, hE.2⟩) hD

/-- ELIM `V = t`: every solution has the form `f ρ'`, where `f` puts `t` in place
of `V`. The variable leaves the context and is substituted into the state. -/
theorem elim {Γ' : Type w'} (f : Γ' → Γ) (h : ∀ ρ, e ρ → ∃ ρ', ρ = f ρ')
    (next : (⟨α, E, D⟩ : State Γ₀ Γ).subst f ⊩ unifiers) : ⟨α, e :: E, D⟩ ⊩ unifiers := by
  intro ρ hE hD
  obtain ⟨ρ', rfl⟩ := h ρ hE.1
  exact next ρ' ((eqs_map f E ρ').2 hE.2) hD

/-- CLASH (and OCCURS, DISTINCT): the pending constraints are contradictory. -/
theorem clash {s : State Γ₀ Γ} (h : ∀ ρ, Eqs s.E ρ → s.D ρ → False) : s ⊩ unifiers :=
  close h

/-! ## Bag variables -/

/-- The context split into the bag variables `V : Fin n → ACU El` of a bag
equation and the rest `Γr`, with `glue` putting them back together. For tuples of
variables, `hglue` holds by `rfl` and need not be given. -/
structure Split (El : Type y) (Γ : Type w) (Γr : Type w') (n : ℕ) where
  V : Γ → Fin n → ACU El
  rest : Γ → Γr
  glue : Γr → (Fin n → ACU El) → Γ
  hglue : ∀ ρ, glue (rest ρ) (V ρ) = ρ := by intro; rfl

/-! ## Bookkeeping -/

/-- Not a rule of the paper: present the same state over another context, related
by `f` with a right inverse `g`. Used to unpack SOLVE's fresh block
`Z : Fin k → ACU El` into named variables `Z1, …, Zk`. -/
theorem rename {Γ' : Type w'} {s : State Γ₀ Γ} (f : Γ' → Γ) (g : Γ → Γ')
    (hfg : ∀ ρ, f (g ρ) = ρ) (next : s.subst f ⊩ unifiers) : s ⊩ unifiers := by
  intro ρ hE hD
  have h := next (g ρ) ((eqs_map f s.E (g ρ)).2 (by rw [hfg]; exact hE))
    (show s.D (f (g ρ)) by rw [hfg]; exact hD)
  show ∃ σ ∈ unifiers, covers σ (s.α ρ)
  have : s.α (f (g ρ)) = s.α ρ := by rw [hfg]
  exact this ▸ h

end Unification.Certification
