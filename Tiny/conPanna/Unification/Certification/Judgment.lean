import Tiny.conPanna.Unification.Problem

/-!
The certification judgment `⟨α ; E ; D⟩ ⊩ answers`.

A state describes the solutions still to be covered: every valuation `ρ` of the
fresh variables `Γ` that satisfies the pending equations `E` and disequations `D`
yields the solution `α ρ` of the original variables. The judgment says every
such solution is covered by the given answers.

States are semantic: an external tool need not produce them, as long as its
derivation can be replayed as applications of the rules, all of which are
instances of `transfer` and `close` below.
-/

namespace Unification.Certification

universe u v w x

/-- A state `⟨α ; E ; D⟩` over fresh variables `Γ`, for original variables `Γ₀`. -/
structure State (Γ₀ : Type v) where
  Γ : Type w
  α : Γ → Γ₀
  E : Γ → Prop
  D : Γ → Prop := fun _ => True

variable {α : Type u} {Γ₀ : Type v}

/-- `⟨α ; E ; D⟩ ⊩ answers`: every solution described by the state is covered. -/
def State.Holds (s : State.{v, w} Γ₀) (answers : UnifierSet.{v, x} Γ₀) : Prop :=
  ∀ ρ, s.E ρ → s.D ρ → answers.Covers (s.α ρ)

@[inherit_doc] infix:50 " ⊩ " => State.Holds

/-- The initial state `⟨id ; E₀ ; ∅⟩` of a problem. -/
def State.start (problem : Problem α Γ₀) : State.{v, v} Γ₀ where
  Γ := Γ₀
  α := id
  E := problem.unifies

/-- The initial judgment is exactly completeness of the answers. -/
theorem start_iff (problem : Problem α Γ₀) (answers : UnifierSet.{v, x} Γ₀) :
    State.start problem ⊩ answers ↔ answers.Complete problem :=
  ⟨fun h γ hγ => h γ hγ trivial, fun h ρ hρ _ => h ρ hρ⟩

variable {answers : UnifierSet.{v, x} Γ₀}

/-- Every non-closing rule is an instance of this: each solution of the
conclusion state is a solution of some premise state, with the same image. -/
theorem transfer {ι : Type} {s : State.{v, w} Γ₀} (premise : ι → State.{v, w} Γ₀)
    (step : ∀ ρ, s.E ρ → s.D ρ →
      ∃ i ρ', s.α ρ = (premise i).α ρ' ∧ (premise i).E ρ' ∧ (premise i).D ρ')
    (h : ∀ i, premise i ⊩ answers) : s ⊩ answers := by
  intro ρ hE hD
  obtain ⟨i, ρ', hα, hE', hD'⟩ := step ρ hE hD
  rw [hα]
  exact h i ρ' hE' hD'

/-- A state with no solutions holds trivially. -/
theorem close {s : State.{v, w} Γ₀} (h : ∀ ρ, s.E ρ → s.D ρ → False) : s ⊩ answers :=
  fun ρ hE hD => (h ρ hE hD).elim

/-- A state holds if one answer covers all its solutions, with a witness
computed from the fresh variables. -/
theorem cover {s : State.{v, w} Γ₀} (σ : Unifier.{v, x} Γ₀) (mem : σ ∈ answers)
    (h : ∀ ρ, s.E ρ → s.D ρ → σ.Covers (s.α ρ)) : s ⊩ answers :=
  fun ρ hE hD => ⟨σ, mem, h ρ hE hD⟩

end Unification.Certification
