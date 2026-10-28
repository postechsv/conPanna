import conPanna.Unification.Unification

/-!
The certification judgment `⟨α ; E ; D⟩ ⊩ unifiers`.

A state describes the solutions still to be covered: every valuation `ρ` of the
fresh variables `Γ` that satisfies the pending equations `E` and disequations `D`
yields the solution `α ρ` of the original variables. The judgment says every
such solution is covered by the given unifiers. `E` is a list, and the rules act
on its first equation, as in the paper.

States are semantic: an external tool need not produce them, as long as its
derivation can be replayed as applications of the rules, all of which are
instances of `transfer` and `close` below.
-/

namespace Unification.Certification

universe u v w w' x

/-- `ρ` satisfies every equation of `E`. -/
def Eqs {Γ : Type w} (E : List (Γ → Prop)) (ρ : Γ) : Prop :=
  E.foldr (fun e p => e ρ ∧ p) True

/-- A state `⟨α ; E ; D⟩` over fresh variables `Γ`, for original variables `Γ₀`. -/
structure State (Γ₀ : Type v) (Γ : Type w) where
  α : Γ → Γ₀
  E : List (Γ → Prop)
  D : Γ → Prop := fun _ => True

variable {α : Type u} {Γ₀ : Type v} {Γ Γ' : Type w}

/-- `⟨α ; E ; D⟩ ⊩ unifiers`: every solution described by the state is covered. -/
def State.Holds (s : State Γ₀ Γ) (unifiers : UnifierSet.{v, x} Γ₀) : Prop :=
  ∀ ρ, Eqs s.E ρ → s.D ρ → ∃ σ ∈ unifiers, covers σ (s.α ρ)

@[inherit_doc] infix:50 " ⊩ " => State.Holds

/-- `⟨αf ; Ef ; Df⟩`: the state over a new context, related to the old one by `f`. -/
def State.subst {Γ' : Type w'} (s : State Γ₀ Γ) (f : Γ' → Γ) : State Γ₀ Γ' :=
  ⟨s.α ∘ f, s.E.map (· ∘ f), s.D ∘ f⟩

/-- The initial state `⟨id ; E₀ ; ∅⟩` of a problem. -/
def State.start (problem : Problem α Γ₀) : State Γ₀ Γ₀ where
  α := id
  E := [unifiedBy problem]

theorem eqs_append (E E' : List (Γ → Prop)) (ρ : Γ) : Eqs (E ++ E') ρ ↔ Eqs E ρ ∧ Eqs E' ρ := by
  induction E with
  | nil => exact ⟨fun h => ⟨trivial, h⟩, fun h => h.2⟩
  | cons e E ih => exact (and_congr Iff.rfl ih).trans and_assoc.symm

theorem eqs_map {Γ' : Type w'} (f : Γ' → Γ) (E : List (Γ → Prop)) (ρ : Γ') :
    Eqs (E.map (· ∘ f)) ρ ↔ Eqs E (f ρ) := by
  induction E with
  | nil => exact Iff.rfl
  | cons e E ih => exact and_congr Iff.rfl ih

/-- The initial judgment is exactly completeness of the unifiers. -/
theorem start_iff (problem : Problem α Γ₀) (unifiers : UnifierSet.{v, x} Γ₀) :
    State.start problem ⊩ unifiers ↔ complete problem unifiers :=
  ⟨fun h γ hγ => h γ ⟨hγ, trivial⟩ trivial, fun h ρ hρ _ => h ρ hρ.1⟩

variable {unifiers : UnifierSet.{v, x} Γ₀}

/-- Every non-closing rule is an instance of this: each solution of the
conclusion state is a solution of some premise state, with the same image. -/
theorem transfer {ι : Type} {s : State Γ₀ Γ} (premise : ι → State Γ₀ Γ')
    (step : ∀ ρ, Eqs s.E ρ → s.D ρ →
      ∃ i ρ', s.α ρ = (premise i).α ρ' ∧ Eqs (premise i).E ρ' ∧ (premise i).D ρ')
    (h : ∀ i, premise i ⊩ unifiers) : s ⊩ unifiers := by
  intro ρ hE hD
  obtain ⟨i, ρ', hα, hE', hD'⟩ := step ρ hE hD
  rw [hα]
  exact h i ρ' hE' hD'

/-- A state with no solutions holds trivially. -/
theorem close {s : State Γ₀ Γ} (h : ∀ ρ, Eqs s.E ρ → s.D ρ → False) : s ⊩ unifiers :=
  fun ρ hE hD => (h ρ hE hD).elim

/-- A state holds if one unifier covers all its solutions, with a witness
computed from the fresh variables. -/
theorem cover {s : State Γ₀ Γ} (σ : Unifier.{v, x} Γ₀) (mem : σ ∈ unifiers)
    (h : ∀ ρ, Eqs s.E ρ → s.D ρ → covers σ (s.α ρ)) : s ⊩ unifiers :=
  fun ρ hE hD => ⟨σ, mem, h ρ hE hD⟩

end Unification.Certification
