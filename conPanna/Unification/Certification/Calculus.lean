import conPanna.Unification.Certification.Judgment
import conPanna.Unification.Certification.Solve

/-!
The surface rules of the certification calculus, one theorem per rule of the
paper draft: DECOMP (also DELETE), CLASH (also OCCURS, DISTINCT), ELIM,
IDENTIFY, SOLVE, and COVER (`cover`, in Judgment.lean).

Variables are the components of the context tuple `Γ`. ELIM and SOLVE change
the context: ELIM removes a variable, SOLVE replaces bag variables by fresh ones.
SOLVE takes one bag equation; its data and validity are in Solve.lean.
-/

namespace Unification.Certification

universe v w w' x y

variable {Γ₀ : Type v} {Γ : Type w} {unifiers : UnifierSet.{v, x} Γ₀}

/-! ## Free part and identification -/

/-- DECOMP (and DELETE): replace the pending equations by consequences of them,
e.g. `f(s⃗) = f(t⃗)` by `s⃗ = t⃗` for a free constructor `f`. -/
theorem decomp {s : State Γ₀ Γ} (E' : Γ → Prop) (h : ∀ ρ, s.E ρ → E' ρ)
    (next : { s with E := E' } ⊩ unifiers) : s ⊩ unifiers :=
  fun ρ hE hD => next ρ (h ρ hE) hD

/-- CLASH (and OCCURS, DISTINCT): the pending constraints are contradictory. -/
theorem clash {s : State Γ₀ Γ} (h : ∀ ρ, s.E ρ → s.D ρ → False) : s ⊩ unifiers :=
  close h

/-- ELIM `V := t`: every solution has the form `f ρ'`, where `f` puts `t` in
place of `V`. The variable leaves the context and is substituted into `α`. -/
theorem elim {Γ' : Type w'} {s : State Γ₀ Γ} (f : Γ' → Γ) (E' : Γ' → Prop)
    (h : ∀ ρ, s.E ρ → ∃ ρ', ρ = f ρ' ∧ E' ρ')
    (next : (⟨s.α ∘ f, E', s.D ∘ f⟩ : State Γ₀ Γ') ⊩ unifiers) : s ⊩ unifiers := by
  intro ρ hE hD
  obtain ⟨ρ', rfl, hE'⟩ := h ρ hE
  exact next ρ' hE' hD

/-- IDENTIFY two aliens: either they are equal (a new equation) or different
(a new disequation). -/
theorem identify {T : Sort y} {s : State Γ₀ Γ} (a b : Γ → T)
    (eq : { s with E := fun ρ => s.E ρ ∧ a ρ = b ρ } ⊩ unifiers)
    (ne : { s with D := fun ρ => s.D ρ ∧ a ρ ≠ b ρ } ⊩ unifiers) : s ⊩ unifiers := by
  intro ρ hE hD
  by_cases h : a ρ = b ρ
  · exact eq ρ ⟨hE, h⟩ hD
  · exact ne ρ hE ⟨hD, h⟩

/-! ## SOLVE -/

/-- SOLVE for one bag equation.

* `V`, `rest`, `glue` split the context into the bag variables and the rest.
* `a` gives the alien class representatives; aliens depend only on the rest.
* `cp` is the compatibility relation on classes; incompatible classes are
  different (`hE`), and S2 is required for every clique of compatible classes.
* `P` (particular solutions per class) and `B` (basis) are the data, read off
  the unifiers; `S0`–`S3` are the side conditions.
* `E'` are the remaining equations, over the whole context.
* One premise per choice `π`: the bag variables become `θ_π` in the images, the
  remaining equations and the disequations (the paper's `αθ_π; E'θ_π; Dθ_π`),
  over the rest plus fresh bags `Z : Fin k → ACU El`. -/
theorem solve {El : Type y} {Γr : Type w'} {n m k : ℕ} {s : State Γ₀ Γ}
    (V : Γ → Fin n → ACU El) (rest : Γ → Γr) (glue : Γr → (Fin n → ACU El) → Γ)
    (hglue : ∀ ρ, glue (rest ρ) (V ρ) = ρ)
    (a : Γr → Fin m → El) (L R : Fin n → ℕ) (La Ra : Fin m → ℕ) (E' : Γ → Prop)
    (cp : Fin m → Fin m → Bool)
    (hE : ∀ ρ, s.E ρ → s.D ρ →
      side L (V ρ) La (a (rest ρ)) = side R (V ρ) Ra (a (rest ρ)) ∧ E' ρ ∧
      ∀ c c', c ≠ c' → cp c c' = false → a (rest ρ) c ≠ a (rest ρ) c')
    (P : Fin m → List (Fin n → ℕ)) (B : Fin k → Fin n → ℕ)
    (S0 : ∀ j, ∃ i, B j i ≠ 0)
    (S1p : ∀ c, ∀ p ∈ P c, dot L p + La c = dot R p + Ra c)
    (S1b : ∀ j, dot L (B j) = dot R (B j))
    (S2 : ∀ G ∈ cliques cp, ∀ v, dot L v + (G.map La).sum = dot R v + (G.map Ra).sum →
      ∃ π : Fin m → Fin n → ℕ, (∀ c ∈ G, π c ∈ P c) ∧
        Below (fun i => (G.map fun c => π c i).sum) v)
    (S3 : ∀ v, dot L v = dot R v → (∃ i, v i ≠ 0) → ∃ j, Below (B j) v)
    (next : ∀ π ∈ choices P,
      (⟨fun (r, U) => s.α (glue r (theta (a r) π B U)), fun (r, U) => E' (glue r (theta (a r) π B U)),
        fun (r, U) => s.D (glue r (theta (a r) π B U))⟩ :
        State Γ₀ (Γr × (Fin k → ACU El))) ⊩ unifiers) :
    s ⊩ unifiers := by
  intro ρ hEρ hDρ
  obtain ⟨heq, hE', hinc⟩ := hE ρ hEρ hDρ
  obtain ⟨π, hπ, U, hU⟩ := solve_decomp (V ρ) (a (rest ρ)) L R La Ra cp heq hinc P B
    S0 S1p S1b S2 S3
  have hρ : ρ = glue (rest ρ) (theta (a (rest ρ)) π B U) := by rw [← hU, hglue]
  have := next π hπ (rest ρ, U) (by show E' _; rw [← hρ]; exact hE') (by show s.D _; rw [← hρ]; exact hDρ)
  rw [hρ]
  exact this

/-! ## Bookkeeping -/

/-- Not a rule of the paper: present the same state over another context, related
by `f` with a right inverse `g`. Used to unpack SOLVE's fresh block
`Z : Fin k → ACU El` into named variables `Z1, …, Zk`. -/
theorem rename {Γ' : Type w'} {s : State Γ₀ Γ} (f : Γ' → Γ) (g : Γ → Γ')
    (hfg : ∀ ρ, f (g ρ) = ρ)
    (next : (⟨s.α ∘ f, s.E ∘ f, s.D ∘ f⟩ : State Γ₀ Γ') ⊩ unifiers) : s ⊩ unifiers := by
  intro ρ hE hD
  have h := next (g ρ) (by show s.E (f (g ρ)); rw [hfg]; exact hE)
    (by show s.D (f (g ρ)); rw [hfg]; exact hD)
  show ∃ σ ∈ unifiers, covers σ (s.α ρ)
  have : s.α (f (g ρ)) = s.α ρ := by rw [hfg]
  exact this ▸ h

end Unification.Certification
