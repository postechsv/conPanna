import conPanna.Unification.Certification.Judgment
import conPanna.Unification.Certification.Solve

/-!
The surface rules of the certification calculus, one theorem per rule of the
paper draft. Each rule acts on the first pending equation `e` of a state
`⟨α ; e :: E ; D⟩`, like the paper's rules on `{s = t} ∪ E`:

| paper            | Lean                 | first equation `e`, and what replaces it        |
|------------------|----------------------|-------------------------------------------------|
| DELETE           | `delete`             | `t = t`; dropped                                |
| DECOMP           | `decomp`             | `f(s⃗) = f(t⃗)`; replaced by `s⃗ = t⃗`             |
| ELIM             | `elim`               | `V = t`; dropped, `V := t` substituted          |
| SOLVE            | `solve`              | a bag equation; dropped, `θ_π` substituted      |
| IDENTIFY         | `identify`           | (none) adds `a = b`, or `a ≠ b` to `D`          |
| CLASH, OCCURS, DISTINCT | `clash`       | (none) the constraints are contradictory        |
| COVER            | `cover` (Judgment.lean) | (none) one unifier covers every solution     |

Not rules of the paper: `rename` (present a state over another context) and the
generic `transfer` and `close` (Judgment.lean) that every rule instantiates.

Variables are the components of the context tuple `Γ`. ELIM and SOLVE change the
context: ELIM removes a variable, SOLVE replaces bag variables by fresh ones; the
state is carried over by `State.subst`. SOLVE's data and validity are in Solve.lean.
-/

namespace Unification.Certification

universe v w w' x y

variable {Γ₀ : Type v} {Γ : Type w} {unifiers : UnifierSet.{v, x} Γ₀}
  {α : Γ → Γ₀} {e : Γ → Prop} {E : List (Γ → Prop)} {D : Γ → Prop}

/-! ## Free part and identification -/

/-- DELETE `t = t`. Dropping an equation only adds solutions to cover, so the rule needs
no proof that `e` is trivial. -/
theorem delete (next : ⟨α, E, D⟩ ⊩ unifiers) : ⟨α, e :: E, D⟩ ⊩ unifiers :=
  fun ρ hE hD => next ρ hE.2 hD

/-- DECOMP `f(s⃗) = f(t⃗)` into `s⃗ = t⃗`, the equations `es`. -/
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

/-- IDENTIFY two aliens: either they are equal (a new equation) or different
(a new disequation). -/
theorem identify {T : Sort y} (a b : Γ → T)
    (eq : ⟨α, (fun ρ => a ρ = b ρ) :: E, D⟩ ⊩ unifiers)
    (ne : ⟨α, E, fun ρ => D ρ ∧ a ρ ≠ b ρ⟩ ⊩ unifiers) : ⟨α, E, D⟩ ⊩ unifiers := by
  intro ρ hE hD
  by_cases h : a ρ = b ρ
  · exact eq ρ ⟨h, hE⟩ hD
  · exact ne ρ hE ⟨hD, h⟩

/-! ## SOLVE -/

/-- The context split into the bag variables `V : Fin n → ACU El` of a bag
equation and the rest `Γr`, with `glue` putting them back together. For tuples of
variables, `hglue` holds by `rfl` and need not be given. -/
structure Split (El : Type y) (Γ : Type w) (Γr : Type w') (n : ℕ) where
  V : Γ → Fin n → ACU El
  rest : Γ → Γr
  glue : Γr → (Fin n → ACU El) → Γ
  hglue : ∀ ρ, glue (rest ρ) (V ρ) = ρ := by intro; rfl

/-- A bag equation `Σᵢ L i • X i + Σ_c La c • {a c} = Σᵢ R i • X i + Σ_c Ra c • {a c}`
over bag variables `X` and aliens `a : Fin m → El`, with the pairs of `compatible`
aliens (which may denote the same element). -/
structure BagEq (n m : ℕ) where
  L : Fin n → ℕ
  R : Fin n → ℕ
  La : Fin m → ℕ
  Ra : Fin m → ℕ
  compatible : List (Fin m × Fin m) := []

/-- Compatibility as a relation: `c` and `c'` are listed as a pair, in either order. -/
def BagEq.cp {n m : ℕ} (q : BagEq n m) (c c' : Fin m) : Bool :=
  q.compatible.any fun (i, j) => (i == c && j == c') || (i == c' && j == c)

/-- The bag equation holds for the bags `X` and aliens `a`. -/
def BagEq.Holds {El : Type y} {n m : ℕ} (q : BagEq n m) (X : Fin n → ACU El)
    (a : Fin m → El) : Prop :=
  side q.L X q.La a = side q.R X q.Ra a

/-- Incompatible aliens are different. -/
def BagEq.Distinct {El : Type y} {n m : ℕ} (q : BagEq n m) (a : Fin m → El) : Prop :=
  ∀ c c', c ≠ c' → q.cp c c' = false → a c ≠ a c'

/-- SOLVE's data: particular solutions `P` per alien, and the basis `B`. -/
structure SolveData (n m k : ℕ) where
  P : Fin m → List (Fin n → ℕ)
  B : Fin k → Fin n → ℕ

/-- The side conditions (S0)–(S3) of the data for a bag equation. -/
structure SolveData.Valid {n m k : ℕ} (q : BagEq n m) (d : SolveData n m k) : Prop where
  S0 : ∀ j, ∃ i, d.B j i ≠ 0
  S1p : ∀ c, ∀ p ∈ d.P c, dot q.L p + q.La c = dot q.R p + q.Ra c
  S1b : ∀ j, dot q.L (d.B j) = dot q.R (d.B j)
  S2 : ∀ G ∈ cliques q.cp, ∀ v, dot q.L v + (G.map q.La).sum = dot q.R v + (G.map q.Ra).sum →
    ∃ π : Fin m → Fin n → ℕ, (∀ c ∈ G, π c ∈ d.P c) ∧
      Below (fun i => (G.map fun c => π c i).sum) v
  S3 : ∀ v, dot q.L v = dot q.R v → (∃ i, v i ≠ 0) → ∃ j, Below (d.B j) v

/-- SOLVE the bag equation `e`, with aliens `a` (which depend only on the rest of the
context). One premise per choice `π`: the bag variables become `θ_π`, over the rest
plus fresh bags `Z : Fin k → ACU El`. -/
theorem solve {El : Type y} {Γr : Type w'} {n m k : ℕ} (sp : Split El Γ Γr n)
    (a : Γr → Fin m → El) (q : BagEq n m) (d : SolveData n m k) (valid : d.Valid q)
    (heq : ∀ ρ, e ρ → q.Holds (sp.V ρ) (a (sp.rest ρ)))
    (hdistinct : ∀ ρ, Eqs (e :: E) ρ → D ρ → q.Distinct (a (sp.rest ρ)))
    (next : ∀ π ∈ choices d.P,
      (⟨α, E, D⟩ : State Γ₀ Γ).subst (fun (r, Z) => sp.glue r (theta (a r) π d.B Z)) ⊩ unifiers) :
    ⟨α, e :: E, D⟩ ⊩ unifiers := by
  intro ρ hE hD
  obtain ⟨π, hπ, Z, hZ⟩ := solve_decomp (sp.V ρ) (a (sp.rest ρ)) q.L q.R q.La q.Ra q.cp
    (heq ρ hE.1) (hdistinct ρ hE hD) d.P d.B valid.S0 valid.S1p valid.S1b valid.S2 valid.S3
  have hρ : ρ = sp.glue (sp.rest ρ) (theta (a (sp.rest ρ)) π d.B Z) := by rw [← hZ, sp.hglue]
  have h := next π hπ (sp.rest ρ, Z)
    ((eqs_map _ E _).2 (by show Eqs E (sp.glue _ _); rw [← hρ]; exact hE.2))
    (by show D (sp.glue _ _); rw [← hρ]; exact hD)
  rw [hρ]
  exact h

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
