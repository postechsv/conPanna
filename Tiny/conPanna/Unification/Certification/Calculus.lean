import Tiny.conPanna.Unification.Certification.Judgment
import Tiny.conPanna.Unification.Certification.Multiset

/-!
The surface rules of the certification calculus, one theorem per rule of the
paper draft: DECOMP (also DELETE), CLASH (also OCCURS, DISTINCT), ELIM,
IDENTIFY, SOLVE, and COVER (`cover`, in Judgment.lean).

Variables are the components of the context tuple `Γ`. ELIM and SOLVE change
the context: ELIM removes a variable, SOLVE replaces bag variables by fresh ones.
Current Lean restriction: SOLVE takes ONE bag equation (the paper allows a system).
-/

namespace Unification.Certification

universe v w w' x y

variable {Γ₀ : Type v} {Γ : Type w} {answers : UnifierSet.{v, x} Γ₀}

/-! ## Free part and identification -/

/-- DECOMP (and DELETE): replace the pending equations by consequences of them,
e.g. `f(s⃗) = f(t⃗)` by `s⃗ = t⃗` for a free constructor `f`. -/
theorem decomp {s : State Γ₀ Γ} (E' : Γ → Prop) (h : ∀ ρ, s.E ρ → E' ρ)
    (next : { s with E := E' } ⊩ answers) : s ⊩ answers :=
  fun ρ hE hD => next ρ (h ρ hE) hD

/-- CLASH (and OCCURS, DISTINCT): the pending constraints are contradictory. -/
theorem clash {s : State Γ₀ Γ} (h : ∀ ρ, s.E ρ → s.D ρ → False) : s ⊩ answers :=
  close h

/-- ELIM `V := t`: every solution has the form `f ρ'`, where `f` puts `t` in
place of `V`. The variable leaves the context and is substituted into `α`. -/
theorem elim {Γ' : Type w'} {s : State Γ₀ Γ} (f : Γ' → Γ) (E' : Γ' → Prop)
    (h : ∀ ρ, s.E ρ → ∃ ρ', ρ = f ρ' ∧ E' ρ')
    (next : (⟨s.α ∘ f, E', s.D ∘ f⟩ : State Γ₀ Γ') ⊩ answers) : s ⊩ answers := by
  intro ρ hE hD
  obtain ⟨ρ', rfl, hE'⟩ := h ρ hE
  exact next ρ' hE' hD

/-- IDENTIFY two aliens: either they are equal (a new equation) or different
(a new disequation). -/
theorem identify {T : Sort y} {s : State Γ₀ Γ} (a b : Γ → T)
    (eq : { s with E := fun ρ => s.E ρ ∧ a ρ = b ρ } ⊩ answers)
    (ne : { s with D := fun ρ => s.D ρ ∧ a ρ ≠ b ρ } ⊩ answers) : s ⊩ answers := by
  intro ρ hE hD
  by_cases h : a ρ = b ρ
  · exact eq ρ ⟨hE, h⟩ hD
  · exact ne ρ hE ⟨hD, h⟩

/-! ## SOLVE

One bag equation over bag variables `V : Fin n → ACU El` and alien classes
`a : Fin m → El`:
  `Σᵢ L i • V i + Σ_c La c • {a c}  =  Σᵢ R i • V i + Σ_c Ra c • {a c}`.
At an element equal to alien `a c`, the count vector `v` satisfies
`L·v + La c = R·v + Ra c`; at every other element, `L·v = R·v`.
-/

/-- `k • X`: `k` copies of `X`. -/
def copies {El : Type y} : ℕ → ACU El → ACU El
  | 0, _ => ∅
  | k + 1, X => X + copies k X

/-- `Σ_j f j`. -/
def sum {El : Type y} {k : ℕ} (f : Fin k → ACU El) : ACU El :=
  (List.ofFn f).foldr (· + ·) ∅

/-- One side of a bag equation: `Σᵢ L i • V i + Σ_c La c • {a c}`. -/
def side {El : Type y} {n m : ℕ} (L : Fin n → ℕ) (V : Fin n → ACU El)
    (La : Fin m → ℕ) (a : Fin m → El) : ACU El :=
  sum (fun i => copies (L i) (V i)) + sum (fun c => copies (La c) {a c})

/-- `L · v`. -/
def dot {n : ℕ} (L v : Fin n → ℕ) : ℕ := (List.ofFn fun i => L i * v i).sum

/-- Component-wise `p ≤ v`. -/
def Below {n : ℕ} (p v : Fin n → ℕ) : Prop := ∀ i, p i ≤ v i

/-- All choices of one particular solution per alien class. -/
def choices {n : ℕ} : {m : ℕ} → (Fin m → List (Fin n → ℕ)) → List (Fin m → Fin n → ℕ)
  | 0, _ => [Fin.elim0]
  | _ + 1, P => (P 0).flatMap fun p => (choices (fun c => P c.succ)).map fun π => Fin.cases p π

/-- The substitution `θ_π`: `V i := Σ_c π c i • {a c} + Σ_j B j i • U j`. -/
def theta {El : Type y} {n m k : ℕ} (a : Fin m → El) (π : Fin m → Fin n → ℕ)
    (B : Fin k → Fin n → ℕ) (U : Fin k → ACU El) : Fin n → ACU El :=
  fun i => sum (fun c => copies (π c i) {a c}) + sum (fun j => copies (B j i) (U j))

/-- SOLVE for one bag equation.

* `V`, `rest`, `glue` split the context into the bag variables and the rest.
* `a` gives the alien class representatives; aliens depend only on the rest.
* `hE` reads the constraints: the bag equation (as coefficients `L R La Ra`),
  the remaining equations `E'`, and pairwise distinct alien classes.
* `P` (particular solutions per class) and `B` (basis) are the data, read off the
  answers; `S1`–`S3` are the side conditions.
* One premise per choice `π`: the bag variables become `θ_π`, over the rest
  plus fresh bags `U! : Fin k → ACU El`. -/
theorem solve {El : Type y} {Γr : Type w'} {n m k : ℕ} {s : State Γ₀ Γ}
    (V : Γ → Fin n → ACU El) (rest : Γ → Γr) (glue : Γr → (Fin n → ACU El) → Γ)
    (hglue : ∀ ρ, glue (rest ρ) (V ρ) = ρ)
    (a : Γr → Fin m → El) (L R : Fin n → ℕ) (La Ra : Fin m → ℕ) (E' : Γr → Prop)
    (hE : ∀ ρ, s.E ρ → s.D ρ →
      side L (V ρ) La (a (rest ρ)) = side R (V ρ) Ra (a (rest ρ)) ∧ E' (rest ρ) ∧
      ∀ c c', c ≠ c' → a (rest ρ) c ≠ a (rest ρ) c')
    (P : Fin m → List (Fin n → ℕ)) (B : Fin k → Fin n → ℕ)
    (S1p : ∀ c, ∀ p ∈ P c, dot L p + La c = dot R p + Ra c)
    (S1b : ∀ j, dot L (B j) = dot R (B j))
    (S2 : ∀ c v, dot L v + La c = dot R v + Ra c → ∃ p ∈ P c, Below p v)
    (S3 : ∀ v, dot L v = dot R v → (∃ i, v i ≠ 0) → ∃ j, Below (B j) v)
    (next : ∀ π ∈ choices P,
      (⟨fun (r, U) => s.α (glue r (theta (a r) π B U)), fun (r, _) => E' r,
        fun (r, U) => s.D (glue r (theta (a r) π B U))⟩ :
        State Γ₀ (Γr × (Fin k → ACU El))) ⊩ answers) :
    s ⊩ answers := by
  -- To be ported from the prototype: peel the particular parts (S2, S1p), then
  -- basis vectors (S3, S1b), as in `Basis.particular` and `Basis.decompose`.
  sorry

end Unification.Certification
