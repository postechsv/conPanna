# Certification by reflection (design)

Goal: close `complete P U` with one kernel evaluation of a Boolean checker on the UDF
certificate, `check c = true`, plus a theorem proved once: `check c = true → complete P U`.
The surface is unchanged: models, rules and obligations keep their form; the obligations are
closed by `certify_comp` (completeness) and `certify_sound` (soundness, §6).
Same rules as the calculus (documentation/derivation-format.md); only the way they are
applied changes (a proved function instead of a tactic script).

## 1. Data and values

Terms are data: `var x | app f ts | acu f ts` (`x`, `f` numbers). A **model** gives

| field | meaning |
|---|---|
| `T : ℕ → Type`, `dflt s : T s` | the Lean type of each sort |
| `Val := Σ s, T s` | a value with its sort |
| `app f : List Val → Option Val` | free constructor `f`, partial (wrong sorts: `none`) |
| `res f` | the result sort of `f` |
| `elemSort f`, `bagSort f`, `toBag`, `ofBag` | ACU operator `f`: `T (bagSort f) ≃ ACU (T (elemSort f))` |

and laws, proved once per model: `app f xs = some v → v.1 = res f`; injectivity
(`app f xs = app f ys = some v → xs = ys`); distinctness (`app f xs = app g ys = some v →
f = g`); `toBag ∘ ofBag = id`, `ofBag ∘ toBag = id`.

`eval ρ : Term → Option Val`, for a valuation `ρ : ℕ → Val`: a variable is `ρ x`; `app` as
the model says; `acu f [t₁,…,tₖ]` is `c t₁ + (… + c tₖ)` (`∅` for `[]`, `c t` for `[t]`),
where `c t` is `{e}` if `t` evaluates to an element `e` (sort `elemSort f`), the bag if it
evaluates to a bag (sort `bagSort f`), and fails otherwise.

Each term has a syntactic sort (`var x`: the variable's declared sort; `app f`: `res f`;
`acu f`: `bagSort f`). **Typing:** if `ρ` respects the declared sorts (`WS ρ`) and `eval ρ
t = some v`, then `v.1` is the syntactic sort of `t`. No well-typedness of `t` is needed.

**Normal form** `norm`: flatten nested `acu f`, drop `∅`, sort the arguments, and replace
`acu f [t]` by `t` only when `t` has the bag sort (a lone element stays `{t}`: in Lean
`{x} ≠ x`). **Lemma:** `WS ρ → eval ρ (norm t) = eval ρ t` (flattening: `c` of a bag is the
bag; sorting: `+` is commutative; `acu f [t] = t` for bags: `ofBag ∘ toBag = id`).

**Substitution lemma:** `eval ρ t' = some v → eval ρ (t[x := t']) = eval ρ[x ↦ v] t`.
**Locality:** `eval` depends only on the variables that occur.

## 2. The judgment and the rules

A state is `(α, E)`: `α` lists the original variables with terms, `E` the pending
equations. It **holds** if for every `ρ` with `WS ρ` that solves every equation of `E`
(both sides evaluate, to the same value) and evaluates every term of `α`, the values of `α`
decode to a solution covered by some unifier. The checker computes the premise states
itself; each rule is sound by the argument on the right.

| rule | checked | sound because |
|---|---|---|
| `delete i` | sides equal | dropping an equation adds solutions |
| `decomp i` | `app f ss = app f ts`, same length | injectivity: `eval ss = eval ts` |
| `clash i` | `app f ≠ app g` | distinctness |
| `ground i` | a position where constructors differ (recursively) | distinctness, injectivity |
| `elim i x` | one side is `x`; `x` not in the other `t` | `ρ x = eval ρ t`, so `ρ[x ↦ eval t] = ρ`: the same `ρ` solves the premise, same image |
| `cover a w` | `E = []`; `α y = norm (σₐ y)[w]` for every `y`; `w` respects sorts; every binder variable occurs in `σₐ` | the witness values `ν = eval ρ ∘ w` give `a := dec ν` |
| `acu-solve` | §3 | §3 |

Premise states are normalized (`norm` after each substitution), sound by the norm lemma.
Only the terms a substitution changes are renormalized (those holding the eliminated
variable, or a bag variable of the ACU system); the others keep their value as they are.

## 3. `acu-solve` on a single row

The certificate gives unknowns `u₁…u_N` (bag variables of `bagSort f`, or aliens of
`elemSort f`), one row `r` with coefficients in {−1, 0, 1}, a basis and the selections, with
fresh variables. Checked:

0. **Sorts:** both sides of the equation have the bag sort; bag variables have the bag sort,
   aliens the element sort.
1. **Rows:** for every summand term `t` of the equation, `Σ_{j : uⱼ = t} rⱼ = count_L t −
   count_R t`, and every `uⱼ` is a summand. Then for every element `e`, the
   count vector `vⱼ = count_e(c uⱼ)` solves the row: `Σ rⱼ vⱼ = count_e(⟦L⟧) − count_e(⟦R⟧) = 0`.
2. **Basis vectors** are nonzero, solve the row, alien entries ≤ 1.
3. **Completeness (single row, exact):** every `eⱼ` with `rⱼ = 0`, and every `eᵢ + eⱼ` with
   `rᵢ = 1`, `rⱼ = −1`, not two clashing aliens, is above a basis vector. **Why enough:**
   an admissible `v ≠ 0` has some `vₖ ≥ 1`; if `rₖ = 0`, `v ≥ eₖ`; if `rₖ = 1` the row
   forces some `vⱼ ≥ 1` with `rⱼ = −1`, so `v ≥ eₖ + eⱼ`, and these two are not clashing
   aliens (admissible `v` holds at most one of a clashing pair); symmetric for `−1`.
4. **Selections:** the listed ones include every legal one; fresh variables are distinct
   and occur nowhere in the state.

Soundness: as `acu_decomp` — the count vectors are admissible, `decompose` (Solve.lean)
writes the columns as `Σ_t B_t · U_t`, the alien vectors used give a legal selection `S`;
set `ρ' = ρ[Z_k ↦ U_k]` (fresh, so `ρ'` agrees with `ρ` on the state). Then `eval ρ' (θ_S uⱼ) =
ρ uⱼ` for every bag variable, the aliens of each selected vector are equal, and `ρ'`
solves the premise with the same image.

Systems of other shapes (several rows, other coefficients) are not checked: `check` returns
`false`, and `certify_comp` fails.

## 4. Bridge to the obligation

The obligation is `complete (Problem.bind fun γ => (L γ, R γ)) [Unifier.bind body₁, …]` in
the literal form `UdfStore.prepare` gives. With `Tup [s₁,…,sₙ] := T s₁ × … × T sₙ`
(defeq to the user's context tuple), generic `enc : Tup ss → (ℕ → Val)` and `dec`:

* the data terms `L̂`, `R̂`, `σ̂ᵢ` **mirror** the Lean terms node for node (`+`, `∅`, `{x}`,
  constructors, variables), so `eval (enc γ) L̂ = some ⟨s, L γ⟩` holds by `rfl`;
* `dec (enc γ) = γ` (generic), and `WS ν → enc (dec ν) = ν` on the variables (generic).

**Theorem.** `check c = true` and the `rfl` facts give `complete P U`: a solution `γ` gives
`ρ = enc γ` solving the initial state; the derivation reaches a `cover` with `ρ'` whose
`α`-values are those of `γ`; the witness gives `a`, and `body a = γ` by `dec`.

## 5. In Lean

| file | contents |
|---|---|
| `conPanna/Reflect/Core.lean` | data terms, models (`Model`, `Op`, `AcuOp`, laws `Model.Lawful`), evaluation |
| `conPanna/Reflect/Check.lean` | the checker `check` |
| `conPanna/Reflect/Eval.lean` | typing, locality, substitution, normalization, constructors, tuples |
| `conPanna/Reflect/AcuStep.lean`, `conPanna/Reflect/AcuSound.lean` | the ACU step: completeness of one row, the row identity, the step |
| `conPanna/Reflect/Model.lean` | the reflection model of a state type, from its constructor model |
| `conPanna/Reflect/Bridge.lean` | the bridge to the goal (`Bridge`) |
| `conPanna/Reflect/Completeness.lean`, `Soundness.lean` | `complete_of_check`, `sound_of_check` |
| `conPanna/Reflect/Tactic.lean` | `certify_comp`, `certify_sound` |

The model of a state type is generated from the constructor model `#dump_model` writes: one
`Op` per constructor (its function and its inverse, both by pattern matching), a tag per
constructor, and `id` as the bag isomorphism of each ACU sort; each law holds by `rfl`.
`#dump_model T` defines it once (`T.reflect.model`). Each tactic assembles one proof term (`complete_of_check` with `Eq.refl true` for the checker
and `rfl` for the mirrors) and lets the kernel alone check it, as `decide +kernel` does.

## 6. Soundness

`sound P U`: every instance of every unifier solves the problem. `checkSound` takes, for each
answer, the images `σ̂` of the problem's variables, substitutes them into both sides, and
compares the normal forms (`norm` at the binder's sorts). **Theorem** `sound_of_check`: an
instance `γ = body a` gives `enc γ = σ̂[enc a]` on the problem's variables (the bridge `hU`),
so each side at `γ` evaluates as its substituted normal form at `enc a` (substitution and
norm lemmas); equal normal forms give `(body γ).1 = (body γ).2`. No certificate is needed.
