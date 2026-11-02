# ACU-SOLVE on a system: design and soundness

Design note for the `acu-solve` rule of the Unification Derivation Format
(documentation/derivation-format.md, §5), before its Lean version. It replaces today's
SOLVE (Calculus.lean, Solve.lean): data P and 𝓑, side conditions S0–S3, cliques of
compatible aliens, IDENTIFY and the disequations `D`.

## 1. What changes

| | today's SOLVE | acu-solve |
|---|---|---|
| equations | one bag equation | a system: several equations of one ACU operator |
| unknowns | bag variables; alien *classes* | bag variables and aliens, all as columns of one vector |
| data | particular solutions P per alien, basis 𝓑 of the bag part | one basis B over all columns |
| premises | one per choice of particular solutions (`choices P`) | one per legal selection of basis vectors |
| aliens that may be equal | IDENTIFY first (premises a = b and a ≠ b), compatibility cliques, S2 | a basis vector holding several aliens; its premise has the pending equations a = b |
| aliens that cannot be equal | disequations `D` | aliens with different top symbols *clash*: no vector holds both |
| side conditions | S0, S1p, S1b, S2 (per clique), S3 | B nonzero, B solves the rows, S3′ (below) |

The data is what Maude computes (one basis of the whole system), so it is read from its
trace rather than recomputed.

## 2. The rule

**Input.** A system of equations of the ACU operator `+` with identity `∅` over elements
`El`, written with columns `j = 1 … n+m`:

- bag columns `X₁ … Xₙ : ACU El` (bag variables), and
- alien columns `a₁ … aₘ : El` (single elements: non-variable terms, element variables).
  Two columns may hold the same term.

Each equation `r` has coefficients `Lᵣ, Rᵣ : columns → ℕ`, and reads

    Σⱼ Lᵣ j · col j  =  Σⱼ Rᵣ j · col j        (col j = Xⱼ, or {aⱼ} for an alien)

A *clash* relation on alien columns: `clash c c'` when both are non-variable terms with
different top symbols (decided syntactically by the checker).

**Data.** A basis `B₁ … B_k : columns → ℕ`.

**Side conditions** (closed facts about numbers):

- (N) every `Bₜ` is nonzero;
- (S) every `Bₜ` solves every row: `Lᵣ · Bₜ = Rᵣ · Bₜ`;
- (S3′) for every vector `v` with `v ≠ 0`, `v c ≤ 1` for alien columns, not both
  `v c = v c' = 1` for clashing `c, c'`, and `Lᵣ · v = Rᵣ · v` for every row: some
  `Bₜ ≤ v` componentwise.

**Legal selections.** `S ⊆ {1 … k}` is legal when every alien column lies in exactly one
selected vector, and every alien-free vector is selected. The checker computes them
from B (a finite enumeration), so they are not a side condition.

**Premise of a legal S.** Fresh bags `Zₜ` for the alien-free `t ∈ S`. For an alien vector
`t ∈ S` with alien columns `Aₜ`, its representative is `rₜ = a_{min Aₜ}`. Substitute

    Xᵢ  :=  Σ_{t∈S alien-free} Bₜ i · Zₜ  +  Σ_{t∈S alien} Bₜ i · {rₜ}          (θ_S)

and add the pending equations `a_c = rₜ` for `c ∈ Aₜ`, `c ≠ min Aₜ`. The other pending
equations are kept, under θ_S. The aliens may depend only on variables other than the
`Xᵢ` (Lean's `Split`), so θ_S leaves them unchanged.

**Example.** The equation `X + {w(N)} = Y + {w(M)}` has columns `Y, w(M), X, w(N)` and the row
`(−1, −1, 1, 1)`, written as `L = (0,0,1,1)` and `R = (1,1,0,0)`. Its basis is

    B₁ = Y X        (1,0,1,0)       alien-free
    B₂ = Y w(N)     (1,0,0,1)
    B₃ = w(M) X     (0,1,1,0)
    B₄ = w(M) w(N)  (0,1,0,1)

`w(M)` and `w(N)` have the same top symbol, so they do not clash. The legal selections
are {1, 2, 3}, giving `X := Z + {w(M)}` and `Y := Z + {w(N)}`, and {1, 4}, giving
`X := Z` and `Y := Z` with the pending equation `w(N) = w(M)`.

## 3. Soundness

**Claim.** If every premise holds (every solution of a premise is covered), the
conclusion holds. It suffices that every solution ρ of the conclusion is the image of a
solution of some premise.

**Proof.** Fix ρ, and read each column as a multiset: `x_i = ρ(Xᵢ)`, and `x_c = {ρ(a_c)}`
for an alien column (one element).

1. **Element vectors are clash-free solutions.** For an element `e`, let
   `v_e j = count of e in x_j`. Each equation holds under ρ, so counting `e` on both
   sides gives `Lᵣ · v_e = Rᵣ · v_e`. This holds even when two columns hold the same
   term, because each column's count is the count in that column's multiset. An alien
   column has `v_e c ≤ 1`. If `v_e c = v_e c' = 1` then `ρ(a_c) = e = ρ(a_c')`, so `c`
   and `c'` do not clash: clashing aliens are different terms, as different top
   symbols make them different elements.
2. **Peeling.** Let H be the predicate "solves every row, alien entries ≤ 1, clash-free".
   If `H v`, `v ≠ 0` and `Bₜ ≤ v`, then `H (v − Bₜ)`: the rows are linear (`dot_sub`),
   and lowering entries keeps the bound and clash-freeness. With (N), (S3′) and this,
   Solve.lean's existing `decompose` gives multisets `U₁ … U_k` with
   `x_j = Σₜ Bₜ j · Uₜ` for every column `j`.
3. **Alien columns fix the alien vectors.** For an alien column c,
   `{ρ(a_c)} = Σₜ Bₜ c · Uₜ`, a sum equal to a single element. So exactly one `t` has
   `Bₜ c · Uₜ ≠ 0`, and for it `Bₜ c = 1` and `Uₜ = {ρ(a_c)}`. For an alien vector `t`,
   `Uₜ` is therefore empty or `{ρ(a_c)}` for each `c ∈ Aₜ`. In the second case all
   aliens of `Aₜ` are equal under ρ.
4. **The selection.** Let `S` = the alien-free vectors, plus the alien vectors with
   `Uₜ ≠ ∅`. By step 3, every alien column lies in exactly one vector of S, so S is
   legal. Under ρ the pending equations `a_c = rₜ` hold, also by step 3.
5. **The premise solution.** Set `Zₜ := Uₜ` for the alien-free `t ∈ S`. For a bag
   column `i`, `x_i = Σₜ Bₜ i · Uₜ`. The unselected alien vectors contribute `∅`, and a
   selected alien vector contributes `Bₜ i · {ρ(rₜ)}`. So `x_i = θ_S(Xᵢ)` under ρ with
   these `Zₜ`. The remaining equations hold, being ρ's. ∎

Nothing above needs two aliens to be distinct terms, or the selection to be maximal
beyond legality. The only facts about the aliens are "one element each" and "clashing
ones differ".

**Why ACU and not AC.** An alien-free vector may be selected with `Zₜ = ∅` (the
identity), so taking all of them is complete. For AC, `∅` does not exist. The legal
selections must then also cover every bag column at least once (the reserved `:cover`
flag), and step 4 picks S among those. The rest of the proof is unchanged.

**Termination.** The checker walks a finite derivation. Each acu-solve has finitely many
legal selections (subsets of a finite basis) and finitely many obligations. No search
happens in Lean. That the producer's derivation is finite is Maude's termination, and is
not needed for soundness.

## 4. The obligations in Lean

| Obligation | Kind | Discharge |
|---|---|---|
| the equations are the rows (`heq`) | equality modulo AC per equation | the existing AC normalizer (`acu_eq`) |
| (N), (S) | closed arithmetic on numerals | `decide` / `norm_num` |
| (S3′) | closed Presburger formula, one per system | `omega`, as today's S3 (`acu_basis`). Local reflection (a verified completeness check) is the Phase 5 alternative if this is slow. |
| clash pairs differ | constructor distinctness | `noConfusion` / `simp` (it was `hdistinct` today) |
| premises = legal selections | computed from B | a Lean function `legal B`; the premises are `∀ S ∈ legal B`, unfolded by `decide`-style evaluation |

S3′ is the only quantified obligation, and it is weaker than today's S3 plus S2, since a
clash-free vector is a special case. Maude's bases leave out clashing vectors, so S3′ is
exactly the condition they satisfy. Today's S3 would fail on them: brute force over the
330 systems of the test set finds 100 minimal solutions missing from Maude's bases, all
of them clashing.

## 5. Lean shape (to implement)

    structure System (n m : ℕ) where        -- columns: Fin n bags, Fin m aliens
      rows  : List ((Fin n → ℕ) × (Fin m → ℕ) × (Fin n → ℕ) × (Fin m → ℕ))   -- L, La, R, Ra
      clash : List (Fin m × Fin m)

    theorem acu_solve (sp : Split El Γ Γr n) (a : Γr → Fin m → El) (q : System n m)
        (B : Fin k → (Fin n → ℕ) × (Fin m → ℕ))
        (valid : q.Valid B)                                   -- (N), (S), (S3′)
        (heq : ∀ ρ, Eqs es ρ → q.Holds (sp.V ρ) (a (sp.rest ρ)))
        (hclash : ∀ r, ∀ (c, c') ∈ q.clash, a r c ≠ a r c')
        (next : ∀ S ∈ legal B, (premise S) ⊩ unifiers) :
        ⟨α, es ++ E, D⟩ ⊩ unifiers

The rule consumes the first equations `es` of the state. A permutation lemma brings the
`:eqs` of the derivation to the front. The proof follows §3, with `decompose` as is.
`premise S` adds the pending equations and the fresh block `Z : Fin (free S) → ACU El`;
`rename` unpacks the block as today.

The free rules, `cover`, `transfer`, `close` and `rename` are unchanged. `identify`,
`D`, `BagEq.compatible`, `cliques`, `choices` and S2 become unused once the producer is
switched (Phase 6). `ground` is an instance of `clash`, since the two sides normalize
differently.

## 6. Open points

- **S3′ cost.** `omega` on systems with many columns: the largest test system has 9
  columns, and a German cell has 6. Measure in Phase 4. Phase 5 adds reflection if
  needed.
- **Aliens inside aliens of the same operator** (an alien holding a bag variable of its
  own system) are outside version 1. The producer rejects them, and no test hits them.
- **`legal B` enumeration** is exponential in the number of alien vectors in the worst
  case, as is the number of premises. It equals Maude's number of maximal selections.
