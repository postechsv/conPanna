# The hypotheses of `complete_of_check`

```lean
theorem complete_of_check (M : Model) (hM : M.Lawful) (c : Cert) (hc : check M c = true)
    (b : Bridge M c.toClaim) : complete b.problem b.unifiers      -- Completeness.lean
```

The theorem turns "the checker accepted this data" into "the user's Lean claim is true".
The kernel can only compute on plain data (trees of numbers), but the claim is about Lean
values, such as bags of `Elem`. The hypotheses close that gap.

Running example: the FSCD test (`producer/tests/udf/FSCD.lean`),
`X X Y a b c ≟ b b b c Z` over `Elem = a | b | c` and `Bag = ACU Elem`.

## 1. `M : Model`: a dictionary from numbers to Lean (`Core.lean`)

In data, everything is a number: sort 0, operator 2, variable 5. `M` says what each number
means in Lean:

- **sorts:** `M.T 0 = Elem`, `M.T 1 = Bag`;
- **constructors:** operator 0 is `Elem.a`, with `build`, and its inverse `unbuild` that
  reads the arguments back out;
- **ACU operators:** for `Bag`, `toBag : Bag → ACU Elem` and `ofBag` back.

With it, `M.eval ρ t` turns a data term `t` into a Lean value, given values `ρ` for its
variables.

## 2. `hM : M.Lawful`: the dictionary respects what the rules assume (`Core.lean`, `Model.Lawful`)

The rules reason about the symbols in a term, not about values. Each such step is valid
only if the model makes it valid:

| Law | Meaning | Justifies |
|---|---|---|
| `unbuild (build x) = x` | constructors are injective | `decomp`: from `f(s) = f(t)`, conclude `s = t` |
| `tag (build_i x) = i` | different constructors give different values | `clash`: `a ≟ b` has no solution |
| `toBag`/`ofBag` are inverse; element sort ≠ bag sort | the bag sort really is bags | ACU-Solve: reasoning with element counts |

For example, if the model sent `a` and `b` to the same Lean value, `clash` would wrongly
discard the solutions where they are equal. Lawful rules that out. The dictionary is
generated from the actual constructors, so each law holds by `rfl`.

## 3. `c : Cert` and `hc : check M c = true`: the derivation is correct (`Check.lean`)

`c` is the claim plus its proof, all as data:

- **the claim:** the variables' sorts, `lhs` and `rhs` as data terms, and the answers
  (each a list of new variables plus the image of each problem variable);
- **the derivation:** the declared sorts and the `steps`, a list of rules.

`check` runs the derivation from the initial state ("variables X, Y, Z; pending:
lhs ≟ rhs"). Each rule checks its side condition and passes its premise states on. Every
branch has to end in one of two ways:

- with no solutions (`clash`, `ground`), or
- with `cover`: a listed answer is at least as general as what the branch has computed.

In words: every solution of the problem follows some branch, and every branch either has
no solutions or is covered by an answer. For FSCD, one `acu` step produces two premise
states, and each ends in a `cover` of one of the two answers.

The proof of `hc` is just `Eq.refl true`: the kernel evaluates `check M c` and gets `true`.
That evaluation is the real work.

## 4. `b : Bridge M c.toClaim`: the data means exactly the user's goal (`Bridge.lean`)

Without this, `check` might have certified some other problem. The bridge says, for every
assignment `γ` of the problem variables:

- `hl`, `hr`: evaluating the data `lhs` (and `rhs`) under `γ` gives exactly the Lean side
  `X + X + Y + {a} + {b} + {c}` (and `{b} + {b} + {b} + {c} + Z`);
- `has`, `hU`: evaluating each answer's data images gives exactly the Lean unifier, e.g.
  `(U, V) ↦ ({b} + U, V, {a} + U + U + V)`.

The tactic (`Tactic.lean`) builds `c` by mirroring the goal node by node, so these
equalities also hold by `rfl`.

## Conclusion

`complete b.problem b.unifiers`. By the bridge, `b.problem` and `b.unifiers` are the user's
own `problem` and `answers`, so the theorem proves the goal as stated.

```
Lean goal  ≡  data claim                       (Bridge, by rfl)
data derivation is correct                     (check = true, by kernel evaluation)
each rule is valid for these Lean types        (Lawful, by rfl; proved once in complete_of_check)
⇒  complete problem answers
```

The rules themselves are listed at the top of `Check.lean`. The project-level reviewer
guide is `documentation/REVIEWER.md`.
