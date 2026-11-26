# The hypotheses of `complete_of_check`

```lean
theorem complete_of_check (M : Model) (hM : M.Lawful) (c : Cert) (hc : check M c = true)
    (b : Bridge M c.toClaim) : complete b.problem b.unifiers      -- Completeness.lean
```

The theorem turns "the checker accepted this data" into "the user's Lean claim is true".
The kernel can only compute on plain data (trees of numbers), but the claim is about Lean
values, such as bags of `Elem`. The hypotheses close that gap.

Each section below says what a hypothesis is, how the tactic `certify_comp` computes it,
and what it looks like for one example. The data shown is the actual proof term of the
FSCD test (`producer/tests/udf/FSCD.lean`), printed with `#print`, lightly trimmed:

```lean
inductive Elem where | a | b | c
abbrev Bag := ACU Elem
def problem : Problem Bag (Bag × Bag × Bag) :=
  .bind fun (X, Y, Z) => (X + X + Y + {a} + {b} + {c}, {b} + {b} + {b} + {c} + Z)
def answers : UnifierSet (Bag × Bag × Bag) :=
  [ .bind fun ((U, V) : Bag × Bag) => ({b} + U, V, {a} + U + U + V),
    .bind fun ((U, V) : Bag × Bag) => (U, {b} + {b} + V, {a} + U + U + V) ]
theorem complete : Unification.complete problem answers := by certify_comp
```

## Overview: where each argument comes from

```
goal  complete problem answers
  │
  ├─ types of the goal ──(Dumper.model, mkModel)──────────► M, hM      (generated Lean defs, rfl)
  ├─ terms of the goal ──(mirrorGoal)─────────────────────► c.toClaim, b (mirrored node by node, rfl)
  └─ Maude's certificate ─(UdfStore / udf.py, Udf.parse, steps)──► c.sorts, c.steps
                                                                hc := Eq.refl true
  proof term:  complete_of_check M hM c hc b      checked by the kernel (closeByKernel)
```

Only `c.sorts` and `c.steps` come from Maude. Everything else comes from the goal itself.

## 1. `M : Model`: a dictionary from numbers to Lean (`Core.lean`)

**What it is.** In data, everything is a number: sort 0, operator 2, variable 5. `M` says
what each number means in Lean: the type of each sort (`T`), the constructors (`ops`, each
with `build` and its inverse `unbuild`), which constructor built a value (`tag`), and the
ACU operators (`acus`, with `toBag`/`ofBag` to `ACU`). With it, `M.eval ρ t` turns a data
term `t` into a Lean value, given values `ρ` for its variables.

**How the tactic computes it.** `Dumper.model` (`Dumper/Base.lean`) collects the sorts and
constructors reachable from the goal's types. `loadModel` (`Tactic.lean`) then uses the
project's `T.reflect.model` if `#dump_model T` defined one (the examples do this in
`ctor.lean`), and otherwise `mkModel` (`Model.lean`) generates the definitions on the spot,
as auxiliary `_reflect_*` constants.

**FSCD.** The generated model:

```lean
T     := fun s => match s with | 0 => Elem | 1 => Bag | _ => Unit
tag 0 := fun y => match y with | a => 0 | b => 1 | c => 2
ops   := [ { args := [], res := 0, build := fun _ => a,
             unbuild := fun y => match y with | a => some () | _ => none },
           { …b… }, { …c… } ]                         -- operators 0, 1, 2 are a, b, c
acus  := [ { elem := 0, bag := 1, toBag := id, ofBag := id } ]   -- ACU operator 0: Bag = ACU Elem
```

So in the data below, `app 1 []` means `b`, `acu 0 [ts]` means the sum of `ts` in `Bag`,
and sort 1 means `Bag`.

## 2. `hM : M.Lawful`: the dictionary respects what the rules assume (`Core.lean`, `Model.Lawful`)

**What it is.** The rules reason about the symbols in a term, not about values. Each such
step is valid only if the model makes it valid:

| Law | Meaning | Justifies |
|---|---|---|
| `unbuild (build x) = x` | constructors are injective | `decomp`: from `f(s) = f(t)`, conclude `s = t` |
| `tag (build_i x) = i` | different constructors give different values | `clash`: `a ≟ b` has no solution |
| `toBag`/`ofBag` are inverse; element sort ≠ bag sort | the bag sort really is bags | ACU-Solve: reasoning with element counts |

For example, if the model sent `a` and `b` to the same Lean value, `clash` would wrongly
discard the solutions where they are equal. Lawful rules that out.

**How the tactic computes it.** Generated with the model: one `rfl` per constructor and
per law, and `decide` for "element sort ≠ bag sort".

**FSCD.** The generated proof, one `rfl` for each of `a`, `b`, `c`:

```lean
{ unbuild := ⟨fun x => rfl, ⟨fun x => rfl, ⟨fun x => rfl, trivial⟩⟩⟩,
  tag     := ⟨fun x => rfl, ⟨fun x => rfl, ⟨fun x => rfl, trivial⟩⟩⟩,
  acu     := ⟨⟨fun x => rfl, ⟨fun x => rfl, of_decide_eq_true (Eq.refl true)⟩⟩, trivial⟩ }
```

## 3. `c : Cert` and `hc : check M c = true`: the derivation is correct (`Check.lean`)

**What it is.** `c` is the claim plus its proof, all as data:

- **the claim** (`c.toClaim`): the shape of the variable tuple (`sh`), `lhs` and `rhs` as
  data terms, and the answers. Each answer is the shape of its new variables plus the image
  of each problem variable.
- **the derivation:** the sort of every variable (`sorts`: the problem's, then the new ones
  the certificate introduces) and the `steps`, a list of rules.

`check` runs the derivation from the initial state ("variables X, Y, Z; pending:
lhs ≟ rhs"). Each rule checks its side condition and passes its premise states on. Every
branch has to end in one of two ways:

- with no solutions (`clash`, `ground`), or
- with `cover`: a listed answer is at least as general as what the branch has computed.

In words: every solution of the problem follows some branch, and every branch either has
no solutions or is covered by an answer.

**How the tactic computes it.**

- *The claim* is mirrored from the goal by `mirrorGoal` and `mirror` (`Tactic.lean`), not
  taken from Maude. The tactic opens the problem's binder and each unifier's binder, then
  walks the Lean terms node by node. A bound variable becomes `var i` (its position in the
  tuple), a constructor becomes `app op args`, and `+`, `{x}` and `∅` on a bag become
  `acu f [...]`.
- *The derivation* comes from Maude's certificate in the Unification Derivation Format
  (UDF, `documentation/derivation-format.md`). `UdfStore.load?`
  (`Unification/Tactics/udfStore.lean`) finds the certificate that `narrow` stored under a
  hash of the claim. If there is none, the tactic runs Maude through
  `producer/tools/udf.py`. `Udf.parse` reads the text, and `steps` (`Tactic.lean`)
  translates each UDF step into a `Rule`:
  - variable names become numbers: the problem's `X1, X2, …` become `0, 1, …`, and each
    new variable `Z…` gets the next number, with the bag sort;
  - for `acu-solve`, `:unknowns` and `:rows` become the arguments and their multiplicities,
    which the checker checks. `:basis` and `:bounds` are only used to reorder Maude's
    selections into the checker's order. Each selection is passed with its elements in
    Maude's order, and its new variables.
- *`hc`* is the term `Eq.refl true`. The tactic computes nothing here. The kernel evaluates
  `check M c` when it checks the proof (`closeByKernel` wraps the proof in an auxiliary
  lemma that the kernel alone checks).

**FSCD.** The certificate (UDF) as `certify_comp` receives it. Maude's trace gives the
`acu-solve` step and two leaves; `producer/tools/udf.py` adds the answers and turns each
leaf into a `cover` step, with the witness: the answer's new variables `#1, #2` instantiated
by the leaf's variables.

```
(problem (= (__ a b c X1 X1 X2) (__ b b b c X3)))
(answers
  (unifier a0 (binders (#1 Bag) (#2 Bag)) (bind X1 (__ b #1)) (bind X2 #2) (bind X3 (__ a #1 #1 #2)))
  (unifier a1 (binders (#1 Bag) (#2 Bag)) (bind X1 #1) (bind X2 (__ b b #2)) (bind X3 (__ a #1 #1 #2))))
(step s0 acu-solve :op __ :eqs (0)
   :unknowns (b X3 a X1 X2)
   :bounds (1 inf 1 inf inf)
   :rows ((-2 -1 1 2 1))
   :basis ((1 0 0 1 0) (1 0 0 0 2) (0 1 1 0 0) (0 2 0 1 0) (0 1 0 0 1))
   :selections ((sel (0 2 3 4) :fresh (Z1 Z2)) (sel (1 2 3 4) :fresh (Z3 Z4))) :premises (s1 s2))
(step s1 cover :answer a0 :witness ((#1 Z1) (#2 Z2)) :premises ())
(step s2 cover :answer a1 :witness ((#1 Z3) (#2 Z4)) :premises ())
```

The resulting `c`. `X, Y, Z` are `var 0, 1, 2`, and Maude's `Z1…Z4` are `var 3…6`:

```lean
{ sh  := (leaf 1).pair ((leaf 1).pair (leaf 1)),          -- Bag × Bag × Bag
  lhs := acu 0 [acu 0 [acu 0 [acu 0 [acu 0 [var 0, var 0], var 1],      -- X + X + Y
                              acu 0 [app 0 []]],                         --   + {a}
                       acu 0 [app 1 []]],                                --   + {b}
                acu 0 [app 2 []]],                                       --   + {c}
  rhs := …,                                                              -- {b}+{b}+{b}+{c}+Z
  answers := [ { sh := (leaf 1).pair (leaf 1),                           -- new variables U, V
                 img := [ acu 0 [acu 0 [app 1 []], var 0],               -- X ↦ {b} + U
                          var 1,                                         -- Y ↦ V
                          … ] },                                         -- Z ↦ {a} + U + U + V
               { … } ],
  sorts := [1, 1, 1, 1, 1, 1, 1],                          -- X, Y, Z, Z1, Z2, Z3, Z4 : Bag
  steps :=
    [ Rule.acu 0 0                                         -- ACU operator 0, equation 0
        [norm (app 1 []), norm (var 2), norm (app 0 []), norm (var 0), norm (var 1)]
                                                           -- arguments b, Z, a, X, Y
        [-2, -1, 1, 2, 1]                                  -- their multiplicities
        [([3, 1, 2, 0], [5, 6]), ([4, 1, 2, 0], [3, 4])]   -- selections, checker's order
        [2, 1],                                            -- premise of each: steps 2 and 1
      Rule.cover 0 [var 3, var 4],                         -- step 1: answer 0 with U, V := Z1, Z2
      Rule.cover 1 [var 5, var 6] ] }                      -- step 2: answer 1 with U, V := Z3, Z4
```

Three things to note:

- The checker computes its own basis and selections. Its first selection matches Maude's
  second one, so the tactic lists that one first, with Maude's new variables `Z3, Z4`, and
  points it to premise step 2.
- The cover witnesses: `:witness ((#1 Z1) (#2 Z2))` becomes `cover 0 [var 3, var 4]`. The
  checker substitutes them into answer 0 and compares the result with the branch's state.
  Here the witness is just a renaming of variables.
- In Lean the multiplicities are written `Int.negSucc 1` (that is −2), `Int.ofNat 2`, and
  so on.

## 4. `b : Bridge M c.toClaim`: the data means exactly the user's goal (`Bridge.lean`)

**What it is.** Without this, `check` might have certified some other problem. The bridge
holds the Lean problem's body, the Lean unifiers, and four facts. For every assignment `γ`
of the problem variables:

- `hl`, `hr`: evaluating the data `lhs` (and `rhs`) under `γ` gives exactly the Lean side
  of the problem;
- `has`, `hU`: the claim's answers are exactly the listed unifiers, and evaluating each
  answer's data images gives exactly the Lean unifier's images.

**How the tactic computes it.** Built by `mirrorGoal` together with the claim. The body and
the unifiers are copied from the goal, and each fact is an `Eq.refl` term, so the kernel
checks it by evaluating both sides.

**FSCD.**

```lean
{ s    := 1,                                                    -- the sides have sort Bag
  body := fun γ => (γ.1 + γ.1 + γ.2.1 + {a} + {b} + {c}, {b} + {b} + {b} + {c} + γ.2.2),
  as   := [ { bsh := (leaf 1).pair (leaf 1), img := …,
              body := fun z => ({b} + z.1, z.2, {a} + z.1 + z.1 + z.2) },
            { …, body := fun z => (z.1, {b} + {b} + z.2, {a} + z.1 + z.1 + z.2) } ],
  hl   := fun γ => Eq.refl (M.eval (M.enc sh γ) (acu 0 [acu 0 [… var 0, var 0 …]])),
  hr   := fun γ => Eq.refl (…),
  has  := Eq.refl …,
  hU   := … }                                                   -- one Eq.refl per answer
```

`hl` states `M.eval (M.enc sh γ) lhs = some ⟨1, (body γ).1⟩`. The kernel checks it by
evaluating the data term under `γ` (`var 0 ↦ γ.1`, `var 1 ↦ γ.2.1`, `var 2 ↦ γ.2.2`,
`acu 0 ↦ +`, `app 0 [] ↦ a`, …) until both sides are the same Lean expression.

## Conclusion

`complete b.problem b.unifiers`. By the bridge, `b.problem` and `b.unifiers` are the user's
own `problem` and `answers`, so the theorem proves the goal as stated:

```lean
theorem UdfTest.FSCD.complete._proof_1_19 : Unification.complete
    (Problem.bind fun γ => (γ.1 + γ.1 + γ.2.1 + {a} + {b} + {c}, {b} + {b} + {b} + {c} + γ.2.2))
    [Unifier.bind fun z => ({b} + z.1, z.2, {a} + z.1 + z.1 + z.2),
     Unifier.bind fun z => (z.1, {b} + {b} + z.2, {a} + z.1 + z.1 + z.2)] :=
  Reflect.complete_of_check M hM c (Eq.refl true) b
```

The chain a reviewer follows:

```
Lean goal  ≡  data claim                       (Bridge, by rfl)
data derivation is correct                     (check = true, by kernel evaluation)
each rule is valid for these Lean types        (Lawful, by rfl; proved once in complete_of_check)
⇒  complete problem answers
```

To see this data for any obligation, `#print` the auxiliary lemma that `certify_comp`
creates (`#print T.complete` names it, e.g. `T.complete._proof_1_19`) with
`set_option pp.proofs true`.

The rules themselves are listed at the top of `Check.lean`. The project-level reviewer
guide is `documentation/REVIEWER.md`.
