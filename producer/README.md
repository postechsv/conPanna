# Producer: Maude side of answer-guided ACU certification

Given a user model, a unification problem and the answers of a prior Maude
`unify`, the producer builds a derivation in the calculus of the paper draft
(https://claude.ai/artifact/NPzPT378gRTqQyyXn7QRXV). A compiler turns the
derivation into a Lean proof of `Unification.complete`. Nothing here is trusted:
Lean checks the result.

| Directory | Contents |
|---|---|
| `lib/` | The general library. `producer.maude` builds derivations; `show.maude` renders them as text. |
| `tools/` | `derive.py` (Maude → derivation), `compile.py` (derivation → Lean), `demo.py` (both, plus Lean's check). |
| `demo/` | Per demo NAME: the request `NAME.maude` (models in `models.maude`), the user's claim `NAME.claim.lean`, and the generated `NAME.deriv` and `NAME.lean`. |
| `tests/` | Development tests of the producer (`examples.maude`, `rules.maude`, `scale.maude`), and `tests/pipeline/`: the same cases run end to end through Lean. |

## Run the demos

From the repository root:

```
python3 producer/tools/demo.py all        # or e.g.: python3 producer/tools/demo.py mixed
```

For each demo this runs Maude (`unify`, then the derivation), compiles the
derivation into a Lean certificate, and checks it with `lake env lean`. The demos:

| Demo | What it shows |
|---|---|
| `l137` | Bakery: DECOMP of a configuration, then one SOLVE with two branches |
| `bakery2` | Unknown bags on both sides: SOLVE with fresh variables (basis vectors) |
| `mixed` | Paper §6.1: IDENTIFY splits two aliens that may cancel |
| `nonlinear` | Paper §6.2: a Hilbert basis of three vectors |
| `enter` | A Bakery transition step: compatible aliens, one SOLVE with a clique |
| `clash` | No unifiers: a free clash (successor vs. zero); empty answer set certified |
| `parity` | No unifiers: SOLVE with no possible choice (`2x = 2y + 1`); empty answer set certified |
| `missing` | Negative: one of Maude's answers removed; the derivation gets STUCK, no certificate |

Known toolchain issue: checking `enter.lean` prints `PANIC at Lean.Expr.appArg!`
messages from a Mathlib simplification procedure. They are harmless; the proof checks.

## Pipeline tests

```
python3 producer/tools/demo.py --dir producer/tests/pipeline all
```

These cover every rule, equation systems sharing variables (`t4`, `t5`), nested bags
(`t6`), a SOLVE on the fresh variables of an earlier SOLVE (`t5`), Bakery steps with
up to four further processes (`s1_enter2`–`4`), and linear equations whose answer sets
grow exponentially (`s2_linear*`).

## The claim file

`NAME.claim.lean` is ordinary Lean: the model (inductives, `ACU` sorts) and the
problem. Its `/- certify {...} -/` header tells the compiler the namespace, the Lean
type of the original variables (`context`), their order (`vars`), and the Lean
counterparts of the Maude operators (`ops`). Later the model, problem and this
header will be dumped from Lean instead of written by hand.

Maude requests still pass a tuple operator name to `certify`; it is ignored. The
producer adds its own tuple operator over the original variables to the model.

## Reading a derivation

- Variables: `X?` original, `U1!` an answer's existential variable (Maude `#1`), `Z1` a fresh variable of SOLVE.
- Bags are written `t + u`, `{a}`, `∅`.
- Each rule line is preceded by its judgment `⊢ α | E | D`: the nontrivial images of the original variables, the pending equations, and the disequations.
- Children are indented. IDENTIFY labels its branches `equal:` and `distinct:`, and SOLVE labels them `branch π`.
- The compiled `NAME.lean` repeats each judgment and rule as a comment above the Lean step that applies it.
