# Producer: Maude side of answer-guided ACU certification

Given a user model, a unification problem and the answers of a prior Maude
`unify`, the producer builds a derivation in the calculus of the paper draft
(https://claude.ai/artifact/NPzPT378gRTqQyyXn7QRXV). Lean checks the result; nothing
here is trusted.

| Directory | Contents |
|---|---|
| `lib/` | The general library. `producer.maude` builds derivations; `show.maude` renders them as text. |
| `tools/` | Command-line tools. `derive.py` runs Maude on a request and writes the derivation. |
| `demo/` | Per demo: the Maude request (`*.maude`, models in `models.maude`), the derivation (`*.deriv`) and the Lean certificate (`*.lean`). The `.lean` files are currently written by hand in exactly the form the compiler will emit. |
| `tests/` | Development tests of the producer: `examples.maude`, `rules.maude` (every rule), `scale.maude` (larger inputs), and their models. |

## Run a demo

```
python3 producer/tools/derive.py producer/demo/mixed.maude   # writes producer/demo/mixed.deriv
lake env lean producer/demo/mixed.lean                        # checks the certificate
```

Known toolchain issue: checking `enter.lean` prints `PANIC at Lean.Expr.appArg!` messages
from a Mathlib simplification procedure. They are harmless; the proof checks.

## Reading a derivation

- Variables: `X?` original, `U1!` an answer's existential variable (Maude `#1`), `Z1` a fresh variable of SOLVE.
- Bags are written `t + u`, `{a}`, `∅`.
- Each rule line is preceded by its judgment `⊢ α | E | D`: the nontrivial images of the original variables, the pending equations, and the disequations.
- Children are indented. IDENTIFY labels its branches `equal:` and `distinct:`, and SOLVE labels them `branch π`.
