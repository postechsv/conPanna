# Producer: Maude side of certified unification

The producer turns Maude's own unification into completeness certificates. Narrowing
(`narrow`, through the Lean tactic `maude_unify`) runs the instrumented Maude once per cell.
That run gives Maude's filtered unifiers and, from its unification trace, a derivation in
the Unification Derivation Format (UDF, `documentation/derivation-format.md`). Lean
replays the derivation through rules proved once (`udf_certify`). Nothing here is
trusted: Lean checks every certificate.

| Path | Contents |
|---|---|
| `../maude/` | Maude with the unification trace (`MAUDE_UNIFICATION_TRACE`); build it with `maude/build.sh`. |
| `tools/trace_tree.py` | Runs the instrumented Maude and rebuilds its search tree from the trace. |
| `tools/trace_to_udf.py` | Extracts the UDF derivation from the tree: free steps, ACU steps with Maude's bases, and a `cover` per leaf from Maude's filter. |
| `tools/unify.py` | Entry of `maude_unify`: unifiers and certificates for narrowing. |
| `tools/udf.py` | Entry of `udf_certify` when no stored certificate exists: a derivation covered by given unifiers. |
| `tools/match.py` | Entry of `maude_match` (subsumption by matching). |
| `tools/test_udf.py` | Regression test: a derivation for every problem in `tests/`. |
| `tests/` | Test problems (`NAME.maude` next to `models.maude`): demos, pipeline cases, three seeds of a generated grid, a German cell. `tests/udf/T4.lean` runs `udf_certify` end to end. |

Certificates made during narrowing are kept in `.cache/udf/`, under a hash of the claim
they certify, so certifying an obligation needs no Maude call.

## Test

From the repository root, after `maude/build.sh`:

```
python3 producer/tools/test_udf.py          # 259 problems
lake env lean producer/tests/udf/T4.lean    # one certificate through Lean
```

The examples (`examples/Bakery`, `examples/TwoPC`) run the whole pipeline: narrowing in
`proof.lean`, certification in `cert.lean`, the linked theorems in `main.lean`.
