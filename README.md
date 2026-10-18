# Expresso conPanna

Prototype framework and tactics for constrained-pattern unification and narrowing.

- `Expresso/` is the semantic framework: patterns and rules (`core.lean`), and ACU
  sorts as quotient types (`ACU.lean`).
- `conPanna/` is unification and narrowing on top of it: the unification problem and
  its certification calculus (`Unification/`), narrowing reduced to unification
  (`Narrowing/`), the model dumper (`Dumper.lean`), and the Maude tactics
  `maude_unify` and `maude_certify_comp` (`Unification/Tactics/`).
  `conPanna/conPanna.lean` imports all of it.
- `producer/` is the Maude side: it computes unifiers and derives certificates that
  Lean checks (see `producer/README.md`).
- `examples/` holds the paper's examples and `Bakery/`, a narrowing proof split into the
  constructor model and the rules (`model/`), the top-down proof with
  deferred obligations (`bakery_pf_uncertain`), the obligations (`bakery_obligation`),
  and the linked proof (`bakery_pf`). The deferral commands are in `conPanna/Later.lean`.

## Build

Install Lean through [elan](https://github.com/leanprover/elan), then run:

```bash
lake build
```
