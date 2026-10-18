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
- `examples/` holds the Bakery narrowing example and the paper's examples.

## Build

Install Lean through [elan](https://github.com/leanprover/elan), then run:

```bash
lake build
```
