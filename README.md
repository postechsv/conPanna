# conPanna

Prototype framework and tactics for constrained-pattern unification and narrowing.

- `Expres- `conPanna/` is the whole framework:
  - patterns and rules (`core.lean`), and ACU sorts as quotient types (`BaseTheory/ACU.lean`);
  - unification and its certification calculus (`Unification/`), narrowing reduced to
    unification (`Narrowing/`), and the `narrow` tactic (`narrow.lean`);
  - the model dumper (`Dumper.lean`) and the Maude tactics `maude_unify` and `maude_match`
    (`Unification/Tactics/`);
  - certification by reflection, `certify_comp` and `certify_sound` (`Reflect/`);
  - deferred obligations (`Later.lean`).
  `conPanna/conPanna.lean` imports all of it.
- `producer/` is the Maude side: it computes unifiers and derives certificates that
  Lean checks (see `producer/README.md`).
- `examples/` holds `Bakery/`, `TwoPC/` and `German/`, each split into the constructor
  model (`ctor.lean`), the rules (`rule.lean`), the top-down proof with deferred
  obligations (`proof.lean`), the obligations (`cert.lean`), and the linked theorems
  (`main.lean`).


Install Lean through [elan](https://github.com/leanprover/elan), then run:

```bash
lake build
```
