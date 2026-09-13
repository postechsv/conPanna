# Expresso conPanna

Prototype framework and tactics for constrained-pattern unification and narrowing.

- `Expresso/Expresso.lean` contains the semantic framework for symbolic expressions such as
term patterns and rewrite rules. 

- `conPanna/conPanna.lean` contains the remaining theory, unification, narrowing, and example code.

## Build

Install Lean through [elan](https://github.com/leanprover/elan), then run:

```bash
lake build
```