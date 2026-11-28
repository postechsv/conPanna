# Reviewer guide

What conPanna proves, what a reviewer has to read to believe it, and what can be skipped.

## 1. End results

| Example | Theorem (file) | Axioms |
|---|---|---|
| Bakery | `Bakery.bakery_mutex`, `Bakery.bakery_abort_mutex` (`examples/Bakery/main.lean`) | `propext`, `Classical.choice`, `Quot.sound` |
| Readers-writers (Petri net) | `ReadersWriters.net_safe` (`examples/ReadersWriters/main.lean`) | `propext`, `Classical.choice`, `Quot.sound` |
| German | `German.german_coherent_linked` (`examples/German/main.lean`) | in progress |

Each says: every step from an initial state reaches a state satisfying the safety
property (mutual exclusion, agreement, coherence). Only Lean's standard axioms are used:
no `sorry`, and no deferred claim remains.

## 2. How unification enters a proof

The invariance proofs (`examples/*/proof.lean`) case-split each rule application with
`narrow`. Every case split rests on a unification claim, which `narrow` defers as an axiom
(`laterAx` for completeness, `laterSoundAx` for soundness; `conPanna/Unification/LaterAx.lean`).
Each claim is then proved as a separate obligation (`examples/*/cert.lean`). `#link`
(`conPanna/Later.lean`) rebuilds the proof with every deferred claim replaced by the
theorem proving it, and the kernel re-checks it. So `#print axioms` on an end result shows
`laterAx` exactly when a claim is still unproved.

## 3. What a claim says

`conPanna/Unification/Unification.lean` (45 lines, plain Lean):

- `complete P U`: every solution of the problem `P` is an instance of some unifier in `U`.
- `sound P U`: every instance of every unifier in `U` is a solution of `P`.

`P` and `U` are about the user's own Lean types: bags are the quotient type `ACU`
(`conPanna/BaseTheory/ACU.lean`), so equality is equality modulo ACU.

## 4. How a claim is proved

Each obligation is closed by one tactic call, `certify_comp` or `certify_sound`
(`conPanna/Reflect/Tactic.lean`). It produces a proof term from one of two theorems:

| Theorem | File | Concludes |
|---|---|---|
| `complete_of_check` | `conPanna/Reflect/Completeness.lean` | `complete P U` |
| `sound_of_check` | `conPanna/Reflect/Soundness.lean` | `sound P U` |

Their hypotheses are what a reviewer has to read:

| Hypothesis | File | Discharged by |
|---|---|---|
| `M.Lawful`: the model of the sorts behaves like their constructors | `conPanna/Reflect/Core.lean` (`Model.Lawful`) | `rfl`, per model |
| `check M c = true` / `checkSound M c = true`: the checker accepts | `conPanna/Reflect/Check.lean` (`check`, `checkSound`) | kernel evaluation |
| `Bridge`: the claim as data evaluates to the Lean goal | `conPanna/Reflect/Bridge.lean` (`Bridge`) | `rfl` |

`check` replays the certificate's derivation over terms as data. Its rules are `delete`,
`decomp`, `elim`, `clash`, `ground`, `cover` and `acu` (ACU-Solve). ACU-Solve computes the
basis of the step's Diophantine equation (the minimal admissible solutions, of total at
most twice the largest multiplicity, `conPanna/Reflect/MinimalBound.lean`) and its
selections itself.

## 5. What need not be trusted

Maude, the Python tools in `producer/`, the certificate cache `producer/.cache/`, and the
tactics. They only produce the data that `check` reads: if any of them is wrong, the kernel
rejects the proof. The certificate (UDF, `documentation/derivation-format.md`) supplies only
witnesses: the shape of the derivation, the answers, and for each ACU-Solve step the
arguments with their multiplicities, the order of each selection and its new variables.
The checker verifies each of them.

## 6. What can be skipped

The proofs of the two theorems: `conPanna/Reflect/Eval.lean`, `AcuStep.lean`,
`AcuSound.lean`, `MinimalBound.lean`, and the inner part of `Completeness.lean`. The
kernel checks them, and `#print axioms` confirms they add no axioms.

## 7. Checking it yourself

The machine needs about 3 GB per Lean process. Check one file at a time:

```
lake build conPanna
lake env lean examples/Bakery/cert.lean          # the obligations
lake build examples.Bakery.main                  # the end results, with #link
```

Then `#print axioms Bakery.bakery_mutex` in a file importing `examples.Bakery.main`.
German's 150 obligations exceed 4 GB as one file; check them in parts.
