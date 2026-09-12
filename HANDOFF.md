# conPanna development handoff

This document records the design decisions and current implementation state needed to continue development in a new conversation. The current repository is `/home/byhoson/workspace/conPanna`.

## Project objective

conPanna is a Lean prototype for constrained-pattern unification and narrowing, with generalized reachability-logic reasoning as the longer-term goal. The code is divided conceptually into:

- **Expresso:** the declarative semantic framework for states, patterns, rules, narrowing, subsumption, and `mapsInto`.
- **conPanna:** equational theories, unification backends and certificates, narrowing automation, and tactics.

The implementation must remain independent of particular user models and examples.

## Central modelling decisions

1. User-defined configuration types such as `Conf` contain only object-language terms. Do not require users to add a constructor for logical variables.
2. Logical variables are Lean variables bound by lambda closures. A constrained term is represented by a closure returning `APattBody`; a rule is likewise represented by a closure returning `RuleBody`. This naturally shares variables between terms and constraints, and between a rule's LHS, RHS, and condition.
3. `Pattern` already represents finite disjunction. An individual result of applying one unifier is called a **successor**; the disjunction of successors is called the **post**.
4. Constraints are semantically important. A backend may compute many structural MGUs, while instantiated pattern and rule constraints filter infeasible branches.
5. Unification must not depend on names or definitions from examples. Earlier example-specific tactic behavior was rejected as “cheating.”
6. The future AC/ACU integration may use an external oracle such as Maude to generate candidates, but Lean certification remains mandatory.

## Repository layout

```text
Expresso/
└── Expresso.lean

conPanna/
└── conPanna.lean

testcases/
├── ex_framework.lean
├── ex_unification.lean
├── narrowing_examples.lean
├── c_unification_examples.lean
└── theory_examples.lean

examples/
└── rw.lean
```

The testcase modules are deliberately not registered as a Lake library. They are examples rather than part of the public library. Each is independently importable; `ex_unification.lean` inlines its small `Conf`/`pat1`/`pat2` setup instead of importing another testcase.

There is no enclosing `Expresso` or `ConPanna` namespace. The directory/module boundaries and Lean namespaces are separate concepts.

## `Expresso/Expresso.lean`

Outermost namespace:

```text
framework
```

Inner structure:

```text
framework
├── Patterns
└── Rules
```

### `framework.Patterns`

Important declarations:

- `State α`: marks a model's state type.
- `APatt α P`: semantics of an atomic-pattern representation `P` over states `α`.
- `APattBody α`: a concrete term plus its constraint (`term`, `requires`).
- `Pattern α P`: semantics of a possibly disjunctive pattern representation.
- `Disjunction P Q`: heterogeneous disjunction, written `p ⊔ q`.
- `EmptyPattern α`: the empty pattern.
- `Subsumes`, written `p ⊑ q`.

Canonical `APatt` instances cover ground terms, `APattBody`, and lambda closures. Lambda-bound variables are existentially quantified by the semantics.

### `framework.Rules`

Important declarations:

- `RuleBody α`: `lhs`, `rhs`, and `requires`.
- `AtRule α R`: semantics for rule representations, including lambda closures.
- `postImage`: semantic image of a source through a rule.
- `NarrowsTo`, written `r ⊢ p ↝ post`.
- `mapsInto`, written `r ⊢ p ↪ q`.
- `mapsInto_of_narrowsTo_of_subsumes`: composes a known narrowing result and a subsumption proof.
- `mapsInto_via_narrowing`: existentially packages the Lean representation type, `Pattern` instance, and value of a tactic-generated post.

The intended user proof decomposition is:

```lean
example : rule ⊢ source ↪ target := by
  apply mapsInto_via_narrowing
  narrow rule against source
  subsume
```

Conceptually, `mapsInto` requires every successor represented by the post to be included in the target:

```text
r ⊢ p ↪ q  iff  for every post, (r ⊢ p ↝ post) implies (post ⊑ q)
```

`mapsInto_via_narrowing` exists to hide the heterogeneous Lean type of the generated post from the user.

## `conPanna/conPanna.lean`

Outermost namespaces:

```text
Theory
Unification
Narrowing
```

### `Theory`

`Theory` is the declarative equality environment shared by reasoning procedures. It records symbols uniformly across arities and attaches structural laws through `OperatorLaw`, currently including commutativity and associativity. Symbols not registered with a structural law are treated as free.

Important declarations:

- `Theory.OperatorLaw`
- `Theory.Symbol`
- root structure `Theory`

The user can place multiple symbols of different arities and different laws in one theory. Avoid arity-specific fields such as `binarySymbols`.

### `Unification`

Public semantic relations:

- `p ⋈ q`: free unifiability.
- `p ⋈[T] q`: unifiability modulo an explicit `Theory` value.

Architecture:

```text
Unification
├── Problem       -- recognize and saturate lambda-closure problems
├── Dispatch      -- select a backend from the explicit theory
├── Certificate   -- candidate, soundness, and completeness interfaces
├── Free          -- free-unification backend
├── C             -- free-commutative backend
├── Exposure      -- turn certified alternatives into user proof states
├── Tactic        -- tactic orchestration
└── Completeness  -- optional automation for the user obligation
```

The free backend exploits Lean's native definitional/constructor unification, but the surrounding problem extraction, basis-variable interface, candidate representation, certification, and proof-state exposure are implemented by this project.

The result interface is uniform across backends: each alternative exposes fresh basis variables and equations describing the original variables in terms of that basis. A C problem can expose multiple alternatives through the same interface.

Tactic forms:

```lean
unify h
unify h in SomeTheory
c_unify h
unify_complete
```

Certification policy:

- Candidate generation and certification are separate.
- Soundness of each returned alternative is normally discharged automatically.
- Completeness is mandatory but exposed as an ordinary user-level proof obligation.
- `unify_complete` is optional automation for easy completeness obligations; it is not part of candidate generation.
- This separation is intentional because completeness may be difficult or unavailable automatically for future theories such as ACU.

Typical proof shape:

```lean
example (h : left ⋈ right) : Goal := by
  unify h
  · unify_complete
  · -- one goal for a computed unifier
    ...
```

### `Narrowing`

Architecture:

```text
Narrowing
├── Problem
├── Goal
├── Backend
├── Materialization
├── Closure
├── Certification
├── Tactic
└── Subsumption
```

Narrowing extracts the equation between the rule LHS and source term, delegates structural solving to unification, substitutes each result into the rule RHS, and conjoins instantiated rule/source constraints. The resulting successor representations are combined into the post. `subsume` proves the remaining post-to-target inclusion.

The `narrow` user interface takes only the rule and source:

```lean
narrow rule against source
```

The user does not provide the intermediate successor or post; the tactic generates and binds it for the following subsumption phase.

## Examples and verification state

The extracted testcase namespaces are:

- `ex_framework`
- `ex_unification`
- `narrowing_examples`
- `c_unification_examples`
- `theory_examples`

All five testcase files were fully elaborated successfully after extraction. The registered core targets also passed `lake build`. After removing examples from the core files, the observed rebuild was approximately 15 seconds for Expresso and 8.2 seconds for conPanna.

The project currently has no Mathlib dependency; it imports Lean directly and pins `leanprover/lean4:v4.25.0-rc2`.

Use Lean LSP tooling by default:

- run diagnostics after edits;
- use goal inspection and multi-attempt tooling while developing proofs;
- use `lake build` when imports or module boundaries change;
- avoid `lake env lean <file>` unless LSP diagnostics are unavailable or inconclusive.

Because the testcase directory is not registered, plain `lake build` checks only the two core library roots. Check testcase/example files directly with Lean LSP.

## Current `examples/rw.lean` work

This file models the Maude readers/writers example. Its current `inv'` explicitly expands `inv` while asking Lean to infer every type:

```lean
def inv' :=
  (fun N => framework.Patterns.APattBody.mk (Conf.mk N o) True) ⊔
  framework.Patterns.APattBody.mk (Conf.mk o (s o)) True
```

This elaborates successfully as:

```lean
Disjunction (Natural → APattBody Conf) (APattBody Conf)
```

The fully qualified `framework.Patterns.APattBody.mk` is needed because exporting the short type name `APattBody` does not export its constructor namespace.

At the time of this handoff, `examples/rw.lean` is modified in the Git worktree. Preserve that user work.

## Working preferences and constraints

- Preserve unrelated or uncommitted user changes.
- Do not make tactics depend on testcase names or declarations.
- Keep user-facing modelling syntax free of explicit logical-variable constructors.
- Maintain backend-independent result and certification interfaces so AC and other theories can be added later.
- Do not change Lake/build configuration unless explicitly requested.
- Prefer small module boundaries for editor performance, but do not reorganize files beyond the requested scope.
- The current `conPanna` repository is the source of truth; the older `bakery/free-unification.lean` is historical prototype material.
