# Lean certification module

Start with **[Calculus.lean](Calculus.lean)**. It is the Lean mirror of the
proof rules in [Maude's CERTIFICATION-PRODUCER](../../certifier/certification.maude).
You do not need to understand the parser or semantic metatheorems to read a
certificate proof.

## Which file does what?

| File | Responsibility | Read it when… |
| --- | --- | --- |
| [Calculus.lean](Calculus.lean) | Surface judgments and inference rules: `Equality`, `Derives`, `Complete`, soundness evidence, and checked `SideCondition` witnesses. Includes comments mapping rules to Maude labels. | Understanding or writing a certificate by hand. |
| [Semantics.lean](Semantics.lean) | Proves the surface rules valid against registered `Structural.Indexed.NativeEq`. `Worklist.exact_system` combines completeness and soundness into the semantic certificate; `exact` handles one equation. | Understanding why rule evidence proves the original semantic goal. |
| [Syntax.lean](Syntax.lean) | Sorted variables, constructor terms, substitutions, equation/state data and successor computations. | Understanding the data supplied to a rule, or its computed child state. |
| [Parser.lean](Parser.lean) | Reads JSON bundles and their Lean type/proof strings; renames dependencies, elaborates evidence and installs checked intermediate declarations. Rejects unresolved variables, holes and `sorry`. Imports only Lean. | Understanding how Python output becomes Lean proof expressions. |
| [Client.lean](Client.lean) | Generates profile metadata, exports requests and calls Python. Connects replies to the parser with a host-fixed expected goal. | Understanding the Lean/external-engine boundary. |
| [Core.lean](Core.lean) | General constructor/ACU semantics and syntactic `Profile` metadata; quotient/flattening invariants supporting rule-validity proofs. | Investigating the semantic foundations, not ordinary certificates. |
| [Sharing.lean](Sharing.lean) | General finite-sharing arithmetic and semantic decomposition proofs, including repeated variables. | Investigating why balanced sharing supports represent solutions. |
| [Enumeration.lean](Enumeration.lean) | Exhaustive support enumeration and its correctness; singleton/zero metatheorems. | Investigating the FINITE-SHARING, ATOM or ZERO foundations. |

Files retain the `DirectCertification` namespaces; filenames are architectural
boundaries, not additional user-facing namespaces.

## Reading a certificate

The surface has three levels:

- `Equality`: structural equality without equation assumptions.
- `Derives`: equality justified by the current equation assumptions.
- `Complete`: every solution of the current state is covered by the fixed answers.

Separate soundness evidence checks each proposed answer against the original
equations. A certificate applies these rules, then uses `Worklist.exact_system`
once. It does **not** repeat their semantic induction proofs.

See `atom_surface_certificate` in
[examples/certification-demo.lean](../../examples/certification-demo.lean):
one explicit ATOM → COVER / COVER tree, followed by the soundness row.
The generated counterpart uses the same calculus and checked witnesses.

## Automated path and where replay happens

```text
Client: export fixed problem E₀, theory B and already-known answers Σ
  → Python/Maude: construct evidence for that fixed Σ
  → Parser: load typed DATA and surface-rule applications in dependency order
  → Parser: elaborate the root exact_system application against the host's goal
  → caller installs the final theorem; Lean's kernel checks it
```

Replay is ordinary checking of rule applications, **not another unification
search**. `ReplayState.accept` in Calculus checks that an explicit child snapshot
equals the rule-computed successor. `SideCondition` checks head distinctions,
all branch slots and equality with the exhaustive support table.

`LeanReady.produce` certifies supplied answers and never reruns native unification.
The optional `LeanReady.coordinate` obtains native answers first, then certifies
them. Python constructs evidence but does not invoke Lean or become trusted.

## Dependencies and current boundary

The semantic import chain is
`Core → Sharing → Enumeration → Syntax → Calculus → Semantics → Client`;
arrows here mean “is imported by.” Independently, `Parser` imports only Lean,
and `Client` imports `Parser`.

The external producer currently supports one stratified ACU bag fragment with
free payload constructors. Accepted proofs establish semantic validity; that
is distinct from a formal guarantee that search always succeeds. Production
narrowing integration and automatic native-model export remain later work.

For the complete calculus, contract and search argument, see
[CERTIFICATION.md](../../CERTIFICATION.md). For remaining milestones, see
[TODO.md](../../TODO.md).

To check the maintained demos from the repository root:

```sh
python3 -B tests/test_certification_compiler.py --build
CONPANNA_COORDINATOR_DEMO=1 python3 -B tests/test_certification_compiler.py --demo
python3 -B tests/test_certification_compiler.py --negatives
```

Keep positive and negative consumers separate under the existing resource caps.
