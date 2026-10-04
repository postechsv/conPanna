# conPanna development handoff

This document records the design decisions and current implementation state needed to continue development in a new conversation. The current repository is `/home/byhoson/workspace/conPanna`.

## Current milestone: direct native certification (2026-10-04)

Read THIS section first; the older NEXT SESSION plan below is historical.

- Active experiment: `certification.lean`, not `certification2.lean`. It imports
  only `examples/bakery_acu.lean` (model-only, no Mathlib or safety proofs).
  The older indirect encoding/calculus remains untouched for comparison.
- `deriving ACU` is now a real deriving handler in `conPanna/Structural.lean`.
  It accepts exactly a nullary unit, unary singleton of another sort, and binary
  self-operation. Roles are inferred from types, not constructor names. This is
  syntactic metadata, not false laws of literal Lean equality on constructors.
- `structural BakeryTheory for Conf` discovers the one derived ACU fragment
  reachable from State Conf, registers the laws and generates indexed/native
  registration automatically. No nontrivial user registration proof. The explicit
  root excludes unrelated imported State instances. Existing `structural ... where`
  and `certify_structural` syntax still work.
- Generic direct metatheorems now include SplitAtom, MutateACU (four-piece
  refinement), and AtomicRemainder (two solution families for X+Y = atom+R).
  All are proved against Structural.Indexed.Eq, with automatic native specialization.
  Lists of quotient classes of those SAME trees are internal proof auxiliaries;
  there is no independent Value/ACU semantics or per-model bridge.
- `derive_direct_profile profile for T.certified` mechanically classifies signature
  heads, supplying cases/rfl metadata. `certify_direct profile` reifies a native
  exactness iff and checks a finite certificate. No problem-specific supporting
  lemma, constructor name, admission, or Mathlib automation is used.
- Prototype `certify_maude name for Conf mod T.certified using profile : lhs with rhs`
  exports the existing native signature, runs native Maude `unify`, parses ALL
  answers through the existing parser/SolutionSet, generates the actual proposition
  with ModCertificate.exactnessType, and reconstructs the direct proof against it.
  Idle and wait(3) remainder queries both return TWO families and are kernel-checked
  with only propext and Quot.sound. Native union argument ordering is reconciled
  through proved commutativity, not trusted comparison or literal equality.
- Boundaries: certificate instructions are selected locally from supported semantic
  macro rules, NOT fetched from Maude proof search yet. Family comparison supports
  logical congruence/branch reordering and binary ACU commutations, not general ACU
  normalization. Remainder output has a compact specialized finite syntax;
  generalized binders/elimination are still a checker extension. Multiple ACU
  fragments, free-constructor inversion, nonlinear problems and general certificate
  search are not supported. Generated declarations reject unresolved proof holes.
- Semantic migration boundary is unchanged: =[T.certified] is indexed equality;
  =[T] and existing Bakery narrowing still use legacy EqMod. Only the forward map
  indexed -> legacy is proved. Production narrowing's completeness holes were not
  touched and must not be claimed solved by these prototype examples.
- Next: use the now-proved direct Mutate/Split rules in answer-guided certificate
  search, then add general existential substitution/elimination and constructor
  decomposition for real Bakery overlap queries. Keep one active certification
  file and use LSP diagnostics/axiom checks. Do not add intermediate Lean files.
- Verification: lake build, model-only file, direct certification file and existing
  Bakery pass. LSP axiom checks on direct Mutate and native remainder certificates
  report only propext/Quot.sound, no source warnings. Existing examples/upair.lean
  fails its old completeness-to-mapsInto lifting at lines 164/188/203; the SAME
  errors reproduce with HEAD's unchanged Structural.lean compiled in /tmp, so
  these are pre-existing, not caused by deriving ACU. Not fixed in this milestone.

## NEXT SESSION: proof-producing Maude unification (2026-10-02)

Read this section FIRST. The long historical notes below are not the active plan.
Baseline commit: `20b1b7a` (Add Bakery certification dumps and explicit Maude
proof proposals). All four integration increments below are committed. The
working tree was clean when this handoff refresh started; this refresh changes
only HANDOFF.md. No code changes or new verification runs in the handoff turn.

Immediate milestone: parse the actual version-1 Maude reply, validate its exact
request/output, and kernel-replay its certificate for Bakery's ground-idle
overlap. The resulting native iff must USE the fetched/parsed certificate, rather
than reuse the existing manually mirrored theorem as evidence of integration.
Reject an omitted branch and a changed request in that same path. Keep the
current fixed strategy; general search and narrowing integration come later.

### First integration increment: exactness and constraint witnesses

The user approved implementation in small verified steps and requested simple,
readable library code. Continue that authorized work; no new implementation
approval is needed. Do not commit unless asked.

- `StructuralSemantics` now accepts any theory with `ModRelation`, including
  `CertifiedTheory`. Legacy theories still select old EqMod. One set of pattern,
  rule, post-image and subsumption definitions serves both relations. Narrowing's
  subsumption-goal reader was adjusted for the extra implicit theory-type argument.
- `Certificate.factorizationTypeWith` / `solutionSetTypeWith` accept a relation.
  `ModCertificate.exactnessType` builds the universal input/output iff using the
  relation at EACH variable's native sort. This is a proposition builder, not a
  checked solver result or a parser. Literal factorization remains available for
  free unification. The old manual structural obligation is now explicitly named
  `literalCompletenessType`; existing tactic lifting still consumes that obligation.
- `framework.Rules.witnessPost` retains original rule/source assignments and
  their constraints, together with a factorization predicate. `witnessPost_exact`
  proves an exact post-image from a universal unification iff and an equivalence
  relation. It needs no predicate congruence and has NO axioms. It is not yet
  wired into `Materialization.successor` or the named-post tactic.
- `Certification2.IndexedExample.ContractRegression` checks the two-family
  exact post with a literal constraint that distinguishes ACU-equal values.
  Its theorem `constrained_two_unifiers` uses only propext and Quot.sound.
  Contract tests exercise Bag/Conf variables, zero/one/two alternatives and a
  changed type when a branch is omitted. These are wrapper-model regressions;
  Native Bakery replay is covered in the third increment below.
- Verified with lean-lsp-mcp diagnostics and axiom checks, `lake build`, and
  `lake env lean` on certification2, Bakery, theory_examples and narrowing_examples. Bakery's
  three pre-existing hcomplete sorries remain. The wrapper theorem's pre-existing
  long-line warning remains.

### Second integration increment: generated Bakery registration

- `certify_structural BakeryTheory for Conf` is now beside the actual theory in
  `examples/bakery.lean`. It generates four sorts (Nat, Mode, ProcSet, Conf), nine
  typed constructor symbols, quoting/evaluation, both syntactic round trips,
  legacy law evidence and `NativeSort` instances for every sort. No native model
  was copied or redefined. The registration proof has NO axioms.
- Shared discovery/validation feeds two emitters: general native metadata and
  the existing unary-wrapper metadata needed by its checker proofs. Supported:
  one ACU operator, unparameterized/non-mutual first-order sorts, direct recursion.
  Unsupported fields/laws and an ACU operator outside the reachable signature
  fail before emission. Semantic cancellation, splitting and free-constructor
  inversion are not generated.
- `Certification2.BakeryRegistration` checks configuration round trips (no axioms),
  payload-constructor distinction in QUOTED SYNTAX, and unit transport through
  Conf followed by the forward legacy adapter (only propext). This proves neither
  the reverse old-EqMod bridge nor faithfulness to the ACU checker.
- Verified: `lake build`, full `certification2.lean`, Bakery, theory_examples and
  narrowing_examples; lean-lsp-mcp diagnostics and axiom checks. Bakery reports
  only its three pre-existing sorries; no new warnings from the registration.
- Bakery is outside the Lake library targets: `lake build +examples.bakery` is
  unsupported. After library changes rebuild its imported artifact with:
  `lake env lean -o .lake/build/lib/lean/examples/bakery.olean -i .lake/build/lib/lean/examples/bakery.ilean examples/bakery.lean`
  before checking `certification2.lean`; otherwise it may import stale metadata.

### Third integration increment: actual Bakery two-family replay

- `Bridge.rel_exact` proves relation reflection for every existing bridge.
  `Structural.Indexed.ACU.rebuild`, `rebuild_congr`, `observe_native` and `checker`
  are generic metatheorems/builders for any registered signature's ACU carrier.
  Atoms decode to actual sorted payload trees, not invented native constructors.
- `Certification2.BakeryEncoding` interprets the generated native algebra: Nat
  and Mode use literal equality; ProcSet uses portable ACU equality under an
  injective encoding of ALL Mode payloads; Conf retains both Nat fields and that
  ProcSet relation. Its model proves compatibility for all nine native symbols.
  The native retraction includes arbitrary wait/crit Nat values. No native model
  was redefined. This interpretation is manually instantiated in the prototype;
  automatic generation of semantic interpretations is NOT implemented.
- `BakeryEncoding.configuration_iff` proves three-field constructor decomposition
  for this interpretation. Semantic regressions reject wait/crit mismatches,
  both directly and inside singleton process sets.
- `Certification2.BakeryCertificate.two_families` kernel-replays the existing
  primitive trace for P+Q = singleton(idle)+R, proving iff the WHOLE two-family
  disjunction over arbitrary native ProcSet assignments. The root-level theorem
  `configuration_two_families` uses the same certificate plus decomposition.
  Both use only propext and Quot.sound; no sorryAx or new axioms. This certifies
  `BakeryTheory.certified`, not completeness for old BakeryTheory/EqMod.
- The checker equation has ProcSet variables and a ground idle payload. It does
  not yet solve variables inside payload constructors or across multiple sorts.
  The Maude trace remains manually mirrored data; no parser/search was added.
- Verified: lean-lsp-mcp full diagnostics and axiom/source audit, `lake build`,
  and full `lake env lean certification2.lean` (exit 0). Only the prototype and
  handoff/TODO were changed; no new library warnings or proof admissions.

### Fourth integration increment: certification dumps and Maude reply data

The user directed this increment toward the existing dump functionality and
`certification2.maude`. It establishes an export/reply DATA path, without claiming
automatic semantic interpretation or a checked external certificate pipeline.

- `Maude.Certification` reuses native signature/law discovery and pattern
  translation. `#dump_maude_model certification Conf mod BakeryTheory` exports
  a free first-order schema: qualified constructor identities, all argument and
  result sorts, and the single ACU bag/operator/unit. No native ACU attributes.
- `#dump_maude_query certification lhs =? rhs from Conf mod BakeryTheory`
  emits a runnable script with a version-1 Request: exact schema, sorted variable
  IDs, ground-atom dictionary, both native inputs, free-constructor projection
  path, and portable equation. Public Meta API: `Maude.Certification.exportQuery`.
  Supported search shape: X+Y = ground-atom+Z with three distinct ProcSet variables;
  enclosing free constructors must match with identical ground other fields.
- Explicitly reject payload variables, differing configuration fields, repeated
  variables, unsupported query shapes/laws, and ACU-containing payload sorts.
  Shared translation now expands Nat literals to zero/succ constructor syntax,
  fixing concrete counter/payload dumps (previously `0` was rejected).
- `conPanna/certification.maude` contains the previous object-level calculus and
  partial overlap strategy, plus schema/request/reply and Certificate DATA.
  `CERT2-SEARCH.certifyOverlap` returns `proposed(request, output, certificate)`.
  Both families remain ONE disjunction. The explicit certificate term is the
  FIXED plan for this strategy, not an automatically accumulated search trace.
  `certification2.maude` remains the original manual-trace/freshness regression
  driver, now loading the shared engine.
- `examples/bakery-certification.maude` is a runnable generated Bakery snapshot;
  its load path is adjusted relative to examples/. Run from repository root:
  `maude -no-banner -no-advise examples/bakery-certification.maude`.
  The dump syntax is documented beside Bakery's native registration.
- `Certification2.BakeryDump` checks the actual exported Maude result contains
  the whole expected disjunction and COMPLETE certificate data matching the
  previously kernel-checked plan. Guarded command tests
  reject symbolic payloads, mismatched counters and repeated variables. These
  are exporter regressions, NOT native certification proofs from parsed replies.
  Existing production candidate unification/matching still use their old path.
- Verified: lean-lsp-mcp diagnostics, `lake build`, fresh Bakery import artifact,
  full `certification2.lean`, theory_examples and narrowing_examples. Both Maude
  drivers run without warnings, return both families, and preserve the original
  freshness checks. Old dumps and a ground wait(3) payload dump also compile.
  Bakery reports only its three existing sorries; no new code warnings/admissions.

Important next boundary: reply parsing must validate the version and EXACT echoed
request, then parse/check the WHOLE output and certificate before decoding the
returned family. Packet sort/constructor IDs follow Maude discovery order, NOT
generated Lean Tag/Symbol indices. Ground-atom IDs are local dictionary indices,
NOT BakeryEncoding.code values: idle is 0 in this example, but e.g. exported
wait(3) is also dictionary atom(0), while BakeryEncoding.code(wait(3)) is 7.
Do not silently use such IDs with the old bridge. Validate native payload trees
and establish the atom remapping/native projection proof when integrating replay.
The schema and echo are data; they do not by themselves establish faithfulness.

Next: parse the versioned reply as untrusted data and connect kernel replay for
the supported Bakery ground-idle query, with exact request/output validation.
Automate the general semantic interpretation before extending beyond that fixed
profile; extend sorted payload-variable rules before claiming coverage of Bakery's
actual atomic overlaps. No-result, timeout or truncated stdout must not mean a
complete empty unifier family. Production proof-carrying results and constrained
lifting remain future increments; Bakery still has its three hcomplete holes.

### Fifth integration increment: fetched reply parsing and kernel replay

Implemented on top of 20b1b7a (uncommitted at time of writing).

- `Maude.Certification.exportQuery` now returns `Query {request, script}`;
  `request` is the exact request text with the schema expanded, as Maude echoes it.
  `Node`, `parseNode` and `parseReply` parse untrusted first-order reply DATA:
  exactly one `result Reply:` term, fully consumed, then `Bye.`. No result,
  trailing text or truncation is an error, never an empty family.
- `Certification2.Reply` (generic, before the Bakery sections): `decode` requires
  `proposed(...)`, the version-1 request EQUAL to the parsed sent request,
  sequential sort/constructor/variable/atom IDs, ACU-sorted variables, atoms in the
  dictionary, and `check input output certificate` on the WHOLE output. `emit`
  adds `<prefix>.input/output/certificate/atoms` constants; atoms are rebuilt with
  the packet schema's qualified native constructors and sort-checked. Also
  `Formula.mapAtoms`. Parsing is not trusted: kernel proofs re-run `check`.
- `Certification2.BakeryReply` runs Maude for the idle and wait(3) overlaps.
  `fetched_two_families`, `fetched_configuration_two_families` and
  `fetched_wait_families` use ONLY the emitted constants; packet atom IDs are
  renamed in the kernel via `remap` (decoded native tree -> BakeryEncoding code;
  wait(3) is packet 0, code 7). Axioms: propext, Quot.sound.
- Regressions: a changed echo (native sides swapped), an omitted branch, "No
  solution." and truncated output are each rejected with the expected message.
- Verified: `lake build`, Bakery artifact rebuilt (three existing sorries only),
  full `certification2.lean` with no warnings, theory_examples, narrowing_examples
  and both Maude drivers. lean-lsp-mcp was NOT available in that session.
- Gaps: native theorem statements are still written by hand (the checked output
  is not yet decoded into a native proposition or `SolutionSet`); the echoed
  native inputs/projection path are compared syntactically, not proved to denote
  the stated native equation; fixed strategy only; no payload variables; not wired
  into narrowing; Bakery's three hcomplete holes remain.

### User's requested outcome

Replace the current candidate-only Maude unification path with a proof-producing
path. Lean exports the native signature, structural laws, and an unconstrained
equation. Maude runs a rule-based unification calculus and returns BOTH the full
unifier family and a derivation. Lean parses and kernel-checks the derivation,
producing soundness AND completeness for exactly that returned family. Narrowing
then attaches the rule/pattern constraints and uses generic lifting theorems.
Supported Bakery examples should no longer require user unification certificates
or a `sorry` for the generated post's completeness. Subsumption/domain proofs
remain separate user work. Do not attempt existential narrowing in this milestone.

This is the intended architecture, NOT an already working automatic solver.
A new certification-calculus dump/query and result/certificate parser are needed,
but they are not the only missing pieces. Do not promise a complete ACU search
algorithm based on the single scripted trace currently present.

### What actually exists

1. **Production candidate path**: `conPanna/Maude.lean` collects native datatype
   constructors and laws, emits a functional LEAN-MODEL, runs built-in `unify`,
   parses stdout, and returns `Unification.Certificate.SolutionSet`. Despite the
   namespace name, this is substitution DATA, not a proof of completeness.
2. **Lean calculus**: `certification2.lean` contains `Rule`, `Certificate`,
   `applyRule`, `replay`, `check_exact`, and generic transport via `Bridge`.
   Successful replay proves an iff of solution predicates. The two-unifier
   `IndexedExample.wrapped_two_unifiers` and actual native Bakery
   `BakeryCertificate.two_families` are kernel checked without admissions.
3. **Maude data path**: `conPanna/certification.maude` runs the scripted overlap
   strategy and returns a versioned native request, whole disjunction and explicit
   fixed-plan certificate. `certification2.maude` loads it for the original manual
   trace regression. `Maude.Certification` exports actual Bakery requests. There
   is NO reply parser, general strategy, automatic trace accumulator or proof
   integration with this external reply yet.
4. **Library registration**: `Structural.Indexed` provides sort/argument-indexed
   signatures, trees, equality, native registration and a forward legacy map.
   `certify_structural T for Conf` now generates metadata for many-sorted native
   signatures with one ACU operator, including Bakery. Generic ACU rebuilding
   supports payload trees; the prototype separately instantiates a semantic model
   and retraction for Bakery. Only the wrapper interpretation is generated.
5. **Latest Bakery tests**: `Certification2.BakeryExamples` imports the actual
   model and proves three simple unit-normalization/variable-solving iff results
   against the OLD BakeryTheory/EqMod. They use general `NativeRules.normalize`
   and `shared`. These do NOT establish Bakery ACU cancellation, splitting,
   automatic native registration, or certificate replay. Their only axiom is
   propext. Do not inflate their significance.
6. **New Bakery replay**: `BakeryEncoding` and `BakeryCertificate` interpret the
   generated actual signature and certify the complete two-family ProcSet equation
   and its Conf wrapper. This interpretation is manually instantiated, and the
   theorem uses indexed equality. Payload-variable unification, automatic semantic
   generation and external certificate parsing remain unsupported. The new
   `BakeryDump` regression checks exporter/reply data separately from that proof.

### Read these entry points, not the whole repository

- `AGENTS.md`: interaction policy; compact explanations; no unrequested changes.
- `examples/bakery.lean`: `NamedPostPrototype` (around 296), native model and
  `BakeryTheory` / its registration (360–396), three user proofs (656–748). Current `narrow ... as post`
  is purely computational. Each proof separately leaves `hcomplete : rule ⊢
  bakeryInv ↪[BakeryTheory] post` as sorry. Do not confuse this interface with the
  older library tactic that opens a completeness bundle directly.
- `conPanna/Maude.lean`: `collectSignature`, `translatePattern`, `inspectTheory`,
  `renderModule`, `runMaude`, `solveWithMaude`, `parseUnifiers`, `toSolutionSet`,
  `solveStructuralTheory`, new `Certification` namespace/dump commands; existing
  backend registration remains before the dump code. Keep matching
  (`matchStructuralTheory`) separate; subsumption search is NOT this task.
- `conPanna/Unification.lean`: `Certificate.Alternative`/`SolutionSet`,
  `factorizationTypeWith`, `StructuralTheorySolver`, `ModCertificate.exactnessType`
  and `literalCompletenessType`,
  and `Constrained.instantiateOverlap`. `ProvenSolutionSet` is an existing
  witness-specialized structure, not automatically the desired universal exact
  solver-result type. Inspect its meaning before reusing its name.
- `conPanna/Narrowing.lean`: `Backend.solvePatternDetailed`,
  `Materialization.successor`, `CompletenessLifting.completenessBundleType` and
  `proveMapsInto`, `Tactic.runModCertified`. Existing lifting consumes user completeness.
- `conPanna/Structural.lean`: old `EqMod`/`ConstructorCongruence`, then
  `Structural.Indexed`, `CertifiedTheory`, `NativeSort`, `certify_structural`.
- `conPanna/StructuralSemantics.lean`: shared theory-generic semantics,
  `witnessPost` and `witnessPost_exact`. `Expresso/Expresso.lean`: actual rule,
  pattern, maps-into and subsumption semantics. Check definitions before changing
  equality or claiming a lifting theorem applies.
- `certification2.lean`: general rules first, checker/Bridge, generic wrapper
  transport, trace DATA, native two-unifier example, contract regressions,
  BakeryExamples, BakeryRegistration, BakeryEncoding, BakeryCertificate and
  BakeryDump at the end. `conPanna/certification.maude`: rule labels, partial
  strategy and version-1 protocol. `certification2.maude`: original trace driver.
  `examples/bakery-certification.maude`: runnable generated native query snapshot.

### Semantic blockers that MUST NOT be hidden

**Old equality vs indexed equality.** `=[T.certified]` is NOT definitionally the
old `=[T]`. The new indexed relation maps into old EqMod; the reverse has not
been proved. The previous inversion approach got stuck recovering argument
types from equality of arbitrary Lean function types. Explicit sort/argument
indices avoid that obstacle; no impossibility theorem for the old approach was
proved. Pick and explain a principled migration/faithfulness plan. Never certify
a stronger/different relation while silently using its completeness for old
EqMod. Avoid growing two independent narrowing implementations.

**Literal vs modulo factorization.** `ModCertificate.exactnessType` now uses
modulo factorization. The production manual path still uses
`literalCompletenessType` and substitutes literal equalities. For example, X =B
empty has the solution X := union empty empty, which factors through X ↦ empty
modulo B, but NOT by literal constructor equality. An oracle cannot prove a
false literal-factorization obligation. Changing the proposition also requires
updating the lifting code that currently substitutes literal equalities.

The desired exact structural certificate has this shape (all variables sorted):

    ∀ x₁ … xₙ,
      lhs(x) =B rhs(x) ↔
        (∃ u₁, ⋀j xⱼ =B σ₁ⱼ(u₁)) ∨ … ∨
        (∃ uₖ, ⋀j xⱼ =B σₖⱼ(uₖ))

Use the appropriate relation at EACH variable's sort, not just the root sort.
Completeness is left-to-right; soundness is right-to-left. Both bind the exact
input equation/signature and exact output family used by materialization.

**Constraints.** Unconstrained structural certification does not check
feasibility. Residual constraints are retained. But transporting arbitrary Lean
predicates across modulo-equal assignments is NOT automatically valid: use proved
predicate congruence or a semantics retaining representative witnesses. For
example, the literal predicate X = empty is not invariant under replacing X by
union empty empty. `witnessPost_exact` now proves the generic lift while retaining
representative witnesses. Integrating it into generated posts and the existing
subsumption continuation is still required; changing only the factorization
proposition cannot repair the old substitution-based lifting code.

### Implementation sequence / useful stopping points

1. Audit and settle the semantic result contract and native bridge before writing
   a large exporter/parser. Support Bakery's actual many-sorted first-order
   signature: Nat (zero/succ), Mode (idle/wait/crit), ProcSet (empty/singleton/union
   ACU), Conf (two Nat fields plus ProcSet). Do not clone/redefine the user model.
   Generate syntactic metadata; do not demand user freeness/reflection proofs.
2. Prove a small but genuine Bakery ACU example through the calculus: include
   payload constructors and an equation with two unifier families, e.g.
   P+Q = singleton(idle)+R. General metatheorems must be separated from the single
   example certificate proof. No problem-specific certification lemmas/tactics.
3. Implement a first end-to-end Maude result protocol on the already supported
   fragment. Prefer an explicit first-order certificate term/accumulator over
   scraping presentation-oriented trace text. Include format version, signature
   identity (or exact structural validation), sorted variable IDs/binder scopes,
   input, output families and rule/context steps. Reuse existing signature
   discovery/process execution where appropriate; a separate calculus encoding
   is required rather than just a cosmetic variant of LEAN-MODEL.
4. Maude search returns the whole solution disjunction plus certificate. Search
   may be heuristic or partial initially, but never present partial exploration
   as complete. One derivation preserving a whole disjunction is different from
   one successful search branch. Account for simplification/normalization too.
5. Parse as untrusted data, replay kernel-checkable Lean rules, then decode the
   CHECKED final formula into exactly the returned SolutionSet. If substitutions
   are printed separately, check that they agree. Reject unknown rules, wrong
   sorts, stale inputs, capture, omitted branches, timeout and truncated output.
   Native Maude `unify` output alone must not count as completeness evidence.
6. Extend to the finite collection of atomic equations actually generated by
   Bakery. Add a proof-carrying backend result containing soundness/completeness;
   wire it into generic constrained-narrowing lifting, then remove the three
   Bakery hcomplete holes. Preserve named posts and separate subsumption proofs.

Do this in verified increments; no requirement to finish it all in one turn.
The user explicitly permits core improvements that simplify the integration,
but report meaningful changes to the semantic contract instead of silently
patching around it. No unrelated work, caching, existential tactics or dm-check.

### Acceptance / trust boundary

- Selected Bakery calls compute unifiers and kernel-checked certificates without
  user certification holes, new axioms or admitted dependencies. Both directions
  are available; universal safety consumes completeness, not soundness.
- Zero, one and multiple-unifier cases; free-constructor mismatch, repeated
  variables, ACU unit and fresh-variable capture; malformed/omitted-branch
  certificates rejected. Unsupported problems fail explicitly, not as success.
- Attach constraints without sending Lean predicates to Maude or pretending
  feasibility was checked. Soundness/completeness of the POST must be lifted by
  proved general lemmas, not identified with unification exactness by assertion.
- Use lean-lsp-mcp for feedback and axiom checking. Run the library build and
  check affected examples; report pre-existing warnings separately. Importing
  Bakery brings some sorries, so inspect theorem dependencies, not import names.
- Keep one active Lean prototype (`certification2.lean`) until code is ready for
  the library. No proliferation of intermediate Lean files. Kernel check rules
  need not follow Maude's search strategy; do not claim polynomial checking or
  complete/terminating search without establishing it.
- Recommend a concise descriptive commit message after edits, as plain text
  WITHOUT backticks. Do not make a git commit unless asked.

### Copy-paste prompt for the new session

> Read AGENTS.md, the NEXT SESSION section of HANDOFF.md (including its restart
> prompt), and TODO.md. Baseline: 20b1b7a; all four implementation increments are
> committed. Continue the authorized Bakery work in small verified steps.
> Inspect Maude.Certification in conPanna/Maude.lean, conPanna/certification.maude,
> examples/bakery-certification.maude, and the Bridge/BakeryEncoding/BakeryCertificate/
> BakeryDump sections of certification2.lean. Propose a compact plan, then implement
> the untrusted version-1 reply parser and kernel replay for the ground-idle overlap.
> Validate the exact echoed schema/native inputs/variables/atom dictionary/projection,
> and bind the whole returned output to the parsed certificate. Prove the native
> two-family iff USING fetched certificate data; reject omitted branches and changed
> requests. Packet sort/symbol IDs and atom IDs are not Lean indices/native codes.
> The indexed-to-old-EqMod map is only forward; Bakery's three hcomplete holes remain.
> Keep native constructors and named-post/subsumption interfaces. Keep library code
> simple, general rules separate from examples, and one Lean prototype. No new
> axioms/sorries, model-specific certification tactics, existential narrowing or
> dm-check. Use lean-lsp-mcp; rebuild Bakery's import artifact as recorded before
> checking the prototype. Report demonstrated capabilities and remaining gaps.
> Recommend a plain-text one-line commit message after code edits; do not commit.

## Previous verified certification milestone (2026-10-01)

ONE active Lean prototype: `certification2.lean`. Read the header guide and jump
to `IndexedExample.wrapped_two_unifiers` for the native two-unifier theorem.
The obsolete `certification.lean` and intermediate bridge/diagnostic Lean files
were removed. Keep further experiments in this file unless separation is necessary.
The companion `certification2.maude` is unchanged.

The consolidated file contains general rule metatheorems and exact replay,
generic positive-formula transport, ACU/free-wrapper metatheorems, and one main
native certificate proof. conPanna.Structural now owns the indexed constructor
semantics, native registration, and `certify_structural T for Conf` generator.
The demo needs one annotation, not handwritten metadata or semantic obligations.
The generator currently supports one ACU datatype with nullary atoms and a free
unary state wrapper; other signatures fail explicitly. No new Lean files added.

Important boundary: `=[T.certified]` selects the new indexed library relation,
which maps into existing Structural.EqMod. No reverse bridge for all old
derivations has been proved. `=[T]` and current narrowing retain their meanings.
This is not yet a complete ACU search procedure, automatic trace importer, or
Bakery certificate. Do not present this demo as certifying current narrowing.

User requirement: no nontrivial semantic registration obligations. Registration
contains syntactic metadata/round trips and existing law witnesses; reflection
and wrapper inversion are library theorems. The user also requires reporting
library limitations and proposing core improvements instead of accumulating
legacy workarounds. Core improvements are now explicitly authorized. Next extend
registration/checker transport to Bakery's richer signature, then migrate rule/
pattern semantics and narrowing to certified theories. Keep the migration explicit
rather than silently reinterpreting old EqMod. See TODO.md.

The remainder records historical design context, not the current work queue.

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
- `Rule α R`: semantics for one atomic rule representation, including lambda
  closures.
- `Rules α R`: semantics for an atomic rule or a finite nondeterministic
  choice of rules.
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
