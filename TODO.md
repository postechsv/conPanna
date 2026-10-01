# TODO

## Short-term goal: certified constrained narrowing

**Active milestone:** proof-producing Maude unification for Bakery, replacing
candidate-only results and user completeness holes. Read the NEXT SESSION section
of HANDOFF.md for the precise contract, entry points, blockers and restart prompt.
The dump/parser are now part of this milestone, not indefinitely deferred work.

Agreed pipeline (2026-10-01):

1. Encode the user's native constructors and registered structural laws as
   first-order data for Maude. Keep arbitrary Lean constraints in Lean.
2. Run the certification calculus as object-level Maude rewrite rules to compute
   unifiers together with a derivation preserving the entire solution set.
3. Replay the certificate in Lean and transport soundness and completeness back
   to the user's constructors through a faithful native-semantics bridge.
4. Attach substituted rule/pattern constraints to the successors and use generic
   lifting theorems to obtain the post-image and its exactness certificate.

All term wrappers, sort/symbol identifiers, and variable indices are internal.
Users keep their own constructors, structural declarations, and pattern syntax.
The native bridge must preserve and reflect EqMod. Transporting constraints along
modulo-equal variable assignments requires congruence of those predicates, or a
wrapper retaining representative witnesses. Feasibility need not be decided:
an infeasible residual constraint denotes an empty successor.

### Current prototype and next step

- First integration increment verified (2026-10-02): shared `ModRelation` pattern/
  rule semantics; universal `ModCertificate.exactnessType` with modulo equations
  at each variable's sort; generic `witnessPost_exact` retaining original constraint
  assignments. The lift has no axioms. Wrapper regressions cover exact post-image
  lifting and zero/one/two-family contract shapes. Production materialization,
  backend proof results and named-post automation are not wired to it yet.
- Second increment: `certify_structural BakeryTheory for Conf` now generates
  metadata for the actual four sorts and nine constructors. Syntactic round trips
  and typed law transport are checked without admissions.
- Third increment: generic sorted-tree ACU rebuilding/checker transport plus a
  manually instantiated interpretation of Bakery's generated native algebra.
  `BakeryCertificate.two_families` replays the primitive trace for the whole
  two-family solution disjunction of P+Q = singleton(idle)+R. ProcSet assignments
  may contain any Mode/Nat payloads. Three-field Conf decomposition and the same
  certificate at the root also check. Dependencies: only propext and Quot.sound.
  Semantic interpretation generation and payload-variable solving remain gaps.
- Fourth increment: existing dumps now have a `certification` mode and native
  query exporter. Version-1 packets retain full sorted signature, native input,
  variable scopes, atom dictionary and projection path. The shared Maude engine
  returns both families plus explicit fixed-plan certificate DATA. A generated
  Bakery script runs; unsupported payload variables/counters/repeated variables
  fail explicitly. Nat literals now translate to zero/succ constructors.
  No reply parser or checked external solver result is integrated yet. Packet
  IDs are independent of generated Lean indices and native payload codes.
- ONE active Lean experiment: `certification2.lean`. Start with
  `BakeryCertificate.two_families` at the bottom.
- General library code, automatic registration, and the single main
  user proof are clearly separated. Superseded experimental Lean files were
  removed; do not add more intermediate files without a concrete need.
- Primitive ACU certificate replay, capture-safe elimination, indexed constructor
  semantics, wrapper inversion, and the two-unifier native example are proved
  without admissions. Rejection/capture regression checks are retained.
- Registration needs syntactic sort/symbol tables, quoting/round trips and
  existing law witnesses—not user freeness, reflection or unification proofs.
  `certify_structural T for Conf` now generates it for many-sorted first-order
  datatypes with one ACU operator. The wrapper fragment retains its specialized
  metadata. Put the annotation beside T's declaration. Unsupported signatures
  are rejected explicitly.
- The indexed relation has a proved map INTO existing Structural.EqMod, not an
  equivalence with all old derivations. Indexed signatures, native registration,
  and the forward bridge now live in conPanna.Structural. `=[T.certified]` opts
  into indexed equality; `=[T]` and existing narrowing retain their semantics.
- `certification2.maude` loads the shared `conPanna/certification.maude` engine
  and remains the original trace regression. `examples/bakery-certification.maude`
  demonstrates the new packet/proposal path. No general search, automatic trace
  accumulator, reply parser or automatic native replay yet.
- `Certification2.BakeryExamples` checks three simple exact unit/variable-solving
  examples against the real old BakeryTheory. It does not test Bakery ACU
  splitting, reflection or the external certificate pipeline.
- `ModCertificate.exactnessType` now uses modulo factorization. The old manual
  obligation is named `literalCompletenessType` and remains in existing lifting.
  Integrate `witnessPost_exact` into materialization/lifting before claiming
  automatic structural completeness; changing the proposition alone is insufficient.
- Next: parse/check the new versioned Maude reply against its exact native
  request, then connect kernel replay for the supported ground-idle query.
  Automate semantic interpretation using general free-constructor/ACU fragment
  proofs before broadening the profile. Validate packet-to-native sort/atom
  mappings: wait(3) has dictionary ID 0, but BakeryEncoding.code is 7.
  Extend the calculus to sorted payload variables before integrating Bakery's
  actual overlaps. Migrate structural rule/pattern semantics and narrowing to
  certified theories. The explicit indexed
  path is transitional, not a reason to build two independent narrowing engines.
  Core changes were authorized; keep reporting semantic migration boundaries.
- Repeated-variable search/termination and checking complexity remain research
  tasks; successful finite certificate checks do not establish a full algorithm.

### Active integration stages (after settling the semantic contract)

- Certification model/query dumping implemented for the restricted overlap shape;
  broaden only as the calculus and native proofs support new problems.
- Untrusted reply parsing, certificate transport, and proof-interface integration.
- Native registration/faithfulness automation and constrained-narrowing lifting.
- Bind the certificate to the exact signature, input equation, and decoded
  unifier family. Reject partial results and malformed/captured/wrong-sort traces.
- Remove Bakery's three hcomplete holes only after the resulting theorems check
  without admitted axioms; retain independent subsumption/domain proofs.
- Maude metaprogramming is optional: ordinary rewrite rules and traces, or an
  explicit certificate accumulator, should suffice for the initial experiments.

## Long-term constrained reasoning

- Use `overlaps` for semantic nonempty intersection between patterns;
  unification is the syntactic process used to determine overlap.
- Describe symbolic results as `over` approximations when only completeness is
  guaranteed and `under` approximations when only soundness is guaranteed.
- Share one constrained-unification core between universal and existential
  one-step narrowing.  Universal proofs consume an over-approximation and
  finish with subsumption; existential proofs consume an under-approximation
  and finish by proving overlap.
- Keep residual-constraint feasibility in the ordinary Lean continuation, not
  as an additional solver certificate.  Infeasible branches may be pruned only
  with a Lean proof of unsatisfiability.

## Maude backend

- Cache generated Maude modules by root state type and structural theory, so
  identical modules are not repeatedly inspected and rendered for atomic
  unification and matching queries.
- Investigate batching queries or reusing a persistent Maude process, so
  multiple queries can share one loaded module instead of launching Maude for
  every query.
