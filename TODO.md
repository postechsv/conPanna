# TODO

## Urgent: a general, terminating ACU certification algorithm (2026-10-05)

This DESIGN milestone takes priority over the implementation stages below.
Do not extend certificate search or narrowing until the algorithm and its
correctness argument are credible at technical-report level.

- Target: for every model satisfying an explicit constructor-only, many-sorted
  contract, and every finite sound and complete native Maude unifier set, the
  certification procedure terminates and emits a Lean-accepted exactness proof.
  An accepted certificate must remain sound independently of Maude's correctness.
- Initially support one ACU component plus free constructors; allow arbitrary
  finite problems, variable sharing/repetition, multiplicities, and empty answers.
  No fixed depth bound, one-tail restriction, or problem-specific control.
- Keep rules indexed by their operator and leave a boundary for combining
  multiple structural theories. Multiple ACU components are the next extension;
  other theories, including AU, are future work, not part of this first theorem.
- Specify the complete proof calculus AND terminating search control, using
  established rule-based algorithms as the foundation. Validate unit collapse,
  repeated-variable reconciliation, constructor decomposition, failure, and
  coverage closure before implementing them.
- Native answers should permit CHECKED early closure of entire branches, rather
  than merely matching final leaves. Preserve a complete terminating fallback;
  claim performance improvements only where justified or measured.
- Explain the mechanism with concrete small equations and plain language.
  Separate proved checker soundness from missing search completeness/termination.
  Keep research/design ahead of implementation and discuss unresolved gaps.
- Current implementation proves replay rules and numeric finite sharing, NOT a
  general ACU certification algorithm. The old bounded shape-specific search was
  removed; no general replacement search is implemented yet. No production
  narrowing changes during this milestone.

### Design checkpoint: finite sharing, not unrestricted mutation

Status: a candidate mathematical design, NOT an implemented general algorithm.
Keep the implementation gate closed until the whole-model argument below is
written and reviewed. A few finite examples do not discharge that argument.

Initial contract to make explicit:

- The ACU carrier has exactly empty, singleton : Atom -> Bag, and union :
  Bag -> Bag -> Bag constructors, as inferred by the existing deriving handler.
- Atom and all its reachable payload sorts are free first-order datatypes and
  cannot contain the Bag carrier. Free configuration constructors may contain
  bags. This stratification is a modeling restriction, not a variable-linearity
  restriction. Arbitrary repeated variables and finite equation systems remain
  allowed. Multiple/nested ACU theories are a later combination theorem.
- Terms use constructors and variables only; no domain predicates or additional
  equations. Certification uses the indexed registered relation. Do not silently
  claim an equivalence with the legacy relation or a result for arbitrary
  ACU-plus-free signatures.

Candidate mechanism, explained as bags of elements (a is a singleton):

1. Decompose free constructors and propagate their variable bindings, retaining
   all sharing. Collect bag equations; solve free payload equations normally.
   Only free-constructor cycles are immediate failures. X = X + Y instead has
   the ACU solutions Y = empty, with arbitrary X.
2. Flatten a selected bag equation and cancel identical bag-variable occurrences.
   Temporarily name each explicit singleton A, retaining A = singleton(payload).
   The remaining balance equation contains bag variables only. Preserve variables
   that cancel completely as unconstrained parameters.
3. Place each left occurrence against each right occurrence in a finite grid.
   Each cell denotes a shared piece of bag. A support is a nonempty subset of
   cells. It is balanced when all occurrences of the SAME input variable have
   the SAME number of selected cells. Give each balanced support its own bag Z;
   the image of an input variable includes Z as many times as that support uses
   each occurrence of that variable. Z may be empty: unit collapse is built in.
   Keep all balanced supports; computing only minimal ones is unnecessary.
4. Enforce the retained singleton equations. A sum equal to one singleton has
   exactly one nonempty summand; it equals that singleton, and all other summands
   are empty. If a parameter occurs twice in that sum it must be empty. Shared
   parameters remain shared across ALL singleton equations. Two singleton
   assignments to one parameter require a free payload unification, not a guess
   that the payloads differ.
5. Compose substitutions through the remaining bag equations. On each resulting
   unconstrained solution family, find and CHECK a whole-image-vector factor
   through a native proposed answer. Check each proposed answer's soundness
   separately using constructor congruence and ACU equality normalization.

Concrete nonlinear checks of the mechanism:

- X + X = Y + Y + Y: a 2-by-3 grid has one nonempty balanced support. It gives
  X = Z + Z + Z and Y = Z + Z, including the empty solution Z = empty.
- X + X = a + Y: write A = a and solve X + X = A + Y. The finite supports give
  coefficient vectors (X,A,Y) = (1,2,0), (1,1,1) twice, (1,0,2), and (2,2,2).
  A = a forces the coefficient-2 parameters empty and chooses one coefficient-1
  parameter to be a. The result is X = a + Z, Y = a + Z + Z. Duplicate support
  presentations may be retained; they are not missing or spurious solutions.

Why the finite-support step might suffice generally:

- Boudet--Contejean, "Syntactic" AC-Unification (1994), Theorem 2 establishes the
  finite-support property for minimal nonzero multiplicity solutions of a single
  balance equation; Sections 3.2--3.3 use it for nonlinear sharing and control.
  https://www.lri.fr/~contejea/publis/1994ccl/main.pdf
- Adaptation to our ACU bag semantics: for each concrete element, its multiplicity
  vector satisfies that balance. Subtract minimal nonzero vectors until it is
  zero. Theorem 2 represents each minimal vector by a balanced support. Collect
  elements into the corresponding Z bags. This explains coverage of arbitrary
  bags, not only bags containing the atoms mentioned by the query.
- Soundness is simpler: a selected cell contributes once on each side; balanced
  supports respect repeated-variable identities. Every parameter assignment
  therefore solves the pure bag equation modulo ACU.
- With p left and q right occurrences there are at most 2^(p*q) supports. Atom
  choices and free payload unification are finite. Sequential composition over
  finitely many bag equations is finite, even though intermediate sizes can grow.
  This is an exponential fallback, NOT a polynomial-time or short-certificate
  claim. Multiplicities occur in the once-for-all correctness argument; there is
  no separate Diophantine solver to trust in problem-specific certificates.

Whole-model proof outline to review (not a claim about current executable code):

- Think of sorts in three layers: free configurations above bags, the bag carrier,
  and free payloads below bags. A payload cannot lead back to a bag by the contract.
- Free configuration decomposition and elimination terminate by the ordinary
  free-unification argument. A cycle involving a configuration variable can only
  pass through free constructors, because that sort cannot occur inside a bag's
  payload. Leave bag comparisons for the bag phase instead of rejecting them.
- The bag phase creates only bag parameters and free payload comparisons, never
  fresh configuration equations. Free payload unification creates no bag equation.
  Thus there is no alternating configuration/bag/payload recursion to control.
- For each remaining bag equation, finite sharing plus singleton splitting gives
  finitely many unconstrained symbolic unifiers. Substitute each into the rest of
  the finite original bag-equation list, and recurse on that shorter list. The
  sharing of parameters is preserved by substitution composition, not by solving
  different occurrences independently.
- Induction on that list proves complete coverage of the whole problem. Each
  final family is itself a symbolic unifier, so a complete native CSU must contain
  an answer through which it factors. A complete whole-vector matcher can find
  that factor; checked equality traces justify it in Lean.
- A zero-sided equation forces every remaining summand empty. An explicit
  singleton among those summands is an actual contradiction. If both sides
  cancel to empty, all remaining input variables stay unconstrained. These cases
  are not omitted because the support grid has no cells.

Proof-system boundary and targeted search:

- A general FiniteSharing rule needs a semantic completeness metatheorem over
  the registered constructors. It must validate the exhaustive support family;
  checking that each supplied support is balanced alone does NOT prove coverage.
- Constructor decomposition, cancellation, variable elimination, singleton
  splitting, actual contradiction, finite sharing, and checked coverage closure
  are proof rules. Do not turn a merely redundant branch into a contradiction.
- A closed branch needs ONE substitution beta that covers its WHOLE family.
  For X = a + R and Y = a + R + R, an answer X = a + Z, Y = a + Z + Z closes
  with beta(Z) = R. This is universal coverage, not finding one feasible instance.
- Native-guided early closure is an optimization before further branching. A
  failed shortcut must use the complete finite fallback. Global soundness and
  completeness of native answers are not assumed by certificate checking.
  The SUCCESS theorem uses symbolic CSU completeness (factorization of every
  syntactic unifier on the original input variables), not merely ground coverage.

Remaining DESIGN obligations before code:

- Write the exact finite-sharing rule and native semantic statement, including
  cancellation, zero-sided equations, unconstrained variables and substitutions.
- Complete the proof that constructor decomposition/variable propagation cannot
  generate endless cross-sort cycles under the stated stratification, and that
  solving singleton payloads cannot create new bag equations.
- Establish sound/complete composition across a finite equation system and
  guaranteed factorization through every correct native symbolic CSU using a
  complete ACU matcher. Preserve all original-variable images and shared scopes.
- Specify how exhaustive finite sharing is CHECKED and prove the general rule;
  an informal search argument must not become an unchecked Lean proof premise.
- Explain the cost honestly. Early closure can save work; no universal speedup
  over native unification or over an independent complete solver is established.

### Precise core metatheorems: completeness first (2026-10-05)

Status: mathematical specification and informal proof decomposition, NOT new
Lean theorems or executable search. Prioritize reconstruction completeness over
termination. Keep all implementation claims above unchanged.

Semantic boundary:

- Write =B below for the EXISTING indexed NativeEq at the appropriate sort.
  FiniteSharing itself needs a registered ACU operator and the existing Profile
  (one ACU operator per sort), not rigid payloads or a new semantic bridge.
- Already present in certification.lean: flatten_congr, eq_of_flatten_perm,
  qfold_flatten, cancel, zero_of_mass, split_atom, and native transport. Internal
  quotient atoms identify payloads modulo their registered equations. Do not
  replace payload equations by literal equality unless rigid_native applies.
- The initial SEARCH contract still separates the bag carrier from its free
  payloads. More general semantic rules do not by themselves prove a complete
  search strategy for multiple/nested ACU components.

Exact FiniteSharing statement:

1. Cancel syntactically shared variable occurrences using the proved bag
   cancellation rule. The remaining active bag variables occur on only one side:
     a1*X1 + ... + ar*Xr =B b1*Y1 + ... + bt*Yt
   All coefficients are positive; multiplication means repeated registered union.
   Retain EVERY original variable, including variables canceled completely.
2. Make p=sum(a) rows and q=sum(b) columns. Each occurrence has its original
   variable index as label. A support is a NONEMPTY subset of the p*q cells.
   It is balanced when rows bearing the same label have equal degrees and
   columns bearing the same label have equal degrees. Let S be ALL such supports.
3. Give each s in S a fresh bag parameter Z_s. Define the generated substitution:
     X_i := sum_s rowDegree_i(s)*Z_s
     Y_j := sum_s colDegree_j(s)*Z_s
   Every input variable not active in the balance is a separate passthrough
   parameter, with its original sort and sharing preserved. Call this vector theta.
4. Required native theorem, for EVERY sorted input valuation rho:
     Balance(rho) iff exists eta, rho =B eval(theta, eta)
   Vector equality compares ALL original inputs, not only active bag variables.
   The parameter scope contains the Z_s and passthrough variables. No feasibility
   assumptions or additional user registration evidence appear in this theorem.

Completeness proof decomposition:

- Flatten each active native bag to a finite list of quotient atom classes.
  Existing flatten_congr gives equal total multiplicities on the two sides.
- For each class, its multiplicity vector is a nonnegative balance solution.
  Repeatedly subtract a componentwise-minimal nonzero balance subsolution;
  the total multiplicity decreases. This is a proof argument, not a runtime
  Diophantine solver or a problem-specific certificate obligation.
- Boudet--Contejean Theorem 2 supplies a balanced cell support for each minimal
  subsolution. Keeping ALL balanced supports therefore generates every vector.
  This finite generation theorem must be proved generally in Lean; citing it
  in this document is not a trusted axiom in the eventual checker.
- Collect the class occurrences assigned to each support into Z_s. Rebuild native
  bags using the existing quotient/rebuilding lemmas. Equality of the reconstructed
  multiplicities gives list permutation; eq_of_flatten_perm returns NativeEq.
- For soundness, each selected cell contributes once on each side. Equal degrees
  for equal variable labels preserve repetitions. Thus every eta solves Balance.
- If p=0 or q=0, there are no supports and all ACTIVE images are empty. If both
  sides cancel entirely there are no active variables: all inputs pass through.
  In particular X+Y =B X gives Y=B empty with arbitrary X, not X=B empty.

Exhaustiveness is checked, not asserted by Maude:

- Define the support family by canonical enumeration of all cell subsets and
  decidable balancedness. Any supplied table must agree with that family, or
  carry a separately checked coverage proof. Merely checking each listed support
  is balanced permits omission and does NOT certify completeness.
- This exhaustive fallback can be exponential in the original equation size.
  Do not claim polynomial checking or small certificates without a separate
  representation/cost argument. Checked native-guided closure may bypass it.

Composition and native closure:

- For an exact family theta_k for E1, constructor congruence gives:
    (E1 AND Erest)(rho) iff
      OR_k exists eta, rho =B theta_k(eta) AND Erest(theta_k(eta)).
  All variables and residual equations use that SAME eta. This is why sequential
  composition preserves correlations. Introduced singleton equations are
  structural equations, not the user's constrained-pattern predicates.
- Sound/complete singleton splitting plus payload solving must produce symbolic
  unifiers of the WHOLE original problem before invoking CSU completeness.
- The success argument needs symbolic, not merely ground, CSU completeness:
  every such unifier theta factors through some native sigma_i on ALL original
  variables. Maude matching proposes beta; checked Equality/Factor data proves
  theta =B sigma_i composed with beta. The existing Factor.sound then closes it.
- A native valuation theorem alone is not an excuse to claim symbolic
  factorization. Lift the rule to open syntax by treating its fresh variables as
  additional sorted free nullary symbols. The same semantic argument applies;
  establish the correspondence with existing Term/Equality once, generally.
- An empty CSU requires proved contradiction leaves for every surviving case.
  Unsupported search, an unsuccessful match, or a redundant branch is NOT False.

Next proof boundary:

- General finite generation of balance vectors by the canonical support family.
- Native bag lifting and the open-variable specialization just described.
- Exact substitution composition and exhaustive singleton/payload processing.
  Only after these arguments are secure should the completeness-tree checker
  gain FiniteSharing/contradiction nodes or Maude gain new search control.

Historical first proof checkpoint (superseded by the current checklist below):
the first general proof auxiliary is now in the
EXISTING certification.lean, namespace DirectCertification.FiniteSharing.

- decompose_minimal proves that EVERY balanced natural multiplicity vector is
  a finite sum of minimal nonzero balanced vectors, including the zero case.
  Dimension and coefficients are arbitrary; no problem-specific bound is used.
- generated_iff_balanced reduces exact generation by a finite list to soundness
  of its generators and coverage of all minimal vectors. These are INTERNAL
  hypotheses for the future grid metatheorem, not per-user/model registration.
- LSP axiom checks for both theorems contain only propext, Classical.choice and
  Quot.sound, no sorryAx. No Mathlib import, new tactic, or solver change.
- The central MINIMAL-VECTOR-TO-BALANCED-SUPPORT theorem remains unproved.
  Therefore the actual canonical support family has NOT yet been certified
  complete, and no native bag exactness/search-success theorem is claimed.
  Prove that representation theorem next, then lift through existing NativeEq.

Historical second proof checkpoint (rounding/enumeration are now proved below):

- minimal_pair_bound proves that opposite-side minimal multiplicities cannot
  both exceed the elementary two-variable solution. No coefficient/arity bound.
- transport_exists constructs a natural-entry matrix with any compatible finite
  row/column totals. minimal_bounded_transport proves every variable-pair block
  of a minimal solution fits its a_i*b_j finite cell capacity after cancellation.
- switch_cost_lt proves that (a,0;c,d) -> (a-1,1;c+1,d-1), for a>=2 and d>c,
  strictly decreases squared-entry cost. Whole occurrence margins can be
  preserved by this exchange. The complete INFORMAL repair argument is documented
  beside these lemmas: a missing zero is obtained by the group-size bound;
  equality of group column totals provides the other row, then cost induction
  makes all entries Boolean. The transposed case uses the same argument.
- Full-file LSP diagnostics report no errors/warnings. Isolated axiom checks on
  the transport/bound/cost theorems contain no sorryAx. No Mathlib or custom tactics.
- Still missing in Lean: the WHOLE matrix-rounding theorem (including exchange
  witnesses and preserved margins), Boolean support extraction, and canonical
  enumeration coverage. Bounded aggregate blocks alone are NOT yet a checked
  representation by balanced occurrence supports. Prove rounding next.

## Short-term goal: certified constrained narrowing

### Current progress (authoritative; older checkpoints below are historical)

Goal: native Maude proposes unifiers; answer-guided search supplies a kernel-checked
soundness/completeness certificate, with no nontrivial user registration/proofs.
Constrained narrowing will consume this only after unification certification works.

- [x] State the restricted modeling contract and the informal complete fallback /
  targeted early-closure argument in CERTIFICATION.md. This is NOT a formal Lean
  search-success theorem or a claim of universal speedup.
- [x] Generate native constructor metadata; retain existing indexed structural
  semantics. Model-only Bakery declarations need no semantic bridge proof.
- [x] Prove reusable cancellation, free decomposition/clash, singleton splitting,
  sorted whole-vector factors, and soundness/completeness aggregation.
- [x] Prove numeric finite sharing for arbitrary coefficients and repeated labels:
  minimal decomposition, Boolean rounding, and nonempty support representation.
- [x] Enumerate EVERY Boolean occurrence grid and filter uniform repeated-label
  degrees. Prove supportGenerators_exact: the computed finite list generates
  exactly the balanced ACTIVE multiplicity vectors. No supplied-list coverage
  premise, fixed search bound, Mathlib import, or proof admission.
- [ ] Lift the enumerated family to exact native/open bag substitutions using
  flatten/rebuild; preserve canceled variables as independent passthrough inputs.
- [ ] Implement exhaustive singleton/payload processing and sorted substitution
  composition for finite equation systems (not just handwritten examples).
- [ ] Implement complete whole-vector factor search and native-answer-guided
  early closure, with the complete finite fallback on shortcut failure.
- [ ] Connect finite dump/replay data to actual Maude certification search; validate
  the exact signature, input, original-variable scopes, and WHOLE answer family.
- [ ] Lift checked unifier exactness into constrained narrowing and remove Bakery's
  completeness holes. Production narrowing is deliberately unchanged so far.

NEXT: native/open bag reconstruction for the proved enumerated support family.
The numeric proof is general; the overall automatic ACU certifier is NOT finished.

### Historical integration notes

The following checkpoints describe earlier experiments, not the current executable
capabilities of certification.lean. Its old elaboration-time Maude harness and
bounded shape recognizers were removed; see the checklist above for active status.

- Restricted `deriving ACU` and explicit-root `structural T for Conf` implemented.
  Model-only example: examples/bakery_acu.lean. No nontrivial user registration.
- Active prototype: certification.lean. Direct SplitAtom/Mutate/AtomicRemainder
  rules proved against indexed semantics; actual native idle/wait(3) Maude answers
  certified exactly with two families, no admissions, no Mathlib.
- Next: answer-guided rule search; general existential substitution/elimination;
  free-constructor decomposition; broader family normalization. Then wire checked
  unifier results into constrained narrowing. Production completeness holes remain.
- Current checker selects supported macro rules locally; native Maude supplies
  answers, not derivation traces yet. Do not claim full ACU certification automation.
- Existing upair.lean has pre-existing completeness-lifting failures at lines
  164/188/203 (reproduced against unchanged HEAD Structural). Repair separately;
  the new direct-certification milestone does not change that legacy narrowing.

Revised pipeline (2026-10-04):

1. Encode the user's native constructors and registered structural laws as
   first-order data for Maude. Keep arbitrary Lean constraints in Lean.
2. Run native Maude unification for candidates, then use them to guide a rule-based
   certification search that accounts for the entire solution set.
3. Replay the certificate directly against registered indexed structural semantics.
   Generate metadata mechanically; require no per-model semantic bridge proofs.
4. Attach substituted rule/pattern constraints to the successors and use generic
   lifting theorems to obtain the post-image and its exactness certificate.

All term wrappers, sort/symbol identifiers, and variable indices are internal.
Users keep their own constructors, structural declarations, and pattern syntax.
Use indexed equality explicitly until legacy EqMod migration is resolved.
Transporting constraints along
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
- Fifth increment: untrusted reply parser plus `Certification2.Reply.decode/emit`
  validate the exact echo and whole family, then emit constants. `BakeryReply`
  proves the idle and wait(3) native iff theorems FROM fetched data, with packet
  atom IDs renamed in the kernel. Changed echo, omitted branch, no result and
  truncation are rejected. Next: generate the native statement/SolutionSet from
  the checked output instead of writing it by hand.
- Historical indirect experiment: `certification2.lean`. Active direct experiment:
  `certification.lean`; do not extend the indirect BakeryEncoding/Bridge pipeline.
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
