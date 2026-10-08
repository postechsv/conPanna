# conPanna development handoff

This document records the design decisions and current implementation state needed to continue development in a new conversation. The current repository is `/home/byhoson/workspace/conPanna`.

## Non-negotiable certification input and integration boundary

Certification receives `(E₀, B, Σ)` from Lean. The proposed native answer set Σ
is ALREADY AVAILABLE: existing unification called native Maude BEFORE the
certification attempt. Do not design or implement certification as another
native `unify` call. It constructs soundness/completeness evidence for this
fixed Σ, using its answers to guide Maude-side proof search and coverage.
The complete fallback is evidence construction, not replacement of Σ.

Production flow: current Lean session -> Python wrapper -> Maude certification
evidence -> Python proof construction -> current Lean session/kernel checking.
Python does NOT launch another Lean executable in that interface. The current
standalone demo invokes native unify for input preparation and launches Lean
as a TEST HARNESS ONLY; do not mistake that harness for the intended integration.
CERTIFICATION.md §§0, 6–8, and Appendix A explicitly specify these boundaries.

## Artifact cleanup — 2026-10-08

- Root `certification.maude` now contains ONLY the maintained
  `CERTIFICATION-PRODUCER`. Seven unused historical modules and the unused
  `LeanReadyBoundary` example in `certification.lean` were removed.
- The distinct older CERT2 engine was RENAMED from
  `conPanna/certification.maude` to `conPanna/maude-cert2.maude`; its existing
  protocol/exporter and saved-script callers were updated, not removed.
  Older references below are historical filenames, not current load paths.
- CERTIFICATION.md §§0 and 3.1 identify the maintained files and map the actual
  Maude `solve` arguments to the mathematical state. Section 4.3 displays the
  actual sharing rule and one retained equation list, without separate D/Balance
  state fields. Search and checker algorithms are unchanged.
- Root `certification.maude` is now a short rules-only system module importing
  `certification-support.maude`. The companion contains nine acyclic fmods:
  TERMS, EVIDENCE, EQUALITY, FREE, ACU-MATCHING, SHARING, BAG-STEPS, COVERAGE,
  OUTPUT (each prefixed CERTIFICATION-). No helper fmod contains rewrite rules.
  Comments distinguish semantic rules from protocol/collection and identify
  helper modules and Lean constructors. Rule/equation bodies, rewrite-rule order
  and equation priority within each function remain intact.
- CERTIFICATION.md section 4 links EVERY main rule to its actual Maude label or
  named evidence-building helper; derived rules are not given invented labels.
- Mathematical states uniformly use `⟨α ; E⟩`; scope changes are labelled outside
  the pair, including FINITE-SHARING. Do not reintroduce a separate triple form.
- Validation after reorganization: all 28 Python tests pass; the automated
  soundness/completeness Lean demo passes without sorry; both legacy saved Maude
  scripts still load/run without warnings. Lean LSP reports no errors in the
  cleaned handwritten certification file.
- After the fmod split, all 28 tests pass again and the full Lean demo passes
  without sorry under unchanged safety limits. One run hit the 30s wall limit;
  the single bounded retry completed. No Lean file, Python protocol or calculus
  rule was changed for this split.

## Current runnable demo: Maude -> Python -> precompiled Lean (2026-10-06)

### Answer-guided witnesses and genuine no-answer comparison — 2026-10-07 (latest)

User requested the remaining optional optimization and a quantitative comparison
against calculus-based unification with NO proposed answers. Implemented using
existing files and rules only; no new permanent Lean file, tactic, core-library
rule, registration work, narrowing change, git commit, or sub-agent.

- Added one finite answer-guided witness attempt in certification.maude:
  existing MUTATE introduces four common-refinement pieces for A1+A2=B1+B2,
  then existing conditional COVER must cover the WHOLE extended image vector.
  Failed attempts discard their temporary state and resume the original fallback.
  A cheap hint tries this only when a supplied answer has >=4 bag parameters.
  It does not recurse into more witness attempts and is not a contract restriction.
- Native matrix_certificate and matrix_manual_certificate in the EXISTING
  examples/certification-demo.lean present exactly the same proposition:
  P+Q=B R+S iff there exist A,B,C,D with P=A+B,Q=C+D,R=A+C,S=B+D.
  Automatic tree MUTATE -> COVER uses four pieces instead of fifteen fallback
  support generators. Manual proof is the ONE general mutate_native rule;
  no generated indices, parser commands or problem-specific supporting lemma.
  Both kernel-check; manual axioms exclude Classical.choice; neither has sorryAx.
- Python adds serialization of the ALREADY PROVED Complete.mutate and the same
  checked ReplayState successor boundary. No semantic rule is added in Lean.
- Added unifyWithoutAnswers diagnostic entry point: receives E/B/initial images
  ONLY. It disables answer matching/early closure, performs the SAME documented
  free/ATOM/ZERO/PURIFY/FINITE-SHARING fallback, and collects solved substitutions
  as a reference CSU. No native Maude unify invocation, no hidden supplied Sigma,
  no Python unification. Leaf numbering/output assembly happen in Maude. The
  production certify entry point still receives fixed Sigma unchanged.
- ATOM trace now keeps typed child states until serialization instead of erasing
  them into JSON strings early; this permits reference-leaf collection/numbering.
  Generated reference scopes retain unused passthroughs and redundant generators;
  the comparison is against the DOCUMENTED exhaustive fallback, not the best
  possible untargeted solver. No claim that the short targeted proof is impossible
  without answers or that targeting always improves performance.
- Real issue found: search was constructing/discarding equality-proof strings
  for every normal-form test. A data-only normalizer now supplies decisions in
  BOTH controls; accepted equality evidence still uses explicit checked rules.
  Sixty-four normalization comparisons and all semantic certificate tests pass.
- --compare separates no-answer unifier computation from soundness-evidence
  formatting and Lean checking. Three producer runs give median timings; each
  successful mode's OWN answer family is checked for exactness of the same E.
  Standalone Lean invocations are TEST HARNESS ONLY, not production verification.
  Detailed generated results: .lake/build/certification/comparison.json.

Final comparison (total Maude producer/evidence rewrites; NOT wall-clock speedup):

| Problem | Untargeted (NO answers) | Targeted (fixed answers) |
| --- | --- | --- |
| 2P=2Q | 28,229 rewrites; 77 checked proof-DAG nodes | 6,558 rewrites; 19 checked nodes |
| 3P=3Q | 459,360 rewrites; 127-node proposed replay; Lean allocation failure | 8,611 rewrites; 22 checked nodes |
| P+Q=[wait n] | 23,975 rewrites; 102 checked nodes | 175,455 rewrites; 83 checked nodes |
| P+[wait n]=Q+[wait n] | 23,721 rewrites; 153 checked nodes | 49,332 rewrites; 106 checked nodes |
| P+Q=R+S | CSU computed (74,850 producer rewrites); Maude stack failure rendering soundness | 116,614 rewrites; 205 checked nodes |
| 2P=3Q control | 51,857 rewrites; 155 checked nodes | 68,587 rewrites; 176 checked nodes |

- 2P=2Q: ~4.3x fewer producer/evidence rewrites and ~4x smaller checked proof.
  3P=3Q: ~53x fewer total producer/evidence rewrites; both Maude searches FINISH,
  but untargeted checking throws std::bad_alloc under unchanged Lean safety caps
  while targeted checking succeeds. This is a CHECKING resource advantage, not
  failure of untargeted unifier computation. Matrix baseline also computes its
  CSU, then hits Maude's stack limit in soundness rendering, not unification.
- Negative controls matter: singleton/cancellation/fallback cases may do MORE
  Maude rewrites when targeted; compact certificates do not guarantee less search.
  Process startup dominates the small Maude wall times (~50–70 ms). Do not
  describe a rewrite-count reduction as an equal wall-clock speedup. Native
  upstream unification time is EXCLUDED. Resource failure is not contradiction.
- Safety limits unchanged (-j1/-M512, OS data768MiB, CPU25s, wall30s); the data
  cap now applies to Maude children as well. Never increase caps to obtain success.
- Verified: 28 Python tests; the expanded 19-case smaller suite plus seven fresh
  corruption rejections (~25.8s capped consumer); separate 640-node balance
  certificate (~23.9s); all successful certificates use standard axioms only.
  New MUTATE has checked successor transport; incomplete diagonal answers cannot
  close its finite attempt. Two nonlinear-equation regression still has TWO
  sharing steps. git diff --check passes; disunification.lean untouched.
- Remaining boundary: these are optional optimizations, not a missing completeness
  mechanism. Complete fallback is still implemented under the restricted contract,
  with INFORMAL search-success argument and kernel-checked replay. Formal search
  guarantee and mixed-theory extension remain separate work; narrowing deferred.

### Conditional EARLY-COVER — 2026-10-07 (previous)

User authorized making certification genuinely targeted. Implemented a finite
proof-producing shortcut in certification.maude; the core Lean calculus,
registration, narrowing, and scope contract were NOT changed. No new permanent
Lean files or tactics. Existing files edited only; disunification.lean untouched.

- `selectCoverage` tries unconditional fixed-Σ factoring, then conditional
  simplification of the whole original image vector under the CURRENT equations.
  It discovers variable definitions/free-head fields, cancels common normalized
  bag occurrences, cancels equal positive powers, and handles uniform zero sides.
  Proofs use existing Derives HYP/DECOMPOSE/CONGR/TRANS/SYMM/CANCEL/MULTIPLICITY.
  Variable aliases are oriented toward a smaller slot; self-containing direct
  replacements are not followed; a visited-variable path stops indirect cycles.
  No state mutation or unification search happens in Python.
- A conditional view that is unchanged modulo B is not matched a second time.
  Otherwise the existing complete finite matcher searches SUPPLIED answers for
  one shared β. Successful COVER has derived equality evidence for ALL original
  input images. Failed finite attempts return to the unchanged complete schedule;
  no unproved branch is discarded. Original candidate soundness remains checked.
- Python adds only two serialization cases: Derives.congr and multiplicity,
  both already present/proved in Replay. No new trusted rule or semantic proof
  obligation. Compilation of the Lean backend is unaffected/cached.
- Actual singleton trace is now ATOM -> two direct COVER leaves. The readable
  atom_manual_certificate comments match this new tree; manual proof unchanged.
  New native power_certificate in the same demo certifies 2P=2Q by one COVER with
  MULTIPLICITY evidence, no grid expansion. Common-singleton and bag-cycle
  examples now also close directly where the factor is available.
- Twenty-four Python tests pass: equal powers, 7P=7Q (no 2^49 support enumeration),
  multiple bag fields, free configuration binding, cyclic definitions/fallback,
  omitted/unsound answers, and typed metadata validation. Existing two-nonlinear-
  equation regression still uses TWO sharing steps, testing fallback retention.
- The 18-case smaller certificate suite (17 old problems plus power) passes with
  standard axioms only. The manual proof additionally passes without choice.
  Seven fresh corruption fixtures reject: wrong ATOM successor, scope, conditional
  hypothesis, hole, duplicate/unsupported node, and final proof. The corruption
  fixture now uses ATOM since direct conditional COVER removes its old BIND.
  Transition type parsing uses the LAST equality, since the source expression
  can include `if i = j` conditions.
- /tmp/conpanna-scheduler-audit.lean checks a newly registered two-bag-field model,
  free configuration binding, and the 7-fold power example. All three certificates
  kernel-check with no sorryAx; conditional COVER works with alternate metadata.
  It remains a TEMPORARY test, not another permanent Lean module.
- Larger balance demo still certifies 2P=[wait(n)]+Q with PURIFY/SHARING fallback
  and exhaustive branches; checked nodes fell from 754 to 640. This is reduced
  evidence size, not a uniform runtime speedup claim. CPU/wall/memory caps unchanged.
  Final capped balance, 18-case/7-corruption consumer, temporary model/7-fold
  power certificates, 24 Python tests, and original certification.lean suite
  all pass. No sorryAx, owned jobs, or diff whitespace errors remain.
- Concrete issue fixed: normalized bags encode P as P+empty, so definitions must
  be looked up in original equations, not mistaken for normalized variable heads.
  The simplification and subsequent normalization still emit checked evidence.
- CERTIFICATION.md §9.1 describes algorithm, finite control, and limitations.
  Σ does NOT automatically supply a factor expressible in the CURRENT scope:
  for 2P=3Q, parameter Z cannot generally be a union-only term in P,Q. Sharing
  introduces witnesses before COVER; known answers need not eliminate all solving.
- --demo's first signature-less historical binding control intentionally remains
  BIND/BIND/COVER and is now labeled LEGACY. Typed Lean requests exercise targeted
  coverage. Do not misread that optional harness control as the current algorithm.
- NEXT: consider answer-guided witness/branch selection if stronger shortcuts are
  desired, or systematic small-problem testing/formal search theorem. All such
  extensions must keep finite shortcut attempts plus complete fallback. Do not
  touch narrowing yet or expose additional user registration/certification work.

### Previous readable native certificate and scheduler audit — 2026-10-07

User clarified that metaprogramming is acceptable UNDER THE HOOD. The manual
certificate's surface must be ordinary and abstract, not a dump parser or sorted
variable-index proof. Sustained implementation remains authorized; narrowing is
still deliberately untouched. No extra permanent Lean file or tactic was added.

- `atom_automated_certificate` and `atom_manual_certificate` in
  examples/certification-demo.lean state IDENTICAL native exactness propositions:
  P union Q =B singleton(wait n) iff either singleton/empty assignment, with a
  shared ticket parameter. The manual proof is one ordinary explicit term with
  ATOM cases, COVER witnesses, then CONGR/UNIT soundness for each answer. It calls
  no producer/parser/replay loader/tactic and has no generated variable indices.
- General proved `NativeRules.singletonCases`, `rightUnit`, `unaryCongruence`
  expose existing semantic rules while hiding quoting/mass/argument tuples.
  Named constructor aliases are trivial syntactic data, not registration proofs
  or problem-specific certificate lemmas. Other original replay rules unchanged.
- Comments explain ACTUAL dump correspondence: ATOM -> two BIND/BIND/COVER
  branches, N:=n. The native surface groups binding equalities/witness emission
  and reverses branch order; it is NOT falsely described as byte-identical to
  the serialized proof. A producer test checks the expanded tree and both βs.
- CERTIFICATION.md §7.4 gives the retained-worklist scheduler's INFORMAL finite
  phase audit: finitely many non-bag bindings; finitely many original frontiers
  between them; decreasing explicit atoms in preparation; once-only sharing;
  permanent solved equations; finite ATOM/ZERO local obligations processed by
  binding/payload checks, not another sharing phase; exhaustive constructor
  cases; final fixed-Σ coverage by the existing exhaustive matcher.
  This advances the previous open implementation audit. It is NOT a formal Lean
  search theorem or a guarantee that all inputs fit the unchanged resource caps.
- Python tests now total 20, all pass: added actual manual-trace correspondence,
  free configuration binding, and two bag fields with distinct purified atoms.
  The latter fixtures use the alternate constructor-code signature, not Bakery
  specific heuristics. Scope includes arbitrary repeated variables as before.
- BOTH new scheduler cases also kernel-check on a freshly registered temporary
  model with TWO bag fields. File: /tmp/conpanna-scheduler-audit.lean (560 checked
  nodes total, standard axioms only). No permanent test Lean file was added.
- Concrete small debugging issues: NativeEq carrier sort cannot be inferred by
  `native_refl registration n` without an expected sort; expected-type `.refl _`
  solves it without exposing tags. The automated native unfolding must qualify
  Substitution.add/zero to avoid collision with Indexed tree constructors.
  A test initially expected ZERO for a cancelled bag cycle; the producer
  correctly uses zero-sided SHARING. These were corrected, not new proof axioms.
- Smaller suite plus SIX fresh corruptions passes after the final manual-proof
  rewrite (destructured native hypotheses, no tuple projection noise).
  Manual axioms: propext, Quot.sound; generated proofs additionally Classical.choice.
  No sorryAx. All jobs sequential under existing -j1/-M512 and OS safety caps.
  The separate 754-node balance demo and original certification.lean handwritten
  suite also pass after the changes. git diff --check passes; no owned jobs remain.
- NEXT: optional conditional EARLY-COVER for smaller certificates; formalize the
  unbounded scheduler/matcher guarantee if desired; then extend the modeling
  contract with a proper combination argument. Do not make these new user
  registration/certification obligations, and do not touch narrowing yet.

### Previous replay-boundary and factor-audit checkpoint

User authorized improving the implementation difficulties and continuing through
several checkpoints while they sleep. No new calculus/search engine/tactics,
narrowing changes, commits, or extra permanent Lean files were added this turn.
Unrelated disunification.lean is untouched.

- Reusable ReplayState in Worklist groups current images/equations at a fixed
  original input scope. substitute/prepend/purify compute the SAME existing rule
  transformations. The compiler emits checked successor equalities for
  BIND/PURIFY/SHARING/ATOM/ZERO, then ReplayState.accept transports an opaque child.
  Python duplicates no substitution/shifting/requirement algorithm.
- Frontend failures identify the offending rule node. Explicit projections avoid
  Lean parsing `generatedName.images` as one identifier during fresh renaming;
  explicit `(sig := Sig)` avoids deferred operator inference in sharing transport.
  These were concrete implementation issues, not missing semantic proof rules.
- Seventeen smaller certificates pass, plus the separate larger balance demo.
  Added ACU cycle P=P+Q (Q=0), impossible P=P+[wait(n)], repeated factor parameter
  2U+V, correlated whole-vector factor with shared U=0, and actual two-equation /
  TWO-answer `overlap_certificate` using native Bakery constructors. That theorem
  certifies P+Q=[wait(n)] and Q+R=[wait(m)]: Q is empty, or the shared singleton
  forces n/m to share its ticket. No problem-specific certificate lemma/hole.
- Optional fresh negative replay suite passes. It validates a positive binding
  control, then rejects wrong successor AT bind_successor, wrong scope, hole,
  duplicate/unsupported node, and wrong final proof. Saved elaboration state is
  restored between fixtures, including their messages/admission warnings.
  Commands: CONPANNA_CERT_NEGATIVES=1 python3 -B certification_compiler.py --demo;
  CONPANNA_CERT_STRESS=1 python3 -B certification_compiler.py --demo separately.
- tests/test_certification_compiler.py uses alternate constructor codes, tests
  typed-input rejection and whole-vector/shared/repeated factor search, omitted
  and unsound families. All 17 tests pass. A two-SHARING regression checks that
  2P=3Q and 3R=2S preserve two INDEPENDENT parameters through both equations.
  The same problem was also kernel-checked separately in the temporary
  /tmp/conpanna-system-audit.lean (533 generated nodes, standard axioms only).
  No additional permanent Lean test file was created for that probe.
  Run python3 -B -m unittest discover -s tests -v.
- validate_request enforces the generated one-bag stratified contract and typed
  term/image data. It rejects UNUSED parameters instead of silently modifying Σ;
  normalization must happen before fixing the semantic goal (empty-sort issue).
  Signature-less legacy binding harness input is retained, not covered by this
  new signature validation. Normal typed Lean requests always export metadata.
- Removed the compiler's unused duplicate equality-text storage; equality node
  numbering now uses a counter. The emitted proof is unchanged by that cleanup.
- Final checks: seventeen-case suite plus SIX fresh corruptions pass again;
  the original certification.lean metatheorem/handwritten suite passes with no
  sorryAx. The focused balance demo remains separately capped. All Lean jobs
  ran sequentially with the unchanged safety limits; no owned test stays running.
- CERTIFICATION.md §8.1 now documents the executable matcher invariant and its
  informal completeness/finiteness argument. Its replay section documents the
  successor boundary and test commands. It remains technical documentation,
  not a timing diary. TODO.md marks these checkpoints and the remaining boundary.
- NEXT: audit the external scheduler's progress with RETAINED solved equations,
  several nonlinear bag fields/equations, and free configuration bindings. No
  contract-wide producer search-success claim yet. Runtime caps can fail to
  obtain evidence; that never certifies impossibility. Narrowing stays deferred.

### Previous continued checkpoint

User authorized continued work and specified the target: a WORKING LEAN demo
certifying a unification problem with the documented calculus. A significant
milestone now passes; no narrowing changes or commits were made.

- Focused demo: examples/certification-balance.lean, ordinary native theorem
  CertificationBalance.certificate. It certifies 2P=[wait(n)]+Q against the fixed
  answer (N, [wait(N)]+R, [wait(N)]+2R), including n's component. No holes or
  problem-specific supporting certification lemmas. Comments describe the ACTUAL
  2-by-2 support table and PURIFY/SHARING/ATOM/BIND/NONEMPTY/COVER structure.
- Run CONPANNA_CERT_STRESS=1 python3 -B certification_compiler.py --demo. It
  checks that focused file separately, without another native unify. Latest
  successful consumer: 19.51 s, 685 checked nodes, root elaboration 90 ms,
  standard axioms [propext, Classical.choice, Quot.sound] only. Same resource caps.
- Breakthrough: share typed TERM data using exported sort/head metadata, then
  share closed completeness nodes with their SAME original indexed types.
  Term sharing reduced the large bundle from ~530 KB to ~200 KB (before adding
  completeness nodes); completeness-node sharing reduced root elaboration from
  ~14 seconds with 20 postponed obligations to ~80-100 ms with NONE. All nodes
  still kernel checked. Python performs only syntactic constructor assembly.
- The earlier claim that the stall was final kernel checking was too coarse:
  finer live checkpoints located a stall at synthetic-obligation completion
  BEFORE the explicit final addDecl call. Some runs also exhausted node-checking
  memory. This does not conclusively diagnose every historical WSL failure.
- Tried smaller batches and restoring Term elaboration state: did NOT solve
  the issue; reverted both. Batch size remains 50. Temporary phase debug logs
  are gated by CONPANNA_CERT_DEBUG. Successful subprocess stderr is now retained.
- Tried optional generated native theorem inside the existing demo: hygiene /
  combined-suite cap problems made that awkward. REMOVED that block and the
  wrapper's source slicing. One focused ordinary Lean demo file replaces those
  experiments; there is no additional calculus/backend implementation.
- All thirteen in ONE process exceeded the CPU cap. Separate capped checks are
  deliberate; do not raise caps. Normal --demo covers twelve smaller cases.
- Final checks PASS: focused balance demo (685 nodes, root 77 ms, consumer
  19.05 s), twelve-regression --demo (consumer 14.46 s), original certification.lean
  metatheorem/examples suite, and freshly produced valid evidence plus corrupt
  binding/factor rejection. No sorryAx in axiom audits. Python syntax and
  git diff checks pass. Generated completeness names retain their rule label;
  #print checked in the focused demo shows PURIFY -> named SHARING directly.
  Maude-only probes for P=P+Q (unit collapse) and P=P+[wait(n)] (failure) close,
  but those probes were NOT separately kernel-checked as new examples.
  Remaining NEXT: complete factor
  matching audit for normalized answers, more sort/scope negatives, then scheduler
  audit. Examples are NOT a contract-wide automatic-search guarantee.
- /tmp/conpanna-purify-check.lean is now only an export/debug harness, and accepts
  CONPANNA_EXPORT_ONLY=1. Request and old/shared bundles are under /tmp/conpanna-*.

### Previous bounded resume checkpoint

User authorized a small resume ("as much as 10% token"); stopped after one focused
harness correction. No test remains running. No narrowing changes.

- The twelve-certificate capped CLI check passed again: 24.80 s wall, 17.77 s
  user+system CPU, peak RSS 1,404,540 KiB. This does NOT explain the earlier 137
  exit or establish a memory/speed guarantee.
- Found and fixed a test-harness defect: --demo saved its proof but never handed
  it to the Lean consumer. It now writes a rule bundle to
  .lake/build/certification/demo.proof.json and passes that exact bundle via
  CONPANNA_CERTIFICATE. Remaining eleven regression certificates still run.
- Corrected --demo passed unchanged caps: Maude+Python 0.097 s, Lean consumer
  18.72 s, standard axioms only, no certificate holes. Production --certify still
  does not run native unify or an external Lean process.
- Failure diagnostics now retain exit/signal, elapsed time, AND subprocess output;
  a deliberate exit-7/output test passed. Python syntax and git diff checks pass.
- Larger 2P=[wait(n)]+Q replay remains unverified. Next resolve its normalization /
  final kernel-check cost; complete factor and scheduler audits still remain.

### Previous paused checkpoint

User requested pause. Do not resume implementation until asked.

Final pending --demo test finished before shutdown: backend modules were ready,
Maude/Python produced bind -> bind -> cover evidence in 0.219s, but its Lean
consumer exited 137. This wrapper test did NOT pass; distinguish it from the
previous successful twelve-certificate CLI check below. No test remains running.

- Twelve certificates in examples/certification-demo.lean PASS the capped CLI
  check, with standard axioms only and no certificate holes: binding, payload,
  clash, occurs, unit, two singleton answers, repeated-variable rejection,
  nonlinear 2P=3Q, finite factor with an empty assignment, configuration fields,
  common-singleton purification/cancellation, and a correlated two-equation case.
- certification.maude now has reusable CERTIFICATION-PRODUCER rules driven by
  exported metadata. The demo Maude file contains only upstream test input.
  Certification takes already-known E/B/Sigma; no native unify or external Lean
  subprocess inside --certify. Python compiles proof constructors, not search.
- Finite whole-vector subbag matching fallback is implemented in Maude, with
  one shared parameter table. Unused answer parameters remain an audit boundary.
- Frontend.lean is the one new, semantic-independent loader module; Replay imports
  it. Closed equality proofs and repeated state data are checked in small batches.
  Identity proof compositions are removed syntactically. No new tactics/rules or
  changes to narrowing. The failed completeness-node splitting was removed.
- Important FAILURE: 2P=[wait(n)]+Q produces Maude evidence quickly, but capped
  Lean replay has NOT completed its final kernel check. One retained variant
  checks all 296 nodes and elaborates the root, then reaches CPU cap. Other
  variants hit memory caps. Do not call this certificate verified or the general
  documented search guarantee implemented. Next discuss/resolve larger replay
  representation before extending the hard cases; do not raise resource caps.
- Original certification.lean regressions pass. Lean rejects corrupt binding and
  factor evidence; Maude rejects omitted/unsound answer families. Frontend LSP
  diagnostics are clean. ONLY our LSP processes 42143/42138/42091 were stopped
  after verified ownership, releasing about 4 GiB; VS Code was untouched.
- Debug stderr is buffered by run_elab unless stderrAsMessages=false; missing
  live messages did NOT locate the earlier failure. Moving the loader exposed
  a syntax error in a trial version; compilation failure was not conclusively
  attributable solely to Replay module size. Retained loader now builds cleanly.
- Resource caps remain -j1/-M512, data 768 MiB, CPU 25 s, wall 30 s. No commits
  made. Untracked disunification.lean is unrelated and untouched. TODO.md contains
  the authoritative executable checklist. Temporary negative/stress files are
  under /tmp/conpanna-*; no additional permanent experiment Lean files were added.

Older details below are historical and some implementation-status claims are
superseded by this checkpoint. CERTIFICATION.md remains technical documentation.

Run `python3 certification_compiler.py --demo` from the repository root.
`--build` precompiles only the backend. Four sequential cached modules live in
conPanna/Certification: Core, Sharing, Enumeration, Replay. Generic proof bodies
were moved, not reimplemented; certification.lean retains its examples. Cross-
module helper theorems are public. Core imports Structural, not the Bakery model.

The end result is examples/certification-demo.lean, theorem
CertificationDemo.certificate. Its statement uses native Bakery constructors:
P =B Q and Q =B [wait(n)] iff there exists N with n =B N and
P =B [wait(N)] and Q =B [wait(N)]. Both soundness/completeness are kernel-checked;
there is no certification hole and no problem-specific supporting certificate
lemma. The final simp only unfolds the data representation into this statement.

Unlike the earlier hand-fixture experiment, the Maude trace is ACTUAL output:
native unify proposes (N,[wait(N)],[wait(N)]); generic sorted binding/whole-state
substitution rules in examples/certification-demo.maude execute BIND/BIND/COVER.
They emit contexts, replacement terms, images, equations, premise indices,
factor data, and soundness evidence as JSON. Python translates existing rule
templates. The independently fixed Lean goal checks the result; accepted output
is audited for standard axioms only. Trace and proof are saved under
.lake/build/certification, not additional permanent Lean source files.

Successful cached run after normal Lake integration: Maude+Python 0.092 s, Lean
parsing 10 ms/elaboration 209 ms, complete consumer 2.38 s. Corrupting the first
binding replacement is rejected against the fixed goal; its temporary invalid
proof was removed after the negative check. Lake validates cached
backend dependencies; Python does not maintain a second build cache. Normal Lake
builds also create editor metadata; Lean LSP reports no errors/warnings. Original
certification.lean examples pass in 6.21 s with standard axioms only. No backend
recompilation occurs on a cached demo run. The wrapper uses one process at a time, -j1 -M512,
768 MiB data-segment limit, CPU 25 s, wall 30 s; timeout kills the process group.
These observations do not diagnose the historical WSL crash or prove generic
memory/speed guarantees.

DEMO LIMITATION: the native-answer parser/signature map and query are fixed to
this binding-chain problem. The rules/semantic backend are general, but the
automatic complete ACU search driver and general model/answer translation are
NOT implemented. Next extend actual evidence production to nonlinear sharing,
then cover singleton/zero branches. Narrowing remains untouched.

User explicitly corrected documentation policy: CERTIFICATION.md is technical
documentation, not an experimental diary. Benchmark/history sections were
removed; keep measurements here and tasks in TODO.md. §12.1 documents the module
and trust boundaries and runnable commands, without chronological experiment logs.

## Controlled full-certificate experiment (2026-10-06): current conclusion

Experiment measurements and limitations belong in this handoff, NOT in
CERTIFICATION.md, which is the technical specification/documentation. The
decision is a FOCUSED refactoring: compile the existing general proofs separately
and construct explicit rule trees outside Lean. Do not replace the semantic
calculus or build another dependent proof-producing interpreter.

- A capped monolithic check stopped before replay, while compiling general
  infrastructure (8.37 s, peak RSS 1,430,324 KiB). No Maude or Python was running.
  This diagnoses that current failure, NOT the historical WSL crash or the lost
  InstructionReplay timeout.
- A TEMPORARY five-module split compiled the same proofs/rules and ALL original
  examples without errors or admissions. Only private theorem visibility was
  relaxed to permit cross-module references; no semantic proof body changed.
- certification_compiler.py is a thin, untrusted constructor translator. Two
  manually supplied structured traces produce full original certificates:
  BIND/BIND/COVER for P:=Q, Q:=[wait(n)], and SHARING/COVER for 2P =B 3Q with
  P:=3Z, Q:=2Z. Both preserve the whole original input vector, including n.
- The accepted statements are exactness against existing registered indexed
  semantics. The producer does NOT define a different equality or new rules.
  Independently fixed expected propositions, kernel checks, and axiom audits
  passed. Wrong binding, missing soundness, and wrong sharing counts were rejected.
- External binding: parse 12 ms, elaborate 276 ms, kernel <1 ms. Nonlinear:
  parse 37 ms, elaborate 709 ms, kernel 2 ms. Original compact binding dump ALSO
  passed: parse 1 ms, elaborate 209 ms, kernel 1 ms. Richer output is NOT faster
  in this comparison; its benefit is construction simplicity, not shorter proofs.
- The compiler is 126 lines of ordinary tree translation, with no new Lean
  metatheorems or tactics. Its currently tested rule subset is not a general
  certification engine. Maude did NOT generate these full structured traces;
  automatic evidence production/search and legacy EqMod integration remain open.

Audit files are grouped under /tmp/conpanna-replay-ab.28D3gH, including the
temporary modules, structured fixtures, and Validation.lean. No permanent Lean
files or library changes were added by this experiment. The monolithic source
still has its heavy replay commands disabled; do not rerun it unrestricted.
The original experimental measurement table was removed from CERTIFICATION.md
at the user's request. Its architectural description remains in §12.1.
Next: package the general proofs as compiled modules, then freeze a restricted
trace format and implement its Maude producer. Keep the resource limits below.

## Earlier boundary experiments (historical; superseded where noted)

DIAGNOSIS CORRECTION: the preceding unit/bind example did NOT test rich scoped
replay information and is not evidence that missing dump fields caused the
earlier resource failure. A later TEMPORARY isolated diagnostic copied the actual
Variable/Term/Binding.prepare definitions, substitution code, Profile, Equality,
and Derives/DerivesArgs types from certification.lean. Object-level Maude emitted
the two Binding.Prepared values, including reduced contexts, removal positions,
lowered replacements, and rfl reconstruction witnesses. Both were accepted and
proved equal to Lean's computed values; the composed image vector and residual
equations also matched explicit states. Original COVER evidence type checked
in both representations: computed state ~33.5 ms vs explicit ~5.93 ms; checking
image computation against the explicit vector ~18 ms. Both were cheap under
default heartbeats/capped resources. This demonstrates elimination of some
reconstruction/reduction work, NOT the cause/cure of the previous runaway.
The full Complete.sound/exactness theorem and the removed failing interpreter
were NOT replayed in this diagnostic. Do NOT say the full BIND/BIND/COVER gate
passed or recommend a giant refactoring on this evidence. Temporary probe files
were removed. Next isolate/profile the actual failing boundary before claiming
a memory diagnosis; retain the proved calculus while considering explicit dumps.

NEW verified small producer-to-kernel result: certification.maude now contains
LEAN-READY-BOUNDARY-NATIVE / LEAN-READY-BOUNDARY-EMITTER. Native unify returns
P:=Z,Q:=Z for union(P,empty)=Q; object-level RIGHT-UNIT/BIND/EMIT produces an
explicit Lean term. The isolated section at certification.lean lines 51–117
checks that term against existing Bakery Indexed.NativeEq, in both directions.
Generic leftEq/bind/rightUnit semantic rules replace dependent scope/image
reconstruction for THIS small fragment. The theorem body is actual Maude output,
not a handwritten proof string. No Maude process runs during normal elaboration.
Actual-dump parsing <1 ms, elaboration 7 ms, kernel <1 ms; wrong BIND answer is
rejected; axiom audit empty. Isolated permanent theorem/rules: 1.47 s, RSS
1,250,020 KiB; import-only baseline: 1.26 s, RSS 1,236,552 KiB. The parsing and
negative-test run: 1.88 s, RSS 1,278,580 KiB. Same limits below, no parallel Lean.
This is a manually configured native query/emitter mapping, not automatic model
export, native-answer parsing, general search, or a full-file compilation.
The producer supports only right-unit normalization and a distinct-variable
binding; that is an explicit EXPERIMENT scope, not the algorithm contract.
No interpretation of the old typed Complete tree is involved. The source's
older BIND/BIND/COVER dump remains unverified. Next test a multi-equation binding
chain with the same native-semantic boundary before generalizing to ACU sharing.
The earlier memory failure's cause remains unisolated; do not claim it fixed.

User's intended pipeline is Maude certification-rule evidence -> explicit Lean
proof term -> kernel checking, NOT another Lean unification/search engine.
Prefer object-level Maude if its rule instrumentation supplies sufficient data;
use meta-level Maude if control of contexts/premises/branches is needed. A Python
proof-term translator is optional; do not stack it onto a meta-level emitter
that can already produce suitable output. Independent native Maude matching
queries may propose factors; every proposal still needs checked evidence.

A dependent InstructionReplay experiment was added, then REMOVED: extracting its
computed BIND/BIND/COVER certificate exceeded default heartbeats. Increasing the
limit coincided with user-reported WSL instability; the crash cause was NOT
established. Do not repeat raised-limit or unrestricted heavy Lean jobs.

Replacement in certification.lean: 27-line LeanReady.prepareProof frontend and
a hand-prepared leanReadyBindingDump using existing typed rules. No new tactic,
library changes, Maude search, Python translator, or new Lean file. A fixed
expected proposition is supplied by Lean independently of the dump. This is a
prepared-input prototype, NOT a secure loader for arbitrary Lean text/macros.

Verification boundary: an isolated capped stdin check importing ONLY Lean
compiled the helper, parsed the actual dump in 1 ms, and installed/audited a
trivial True proof (no axioms). It does NOT certify Bakery or check its replay
premises. Full certification.lean check stopped with out-of-memory under imposed
limits (12.34 s, peak RSS 1,588,324 KiB), with no certificate result. The actual
native test and negative factor test are therefore DISABLED in a block comment;
their theorem/axiom audit are not claimed verified. Text parsing is not the
observed bottleneck. Do not mark the cheap native acceptance gate complete.

Safety: -j1, -M512, wall deadline 30 s, CPU 25 s; prlimit --data=805306368.
An earlier 1 GiB VIRTUAL ADDRESS cap caused signal 11 even for `import Lean`;
it is not a usable RAM guard here. Lean's -M is not a strict RSS limit (minimal
frontend check peaked at 1,261,296 KiB). Avoid parallel CLI/LSP workers. Do not
increase limits or rebuild the full file repeatedly without discussing resources.

NEXT: agree a resource-safe way to check the existing native rule infrastructure
and the explicit dump in isolation. Then implement the simplest sufficient Maude
evidence producer. General automated certification/search is still unfinished;
the earlier proved calculus remains, but the next step is NOT more isolated rules.

## Current milestone: direct native certification (2026-10-04)

Read THIS section first; the older NEXT SESSION plan below is historical.

**Current override (2026-10-05):** certification.lean was refactored to reusable
native rules, typed equality/factor data, and handwritten certificate examples.
The old bounded shape recognizers and elaboration-time Maude harness are gone.
Its FiniteSharing namespace now PROVES numeric decomposition, Boolean rounding,
and exactness of an EXECUTABLY enumerated support family for arbitrary repeated
labels/coefficients. bags_generated and finiteSharing_native now PROVE tree/native
bag-image exactness too, retaining inactive inputs as independent passthroughs.
Sharing now generates typed open substitutions; Worklist.Complete.sharing and
Soundness.sharing check their completeness/soundness. One substitution transforms
the WHOLE input vector and every residual equation, preserving skipped sorts and
inactive inputs. nonlinear_replay_certificate checks 2P =B 3Q in the mixed scope
[ticket, P, Q], with generated images [ticket, 3Z, 2Z], by explicit finite data.
Full-file LSP checks and axiom audits pass without errors, warnings, or sorryAx.
Coefficient-aware singleton/zero rules (CERTIFICATION.md §4.4) now have general
IFF metatheorems AtomProcessing.sum_atom/sum_zero and typed Complete.atom/zero
replay. Every coefficient-one supplier requires a child; inactive fields are
not constrained. Explicit atoms yield payload equations via Derives.decompose;
Complete.nonempty rejects atom =B unit. Four Bakery proof terms check two
suppliers, payload equality, inactive passthroughs, and an empty answer family.
Binding.Removal now deletes one live position at ANY sort; its replacement is
scoped without that variable. Binding.complete/sound, Soundness.binding, and
Complete.bind check the generated substitution modulo B, propagated through ALL
equations/images. binding_system_certificate composes two bindings across a
two-equation Bakery system. Purification.exact proves fresh naming preserves
solutions in BOTH directions; its typed template computes the original equation
when filled by the named term. Complete.purify retains the defining equation and
supports arbitrary worklist position. purification_binding_certificate composes
PURIFY/BIND/DECOMPOSE/COVER. Full LSP/axiom checks pass without warnings/sorryAx.
Automatic scoped binding preparation and free-step selection now work without
model names or arity/depth bounds. Binding.prepare computes variable deletion and
checks the entire replacement; FreePhase.classify chooses DELETE/ORIENT/BIND/
DECOMPOSE/CLASH/FREE-OCCURS or postponement. FreeOccurs.Proper.sound proves proper
FREE occurrences impossible modulo B using an invariant depth (ACU union=max,
free heads add one). Bag self-unions are NOT rejected. Worklist.closeFree compiles
occurs/clash witnesses into existing replay data; automatic_occurs_certificate
and automatic_clash_certificate certify empty Bakery answer families without
user-supplied paths or problem-specific lemmas. Existing derive_direct_profile
now forwards decidable sort/head equality from generated tags automatically.
Full LSP/axiom checks pass without warnings/sorryAx. Only certification.lean was
changed for code; no tactics, new Lean files, library/narrowing changes, or Maude
calls were added. The free-phase checklist item is PARTIALLY complete: selection
and rejection work, but repeated binding/decomposition/deletion execution and
postponed-equation scheduling do not exist yet. Factor search was NOT started.
No general automated search is claimed. Follow TODO.md's current checkbox list
and CERTIFICATION.md §12.1. Next implement the repeated typed free-phase worklist
driver, then automatic bag preprocessing and phase scheduling using these checked
primitives.
Do not touch narrowing yet.
The older capability descriptions below remain historical context.

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
