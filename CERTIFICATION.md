# A finite, answer-guided ACU certification calculus

Technical design note — study-oriented revision, 2026-10-09.

## 0. Purpose, reading guide, and status

The maintained artifact has one Maude engine, with matching checker and examples:

| File | Role |
| --- | --- |
| [certification.maude](certifier/certification.maude) | Nine functional support modules followed by `CERTIFICATION-PRODUCER`, which groups ALL rewrite rules. |
| [wrapper.maude](certifier/wrapper.maude) | Fixed wrapper template loading cached `ctor.maude` and the calculus; native module/sort import information is substituted. |
| [Calculus.lean](conPanna/Certification/Calculus.lean) | Surface equality/state/soundness rules, mirroring Maude. Read this first. |
| [Semantics.lean](conPanna/Certification/Semantics.lean) | General semantic validity proofs and final exactness acceptance. |
| [Client.lean](conPanna/Certification/Client.lean) | Generated metadata, request export and Python coordination. |
| [Parser.lean](conPanna/Certification/Parser.lean) | Parse and elaborate the Python proof bundle; check closed intermediate declarations against the fixed final goal. |
| [certifier.py](certifier/certifier.py) | Untrusted assembly of Maude evidence into applications of those Lean rules. |
| [certification-demo.lean](examples/certification-demo.lean) | Automated certificates and readable manual counterparts over the same Bakery constructors. |
| [certification.lean](certification.lean) | Additional explicit, handwritten calculus certificates. |

The differently named `conPanna/maude-cert2.maude` is an older overlap experiment,
retained only for its existing CERT2 protocol callers. It and `certification2.*`
are NOT the implementation of this document. Start with the files in the table.

**Reading the Maude source:** `certifier/certification.maude` preserves separate
functional modules and ends with ONE short system module containing ALL rewrite
rules. Its groups distinguish request/output
protocol (A.1) from semantic closure and state steps (A.2–A.4); rules marked
“trace assembly” only collect finished children. Follow its imports to the
functional modules below. Each `fmod` groups its own declarations and equations.
Rule comments identify the relevant helper module and Lean constructor.

| Functional module in `certifier/certification.maude` | Responsibility |
| --- | --- |
| [CERTIFICATION-TERMS](certifier/certification.maude#L17) | Constructor terms, sorted contexts, metadata and substitutions. |
| [CERTIFICATION-EVIDENCE](certifier/certification.maude#L147) | States, proof-tree records and primitive equality-premise formatting. |
| [CERTIFICATION-EQUALITY](certifier/certification.maude#L278) | ACU normal forms, equality proofs and proposed-answer soundness. |
| [CERTIFICATION-FREE](certifier/certification.maude#L427) | Free-constructor equation selection and proper-occurs paths. |
| [CERTIFICATION-ACU-MATCHING](certifier/certification.maude#L491) | Whole-vector answer factoring, including finite ACU matching. |
| [CERTIFICATION-SHARING](certifier/certification.maude#L651) | Occurrence grids, balanced supports and the sharing substitution. |
| [CERTIFICATION-BAG-STEPS](certifier/certification.maude#L841) | Bag selection, ATOM/ZERO children, purification and preparation. |
| [CERTIFICATION-COVERAGE](certifier/certification.maude#L976) | Conditional coverage and optional answer-guided witnesses. |
| [CERTIFICATION-OUTPUT](certifier/certification.maude#L1221) | Completed-tree serialization and diagnostic leaf collection. |

All imports are acyclic: TERMS → EVIDENCE → EQUALITY → matching/sharing;
FREE and BAG-STEPS also feed COVERAGE; OUTPUT formats completed traces.
The producer imports COVERAGE and OUTPUT, including their dependencies.
Equality-premise derivations such as cancellation and decomposition are helpers
emitting checked evidence, not additional solver rewrite rules. This module
split changes no proof rule, equation, or wire format.

This document explains how to certify an ALREADY COMPUTED finite unifier set
against registered constructor semantics. The certification input is
`(E₀, B, Σ)): the original equations, structural theory, and supplied answers.
Native Maude `unify` is upstream; certification does not call it again to
discover or replace Σ. It constructs evidence for this FIXED requested set.

The goal is exactness: every proposed answer solves the equations (soundness),
and every solution is an instance of some proposed answer (completeness).
The answer's origin is not trusted. The current Lean session checks the proof
against its independently fixed original problem and answers.

**Suggested reading order:**

1. Sections 1–2 fix the allowed models and the proposition being certified.
2. Section 3 distinguishes equality evidence, state transformations, coverage
   closure, and their final aggregation.
3. Section 4 gives the rules, state/evidence displays, and Lean definition links.
4. Section 5 works through concrete certificates and readable Maude dump trees.
5. Sections 6–8 explain answer-guided control, the evidence pipeline, and the
   implementation boundary. Sections 9–10 give references and rule provenance.
6. Appendix A collects the search-guarantee arguments. It is not a prerequisite
   for understanding the structure of an individual certification proof.

**Status:** the reusable rule checker and restricted external producer are
implemented, with kernel-checked demonstrations. General rule-validity and
accepted-certificate exactness proofs exist in Lean. The whole search-success
argument is informal, not a formally verified end-to-end search theorem.
Supported examples are evidence of implementation behavior, not a general
guarantee that every request succeeds within the prototype's resource limits.

Keep three claims separate:

- **Rule validity:** a checked rule has its stated semantic effect.
- **Search success:** a specified finite strategy can construct a certificate
  for every legal problem with a finite sound, symbolically complete supplied set.
- **Implementation correctness:** the exporter, search program, compiler, and
  replay mechanism actually implement that strategy and preserve the request.

Appendix A argues the second under the contract below; Lean checks the first
and final aggregation for individual accepted certificates. It need not invoke
a search-success theorem when checking one certificate.

Maude hosts certification search, Python assembles explicit rule applications,
and Lean checks them. Supplied answers can close branches early (§6); the
finite fallback remains available when these checked shortcuts fail.

## 1. Scope and modeling contract

### 1.1 Mathematical contract

Let the signature have finitely many explicitly distinguished sorts and finitely
many first-order constructor symbols with fixed argument and result sorts.
Terms are finite trees of constructors and sorted variables. Distinct sorts are
distinguished by signature tags, not by proving inequalities between Lean types.

There is one distinguished sort `Bag`, with exactly these constructors:

```text
empty     : Bag
singleton : Atom → Bag
union     : Bag → Bag → Bag
```

The names are illustrative. Only their types and registered roles matter. Write
`0` for `empty`, `s + t` for `union s t`, and `[a]` for `singleton a`.

The equational theory `B` consists exactly of associativity, commutativity, and
the two-sided unit law for this union, together with congruence. In particular:

- There is no idempotence, absorption, arithmetic evaluation, or additional
  constructor equation.
- All other constructors are free: distinct heads cannot be identified, and
  equality of equal-headed terms decomposes into equality of their arguments.
- No sort reachable through constructor arguments from `Atom` reaches `Bag`.
  Thus a singleton payload cannot contain a bag, directly or indirectly.
- Free configuration sorts may contain bags and may be recursively defined.

The last restriction is **stratification**, not linearity. The problem may have
arbitrarily repeated variables, arbitrary finite multiplicities, variables shared
between terms and equations, and any finite number of equations. There is no
one-tail restriction, fixed mutation depth, or fixed search-depth bound.

A typical admissible shape is:

```text
Ticket: free zero/successor constructors
Mode:   idle | wait(Ticket) | crit(Ticket)
Bag:    empty | singleton(Mode) | union(Bag, Bag)
Conf:   configuration(Ticket, Ticket, Bag)
```

A violating shape is:

```text
Mode: nested(Bag)
```

Here bags can contain payloads that contain bags again, invalidating the phase
separation used in the proof. This shape is excluded even if a particular query
happens not to use `nested`.

### 1.2 Semantic contract

`s =B t` means constructor congruence generated by the stated ACU laws, at the
appropriate sort. It does **not** mean arbitrary equality in a commutative monoid.
For example, cancellation and singleton cardinality need the free-bag semantics;
ACU laws alone do not establish them for every possible monoid interpretation.

The intended library instantiation is the existing registered, indexed relation
`Structural.Indexed.NativeEq`, written using the registered structural notation.
Native quoting/evaluation must realize the same sorted constructor presentation.
The abstract syntax in this document describes user constructors; it is not a
second, independently chosen application semantics.

No reverse equivalence with the legacy `Structural.EqMod` relation is assumed.
Transporting the result to that relation is a separate library obligation.

### 1.3 Explicit exclusions and frontend boundaries

The theorem below does not yet cover:

- Multiple ACU operators, including an ACU ticket-addition operator alongside
  process union; nested ACU fragments; AU or other structural theories.
- Other constructors returning `Bag`, or payloads containing `Bag`.
- Defined functions, user equations, subtyping/subsorts, coercion-based equations,
  higher-order terms, dependent constructor fields, or infinite constructor trees.
- Domain constraints, feasibility, narrowing, subsumption, or reachability.
- A minimal answer set, polynomial running time, or uniformly small certificates.

For example, Lean's natural numbers can supply free zero/successor constructors;
this theorem does not additionally treat the defined function `Nat.add` as ACU.
Constraints using arithmetic may exist elsewhere in the application, but are not
part of the unconstrained unification problem certified here.

The mathematical contract allows finite many-sorted signatures, including free
recursive dependencies. The current registration frontend has additional
implementation restrictions, such as its supported datatype-declaration forms.
The theorem does not assert that the frontend already accepts every signature
allowed mathematically. Mechanical registration is an implementation task, not
an extra semantic proof assigned to the model author.

## 2. Definitions and exact target

A **context** is a finite collection of variables, each with a sort. Variables
are identified by context slots; displayed names are not identities. Fresh
contexts are renamed apart, and substitution is capture-free.

Write `σ : X ⇒ Γ` for a sorted substitution mapping each variable of `X` to a
term over parameter context `Γ`. Composition `σδ` means applying `δ` to every
image of `σ`. Thus `σ : X ⇒ Γ` and `δ : Γ ⇒ Δ` give `σδ : X ⇒ Δ`.

Substitutions are compared modulo `B` **componentwise on all original variables**:

```text
σ =B τ on X  iff  for every x in X, σ(x) =B τ(x).
```

Let `E₀` be a finite list of sorted equations over original context `X`. The
context includes every input whose image must be retained, even if absent from
`E₀`. An unconstrained input is represented by a passthrough parameter.

A substitution `ρ : X ⇒ Δ` is a **symbolic unifier** if every equation in `E₀ρ`
holds modulo `B`, treating variables of `Δ` as independent symbols. This is not
merely a statement about ground instances.

A finite proposed answer list is:

```text
Σ = [σ₁ : X ⇒ Γ₁, …, σₙ : X ⇒ Γₙ].
```

Its two required properties are:

```text
Sound(Σ):
  every σᵢ is a symbolic unifier of E₀.

Complete(Σ):
  for every finite Δ and every symbolic unifier ρ : X ⇒ Δ,
  there exist i and β : Γᵢ ⇒ Δ such that ρ =B σᵢβ on X.
```

This is completeness by **factorization of substitutions**. Ground coverage
alone is not the premise used in the search-success theorem.

Normalize native answers by consistently renaming their parameters, retaining
identity/passthrough images for omitted inputs, and removing unused parameters.
Do not discard shared parameter identities or compare answer fields separately.
All subsequent statements concern this normalized list; construct the native
certificate proposition after normalization. Unused existential parameters are
not silently retained in that proposition, which matters for potentially empty
native sorts.

The eventual native exactness certificate says:

```text
for every native input valuation v,

  E₀(v)
    iff
  (exists η₁, v =B eval(σ₁, η₁))
    or … or
  (exists ηₙ, v =B eval(σₙ, ηₙ)).
```

An empty answer list gives `E₀(v) iff False`. It therefore requires exhaustive
contradiction evidence, not an unsuccessful search or match.

## 3. States, proof levels, and how they fit together

### 3.1 What a state represents

A search state is:

```text
S = ⟨α : X ⇒ Γ ; E over Γ⟩.
```

Here `X` is the FIXED original input-variable context, `Γ` is the CURRENT
parameter context, `α` records every original variable's current image, and
`E` is the remaining equation list. Introducing or removing a parameter changes
`Γ`; it does not change which original variables must be accounted for.

**Correspondence with the actual Maude state.** The active solver constructor is:

```maude
solve(HS, C, IM, ES, F, ORIG, AS, INPUTS)
```

| Maude argument | Meaning here |
| --- | --- |
| `C` | Current sorted variable context Γ. |
| `IM` | Image vector α for ALL original inputs. |
| `ES` | The ONE current equation list E, including singleton requirements. |
| `HS` | Fixed constructor/sort metadata and structural roles. |
| `ORIG` | Fixed original equations E₀. |
| `AS` | Fixed supplied answer set Σ. |
| `INPUTS` | Fixed original input context X. |
| `F` | Proof continuation: how to wrap the finished child trace into earlier steps. |

See the [constructor declaration](certifier/certification.maude#L168). `⟨α ; E⟩` is
a mathematical projection of this active state, NOT a literal pair constructor
in Maude: it displays IM/ES with C implicit in their types. We use this same
two-field notation for EVERY rule. When scope changes need emphasis, we write
`⟨α ; E⟩ in scope Γ` and label the new scope outside the successor state.
The remaining request arguments stay
fixed; F belongs to evidence assembly rather than the state's solution set.
The producer also has pending/finished states for collecting proof children;
they are runtime control states, not extra components of this mathematical pair.

For any target context `Δ`, the state represents:

```text
Denote(α, E, Δ) =
  { ρ : X ⇒ Δ |
      exists δ : Γ ⇒ Δ,
      δ unifies E and ρ =B αδ on ALL original variables }.
```

The initial state is `⟨identity ; E₀⟩`. An exact state transformation preserves
this set, or represents it as the union of its children's sets. A dead state
represents no solutions.

Example: after binding `P := Q`, the original inputs `(P,Q)` are still
recorded, now by the image vector `(Q,Q)`. Keeping both components prevents
later coverage from silently forgetting the original P.

Lean: [ReplayState](conPanna/Certification/Syntax.lean#L490),
[ReplayState.substitute](conPanna/Certification/Syntax.lean#L496).

### 3.2 Three proof levels, followed by one final aggregation

The same word “rule” has been used for different jobs. Keep these separate:

| Level | Input → output | What it establishes | Lean representation |
| --- | --- | --- | --- |
| Equality evidence | Terms, optionally equations E → proof of a term equality | A law, or a consequence of E; it does NOT change the search state | `Equality`; `Worklist.Derives` |
| State transformation | One state → one state or a finite family of states | Every parent solution is represented by a child; the abstract transformations below are exact | Constructors such as `Complete.bind`, `purify`, `atom`, `sharing` |
| Coverage closure | State and supplied answer σᵢ, with a factor β → coverage proof | All solutions of this state factor through that answer; no further child is needed | `Complete.cover`; contradiction leaves close empty states |
| Final aggregation | Root coverage AND supplied-answer soundness → exactness | The requested unifier set has neither missing solutions nor junk | `Worklist.exact_system` |

There are two equality judgements, not two user-facing equalities:

```text
⊢B s = t       equality valid without assuming the current equations
E ⊢B s = t     equality valid for every valuation satisfying E
```

Both conclude the SAME structural relation `=B`. The distinction is whether
the proof may use hypotheses from E. Lean's
[Equality](conPanna/Certification/Calculus.lean#L37) records the first;
[Derives](conPanna/Certification/Calculus.lean#L91) records the second.

Write the coverage judgement as:

```text
Σ ⊢ S covered

meaning: every solution represented by S factors through some σᵢ in Σ.
```

Search follows state arrows DOWN a tree. Checking combines child proofs UP
that tree:

```text
Unary exact step:                 Exhaustive branching step:

S → S'                           S → {S₁, …, Sₖ}
Σ ⊢ S' covered                   Σ ⊢ S₁ covered  …  Σ ⊢ Sₖ covered
────────────────                 ────────────────────────────────
Σ ⊢ S covered                    Σ ⊢ S covered
```

ALL children are required, not just the branch corresponding to one successful
unifier. An empty branch family is acceptable only when a checked rule proves
that the parent has no solutions.

A COVER leaf supplies inclusion in the proposed answers, not exactness by itself.
Independently check that every proposed answer solves every original equation:

```text
Σ ⊢ ⟨identity ; E₀⟩ covered       Sound(E₀, Σ)
─────────────────────────────────────────────
Exact(E₀, Σ)
```

This is [exact_system](conPanna/Certification/Semantics.lean#L1057).
[Complete.sound](conPanna/Certification/Semantics.lean#L916) proves the validity of
a COVERAGE tree; despite its name, it is not the separate proposed-answer
soundness proof. That reverse direction is supplied by
[SystemSoundness.sound](conPanna/Certification/Semantics.lean#L1045).

### 3.3 The overall procedure

The inputs `E₀, B, Σ` are already fixed. Native unification has supplied Σ;
none of the following steps acquires a new answer set.

```text
Completeness side:
  root ⟨identity ; E₀⟩
    → try checked COVER using a supplied answer
    → otherwise transform/split the state
    → cover EVERY child, or prove it contradictory
    → combine the children into root coverage

Soundness side:
  for EVERY σᵢ and EVERY equation s =B t in E₀,
    construct unconditional equality evidence for sσᵢ =B tσᵢ

Final step:
  combine these two proofs into the original exactness proposition.
```

The fallback first processes free constructors, then bag balances, singleton
requirements, and their free payload equations. The detailed search-success
argument is in Appendix A; understanding individual certificates does not require
reading it first.

## 4. Proof rules and their Lean counterparts

### Reading convention

A state arrow describes the mathematical transformation. A displayed equality
judgement describes evidence used BY a transformation or closure. A coverage
inference closes a proof; it is not another state transition.

In state displays, `E` denotes ALL other equations, and `ασ` means apply the
same substitution σ to EVERY original input image. Substitution must also act on
EVERY equation; substitutions are never selected independently per component.

The abstract presentation may delete a solved equation. The implementation often
RETAINS it, adds derived requirements, and closes by conditional COVER.
Consequently, DELETE, ORIENT, DECOMPOSE, NORMALIZE, and CANCEL need not appear as
separate completeness-tree nodes. Their evidence can instead occur inside a
node's `premise` or `derived` fields. This is not a different semantics.

### 4.1 Free constructors and substitution — state transformations

**Intuition: compare constructor heads, then their arguments.** For example,
`wait(n) =B wait(m)` reduces to `n =B m`; binding `n:=m` changes the
original image vector `(n,m,P)` to `(m,m,P)` everywhere. In contrast,
`wait(n) =B crit(m)` is impossible because the free constructor heads differ.
Likewise, `n =B succ(n)` would require a finite free-constructor term to contain
itself strictly, so FREE-OCCURS closes that case.
The formal rules make these steps explicit:

```text
DELETE
  ⟨α ; t =B t, E⟩ → ⟨α ; E⟩

ORIENT
  ⟨α ; t =B x, E⟩ → ⟨α ; x =B t, E⟩
  x is a variable; orient consistently rather than flipping repeatedly.

DECOMPOSE
  ⟨α ; f(s₁,…,sₖ) =B f(t₁,…,tₖ), E⟩
  → ⟨α ; s₁ =B t₁,…,sₖ =B tₖ, E⟩
  f is a free constructor.

CLASH
  ⟨α ; f(…) =B g(…), E⟩ → dead
  f and g are distinct free heads at the same non-Bag result sort.

BIND                         θ = [x := t]
  ⟨α ; x =B t, E⟩ → ⟨αθ ; Eθ⟩
  t is scoped WITHOUT x; remove x from the live context.

FREE-OCCURS
  ⟨α ; x =B t, E⟩ → dead
  x occurs strictly below free constructors in t, along a free-only path.
```

| Rule | Maude label or helper (no standalone label where noted) | Lean definition or evidence constructor |
| --- | --- | --- |
| DELETE | [`chooseTerm(S,A,A,HS,P)`](certifier/certification.maude#L470) skips a reflexive equation; no standalone rewrite rule | [Equality.refl](conPanna/Certification/Calculus.lean#L37); bookkeeping, not a separate `Complete` constructor |
| ORIENT | [`chooseTerm`](certifier/certification.maude#L474) orients the selected premise via `symmText`; no standalone rewrite rule | [Derives.symm](conPanna/Certification/Calculus.lean#L91) |
| DECOMPOSE | [`chooseArgs`](certifier/certification.maude#L482) with [`decompText`](certifier/certification.maude#L270) derives a field equation; no standalone rewrite rule | [Derives.decompose](conPanna/Certification/Calculus.lean#L91), justified by [decompose_native](conPanna/Certification/Semantics.lean#L144) |
| CLASH | [`[clash-and-emit]`](certifier/certification.maude#L1437) | [Complete.clash](conPanna/Certification/Calculus.lean#L123) |
| BIND | [`[bind]`](certifier/certification.maude#L1430) | [Complete.bind](conPanna/Certification/Calculus.lean#L123), [Binding.Removal](conPanna/Certification/Syntax.lean#L153), [Binding.complete](conPanna/Certification/Semantics.lean#L599) |
| FREE-OCCURS | [`[occurs-and-emit]`](certifier/certification.maude#L1444) | [Complete.occurs](conPanna/Certification/Calculus.lean#L123), [FreeOccurs.Proper.sound](conPanna/Certification/Semantics.lean#L658) |
| Free-step selection | [`chooseTerm`](certifier/certification.maude#L470) in `CERTIFICATION-FREE` | [FreePhase.classify](conPanna/Certification/Syntax.lean#L404) |

BIND is valid at any sort when the scoped-replacement condition holds. The
mandatory free phase uses it at non-bag sorts; optional bag bindings are shortcuts.
Typed context removal enforces no occurrence of x in the replacement and a
strict one-variable decrease. The SAME generated substitution changes the
entire worklist and image vector.

Do not clash raw `empty` and `union` heads or reject arbitrary bag occurrences:
`P =B P+Q` has solutions with `Q=0`. Under the stratified contract, a
same-sort non-bag occurrence cannot run through a bag and return to its own sort,
so the ordinary free occurs argument is legitimate in the mandatory free phase.

### 4.2 Bag normalization, cancellation, and purification

**Intuition: separate bag distribution from singleton requirements.** A
**pure balance** is an equation containing only bag variables combined by union,
possibly repeated. “Balance” simply means an equation between two bag sums;
“pure” means no explicit singletons remain in that equation.

We prepare such an equation by flattening unions, canceling common occurrences,
and naming each remaining explicit singleton with a fresh bag variable:

```text
Original:    ((P+0)+P)+C =B ([wait(n)]+Q)+C
NORMALIZE:          2P+C =B [wait(n)]+Q+C
CANCEL:              2P =B [wait(n)]+Q
PURIFY:              2P =B A+Q          ← pure balance
                      A =B [wait(n)]    ← separate retained requirement
```

Here `2P` means `P+P`. We have not discarded the singleton: its defining
equation remains a requirement. FINITE-SHARING will first describe how the bags
P,A,Q can be distributed; later rules enforce that A is exactly `[wait(n)]`.

**Formal rules.** NORMALIZE makes the union structure explicit without changing
the original-variable context. It is equality evidence plus an optional change
of presentation:

```text
NORMALIZE                                  nf flattens + and removes 0
  ⊢B s = nf(s)       ⊢B t = nf(t)
  ⟨α ; s =B t, E⟩ → ⟨α ; nf(s) =B nf(t), E⟩
```

Its proofs use `Equality.assoc`, `comm`, `unit`, `congr`, `trans`,
and `symm`; see [Equality](conPanna/Certification/Calculus.lean#L37).
Maude: [`norm`](certifier/certification.maude#L328) in `CERTIFICATION-EQUALITY`
constructs NORMALIZE evidence; `normalized` computes data-only normal forms
for decisions. There is no standalone `[normalize]` rewrite rule.

CANCEL removes the same bag contribution from both sides. It has a state
presentation and an evidence presentation:

```text
CANCEL — state
  ⟨α ; C+L =B C+R, E⟩ → ⟨α ; L =B R, E⟩

CANCEL — evidence                         MULTIPLICITY-CANCEL — evidence
  E ⊢B C+L = C+R                           E ⊢B kU = kV     k > 0
  ───────────────                          ──────────────────────
  E ⊢B L = R                               E ⊢B U = V
```

Here `kU` means k repeated copies, not arithmetic on payloads. Replay can
retain the original equation and use the derived equality for the next step.
Lean: [Derives.cancel](conPanna/Certification/Calculus.lean#L91),
[Derives.multiplicity](conPanna/Certification/Calculus.lean#L91),
[cancel_native](conPanna/Certification/Semantics.lean#L253),
[multiplicity_native](conPanna/Certification/Semantics.lean#L119).
Maude: [`cancelText`](certifier/certification.maude#L1101) and
[`multiplicityText`](certifier/certification.maude#L1091) in
`CERTIFICATION-COVERAGE` construct CANCEL and MULTIPLICITY-CANCEL evidence.
[`sharingPremise`](certifier/certification.maude#L809) also emits cancellation
evidence during sharing preparation.
Neither is a standalone solver rewrite rule.

Both rules rely on the FREE bag algebra, not just an arbitrary ACU monoid.
Common syntactic occurrences can be canceled without comparing payloads.

PURIFY names a singleton while retaining its defining equation. It is an exact
state transformation introducing a fresh witness:

```text
PURIFY
  ⟨α ; e[[t]], E⟩ in scope Γ
  → ⟨lift(α) ; e[A], A =B [t], lift(E)⟩ in scope Γ,A

  A is fresh. e[·] selects ONE occurrence in the equation.
  All pre-existing terms are lifted into the extended scope.
```

An old solution extends with `A:=[t]`; the defining equation ensures that
every new solution restricts back to an old one.

Lean: [Complete.purify](conPanna/Certification/Calculus.lean#L123),
[Purification.state](conPanna/Certification/Syntax.lean#L474),
[Purification.exact](conPanna/Certification/Semantics.lean#L865).
The typed fresh-slot template must reconstruct the exact old equation when its
slot is filled; an external dump cannot simply assert that the replacement is valid.
Maude: [`[purify]`](certifier/certification.maude#L1494) invokes
[`beginPurify`](certifier/certification.maude#L918) in
`CERTIFICATION-BAG-STEPS`; `[prepare-next]` continues preparation and
`[purify-collect]` wraps the finished child. Only `[purify]` is the semantic step.

After preparation, the selected pure balance has the general form:

```text
a₁X₁ + … + aᵣXᵣ =B b₁Y₁ + … + bₛYₛ.
```

Coefficients are positive; no active variable occurs on both sides. Other live
variables remain passthroughs.

### 4.3 FINITE-SHARING — a state transformation introducing parameters

This rule solves a PURE variable balance. It does not decide singleton or payload
requirements; those equations are carried to its child.

**Intuition: describe how the two sides share their contents.** Start with:

```text
P + Q =B R + S
```

The same total bag is divided in two ways: into P/Q on the left, and R/S on the
right. Introduce pieces describing where contents belong in BOTH divisions:

```text
                    Right occurrence
                      R       S
Left occurrence  P    a       b
                 Q    c       d

P =B a+b    Q =B c+d    R =B a+c    S =B b+d
```

For example, a is the piece contributed by P on the left and R on the right.
Reading row sums reconstructs the left variables; reading column sums
reconstructs the right variables. Both totals contain exactly a,b,c,d, so they
agree. These are bags of occurrences, not set intersections: duplicate elements
are preserved. Any piece may be empty.

**Repeated variables need an extra consistency check.** In `P+P =B Q+Q+Q`,
there are TWO rows labelled P and THREE columns labelled Q. The rows represent
occurrences of the SAME variable, not two independently assignable bags.
Therefore their reconstructed expressions must agree; likewise for the Q columns.

To see this, put a copy of the SAME fresh bag Z in each selected cell;
`.` means no contribution. Compare these two patterns:

```text
Consistent pattern                      Inconsistent pattern

           Q₁   Q₂   Q₃   row sum                   Q₁   Q₂   Q₃   row sum
     P₁     Z    Z    Z      3Z               P₁     Z    .    .       Z
     P₂     Z    Z    Z      3Z               P₂     .    .    .       0
column     2Z   2Z   2Z                  column      Z    0    0
sum                                     sum
```

The subscripts distinguish occurrences, NOT variables. On the left, BOTH P
rows reconstruct 3Z and ALL Q columns reconstruct 2Z. Thus `P:=3Z, Q:=2Z`
works: the left total is `2(3Z)` and the right total is `3(2Z)`.

On the right, the two P occurrences would require `P =B Z` AND `P =B 0`;
the Q occurrences disagree too. This is not a valid family for an arbitrary Z.
Z=0 could make those particular equations hold, but a sharing parameter must
remain freely assignable, not require a new constraint.

**How enumeration works: continue `2P =B 3Q`.** There are six cells. For each
cell, choose selected or unselected: this gives `2⁶ = 64` grids. These choices
enumerate patterns, NOT concrete values for P or Q. Write a grid as two rows
of digits: `1` selects a cell and `0` does not. For example, `100 / 000`
selects only the top-left cell.

For each grid, count selected cells in each row and column:

| Grid: P₁ row / P₂ row | Row counts | Column counts | Keep? |
| --- | --- | --- | --- |
| `000 / 000` | 0, 0 | 0, 0, 0 | No: no cells are selected. |
| `100 / 000` | 1, 0 | 1, 0, 0 | No: repeated P and Q occurrences disagree. |
| `111 / 000` | 3, 0 | 1, 1, 1 | No: the P occurrences disagree. |
| `110 / 110` | 2, 2 | 2, 2, 0 | No: the Q occurrences disagree. |
| `111 / 111` | 3, 3 | 2, 2, 2 | Yes: both P rows agree, and all Q columns agree. |

These trials explain the terminology: a nonempty selection of cells is a
**support** (a sharing pattern). It is **balanced** when repeated occurrences of
each variable have equal counts. Thus the full grid is balanced, whereas the
other nonempty grids shown above are not. FINITE-SHARING keeps exactly the
balanced supports.

The table shows representative trials, not all 64. In fact only the full grid
survives: if each P row has d cells and each Q column has e, counting all selected
cells gives `2d=3e`, with `0≤d≤3` and `0≤e≤2`. The only nonempty possibility
is d=3,e=2.

Now give that ONE retained support ONE fresh bag parameter Z, placing a copy of
the SAME Z in EVERY selected cell. Each P row has three selected cells, so a P
occurrence receives three copies of Z; each Q column has two, so a Q occurrence
receives two. The output substitution is:

```text
θ(P) := Z+Z+Z
θ(Q) := Z+Z
```

That is the entire pattern-generation step for this equation: enumerate grids,
check counts, allocate a parameter, and read off copies. No bag values have been
guessed. Discarding the empty grid does not discard the empty solution: assigning
Z:=0 already gives `P =B 0` and `Q =B 0`.

**What if several patterns survive? Change the example to `2P =B 2Q`.** Its
2-by-2 grid has 16 selections. Exactly THREE are nonempty and balanced:

```text
Pattern U             Pattern V             Pattern W
           Q₁ Q₂                 Q₁ Q₂                 Q₁ Q₂
     P₁     1  0           P₁     0  1           P₁     1  1
     P₂     0  1           P₂     1  0           P₂     1  1
```

Give each retained support its OWN independent fresh bag U,V,W. Replace every
`1` in that support's grid with a copy of its bag, then read the counts:

| Pattern | Copies in EACH P row | Copies in EACH Q column | Contribution to θ(P) and θ(Q) |
| --- | --- | --- | --- |
| U: diagonal | 1 | 1 | U |
| V: opposite diagonal | 1 | 1 | V |
| W: full grid | 2 | 2 | W+W |

Add these contributions, rather than choosing one of the patterns:

```text
θ(P) := U+V+W+W
θ(Q) := U+V+W+W
```

This is how several balanced supports coexist: their independent contributions
are ADDED to reconstruct each variable. This is ONE unifier with THREE
parameters, not three alternative unifiers.
For example, assigning U:=[a], V:=[b], W:=0 gives `P =B [a]+[b]` and
`Q =B [a]+[b]`: both diagonal patterns contribute at once.
Keeping the full-grid parameter is redundant here, but harmless; the exhaustive
rule does not try to minimize its generated family.

For the earlier `P+Q =B R+S` example, no variable labels repeat, so the same
2-by-2 enumeration keeps all 15 nonempty selections. Its four single-cell
patterns reproduce the parameters a,b,c,d in the introductory grid when all
other pattern parameters are assigned 0.

**Formal construction.**

Let `p = sum aᵢ` and `q = sum bⱼ`. Make p occurrence rows and q occurrence
columns, labelled by their original variables. A support is a nonempty subset of
the p*q cells. Keep ALL supports satisfying:

- Every row labelled Xᵢ has the same degree dᵢ(S).
- Every column labelled Yⱼ has the same degree eⱼ(S).

A degree counts selected cells. With one fresh bag parameter Z_S per retained
support S, define:

```text
θ(Xᵢ) = sum over all retained S of dᵢ(S) copies of Z_S
θ(Yⱼ) = sum over all retained S of eⱼ(S) copies of Z_S

Selected equation, derived from the current equation list:
  E ⊢B a₁X₁ + … + aᵣXᵣ = b₁Y₁ + … + bₛYₛ

FINITE-SHARING
  ⟨α ; E⟩ in scope Γ
  → ⟨αθ ; Eθ⟩ in scope Γ′
```

There is only ONE equation list E: singleton requirements are ordinary members
of it. The explicit sum equation is a checked premise selected from, or derived
from, E; it is not a separate state component named “Balance”. The SAME θ acts
on every equation and every original input image. Replay retains the selected
equation too; its weighted balance becomes an ACU identity after substitution.
Other equations may still need solving.

Γ′ adds fresh support parameters to Γ. Unrelated live variables have same-sort
passthrough images. For a fixed selected equation and enumeration order, this
step is DETERMINISTIC: compute all supports, one θ, and ONE child state. There is
no choice of a single support and no child per support; all Z_S coexist and any
may be empty. ATOM's multiple children are a different kind of rule.

**Actual Maude rule.** This is the maintained producer's entry into the step:

```maude
crl [finite-sharing] : solve(HS, C, IM, ES, F, ORIG, AS, INPUTS) =>
  sharingState(HS, C, IM, ES, F, ORIG, AS, INPUTS, A, B, P)
  if noCover := selectCoverage(C, IM, ES, AS, INPUTS, HS) /\ none := choose(ES, 0, HS) /\
    balanceChoice(A, B, P) := selectBag(ES, 0, HS) .
```

Here A,B are the selected bag terms and P is evidence for their equation, not
a pattern parameter. The guards say that coverage has not already closed the
state, no free step is selected, and a bag balance is selected. The functions
`sharingState`/`prepareSharing` count and cancel variable occurrences, enumerate
supports, and compute θ. `launchSharing` creates a pending SHARING node with
ONE child solver whose IM and ES are both substituted. `[sharing-collect]`
wraps that child's finished trace into the SHARING evidence node.

Thus the mathematical arrow summarizes deterministic helper computation and
child creation, not a different pair-based implementation. See
[`[finite-sharing]`](certifier/certification.maude#L1486) and
[`launchSharing`](certifier/certification.maude#L828) in `CERTIFICATION-SHARING`.

For `2P =B 3Q`, the only nonempty balanced support is the full rectangle shown
in the intuitive example above. Hence `θ(P)=3Z, θ(Q)=2Z`. Section 5.3 shows
the corresponding certificate.

Why keep ALL balanced supports? A selected pattern can describe only part of
the solution space. The general rule retains every such pattern, so every
solution can be assembled from their parameter bags. The finite-sharing theorem
justifies that last completeness claim; it is not inferred merely from this
example. Parameters may be empty, making unused patterns harmless. The family
can be redundant: for `P+Q =B R+S`, the four single-cell patterns already give
the four-piece description above, but the exhaustive rule retains larger
supports too. It prioritizes complete coverage over a minimal answer.

If one side has no occurrences, every active variable is sent to empty.
If both sides cancel, there are no active variables and all variables pass
through. Thus `X+Y =B X` leaves X arbitrary and forces Y=0; `X =B X`
leaves X arbitrary.

The general semantic lemma states:

```text
δ unifies a₁X₁ + … + aᵣXᵣ =B b₁Y₁ + … + bₛYₛ
  iff
exists η, δ =B θη on ALL old live variables.
```

Its finite-support argument is in Appendix A.1, not an extra obligation for each
user problem. Lean links:

- Enumeration: [supportGenerators](conPanna/Certification/Enumeration.lean#L191),
  [supportGenerators_exact](conPanna/Certification/Enumeration.lean#L225).
- Semantic lift: [finiteSharing_native](conPanna/Certification/Semantics.lean#L88),
  [Sharing.complete / sound](conPanna/Certification/Semantics.lean#L684).
- Replay: [Complete.sharing](conPanna/Certification/Calculus.lean#L123);
  [Complete.sharingTable](conPanna/Certification/Calculus.lean#L222) checks the
  supplied table equal to the exhaustive enumeration.

The displayed state transition uses that same retained-worklist convention:
no selected equation or singleton requirement is silently removed.

### 4.4 Singleton and zero processing — exhaustive state branching

**Intuition: a singleton has exactly one occurrence to distribute.** Thus
`P+Q =B [t]` has two possibilities: P supplies `[t]` and Q is empty, or the
reverse. But `2P =B [t]` is impossible: any nonempty P contributes at least
two occurrences. Equal payloads do not merge those occurrences, since there
is no idempotence. For `P+Q =B 0`, both contributions must be empty.

The rules below generalize these observations to arbitrary positive coefficients
and explicit singleton summands. Every possible supplier gets a branch.
**Formal construction.**

Normalize a singleton requirement, combining repeated variables:

```text
F = [u₁]+…+[uₖ] + c₁Z₁+…+cₗZₗ =B [t].
```

The Zᵢ are distinct and each cᵢ is positive. Define θ₀ to send every Zᵢ to 0,
and θⱼ to send Zⱼ to [t] and every other Zᵢ to 0. The familiar cases are:

```text
ATOM-MANY     k ≥ 2
  ⟨α ; F, E⟩ → dead

ATOM-ONE      k = 1
  ⟨α ; F, E⟩ → ⟨αθ₀ ; u₁ =B t, Eθ₀⟩

ATOM-CHOOSE   k = 0
  ⟨α ; F, E⟩ → { ⟨αθⱼ ; Eθⱼ⟩ | cⱼ = 1 }
  If there is no coefficient-one index, the branch family is empty.

ZERO          G = [u₁]+…+[uₖ] + c₁Z₁+…+cₗZₗ =B 0
  k > 0:  ⟨α ; G, E⟩ → dead
  k = 0:  ⟨α ; G, E⟩ → ⟨αθ₀ ; Eθ₀⟩
```

The replay uses ONE general ATOM rule, rather than primitive constructors named
ATOM-MANY/ONE/CHOOSE. Its summands tᵢ may be variables OR explicit singletons:

```text
ATOM — actual retained-equation presentation
  E ⊢B sumᵢ cᵢtᵢ = [t]

  ⟨α ; E⟩
    → { ⟨α ; tⱼ =B [t],
                tᵢ =B 0 for every other positive-coefficient i,
                E⟩ | cⱼ = 1 }

ZERO — actual retained-equation presentation
  E ⊢B sumᵢ cᵢtᵢ = 0

  ⟨α ; E⟩
    → ⟨α ; tᵢ =B 0 for every positive-coefficient i, E⟩

NONEMPTY
  E ⊢B [u] = 0
  ⟨α ; E⟩ → dead
```

These children retain the SAME α and scope until a later BIND changes them.
If two explicit singletons occur, choosing either forces the other empty, so
NONEMPTY closes every case. If exactly one occurs, only its choice survives,
and singleton decomposition yields the payload equation. These are the
ATOM-MANY/ONE cases derived from ATOM plus general rules.

Repeated variables stay shared. For `2P =B [a]`, the coefficient-aware ATOM
rule has no coefficient-one choice. A dump that instead lists `P,P` as two
occurrences has two children, each requiring BOTH `P=[a]` and `P=0`;
both close by contradiction. Neither presentation may silently discard a case.

A binding must update other requirements too: after `Z:=[u]`, a second
requirement `Z =B [v]` becomes `[u] =B [v]`, then `u =B v`.
Under the contract, these payload equations cannot create more bag equations.

Lean: [Complete.atom](conPanna/Certification/Calculus.lean#L123),
[Complete.zero](conPanna/Certification/Calculus.lean#L123),
[Complete.nonempty](conPanna/Certification/Calculus.lean#L123).
Maude labels: [`[atom-split]`](certifier/certification.maude#L1453),
[`[zero-split]`](certifier/certification.maude#L1465), and
[`[nonempty-close]`](certifier/certification.maude#L1477).
`[atom-collect]` / `[zero-collect]` assemble finished children; their requirements
come from `CERTIFICATION-BAG-STEPS`. ATOM-MANY/ONE/CHOOSE are derived cases of
these rules, not additional Maude labels.
Their exact requirements are computed by
[atomRequirements](conPanna/Certification/Syntax.lean#L484) and
[zeroRequirements](conPanna/Certification/Syntax.lean#L480);
the general semantic lemmas are
[AtomProcessing.sum_atom](conPanna/Certification/Enumeration.lean#L715) and
[sum_zero](conPanna/Certification/Enumeration.lean#L694).
Coefficient-zero entries impose only reflexive equations and remain unrestricted.
The binary special case is also exposed as
[Complete.split](conPanna/Certification/Calculus.lean#L123) and
[NativeRules.singletonCases](conPanna/Certification/Semantics.lean#L195).

### 4.5 COVER — proof closure, not a state transformation

**Intuition: show that a supplied answer already includes every current solution.**
Suppose `E={P =B Q}`, the original images are `(P,Q)`, and a supplied answer is
`σ=(Z,Z)`. Choose `β(Z)=P`: reflexivity proves `P =B P`, while the current
equation gives `Q =B P` by symmetry. Hence `(P,Q)` agrees with `(P,P)=σβ`
for every solution of E. The state is covered without solving anything further.

**Formal closure.**

COVER takes a supplied answer σᵢ and ONE substitution β from its parameters to
the current scope. It requires every original input image to agree:

```text
COVER / EARLY-COVER
  σᵢ ∈ Σ       β : parameters(σᵢ) ⇒ Γ
  E ⊢B α(x) = σᵢ(x)β       for EVERY original variable x
  ──────────────────────────────────────────────────────
  Σ ⊢ ⟨α ; E⟩ covered
```

There is no child state. A valuation δ satisfying E supplies the answer witness
βδ; the equalities establish factorization of the ENTIRE original input vector.

At a solved leaf `E=[]`, the equalities are unconditional: this is ordinary
COVER. At an unsolved state, they may use E: this is EARLY-COVER. Both are the
SAME [Complete.cover](conPanna/Certification/Calculus.lean#L123) constructor.
Maude: [`[cover-and-emit]`](certifier/certification.maude#L1414) implements both COVER and
EARLY-COVER, using [`selectCoverage`](certifier/certification.maude#L1160) in
`CERTIFICATION-COVERAGE` and whole-vector
factoring in `CERTIFICATION-ACU-MATCHING`. There is no separate early-cover label.
Early closure does NOT assert that E is trivial or that the current state is
exactly that answer's whole family; only the required inclusion is established.

Evidence inside COVER uses
[Derives.hyp / symm / trans / congr](conPanna/Certification/Calculus.lean#L91),
possibly cancellation, multiplicity cancellation, and free decomposition.
Unconditional ACU proofs enter via `Derives.axiom`.

A failed matcher, unsupported syntax, resource cutoff, or redundant branch is NOT
a contradiction leaf. Empty states need checked CLASH, FREE-OCCURS, NONEMPTY,
or the exhaustive singleton/zero argument of §4.4.

### 4.6 MUTATE — optional state transformation introducing sharing witnesses

**Intuition: make missing sharing pieces available to COVER.** For
`P+Q =B R+S`, a supplied answer may describe the four pieces in the grid of
§4.3: `P:=p+q, Q:=r+t, R:=p+r, S:=q+t`. We know the original bags, but have not
yet named those pieces. MUTATE introduces them as fresh parameters with four
defining equations; those equations can then justify a COVER factor. It does
not guess arbitrary pieces and assume they happen to work.

**Formal transformation.**

A factor β must use terms available in the current scope. Sometimes the answer
needs pieces of bags that are not expressible there. MUTATE introduces them:

```text
MUTATE
  ⟨α ; A₁+A₂ =B B₁+B₂, E⟩ in scope Γ
  → ⟨lift(α) ;
       A₁ =B p+q, A₂ =B r+t,
       B₁ =B p+r, B₂ =B q+t,
       lift(A₁+A₂ =B B₁+B₂, E)⟩ in scope Γ,p,q,r,t

  p,q,r,t are fresh bag variables; all old terms are lifted.
```

Every old solution has such a four-piece common refinement; conversely the
four defining equations imply the old balance. This is a general exact rule,
not a guess that one particular solution has those pieces.

Lean: [Complete.mutate](conPanna/Certification/Calculus.lean#L123),
[mutated](conPanna/Certification/Syntax.lean#L449),
[mutate_native](conPanna/Certification/Semantics.lean#L221).
Maude: [`[witness-cover-and-emit]`](certifier/certification.maude#L1422) closes with a
composite MUTATE → COVER trace constructed by
[`tryWitness`](certifier/certification.maude#L1185) / `finishWitness` in
`CERTIFICATION-COVERAGE`. There is no standalone `[mutate]` rule in this producer.
It may enable immediate COVER by a supplied four-parameter answer (§5.4).
The complete fallback remains FINITE-SHARING; unrestricted MUTATE search is not
the prescribed termination argument.

### 4.7 Proposed-answer soundness and final aggregation

**Intuition: coverage rules out missing solutions; soundness rules out junk.**
For `P+Q =B [t]`, an extra proposed answer `P:=[t], Q:=[t]` would not damage
coverage, but it is not a unifier: substitution produces `2[t] =B [t]`, which
is false. Checking each proposed answer independently rejects such junk.
Combining this with root coverage establishes BOTH directions of exactness.

**Formal aggregation.**

Soundness checks the SUPPLIED answers, independently of the coverage tree:

```text
ANSWER-SOUND
  ⊢B sσᵢ = tσᵢ       for every (s =B t) ∈ E₀
  ──────────────────────────────────────────
  σᵢ solves E₀

EXACT
  Σ ⊢ ⟨identity ; E₀⟩ covered       every σᵢ ∈ Σ solves E₀
  ───────────────────────────────────────────────────────
  E₀(v) iff ∨ᵢ exists ηᵢ, v =B σᵢ(ηᵢ)   for every v
```

The equalities are unconditional in each answer's independent parameters.
Assuming E₀ itself here would make soundness circular.

Lean: [Soundness](conPanna/Certification/Calculus.lean#L65) records evidence for
one equation and all answers;
[SystemSoundness](conPanna/Certification/Calculus.lean#L247) combines equations.
[exact_system](conPanna/Certification/Semantics.lean#L1057) combines this with root
coverage. For a single equation,
[exact](conPanna/Certification/Semantics.lean#L1066) is the convenience theorem.
Maude: [`[emit-sound-evidence]`](certifier/certification.maude#L1401) emits ANSWER-SOUND
evidence using [`answersProof`](certifier/certification.maude#L394) in
`CERTIFICATION-EQUALITY`;
[`[emit]`](certifier/certification.maude#L1406) packages it with completed root coverage.
EXACT is the Lean aggregation above, NOT an additional Maude search rule or a
claim that formatting JSON proves exactness.

These are proved rule-validity/aggregation theorems. The claim that a SEARCH
procedure can always find their premises is different, and belongs to Appendix A.

## 5. Worked certificates: states, dump trees, and Lean proofs

These examples use the notation `a(n)=[wait(n)]`, `0=empty`, and
`+=union`. The constructors are those of the Bakery model; the rules are
general. In every example, the answer family is supplied BEFORE certification.

Dump displays below are READABLE PROJECTIONS of rule records: names replace
sorted slot indices, and routine scope/image/equation fields are abbreviated.
They are not literal JSON inputs or copy-paste Lean syntax. Rule names and the
`child`, `children`, `premise`, `index`, `beta`, and `derived` fields
correspond to the actual [Maude serializer](certifier/certification.maude#L1257).
The full wire format also carries sorted constructor terms and checked snapshots.

### 5.1 Two unifiers: P+Q =B [wait(n)]

Input and requested answer set:

```text
Original inputs X = (n,P,Q)
E₀ = {P+Q =B a(n)}

σ₀(N): (n,P,Q) := (N, a(N), 0)
σ₁(N): (n,P,Q) := (N, 0, a(N))
```

**Completeness, down the state tree.** ATOM must account for both singleton
suppliers. Its actual retained-equation children are:

```text
S₀ = ⟨(n,P,Q) ; P+Q =B a(n)⟩
  ── ATOM ──→
  S_L = ⟨(n,P,Q) ; P =B a(n), Q =B 0, E₀⟩
  S_R = ⟨(n,P,Q) ; P =B 0, Q =B a(n), E₀⟩
```

No variables have been substituted away yet. In S_L, choose σ₀ and β(N)=n:

```text
E_L ⊢B n = n             REFL
E_L ⊢B P = a(n)          HYP: the branch's first requirement
E_L ⊢B Q = 0             HYP: the branch's second requirement
```

These are precisely the three original-input component equalities required by
COVER. S_R closes against σ₁ with the SAME kind of factor β(N)=n. Combining
BOTH COVER proofs using ATOM establishes root coverage.

**Soundness, independently.** Substitute the two proposed assignments into E₀:

```text
σ₀:  a(N)+0 =B a(N)       COMM then left UNIT
σ₁:  0+a(N) =B a(N)       left UNIT
```

No branch hypotheses are used for these equalities. Aggregation now proves:

```text
P+Q =B a(n)
iff
  (exists N, n =B N and P =B a(N) and Q =B 0)
  or
  (exists N, n =B N and P =B 0 and Q =B a(N)).
```

The dump's completeness part and separate soundness part have this structure:

```text
{
  proof: {
    rule: "atom", premise: HYP(P+Q =B a(n)),
    children: [
      { rule: "cover", index: 0, beta: [N := n],
        derived: [REFL(n), HYP(P=a(n)), HYP(Q=0)] },
      { rule: "cover", index: 1, beta: [N := n],
        derived: [REFL(n), HYP(P=0), HYP(Q=a(n))] }
    ]
  },
  sound: [[ equality evidence for σ₀, equality evidence for σ₁ ]]
}
```

The soundness array has one row per original equation and one entry per answer.
The two syntactic levels in this record matter: `atom/cover` form the
COMPLETENESS tree, while `hyp/refl/comm/unit` form EQUALITY evidence inside
that tree or the independent soundness part.

Python assembles the corresponding proof applications, schematically:

```text
Worklist.exact_system
  E₀  [σ₀,σ₁]
  (Complete.atom
    premise = Derives.hyp(...)
    children = [
      Complete.cover(0, β, component derivations),
      Complete.cover(1, β, component derivations)])
  (SystemSoundness.cons
    (Soundness.cons equality_for_σ₀
      (Soundness.cons equality_for_σ₁ Soundness.nil))
    SystemSoundness.nil)
```

The actual ATOM constructor represents children by a function over ALL eligible
indices, not a literal list. The compiler also supplies typed data and scope
checks omitted here. It does not perform a new search in Lean.

See the same proposition in
[atom_automated_certificate](examples/certification-demo.lean#L227) and
[atom_manual_certificate](examples/certification-demo.lean#L265).
For the explicit surface-rule tree, see [atom_surface_certificate](examples/certification-demo.lean). Its completeness proof is ATOM with two COVER children; soundness is the separate equality row. Data names n, p and q hide variable-position bookkeeping, and right_unit is the fixed COMM → UNIT derivation already used by Maude.

The older manual proof uses the semantic ATOM rule `NativeRules.singletonCases`,
then witnesses N:=n in both branches. Its branch order differs from the dump;
its rule/case structure agrees. It contains no parser or certification tactic.

For contrast, `2P =B a(n)` has the supplied answer set `Σ=[]`. If ATOM lists
the repeated occurrences separately, both choices require `P=a(n)` AND `P=0`:

```text
ATOM(terms=[P,P], coefficients=[1,1])
  child 1: BIND(P:=a(n)) → NONEMPTY from a(n)=0
  child 2: BIND(P:=0)    → NONEMPTY from 0=a(n), using SYMM
```

This is a valid expanded replay shape; equivalent branch ordering is harmless.
A coefficient-combined ATOM instead uses `[P]` with coefficient `[2]` and has
no eligible children. Both presentations prove absence of solutions, rather
than interpreting a solver's failure as a proof. Soundness of the empty answer
list is vacuous. See [repeatedSystem](examples/certification-demo.lean#L366).

### 5.2 Early coverage: 2P =B 2Q

```text
E₀ = {P+P =B Q+Q}
Σ = { σ(Z): P:=Z, Q:=Z }
```

Choose β(Z)=P directly at the root. Reflexivity proves the P component.
For Q, use the current equation:

```text
E₀ ⊢B 2P = 2Q            HYP
E₀ ⊢B P = Q              MULTIPLICITY-CANCEL
E₀ ⊢B Q = P              SYMM
```

The completeness tree is a SINGLE COVER leaf:

```text
proof: COVER(index=0, beta=[Z:=P],
             derived=[REFL(P), SYMM(MULTIPLICITY(2,HYP(0)))])
sound: REFL(Z+Z)
```

MULTIPLICITY is an equality derivation INSIDE COVER, not a state transition
whose child must be searched. The original equation remains in the state.
Together these proofs certify `2P =B 2Q iff exists Z, P =B Z and Q =B Z`.

See [power_certificate](examples/certification-demo.lean#L316).
This is genuinely targeted: the supplied diagonal answer suggests the factor;
its checked conditional equalities avoid the sharing grid. It does not imply
that an independent solver could not discover the same cancellation.

### 5.3 A fresh witness is necessary: 2P =B 3Q

```text
Original inputs: (n,P,Q), with n a passthrough
E₀ = {2P =B 3Q}
Σ = { σ(N,W): n:=N, P:=3W, Q:=2W }
```

The singleton-free balance has a 2-by-3 occurrence grid. Its full rectangle is
the only nonempty balanced support: θ(P)=3Z and θ(Q)=2Z. FINITE-SHARING gives:

```text
⟨(n,P,Q) ; 2P =B 3Q⟩
  → ⟨(n,3Z,2Z) ; 2(3Z) =B 3(2Z)⟩
  COVER closes this child using σ with β(N)=n, β(W)=Z.
```

The final line is COVER proof closure, not another exact state transformation.
The selected equation is shown retained, as in replay.
All three image components agree with σβ; unconditional ACU evidence suffices.

```text
proof:
  SHARING(rows=[P,P], cols=[Q,Q,Q], generators=[(3,2)])
    child: COVER(index=0, beta=[N:=n,W:=Z])
sound:
  ACU equality evidence: 2(3W) =B 3(2W)
```

This illustrates why supplied answers do not make all witnesses available:
there is no union-only expression in the CURRENT P,Q that universally extracts
the required W. SHARING first introduces Z existentially. Z may be empty;
no feasibility or nonemptiness constraint has been added.

See [nonlinearAnswers and automated replay](examples/certification-demo.lean#L390)
and the explicit rule proof
[nonlinear_replay_certificate](certification.lean#L266).
The finite enumeration/checking theorem is shared infrastructure, not a
problem-specific completeness assumption.

### 5.4 Four sharing pieces: P+Q =B R+S

The proposed answer is:

```text
σ(p,q,r,t):
  P:=p+q, Q:=r+t, R:=p+r, S:=q+t.
```

There is no need to run the entire 2-by-2 support enumeration if MUTATE makes
these pieces available:

```text
⟨(P,Q,R,S) ; P+Q =B R+S⟩
  → ⟨(P,Q,R,S) ;
       P =B p+q, Q =B r+t, R =B p+r, S =B q+t,
       P+Q =B R+S⟩
  COVER closes this child with β equal to the four fresh pieces.
```

The first step extends the scope; it does not bind away P,Q,R,S.
The final line is COVER closure using the four defining hypotheses:

```text
proof:
  MUTATE(p,q,r,t)
    child: COVER(index=0, beta=[p,q,r,t],
                 derived=[the four defining hypotheses])
sound:
  ASSOC/COMM evidence: (p+q)+(r+t) =B (p+r)+(q+t)
```

This is the implemented optional witness-introduction shortcut. If its local
COVER attempt fails, the fallback resumes from the original state; no unproved
case is removed. See
[matrix_certificate](examples/certification-demo.lean#L345) and
[matrix_manual_certificate](examples/certification-demo.lean#L356).
The latter is one application of `mutate_native`, whose IFF packages the
general exact transformation.

### 5.5 Naming a singleton, then handling its payload

For `[wait(n)] =B [wait(m)]`, supply `σ(N)=(N,N)` for original inputs (n,m).
One valid derivation explicitly exercises PURIFY and BIND:

```text
⟨(n,m) ; [wait(n)] =B [wait(m)]⟩
  ── PURIFY ──→
⟨(n,m) ; A =B [wait(n)], A =B [wait(m)]⟩
  ── BIND A:=[wait(m)] ──→
⟨(n,m) ; [wait(m)] =B [wait(n)], [wait(m)] =B [wait(m)]⟩
  COVER closes this state with σ and β(N):=n,
  using REFL(n) and the derived payload equality m =B n.
```

Payload equality is derived twice through free heads: singleton, then wait.
No payload variable needs to be bound away: conditional COVER can use m =B n
directly to prove that the original vector (n,m) agrees with (n,n).
Soundness is reflexivity of `[wait(N)] =B [wait(N)]`.

The corresponding proof-tree SHAPE is:

```text
PURIFY
  BIND(A := [wait(m)])
    COVER(N := n,
      derived = [REFL(n), DECOMPOSE(wait, DECOMPOSE(singleton, HYP))])
```

DECOMPOSE is inside COVER's equality evidence, rather than a separate
completeness node. See the explicit
[purification_binding_certificate](certification.lean#L538).
This is a valid handwritten derivation, not a claim that the producer must choose
purification for this simple query; it can decompose the original equation directly.

For purification COMBINED with nonlinear sharing, see
[the commented balance demonstration](examples/certification-balance.lean#L45):
`2P =B [wait(n)]+Q` produces PURIFY → SHARING → ATOM, with BIND/NONEMPTY
for contradictions and COVER for the surviving cases. Its comments spell out
the five generated support parameters and their images.

### 5.6 Two necessary families with explicit singletons

Consider one bag equation with free payload variables `n,m`:

```text
[wait(n)] + X =B [wait(m)] + Y.
```

Two solution families suffice:

```text
σ₁:
  n := N, m := N, X := R, Y := R

σ₂:
  n := N, m := M, X := [wait(M)] + R, Y := [wait(N)] + R.
```

The first family pairs the two displayed singletons. Singleton injectivity
generates the payload equation `n =B m`, and cancellation equates the remainders.
The second sends each displayed singleton into the opposite remainder; their
remaining common bag is `R`.

The exhaustive grid/atom rules generate these possibilities, potentially with
redundant presentations. Whole-vector factors close them against the proposed
answers. Both families include `R=0`. Even when the payloads agree, two singleton
occurrences remain two occurrences; the branches may overlap without becoming
unsound. The first family cannot be omitted: it includes `n=m` and `X=Y=0`, which
the second does not.

Nonlinear balance is handled independently. For `2X =B 3Y`, FINITE-SHARING yields
`X:=3Z, Y:=2Z`, including `Z=0`. For `X+Y =B X`, cancellation yields arbitrary
`X` and `Y=0`; there is no occurs failure. Multiple equations simply reuse these
steps with their shared substitution environment.

A readable summary of the two surviving cases is:

```text
Case 1: pair the displayed singletons
  derive n =B m, and X =B Y
  COVER σ₁ with N:=n, R:=X

Case 2: send each displayed singleton into the opposite remainder
  introduce shared remainder R
  X =B [wait(m)]+R, Y =B [wait(n)]+R
  COVER σ₂ with N:=n, M:=m and that SAME R
```

These are a semantic summary of surviving branches, NOT a claim that the dump
contains a primitive “pair” rule. The fallback obtains the cases through PURIFY,
FINITE-SHARING, and exhaustive ATOM, then payload decomposition/binding and COVER.
Soundness checks σ₁ by congruence and σ₂ by reordering the two displayed
singletons and common remainder. Other generated branches can be contradictory
or redundant, but each needs its own checked closure.

For a checked two-equation example where the shared payload is forced only in
one branch, see [overlap_certificate](examples/certification-demo.lean):
`P+Q=[wait(n)]` and `Q+R=[wait(m)]`. Whole-state substitutions and
whole-vector COVER preserve the correlation between the two equations.

## 6. Where native answers can accelerate search

The targeted search receives the same already known `Σ` as Appendix A.4. At each
branch, it can select one of those answers and attempt a checked factor/closure
before exhaustive expansion. It searches for a certificate of the supplied
answers, not for native answers that have yet to be computed.

The exhaustive reference derivation is the fallback, not necessarily the path
performed first. Add this optional general closure rule:

```text
EARLY-COVER
  choose σᵢ and a candidate β over the current parameters;
  derive, from the current equations E,
    α(x) =B σᵢ(x)β for every original x;
  conclude Σ ⊢ ⟨α ; E⟩ covered without expanding this branch further.
```

Its conditional equality derivation must use checked general rules. Merely
observing agreement on one solution instance does not close the branch.

One useful derived rule is:

```text
MULTIPLICITY-CANCEL
  kU =B kV, k > 0
  ───────────────
  U =B V.
```

It follows by cancellation of equal positive natural multiplicities in the free
bag normal form, not from ACU in an arbitrary monoid. For `X+X =B Y+Y`, a native
answer `X:=Z, Y:=Z` suggests `β(Z):=X`. MULTIPLICITY-CANCEL derives `Y =B X`,
so the whole branch closes without constructing its sharing grid.

Search may try answer-guided bindings, atom choices, and coverage closures first.
The successful checks are certificate steps. On failure, the finite fallback
remains available; no candidate-guided pruning may remove an unproved case.
Perform only finite shortcut attempts before falling back, or use a fair schedule
that cannot starve it. Unrestricted rewriting/search is not the prescribed control.

### 6.1 Implemented conditional coverage

The producer tries unconditional whole-vector coverage first. If it fails, it
computes a proof-producing conditional view of the current image vector using
the CURRENT equations, without deleting variables or altering the worklist:

1. Find variable definitions, also through checked decomposition of matching free
   constructors. Orient variable aliases toward a smaller slot. A replacement
   containing the replaced variable is not followed.
2. Cancel identical normalized bag occurrences, preserving multiplicities.
   When the remaining sides are equal positive powers, use MULTIPLICITY-CANCEL.
   Uniform zero-sided balances similarly justify the variable's empty image.
3. Lift replacements through any constructor arity by CONGR, compose the equation
   evidence by TRANS/SYMM, and normalize with explicit ACU equality evidence.
4. Match each SUPPLIED answer vector against that conditional view using the
   existing finite whole-vector matcher. A successful factor emits COVER with
   proofs of `E ⊢ α(x) =B σᵢ(x)β` for EVERY original input x.

The variable path is visited at most once per slot; recursive constructor
processing descends through finite terms. Equation lookup and cancellation
traverse finite lists, and factor attempts traverse the finite supplied family.
Thus this is a finite shortcut, not an unbounded rewriting solver. Cyclic
definitions stop expansion. If the view did not change modulo B, the already
failed unconditional matching attempt is not repeated. Any other failure returns
to the complete schedule in Appendix A.2–A.3. No unproved branch is pruned, and
candidate soundness for the original equations is still checked separately.

For `P+Q=[a]`, ATOM's two branches now close directly by conditional COVER from
`P=[a],Q=0` or `P=0,Q=[a]`, instead of two BIND transitions each. For `kP=kQ`,
the diagonal supplied answer permits COVER using multiplicity cancellation,
without constructing the `k`-by-`k` grid. For `P+[a]=Q+[a]`, CANCEL permits
coverage by the supplied diagonal answer without purification/sharing. These
avoid actual calculus expansion, not just parsing or pretty-printing overhead.
None is a uniform speedup claim: an unsuccessful shortcut still costs work.

The shortcut is deliberately incomplete. For `2P=3Q`, the supplied family
`P=3Z,Q=2Z` is exact, but Z cannot generally be expressed as a union-only term
of the CURRENT P and Q. Knowing that family does not supply a constructor-term
factor in this scope. The fallback introduces sharing parameters and then
covers the resulting vector. This is a witness-scope limitation of EARLY-COVER,
not a missing case in the complete fallback or a new user proof obligation.

There is no general claim that proposed answers avoid reconstructing a complete
reference derivation in the worst case. They provide genuine checked early
closure opportunities; a uniform speedup is a separate question.

#### Answer-guided witness introduction

After ordinary and conditional COVER fail, the producer may try ONE existing
MUTATE step on the selected union balance `A₁+A₂ =B B₁+B₂`:

```text
introduce p,q,r,t with
  A₁ =B p+q, A₂ =B r+t, B₁ =B p+r, B₂ =B q+t;
retain the lifted original equations and EVERY original input image;
try conditional COVER of this entire extended state by the SUPPLIED answers.
```

MUTATE already has a proved semantic completeness rule; its four-piece common
refinement introduces genuine witnesses rather than guessing a constructor term
for a witness that may not exist in the current scope. The attempt is emitted as
MUTATE followed by COVER ONLY if the latter succeeds. Otherwise the temporary
state is discarded and the original exhaustive strategy resumes. Coverage in
the extended state still uses ONE shared substitution for the whole image
vector, so correlations are not lost. Candidate soundness remains independent.

A cheap scheduling hint limits this particular attempt to supplied families
containing an answer with at least four bag parameters. This is an OPTIONAL
shortcut policy, not a modeling restriction or a premise of the fallback's
completeness argument. Local coverage in the extended state does not recursively
attempt further mutation, so the additional attempt is finite.

For `P+Q=R+S`, the supplied answer
`P=p+q, Q=r+t, R=p+r, S=q+t` now permits MUTATE -> COVER using four pieces,
instead of the fallback's exhaustive 2-by-2 support table and fifteen generators.
This does not remove the need for sharing in `2P=3Q`: that example still uses
the complete fallback. No claim is made that all witness-producing shortcuts
are implemented, or that this policy always speeds up search.

The producer separates data-only normal-form computation from equality-proof
construction. Equality tests and matcher checks do not generate discarded proof
strings; accepted equality evidence still uses the same explicit ACU rules.
This shared implementation improvement applies to BOTH targeted and untargeted
control, not just the targeted benchmark.

### 6.2 Concrete efficiency benefit and its limits

The target is a coverage proof, not rediscovery of the proposed answers. Once
EARLY-COVER proves that EVERY solution of a current branch factors through an
answer, that branch needs no further unification splits. This can save both
search and the corresponding exhaustive certificate subtree. Merely prioritizing
the choices suggested by an answer would not suffice: unexplored alternatives
would still need coverage evidence.

The empirical comparison command is `python3 -B tests/test_certification_compiler.py --compare`.
Its targeted run receives `(E₀,B,Σ)`. Its untargeted diagnostic entry point receives
ONLY `(E₀,B)`: it disables answer matching and all answer-guided shortcuts, uses
the SAME free/ATOM/ZERO/PURIFY/FINITE-SHARING rules, and collects solved leaves as
its own reference answer family. Thus this is not merely an ablation of conditional
coverage with answers still available. It is NOT native Maude unification; native
answer acquisition is upstream and excluded from the comparison.

The untargeted family is deliberately not minimized: redundant support parameters
and unused passthrough slots are retained. Each mode's independently fixed Lean
goal checks exactness of its OWN family for the same equations. Neither family
is required to have identical syntax. Untargeted soundness-evidence rendering is
a separate measured phase after the unifier computation; this distinguishes
search failure from evidence/checker failure. Producer rewrite counts, proof-DAG
nodes, and Lean checking costs are separate quantities. Three producer runs give
median process timings; rewrite counts are deterministic. Resource failures are
reported with their phase and are never treated as contradictions or as evidence
of theoretical incompleteness. No uniform speedup or polynomial complexity claim
follows from these small fixtures. Measurements belong in the handoff/report,
not in the mathematical argument.

For example, consider `kX =B kY`, where `k > 0` counts repeated bag-variable
occurrences. Native unification proposes `X:=Z, Y:=Z`. Choose `β(Z):=X`;
MULTIPLICITY-CANCEL proves `Y =B X`, so one checked conditional factor closes the
whole problem. Soundness of the proposed answer is checked separately.

In contrast, the specified exhaustive sharing fallback has a `k × k` occurrence
grid. It includes at least `k!` balanced supports: every permutation matrix is
a support with degree one at every occurrence. Early closure avoids enumerating
these redundant supports altogether, rather than enumerating them and comparing
the final answers afterwards. Its work here is reading the finite terms and
checking the multiplicity-cancellation/factor evidence, not traversing that grid.

This comparison is with our enumerative fallback, NOT a lower bound on solving
the equation from scratch. An optimized independent solver can use the same
multiplicity rule. Proposed answers supply a concrete coverage hypothesis and
factor to attempt; they do not create a new algebraic shortcut or ensure that
such a shortcut exists for every problem. When checked early closure fails, the
complete fallback may still perform all the original search, plus the failed
shortcut attempts. The document therefore specifies a genuine branch-pruning
mechanism. The targeted shortcuts and fallback are implemented in the prototype;
no uniform speedup, general complexity improvement, or formally verified search
implementation follows from their successful examples.

## 7. Dumps, replay, and cost

The implemented wire format mirrors the proof levels of §3.2:

```text
Maude:  { proof: completeness tree, sound: per-equation/per-answer equalities }
                   │                              │
Python:     Complete rule applications      Soundness rule applications
                   └────────── exact_system ──────┘
Lean:       check the resulting proof against the FIXED native exactness goal
```

Unary state rules have a `child`; ATOM has `children`; COVER and contradiction
nodes have no completeness children. A node's `premise` selects/derives an
equation from its current worklist. COVER's `derived` field contains equality
proofs for every original image, not further search branches.
[traceText](certifier/certification.maude#L1257) serializes these records;
[compile_components](certifier/certifier.py#L435) assembles the two proof
parts; [LeanReady.prepareProof](conPanna/Certification/Parser.lean#L138)
loads checked nodes against Lean's independently fixed goal.

The compiler can share repeated subproofs as named, dependency-ordered nodes.
That DAG is a compact presentation of the same inference tree, not another
proof calculus. The readable trees in §5 omit scope encodings and this sharing,
but retain the proof-rule nesting and all required branches.

A rule dump records:

- The exact signature/theory, original context, and input equation list.
- Context extensions, binding substitutions, and equation selections.
- A checked exhaustive support enumeration and the generated image vector.
- Every singleton-choice branch, or a proved closure of an unexpanded branch.
- Genuine contradiction leaves or checked whole-vector coverage factors.
- A soundness equality trace for every proposed answer and every input equation.

At a grid cell, binary include/exclude enumeration is exhaustive by construction.
Its completed leaves are classified by decidable degree comparisons; balanced
nonempty leaves supply parameters. This offers a finite rule-dump representation
of enumeration, without an unchecked claim that a supplied short list is complete.
Other compact representations need their own checked exhaustiveness argument.

The `p*q` grid can have `2^(p*q)` subsets. Atom choices and substitution expansion
can cause further growth. This document claims finiteness and completeness, not
polynomial search or polynomial certificate size in the original problem.
Explicit expanded enumeration traces can make omission checks local, but may
themselves be exponential. Merely removing a Diophantine solver does not remove
the combinatorial difficulty of ACU unification or matching.

No linear-equation solver or Hilbert-basis completeness assertion is trusted in
an individual certificate. Arithmetic appears in the general completeness proof;
problem search uses finite sharing, singleton cases, free rules, and matching.

Maude hosts these rules and their control, while its native solver proposes
answers upstream. Section 8.1 describes the implemented evidence boundary;
the Maude implementation itself is not verified in Lean. Raw rule traces must contain enough context and
branch information for replay; a successful rewrite path alone is not a complete
proof of exhaustiveness.

### 7.1 Inspectable coordinator: native answers, then targeted evidence

For a single Bash script that prints every stage with explanations and separators:

```sh
bash scripts/certify-demo.sh
```

It calls the existing coordinator stages and shows the constructor module,
actual Maude queries, native unifiers and certification statistics in stdout.
Intermediate JSON is saved, NOT printed; the JSON-bearing Maude result line
is replaced with a pointer to its saved transcript. All artifacts remain in
`certifier/.cache`. This is a HARDCODED walkthrough of the atomic
example: fixed paths, no arguments or helper functions (only a stage timer variable). Each command
can be copied and run manually. Run from the repository root with `maude` on PATH.
It does not run Lean. To capture the whole transcript, append
`| tee /tmp/certification-transcript.txt`.
Each stage prints its elapsed wall-clock time, including preparation, process
startup and displayed output, not just Maude's internal rewrite time.

The standalone frontend lives in `certifier/`: `certifier.py`, the fixed
`wrapper.maude` template, and `certification.maude` containing the unchanged
calculus modules. Its demo constructor module is `examples/bakery.maude` inside
that directory. Copying these files outside the Lean repository suffices to run
the engine with Python's standard library and Maude; Lean is not required for
evidence construction. It coordinates TWO sequential Maude operations:

```text
constructor-only .maude file + native unify command
  → infer signature/sort map and original variable slots
  → native unify → parse and freeze Σ
  → certify(E₀,B,Σ) in CERTIFICATION-PRODUCER
  → compile the evidence → return Σ and a Lean-ready proof bundle
```

This does not change the calculus's input contract. The `--certify` entry point
still receives ALREADY supplied answers and never runs native unification.
Only the new coordinator obtains answers upstream, before calling the same
fixed-answer certifier. It never starts Lean, precompiles the backend, or declares
the result verified. The current Lean session checks the returned proof against
its original problem and the returned answer DATA. It must not accept an
externally supplied replacement for the original problem.

**Input and boundary.** No hand-written JSON request/name map is needed by the
standalone frontend. It accepts ONE closed functional module with explicit
`sort`/`sorts` declarations and unambiguous prefix `op` declarations marked
`[ctor]`. Exactly one binary homogeneous operator is marked
`[ctor assoc comm id: unit]`. The unit is a declared nullary constructor; the bag
carrier also has exactly one unary singleton constructor, with stratified free
payloads as required by the existing calculus contract. Imports, subsorts,
equations, rules, overloaded/mixfix names and additional attributes are rejected.
Sort and constructor codes follow declaration order. Original variable slots
follow alphabetically sorted variable names, preserving sharing across every
equation; their sorts are inferred from typed occurrences in the command.

The existing Lean API still accepts already-exported typed data and fixed
answers through `--certify`. The optional coordinator regression now calls the
SAME constructor-file/command frontend and independently fixes `atomSystem` in
Lean. The [legacy exported fixture](examples/certification-request.json) is kept
only for the regression checking agreement of inferred metadata with prior
typed export. It is NOT input to either demo. Automatic native-model export from
Lean and integration into narrowing remain outside this packaging change.

Currently the adapter accepts simple, unambiguous constructor-prefix syntax and
a nonempty finite equation system under the existing single stratified ACU
contract. It supports multiple answers, shared/repeated parameters, missing
identity bindings, empty answer families, and flattened associative output.
Fresh parameter slots are local to each answer and only occurring slots remain.
Unknown syntax, bad sorts/arities, ambiguous name maps, and cyclic substitutions
are rejected. Mixfix/overloaded native names, arbitrary native equations or
subsorts are not supported by this parser. Saved Maude scripts currently require
paths without whitespace/quotes. These are adapter boundaries, not additional
semantic proof rules. Names and answer origin remain untrusted by Lean.

**All-in-one test, from the repository root:**

```sh
python3 -B certifier/certifier.py \
  --ctor certifier/examples/bakery.maude \
  --unify 'unify in BAKERY-DEMO-NATIVE : union(P:Bag,Q:Bag) =? singleton(wait(N:Ticket)) .'
```

Progress goes to stderr; stdout is one JSON result containing the fixed target,
the returned answer data as a Lean expression, and the existing `rule-bundle-v1`
certificate. Every generated file is written to `certifier/.cache` by default,
including the supplied model copied as `ctor.maude`, inferred request, scripts,
transcripts, frozen answers and proof bundle. The wrapper template is instantiated
there with the native module name; it loads the fixed filenames `ctor.maude` and
`certification.maude`. The latter is a copy of the fixed engine, not a newly
generated calculus. The cache is one sequential workspace; old proof artifacts
are invalidated before another request starts. Use separate `--out` cache
directories for independent workflows. Existing JSON coordinator input remains
available through `--coordinate --request ...` for typed Lean callers.

The wrapper's native import renames all client sorts to `NativeSort0`,
`NativeSort1`, etc. This isolates client names such as `Terms` and their operation
signatures from the calculus's own data types/helpers. Native unification still
runs in the ORIGINAL module; sort codes and encoded answers are unchanged.
This uses ordinary [Maude module renaming](https://maude.cs.illinois.edu/maude1/manual/maude-manual-html/maude-manual_57.html),
not a new proof rule or modeling annotation.

**Manual step 1: native unification.** Preparing the script runs no process:

```sh
python3 -B certifier/certifier.py --prepare-native \
  --ctor certifier/examples/bakery.maude \
  --unify 'unify in BAKERY-DEMO-NATIVE : union(P:Bag,Q:Bag) =? singleton(wait(N:Ticket)) .'

cat certifier/.cache/01-native-query.maude
cat certifier/.cache/ctor.maude

(
  cd certifier/.cache
  timeout 30s maude -no-banner -no-advise -no-wrap 01-native.maude \
    > 01-native.stdout 2>&1
)

cat certifier/.cache/01-native.stdout
```

The query is literally:

```maude
unify in BAKERY-DEMO-NATIVE : union(P:Bag,Q:Bag) =? singleton(wait(N:Ticket)) .
```

Expect TWO unifiers: one with P empty and Q the singleton, and one with the
reverse assignment. N is represented by a fresh Ticket parameter. Native
parameter names and answer ordering may differ; they are not proof assumptions.

**Inspect the bridge between the two calls.** This command parses the saved
native transcript and generates the wrapper/target query; it runs NO Maude:

```sh
python3 -B certifier/certifier.py \
  --parse-native certifier/.cache/01-native.stdout

cat certifier/.cache/wrapper.maude
cat certifier/.cache/02-target-query.maude
```

`02-target.json` is the frozen `(E₀,B,Σ)` request. The wrapper LOADS `ctor.maude`
and the maintained `certification.maude`; its `CERTIFICATION-QUERY` module imports
both the native constructor module and `CERTIFICATION-PRODUCER`. Importing does
not translate native terms: the Python adapter uses the inferred map to encode
the answers as `v(i)`/`a(head,args)`. The second query is an ordinary
`rew in CERTIFICATION-QUERY : certify(...) .`, with all supplied answers explicit.
It contains NO native `unify` call.

**Manual step 2: targeted certification, then proof assembly.**

```sh
(
  cd certifier/.cache
  timeout 30s maude -no-banner -no-advise -no-wrap 02-target.maude \
    > 02-target.stdout 2>&1
)

python3 -B certifier/certifier.py \
  --compile-trace certifier/.cache/02-target.stdout
```

The Maude result is a JSON-encoded `result State: result(...)`: a completeness
tree and per-answer soundness evidence. Python decodes and compiles this into
ordinary applications of the existing Lean rules. Inspect `03-trace.json` for
the rule tree and `04-proof.json` for its typed, dependency-ordered proof nodes.
No search runs during `--compile-trace`.

| Artifact under `certifier/.cache` (or `--out`) | Meaning |
| --- | --- |
| `00-request.json`, `ctor.maude` | Initial exported input and native model. |
| `01-native-query.maude`, `01-native.maude`, `01-native.stdout` | First query, directly executable script, native output. |
| `02-target.json` | Parsed answers, now fixed as the certification target. |
| `wrapper.maude`, `02-target-query.maude`, `02-target.maude`, `02-target.stdout` | Imports, second query/script and targeted output. |
| `certification.maude` | Unchanged engine copied into the cache for the wrapper's fixed import. |
| `03-trace.json` | Decoded Maude rule evidence. |
| `04-proof.json`, `result.json` | Lean-ready proof bundle and full coordinator reply. |
| `status.json` | Last completed stage; `kernel_checked` remains false because Python never checks proofs. |

**Optional kernel-checking test:**

```sh
CONPANNA_COORDINATOR_DEMO=1 python3 -B tests/test_certification_compiler.py --demo
```

This also runs the existing regression examples. The additional optional block
in [certification-demo.lean](examples/certification-demo.lean) makes ONE Python
coordinator call for the atomic problem, creates the actual returned answer DATA,
and kernel-checks the certificate against its independently defined `atomSystem`.
Look for `ONE coordinator call: native unifiers + targeted proof, kernel-checked
against atomSystem`. Its inspectable directory is `certifier/.cache/lean-atom`.
The original examples still have their existing calls; “one call” means one
coordinated request, not one process for the entire regression file.

The `--build`, `--demo` and `--compare` harnesses live in the existing
`tests/test_certification_compiler.py`, outside the standalone engine. Only that
test harness invokes Lean. The packaged coordinator has no model-specific demo
fixtures and never invokes Lean, including in fixed-answer and staged modes.
Safety limits remain unchanged; do not raise them to force a regression pass.

### 7.2 Lean surface-calculus boundary and evidence correspondence

The module separation below is implemented. It changes neither the mathematical
calculus nor its search strategy: the existing rules are exposed in Calculus.lean,
with semantic justification in Semantics.lean and loading machinery in Parser.lean.
Start with Calculus.lean if you already understand the Maude calculus.

#### The language a certificate uses

A certificate has three kinds of proof, followed by one acceptance theorem:

| Judgment | Meaning | Current Lean declaration |
| --- | --- | --- |
| `t =B u` | Equality justified by structural axioms alone. | `Substitution.Equality`, with `Equalities` for argument vectors. |
| `E ⊢ t =B u` | Equality justified by the current equations and structural/free-constructor properties. | `Worklist.Derives`, with `DerivesArgs` for argument vectors. |
| `⟨α ; E⟩ ⇒ Σ` | Every valuation solving E makes the original-input images α an instance of a proposed answer. | `Worklist.Complete`; `ReplayState.Certified` packages the same judgment with a state. |
| `Σ solves E₀` | Each supplied answer satisfies every original equation. | `Soundness` per equation; `Worklist.SystemSoundness` for the whole system. |
| Exactness | Original solutions are exactly the instances of Σ. | `Worklist.exact_system` combines the last two proofs. |

The first two rows are premise-evidence levels, not alternative unification
algorithms. Completeness is a state-proof tree; soundness is a collection of
unconditional equality proofs after substituting the proposed answers.
The acceptance theorem is public, but its semantic proof is not part of each
emitted certificate. All declaration names in this section are relative to
`DirectCertification.Substitution` unless otherwise stated.

#### Exhaustive correspondence for the current producer

The source of the completed state-node tags is
[traceText](certifier/certification.maude#L1221). Python's
[nested_complete](certifier/certifier.py) translates exactly these ten tags:

| Maude rule/helper → completed node | Python tag | Lean surface rule | Required evidence / children |
| --- | --- | --- | --- |
| `[cover-and-emit]` → `coverNode` | `cover` | `Complete.cover` | One answer index, one parameter substitution β, and a derivation for the ENTIRE input-image vector; no child. |
| `[bind]`, `finish` → `bindNode` | `bind` | `Complete.bind` | Typed variable removal, replacement, derived binding equation, and one substituted child. |
| `[clash-and-emit]` → `clashNode` | `clash` | `Complete.clash` | Two distinct FREE heads and a derived equality between their applications; no child. |
| `[occurs-and-emit]` → `occursNode` | `occurs` | `Complete.occurs` | A proper path through FREE constructors and a derived binding equation; no child. |
| `[atom-split]`, `[atom-collect]` → `atomNode` | `atom` | `Complete.atom` | Derived sum/singleton equality and EVERY coefficient-one supplier child, not just the successful child. |
| `[zero-split]`, `[zero-collect]` → `zeroNode` | `zero` | `Complete.zero` | Derived sum/unit equality and one child containing all required zero equations. |
| `[nonempty-close]` → `nonemptyNode` | `nonempty` | `Complete.nonempty` | Derived equality of a FREE bag atom with the unit; no child. |
| `[finite-sharing]`, `[sharing-collect]` → `sharingNode` | `sharing` | `Complete.sharingTable` | Slots, coefficients, occurrence labels, a CHECKED exhaustive support table, a derived balance equation, and one substituted child. |
| `[purify]`, `[purify-collect]` → `purifyNode` | `purify` | `Complete.purify` | Named term, fresh-variable template and equation position, and one scope-extended child retaining the definition. |
| `tryWitness`, `[witness-cover-and-emit]` → `mutateNode` | `mutate` | `Complete.mutate` | Derived binary balance and one child with four fresh sharing parameters. The helper finishes it with COVER. |

Lean's `Complete.sharingTable` is a derived presentation of `Complete.sharing`:
it checks that the explicit table equals the exhaustive enumeration. Python also
supports the basic `.sharing` form when a record omits that table. The maintained
producer supplies the explicit table. These are not two different algorithms.

Likewise, `Complete.split` exists for handwritten binary singleton proofs, but
the maintained producer emits `atom`, NOT a `split` tag. Do not invent a dump
rule for every available Lean constructor. The generalized `Soundness.sharing`
constructor is also available for handwritten/legacy proof assembly; production
`answersProof` instead supplies equality traces for the fixed native answers.

The primitive and derived premise evidence is mapped independently:

| Maude evidence tag | Lean rule |
| --- | --- |
| `refl`, `symm`, `trans`, `congr` | `Equality.refl`, `.symm`, `.trans`, `.congr` |
| `unit`, `comm`, `assoc` | `Equality.unit`, `.comm`, `.assoc` |
| `swap_right` | `Equality.swap_right`, a fixed derived ACU rule |
| `scoped` | Context annotation only; Python compiles the child in that scope. No new proof rule. |
| `hyp` | `Derives.hyp`, selecting a current equation by a checked index |
| `axiom` | `Derives.axiom`, embedding structural equality evidence |
| `symm`, `trans`, `congr` in a premise derivation | `Derives.symm`, `.trans`, `.congr` |
| `decompose` | `Derives.decompose`, requiring a free head and a typed argument position |
| `cancel` | `Derives.cancel`, canceling a common bag prefix |
| `multiplicity` | `Derives.multiplicity`, canceling a CHECKED positive repetition count |

Vector evidence uses `.nil`/`.cons` of the corresponding typed list judgment.
Production `answersProof` produces one row per original equation and one
structural equality per proposed answer. Python builds `Soundness.nil/cons` for
each row, then `SystemSoundness.nil/cons` for the system. Its root application is
`Worklist.exact_system registration ... completeness soundness`.
Protocol rules (`start`, `emit`, pending-state collection) have no additional
semantic proof constructor. EARLY-COVER is COVER with stronger premise evidence,
not another certificate rule. Maude search/matching guards are not trusted proof
premises: the certificate must carry the corresponding checked evidence.

#### Typed data and side conditions underneath the surface

Python emits named surface-rule applications. Its shared proof bundle additionally
contains typed data and checked side-condition witnesses:

- Typed constructor terms, equation lists and before/after state snapshots.
  These are legitimate shared DATA, not additional semantic reasoning.
- `ReplayState.accept`, which transports a checked child across an explicit
  successor-state equality. Its proof currently uses `rfl` to check substitution
  or scope extension. This check must be preserved, not trusted or discarded.
- Named [SideCondition witnesses](conPanna/Certification/Calculus.lean#L352),
  shared by generated and handwritten certificates. These package elementary
  finite proofs, not extra semantic reasoning or new unification rules:

| Witness | Input → checked result |
| --- | --- |
| `headsDiffer profile f g checked` | A proof that constructor codes differ → the sorted heads differ (CLASH). |
| `finCons first rest` | First-slot proof and ALL remaining-slot proofs → an exhaustive finite proof vector (ATOM children, row counts, disjointness). |
| `noSupplier checked` | A proof that coefficient k ≠ 1 → the coefficient-one supplier branch is impossible. It cannot skip an eligible branch. |
| `tableCons row tail` | Componentwise equality for the first row and equality of the entire remaining table → equality of support tables (FINITE-SHARING). |

For example, the ATOM children for `P + Q = [wait n]` are now written as
`finCons (fun _ => COVER₀) (finCons (fun _ => COVER₁) Fin.elim0)`.
Both children remain mandatory. The FINITE-SHARING check remains equality with
`supportGenerators rowLabels colLabels`, not merely validity of some supplied
supports. `tableCons` hides the fixed `congr`/`funext` expansion; it does not hide
an assumption or run search. Numeric checks still use kernel-checked proofs.

The surface language therefore needs rules PLUS typed data and checked
side-condition witnesses. It cannot consist only of rule labels and child IDs.
Witness construction may be internal; a displayed manual certificate should
read as an application of the same public rule with its witnesses and children.
No problem-specific theorem, tactic, extra user registration proof, or external
producer-correctness assumption should be introduced for this separation.

#### Implemented four-boundary architecture

These are the current modules. Syntax.lean contains their shared typed DATA and
substitution operations; Core/Sharing/Enumeration contain general internal support.

| Boundary | Owns | Does NOT own |
| --- | --- | --- |
| `Calculus.lean` | State/judgment declarations, the public rules above, derived rule interfaces and their checked syntactic side conditions. | Native semantic induction, model export, IO, JSON, or certificate search. |
| `Semantics.lean` | Interpretation into the registered structural relation; general rule-validity proofs; the public exactness acceptance theorem. | External parsing or search. |
| `Parser.lean` | Bundle decoding, dependency/name management, term parsing/elaboration, closedness checks and checked intermediate declarations. | Unification, coverage search, semantic proof discovery, or subprocess calls. |
| `Client.lean` | Registered-profile generation, request export, calling Python, and passing the reply to Parser with an independently fixed expected goal. | New calculus rules or a second proof interpreter. |

Existing substitution and finite-sharing support is reused underneath. Syntax.lean
contains the extracted prerequisite syntax/computation definitions. Rule declarations
and semantic validity proofs are physically separated, not hidden behind an
import-only facade. Existing declaration names and the Python proof-bundle format
are preserved; neither a second calculus nor a new Python parser is introduced.

Dependency direction: shared support → Calculus → Semantics; Parser need not
import semantic proofs; Client brings Semantics and Parser together. The final
acceptance theorem is implemented in Semantics but is a public certificate entry
point, so emitted proofs never need its internal semantic argument.

Parser imports only Lean and has no subprocess calls. Client owns the profile
command, JSON export and external calls. The former mixed Replay and Frontend
files have been replaced, not retained as alternative implementations. The
optional coordinator demo calls Client's coordinate and Parser's
prepareCoordinatorAnswers/prepareBundle: it no longer parses answers inline or
compresses an already decoded bundle merely to parse it again.

The current bundle contains Lean type/value STRINGS and is parsed as ordinary
Lean term syntax. This established interface is unchanged by the module split;
there is no second structured-certificate format or duplicate parser in Python.
The supported compiler emits fixed rule templates, but the
current Lean term parser does not itself enforce a rule-name whitelist. Typed
checking against the fixed goal is the logical boundary, not a claim that
arbitrary Lean syntax is a restricted or resource-safe language.

**Refactoring acceptance examples:** the existing handwritten two-answer
[atom_manual_certificate](examples/certification-demo.lean#L265) and its generated
counterpart use the same unchanged rules. The new atom_surface_certificate gives
an explicit ATOM → COVER / COVER evidence proof for the ORIGINAL atomSystem and
atomAnswers, with no parser, tactic or problem-specific proof lemma. Every
generated proof node must be a listed public
rule, typed DATA, or checked side-condition evidence. Only the one root
acceptance theorem connects the evidence to the semantic exactness goal. No new
search, new axioms/sorries, regenerated answers, or claim of linear kernel runtime
is justified by changing module boundaries.

## 8. Implementation map and remaining boundary

### 8.1 What already exists

The reusable prototype lives in `conPanna/Certification`; `certification.lean`
contains its handwritten examples and metatheorem audits. It has semantic rules,
native constructor decomposition, bag flattening/permutation transport, sorted
substitutions, finite equality evidence, whole-vector factors, and soundness/
coverage aggregation. Its numeric finite-sharing namespace also proves minimal
decomposition, opposite-pair bounds, integer transport existence, and the local
rectangle cost decrease.

The numeric finite-sharing argument is now proved in Lean:
`boolean_transport_exists` rounds arbitrary finite transport margins to a
zero/one matrix using the opposite-pair bound. `minimal_nonempty_boolean_support`
connects original variable labels/coefficient counts to a nonempty support with
uniform repeated-occurrence degrees. `boolean_supports_exact` proves that every
balanced active multiplicity vector is a finite sum of these support-degree
vectors, and conversely. Inactive coordinates are excluded only from the active
balance; original canceled variables still require independent passthrough
images. These are general metatheorems, not sampled coefficient cases or extra
registration obligations.

`supportGenerators` now computes the canonical finite family: enumerate every
Boolean grid, keep only nonempty grids with uniform repeated-label degrees, and
extract their degree vectors. `mem_booleanMatrices` proves that no Boolean grid
is omitted; `supportDegrees_eq` recovers the unique active vector from its margins.
`supportGenerators_exact` proves that the computed list generates exactly every
balanced active multiplicity vector. The proof no longer assumes that a supplied
generator list covers all minimal solutions. Duplicate degree vectors are harmless
and may remain. This is an exponential exhaustive fallback, not a polynomial-time
claim.

The native semantic lift is now proved as well. `generated_weights` allocates
numeric witnesses by generator POSITION, rather than counting identical vectors
multiple times. `lists_generated` collects each quotient atom class into finite
parameter bags. The dictionary contains all classes present in the input bags,
not only atoms named in the query, so arbitrary payload values are preserved.
`bags_generated` proves the exact coefficient equation in existing indexed tree
equality; `finiteSharing_native` specializes it mechanically through the existing
Registration quotation/rebuilding theorems. Every original bag-variable image is
included. Inactive inputs get independent passthrough images, including when the
grid is empty; no original variable is accidentally forced to the unit.

These are semantic rule-validity metatheorems. Choosing representatives and
multiplicity decompositions is part of their classical proof, NOT a runtime
Diophantine solver or a new user registration obligation.

Typed open-substitution generation and finite sharing replay are now implemented.
`Sharing.Slots` selects bag variables once in a many-sorted context, skipping
unrelated fields without requiring a sort-equality oracle. `Sharing.answer`
computes fresh support parameters and their images, retaining inactive inputs
and skipped fields as independent passthroughs. `Sharing.complete` and
`Sharing.sound` prove this generated family exact against native registered
semantics. `Worklist.Complete.sharing` applies ONE generated substitution to the
whole original image vector and EVERY residual equation; `Soundness.sharing`
checks the same layout in the reverse direction. The canonical support family is
computed, not accepted under a supplied-list coverage assumption. Old input
slots remain behind the fresh parameters; unused active slots are harmless.
The external producer implements the finite fallback described in Appendix A.3.4.
These rule-validity proofs alone do not establish that its implementation always
succeeds; that search theorem is not formalized.

The coefficient-aware rules of §4.4 also have general semantic IFF proofs:
`AtomProcessing.sum_atom` characterizes ALL singleton suppliers for arbitrary
coefficient sums; `sum_zero` characterizes exactly the empty contributing terms.
Their proofs use natural-number mass, not a solver or a Diophantine oracle.
`Worklist.Complete.atom` requires a child for EVERY coefficient-one index;
`Complete.zero` requires one child with every positive-coefficient term empty.
Both retain the same residual equation context and original-variable images.
Coefficient-zero entries add only reflexive equations and remain unrestricted.
`Complete.nonempty` closes free-atom/unit contradictions. Explicit singletons
are allowed among the summands, so the selected supplier equation decomposes
to payload equations modulo B using the existing free-head rule. This implements
the semantic branching content of ATOM-ONE/CHOOSE/MANY and ZERO, not the complete
purification, variable-binding, or equation-scheduling algorithm.
The equality-data constructors `Equality.copies_zero`, `sum_zero`, and
`sum_choice` generate finite ACU soundness traces without search.

Sorted BIND and PURIFY replay are now implemented as well.
`Binding.Removal` identifies a position, computes a strictly shorter context,
and generates the full substitution. Its replacement lives in that shorter
context; no user semantic proof of an occurs check is required. `Binding.complete`
restricts each original valuation and reconstructs ALL original fields modulo B;
`Binding.sound` proves the binding solved for every reduced valuation.
`Complete.bind` propagates this same substitution through all residual equations
and images; `Soundness.binding` checks the generated binding-answer family.
The shared `substituteEquations_holds` metatheorem is reused by BIND and sharing.

`Purification.source` computes the old equation by filling a fresh-slot template
with its named term. `Purification.exact` proves naming exact, with a single
correlated valuation over the whole original context. `Complete.purify` can
replace an equation at any worklist position; its child retains the defining
equation, the template, and every lifted residual equation. This is a general
typed abstraction primitive, specialized to singleton terms by the intended
algorithm. It is NOT automatic occurrence extraction or a phase scheduler.

The library supplies automatic free-step selection; repeated external scheduling
is implemented in `CERTIFICATION-PRODUCER`, not in a second Lean-side solver.
`Binding.prepare` computes deletion of the selected sorted variable and traverses
the complete replacement, returning a checked term in the reduced scope.
`FreePhase.classify` selects DELETE, ORIENT, BIND, DECOMPOSE, CLASH, FREE-OCCURS,
or postponement generically, with no constructor-name or depth/arity bound.
The existing profile generator forwards decidable equality from generated finite
sort/head tags; users supply no extra instances or semantic registration proofs.

`FreeOccurs.findProper` discovers an occurrence beneath at least one free head,
traversing only free heads. `FreeOccurs.Proper.sound` validates that witness using
a structural-law-invariant depth: ACU union takes the maximum, the unit has depth
zero, and a free constructor adds one above its deepest field. Thus a proper
free occurrence cannot equal its containing term modulo B. Scope extraction
failure alone is NOT a contradiction: `P =B P+Q` is postponed, since Q may be zero.
`Worklist.closeFree` compiles discovered occurs/clash witnesses to checked finite
completeness data. Two automatic Bakery examples certify empty answer families
for `n =B succ(n)` and `wait(n) =B crit(n)`, without user-supplied witnesses or
problem-specific lemmas. Full-file LSP and axiom audits pass without admissions.
The external producer repeatedly executes free steps and schedules residual ACU
equations. Its contract-wide scheduling audit remains separate from these
kernel-checked rule-validity results.

### Precompiled checker and external certificate construction

The general infrastructure is compiled independently of individual certificates:

- `conPanna/Certification/Core.lean`: constructor and ACU semantic rules.
- `Sharing.lean`: finite-sharing arithmetic and semantic existence proofs.
- `Enumeration.lean`: exhaustive supports and singleton/zero metatheorems.
- `Syntax.lean`: typed certificate data and substitutions.
- `Calculus.lean` / `Semantics.lean`: surface rules and their semantic validity.
- `Parser.lean`: semantic-independent loading of closed rule evidence.
- `Client.lean`: generated profiles, request export and coordinator calls.

`certification.lean` contains examples using these modules, not a second copy
of the calculus. `examples/certification-demo.lean` is a lightweight consumer.

Native answer acquisition is UPSTREAM of certification and is already performed
by the existing unification functionality:

```text
Lean's existing unification call -> native Maude unify -> Σ available in Lean
```

The intended CERTIFICATION pipeline then takes the fixed `(E₀, B, Σ)`:

```text
current Lean session: certification request (E₀, B, Σ)
  -> Python wrapper: forward that request, without calling native unify
  -> Maude certification rules: answer-guided evidence for the supplied Σ
  -> Python constructor compiler: explicit Lean proof term
  -> current Lean session: elaboration and kernel checking against the fixed goal
```

Python does not run a second Lean executable in this intended interface. Lean
remains the host and checker. Internal coverage/factor search belongs to the
Maude certification procedure described above, not to Python or Lean.

The trace supplies sorted contexts, binding/removal positions, replacement terms,
whole image vectors, residual equations, premise references, and coverage factors.
Sharing steps additionally supply coefficients and finite-layout evidence,
including an explicit support table checked equal to the exhaustive enumeration.
Python constructs applications of existing general rules; it is not a trusted
solver and needs no compiler-correctness theorem. An incorrect translation must
fail Lean checking against the independently specified problem and answer set.

`LeanReady.prepareProof` parses the generated term against that goal and rejects
unresolved variables and admissions. Installing the resulting theorem invokes
the kernel. Production input must be restricted structured data and approved
rule templates: arbitrary Lean syntax or tactics are not a security sandbox.
The backend is precompiled once; individual proofs import it rather than
re-elaborating its metatheorems. No proof-producing dependent interpreter runs
inside kernel reduction.

The constructor compiler may share repeated typed terms, state data, equality
evidence, and completeness nodes in a finite dependency-ordered bundle.
Lean assigns fresh internal names,
checks each closed value, and then checks the aggregate against the independently
fixed goal. Term/state data are reducible definitions; equality and completeness
nodes are opaque definitions with checked bodies and their original indexed
rule types. Neither form introduces an axiom or a new proof
rule. Each declaration retains Lean's ordinary local checking budget; process
CPU, wall-time, and memory limits still bound the complete request.

`Worklist.ReplayState` groups the current sorted image vector and residual
equations at the same original inputs. Each nonterminal replay node supplies an
explicit successor snapshot. Lean computes the existing rule's required successor
and checks an ordinary equality with that snapshot; `ReplayState.accept` then
transports the independently checked child certificate. BIND/SHARING use one
substitution on both fields, PURIFY uses the existing scope-extension/definition
functions, and ATOM/ZERO prepend their exact requirements. The equality is
checked once as a named node; it is not a new semantic assumption or a
producer-correctness certificate. Python assembles these applications without
duplicating substitution, variable shifting, or requirement computation.
Errors identify the failed rule node, including its successor check.

The baseline consumer exports typed equations, scopes, and fixed proposed answers
with generated constructor metadata. It calls `LeanReady.produce`, then checks
the returned bundle in the same Lean session. The reusable object-level producer
lives in `CERTIFICATION-PRODUCER` inside `certification.maude`. It applies free,
singleton/zero, purification, sharing, and whole-vector factor rules. Appendix A.3.4
audits its unbounded schedule; no formal implementation/search theorem or
uniform success within the resource caps is claimed. Demonstration cases alone
are not that audit.

The optional standalone test harness separately PREPARES a binding-chain input
using native `unify` and launches Lean as its test consumer. Its native-answer
parser is intentionally demo-specific. Neither that preparation call nor its
external Lean invocation belongs to the baseline certification interface.
No new general native-answer parser is needed there: the host already has Σ.

Run from the repository root:

```sh
python3 tests/test_certification_compiler.py --build
python3 tests/test_certification_compiler.py --demo
CONPANNA_CERT_STRESS=1 python3 tests/test_certification_compiler.py --demo
python3 tests/test_certification_compiler.py --negatives
python3 -B -m unittest discover -s tests -v
```

The first command precompiles the backend; the second reuses cached modules,
calls Maude, saves its trace/proof under `.lake/build/certification`, and checks
the final theorem. A built project dependency environment is required.
Compilation and subprocesses are sequential and resource-limited.
`--negatives` reuses the demo's marked dependency prefix and negative-test block
in an ignored generated consumer. It checks the seven malformed bundle cases
plus omitted support rows, false head distinctions and skipped eligible suppliers.
Keep positive and negative consumers separate so each has its own unchanged
CPU/memory/wall budget; no additional maintained Lean file or checker is needed.

The smaller suite also presents `overlap_certificate` in native constructors:
`P+Q=[wait(n)]` and `Q+R=[wait(m)]` have two supplied families. Either Q is
empty and P/R are the independent singletons, or Q is the common singleton,
n and m share its ticket, and P/R are empty. This checks correlated equation
processing, exhaustive branches, payload decomposition, and whole-vector
coverage. It is not a problem-specific semantic proof hidden in a tactic.

The same file presents `atom_automated_certificate` and `atom_manual_certificate`
with IDENTICAL native propositions for `P+Q=[wait(n)]` and its two supplied
unifiers. The manual theorem is an ordinary explicit proof term: ATOM case
analysis, a COVER witness in each branch, then CONGR and UNIT for both answers'
soundness. `NativeRules.singletonCases` hides quoting and the singleton-mass
witness; `unaryCongruence` hides the unary argument tuple; `rightUnit` is the
derived COMM/UNIT composition. These are generic proved rules, not problem
certification lemmas or tactics. Constructor aliases are syntactic metadata only.

The producer now has ATOM with two DIRECT conditional COVER children, matching
the manual proof's two cases and witness N:=n without scoped BIND snapshots.
Comments record the different branch order and derived equality abbreviations.
This is a correspondence of proof rules and branches, not literal identity of
serialized proof trees. The manual theorem calls neither producer,
parser, generated-proof loader, nor certification tactic. The automated theorem
only unfolds representation data after the generated certificate is checked.

The optional negative suite corrupts freshly produced ATOM/conditional-COVER evidence after
checking an unmodified control. A wrong successor must fail at its transition
node; using the wrong branch hypothesis must fail inside COVER. Scope errors,
admissions, duplicate/unsupported node declarations, and a
wrong final proof must also be rejected. The Python tests separately check
signature/input validation and answer-guided matching using a different
constructor-code fixture. Passing these tests does not establish contract-wide
search success or turn the Lean term parser into a security sandbox.

The opt-in stress command checks `examples/certification-balance.lean` separately
from the smaller regression suite. This focused Lean demonstration certifies
`2P =B [wait(n)] + Q` against a supplied answer family, using purification,
exhaustive sharing, singleton branches, binding, contradiction, and coverage
rules. Its ordinary `certificate` theorem states both directions using native
Bakery constructors; the final simplification only unfolds the representation
after replay. It does not add another implementation, native-unification call,
problem-specific certification lemma, or user registration proof.

The proof groups equal required totals when finding a rectangle. This may merge
several label classes, which only enlarges the available class and weakens the
required bound. The label-count argument checks that the document's opposite-pair
bound implies this rounding condition. A least squared-cost transport is used
inside the classical existence proof, not as an executable runtime optimizer.

The refactored prototype additionally proves positive-multiplicity cancellation
for arbitrary `k > 0`, and admits checked cancellation/free decomposition inside
conditional equation derivations. `Worklist.Complete.cover` implements
EARLY-COVER directly: choose an answer and ONE factor, then prove the complete
input vector equal to its images under the current equations. Constructor clash
closes contradictory branches. `Worklist.exact_system` combines completeness and
per-answer soundness for finite equation systems without trusting Maude.

Explicit, tactic-free Bakery certificate terms demonstrate a two-answer atom
split, early closure for `kP =B kQ` for every positive `k`, and an empty answer set
justified by free-head clash. `nonlinear_sharing_certificate` additionally applies
the general native finite-sharing metatheorem to the coefficient equation
`2P =B 3Q`: its computed support has degrees `(3,2)`, denoting the family
`P =B 3Z, Q =B 2Z`, including an empty Z. It uses only the registered Bakery
constructors and finite syntactic layout checks, with no problem-specific
supporting proof lemma or custom proof tactic. `nonlinear_replay_certificate`
also certifies this equation through the actual typed replay constructors in the
mixed original scope `(ticket, P, Q)`: the generated answer images are
`(ticket, 3Z, 2Z)`. Its proof is a sharing step followed by identity-factor cover,
paired with the soundness sharing step, not a problem-specific semantic lemma.
Their evidence is currently handwritten, not automatically searched or dumped.
Further explicit Bakery replay certificates prove:
`2P+Q+R =B [wait(n)]` has two supplier families;
`[wait(n)]+2P =B [wait(m)]` yields `P=0` and `n =B m`;
`0P+2Q =B 0` leaves P unrestricted; and `2P =B [wait(n)]` has no solution.
The last result is justified by the absence of coefficient-one suppliers, NOT
an external solver's failure to find an answer. The top-level proofs consist
only of general replay/equality constructors, without problem-specific lemmas.
`binding_system_certificate` additionally checks the system `P =B Q,
Q =B [wait(n)]` by two scope-reducing bindings, yielding `(n,[wait(n)],[wait(n)])`.
`purification_binding_certificate` checks `[wait(n)] =B [wait(m)]` by naming the
left singleton, binding the name to the right singleton, decomposing the retained
payload equation, and covering `(N,N)`. Both are single explicit certificate
terms; the general rule-validity proofs, not problem lemmas, do the reasoning.
The profile generator checks the single-bag
stratified frontend contract using existing registered constructor metadata.
The old shape-specific recognizers and elaboration-time Maude search have been
removed from this file; separate Maude experiment files remain historical work.

Those are useful ingredients, NOT a formal proof of Theorem A.3.3 or A.4.3. The finite
whole-vector matcher is implemented and has the informal invariant/coverage
argument in §A.4.1. The retained-worklist scheduler now has the informal
progress/exhaustiveness audit in §A.3.4; their combined FORMAL search-success
theorem remains open. Successful examples alone establish neither argument.
The retained semantic mutation/split rules are useful derived steps, not a
complete fallback algorithm or a replacement for the finite-sharing theorem.

### 8.2 Design verdict and next gate

Under the stated one-bag stratified contract, the argument above gives a credible
finite complete calculus and a conditional reconstruction-success argument. Its
reasoning does not depend on variable-linearity restrictions or finitely many
hand-picked examples. It is not a proof of general mixed-theory combination, an
efficiency result, or a formal verification of the implementation. The prototype
implements the finite fallback, with the retained-storage audit in §A.3.4 and
independently kernel-checked evidence for successful runs.

The remaining gates are formalizing the search/control guarantee if desired,
strengthening the finite conditional EARLY-COVER attempts, and extending the
modeling contract with a separate combination argument. The prototype's safety
timeouts do not replace the finite complete schedule or justify contradiction.
Completing every Lean search meta-theorem before using the scientific prototype
is optional; silently replacing the strategy by bounded case-by-case search is
not. Narrowing integration is outside this document's present implementation.

## 9. References and attribution boundaries

- Alexandre Boudet and Evelyne Contejean, **“Syntactic” AC-Unification** (1994),
  particularly Theorem 2 and the occurrence-sharing treatment of nonlinear
  equations. This is the finite-support foundation; the stratified ACU strategy,
  singleton processing, and answer-guided reconstruction theorem in this note
  are an adaptation, not claims directly quoted from that paper.
  [Author-hosted paper](https://www.lri.fr/~contejea/publis/1994ccl/main.pdf).
- Alberto Martelli and Ugo Montanari, **An Efficient Unification Algorithm**
  (1982), Section 2, for free first-order equation transformations. Applying free
  rules while postponing the ACU carrier requires the stratification argument
  explicitly supplied in this note.
  [Paper](https://courses.grainger.illinois.edu/cs576/sp2017/readings/01-jan-19/martelli-montanari-unif.pdf).
- **Maude Manual**, Chapter 13 and matching commands, for the native unification
  and matching interfaces. Native completeness requires a supported theory and
  no answer truncation. A returned answer list is still checked rather than
  trusted, and the theorem here is stated by the list's mathematical properties.
  [Unification](https://maude.cs.illinois.edu/manual/maude-manualch13.html),
  [Matching commands](https://maude.cs.illinois.edu/manual/maude-manualap1.html).

The document does not establish novelty of the underlying unification algorithm.
Potential research contributions are the semantic registration/replay framework,
checked answer-guided certification, and its integration with the existing Lean
semantics; those require implementation and evaluation beyond this design note.

## 10. Related work, rule provenance, and differences

### 10.1 How to read the attribution

The calculus is a combination and adaptation of established ideas, not a claim
to have invented ACU unification. The following categories distinguish its
provenance:

- **Reused:** a standard mathematical rule or definition, restated with sorted
  contexts and our structural relation.
- **Inspired/adapted:** a mechanism based on a cited result, but changed for this
  contract, semantics, or certification purpose.
- **Derived:** a consequence of the free-bag semantics proved in this document;
  no particular paper is claimed as its exclusive source. This does not imply
  that the mathematical fact is new.
- **Project-specific proposal:** a proposed organization or certificate interface,
  whose novelty has not been established by a comprehensive literature review.

“Reused” concerns mathematical rule patterns, not a claim that source code or
verbatim text was copied. This is a provenance account of the proposed calculus,
not a licensing audit of every existing prototype implementation.

### 10.2 Rule-by-rule provenance

| Rule or mechanism in this document | Provenance | Adaptation and limits of the claim |
| --- | --- | --- |
| `DELETE`, `ORIENT`, `DECOMPOSE`, `CLASH`, `BIND` (§4.1) | Reused free first-order unification transformations; Martelli–Montanari, §2. | Sorted contexts, modulo equality, and postponed bag equations are our setting. Raw free-head clash is not used on ACU roots. These are not new rules. |
| `FREE-OCCURS` (§4.1) | Reused free occurs checking, with an equational guard. | Its use is restricted to free-constructor cycles. Stratification justifies the mandatory non-bag phase. Ordinary syntactic occurs checking is deliberately not used for bag cycles. |
| Equality evidence and `NORMALIZE` (§4.2, §A.4.2) | Reused equational logic and standard ACU normalization. | Reconstructed evidence targets the registered relation. Neither normalization nor proof-producing equality checking is claimed novel; certified AC reasoning already exists (§10.4). |
| `CANCEL` (§4.2) | Standard flattened AC cancellation; it already appears in Stickel's AC algorithm. | Our justification uses the constructor-generated free bag algebra, including empty remainders. It is not valid merely from assuming an arbitrary ACU interpretation. |
| `MULTIPLICITY-CANCEL` (§6) | Derived from equality of generator multiplicities in a free commutative monoid. | Used as a general checked shortcut; no claim that the algebraic fact is new or that it is the cited papers' specific trace rule. |
| `PURIFY` (§4.2) | Inspired by standard variable abstraction/purification in equational unification and theory combination. | We name singleton terms and retain their equations. We do not import the entire Baader–Schulz combination algorithm or its general combination theorem (§10.5). |
| `FINITE-SHARING` (§4.3) | Adapted from Boudet–Contejean's finite-support theorem and occurrence-sharing treatment of nonlinear AC equations. | We collect all balanced supports into one parameterized pure-balance family, allow empty parameters, and later enforce singleton requirements. This is not a literal copy of their mutation/merge/pruning algorithm. |
| `MUTATE` (§4.6) | Derived from common refinement of finite bags; reused from the existing prototype's semantic mutation rule. | Introduces four existential sharing pieces, optionally enabling supplied-answer coverage. It is not the complete fallback, and its name does not assert identity with Boudet–Contejean's mutation algorithm. |
| Minimal decomposition and opposite-pair bound (§A.1.2–§A.1.3) | Standard nonnegative-balance arguments; the pair bound is part of the reasoning behind Boudet–Contejean's Theorem 2. | Internal completeness arguments, not a separate runtime Diophantine solver or per-problem arithmetic certificate. No novelty claim. |
| Rectangle rounding (§A.1.4) | Our explicit proof organization for the required finite-support property. | It makes repeated occurrence degrees explicit. We claim neither a new finite-support theorem nor priority for this matrix argument. |
| `ATOM-MANY`, `ATOM-ONE`, `ATOM-CHOOSE`, `ZERO` (§4.4) | Derived from free-bag multiplicities and singleton injectivity. | The exact branching formulation is tailored to the three-constructor fragment. These are elementary ACU consequences, not rules taken from an order-sorted membership calculus. |
| Shared substitution propagation and composition (§4.1, §A.3) | Reused substitution composition and complete-unifier-set reasoning. | The finite free/bag/payload schedule is justified by our stratification, not a claim about arbitrary interacting theories. |
| `COVER` and whole-vector factorization (§4.5, §A.4.1) | Reused instantiation preorder and the standard definition of a complete set of unifiers. | We make the factor a checked certificate object on every original input. Comparing complete vectors preserves correlations; the mathematical factorization principle is not new. |
| `EARLY-COVER` (§6) | Project-specific proposed control, built from standard factorization and checked consequence derivations. | It can avoid expanding a branch when coverage is already proved. This is not a claimed new general subsumption theorem, nor a guarantee that native answers always accelerate reconstruction. |
| Proposed-answer soundness plus coverage aggregation (§A.4.4) | Reused logical inclusion in both directions; architecturally inspired by skeptical external-solver certification, notably SMTCoq. | The target is exactness of a symbolic unifier set over registered constructor semantics, rather than a SAT/SMT result. The native solver remains outside the trust boundary. |
| Exhaustive sharing/atom dumps (§7) | Standard explicit case-tree certification, organized for the proposed calculus. | Both branches or checked alternatives must be accounted for. A positive native computation trace alone is not completeness evidence. The prototype wire format is implemented; its producer is not formally verified. |

### 10.3 Classical AC unification and the nonlinear sharing foundation

Stickel's **A Complete Unification Algorithm for Associative-Commutative
Functions** (1975) already flattens AC terms and removes common arguments before
solving. It also gives the substitution/generalization viewpoint. These are
classical foundations, not contributions of our framework.
[Original proceedings paper](https://www.ijcai.org/Proceedings/75/Papers/011.pdf).

Boudet and Contejean's **“Syntactic” AC-Unification** (1994) is the closest source
for our nonlinear sharing mechanism. Their Theorem 2 represents minimal balance
solutions by subsets of occurrence-pair generators. Their subsequent algorithm
uses linearization, reconciliation of repeated occurrences, and a restriction on
substitutions of introduced variables to preserve completeness while controlling
search. [Author-hosted paper](https://www.lri.fr/~contejea/publis/1994ccl/main.pdf).

Our changes are explicit:

1. The initial model contract is narrower: one stratified bag component, not a
   general mixed AC signature.
2. It is ACU: parameters may be empty. Thus the pure balance can use all balanced
   supports simultaneously; there is no obligation to choose only nonempty
   contributions to every input variable.
3. Explicit singleton requirements are discharged separately by exhaustive
   cardinality cases and free payload unification.
4. A complete finite reference family is used to certify an independently
   proposed answer set, which may have a different representation.

The occurrence grid is still an arithmetic balance construction in mathematical
substance. Saying “no explicit Diophantine solver” is a statement about the search
and certificate interface, not a claim to have removed the arithmetic foundation
or its worst-case combinatorial cost. We do not claim that enumerating all
supports improves on optimized classical AC/ACU unification.

### 10.4 Existing certified AC algorithms and proof-assistant tactics

Ayala-Rincón, Fernández, Ferreira Silva, and Nantes Sobrinho's **A Certified
Algorithm for AC-Unification** (FSCD 2022) formalizes an adjusted Stickel algorithm
in PVS and proves termination, soundness, and completeness. Its extended account,
**Certified First-Order AC-Unification and Applications**, supplies further details
and revises a completeness-proof hypothesis. These are important precedents: we
must not claim that formal certification of AC unification is new.
[FSCD paper](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.FSCD.2022.8),
[extended account](https://www3.risc.jku.at/publications/download/risc_7111/main.pdf).

The difference is the intended artifact. Those works certify an AC-unification
algorithm itself. Our target is a reusable Lean replay interface for certifying
the exact answer set proposed by a separate native engine, against registered
user constructor semantics. Our initial contract is deliberately restricted and
includes a unit law; their AC correctness results do not automatically establish
this ACU replay theorem. Conversely, our informal argument is not a stronger
result than their completed formal verification. Their proof rules and PVS
development have not been ported into our prototype.

Contejean's **A Certified AC Matching Algorithm** (RTA 2004) proves inference
rules for free/C/AC matching sound, complete, and decreasing in Coq, with a
corresponding CiME algorithm. This directly supports the feasibility of a checked
matching component. It does not, by itself, prove completeness of an ACU unifier
set or the composition argument of §A.3. Its rules are related work, not the rules
already implemented by our generic matching fallback.
[Author's abstract](https://www.lri.fr/~contejea/publis/2004rta/abstract.html).

Braibant and Pous's **Tactics for Reasoning modulo AC in Coq** (CPP 2011) combines
a certified equality decision procedure with untrusted matching. It supports
units, multiple operations, and user-defined equivalence relations. This is a
particularly close precedent for the acceptance principle used in `COVER`:
a matcher proposes a substitution, and checked equality validates it.
[Paper](https://arxiv.org/abs/1106.4448).

The additional obligation in our work is exhaustive coverage of ALL unifiers.
Validating one rewriting match requires soundness of that match, not a proof that
the matcher returned every possibility. Hence our reference derivation and
coverage factors cannot be replaced by equality checks on proposed unifiers.
The earlier work also shows that registration and reasoning under an equivalence
relation are not new in themselves. Our free-constructor contract is needed for
exhaustiveness, cancellation, and contradiction rules; successful equality proofs
can work under much more general registered associative/commutative operations.

### 10.5 Purification and combination of equational theories

Baader and Schulz's **Unification in the Union of Disjoint Equational Theories:
Combining Decision Procedures** (1991 technical report; 1996 journal version)
studies general combination under component-theory requirements, including
unification with constant restrictions. This is a standard background for
purification and for the eventual multiple-theory extension.
[Author-affiliated report entry](https://iccl.inf.tu-dresden.de/web/LATPub24/en),
[journal DOI](https://doi.org/10.1006/jsco.1996.0009).

Our phase ordering is a special-purpose simplification justified by the sort
dependency contract. It is not a newly invented general combination method:
no payload equation can lead back to a bag equation, so we avoid the general
cross-component interaction problem. We do not claim to implement that paper's
variable-identification, constant-restriction, or full combination machinery.
Allowing bags inside payloads, or multiple interacting structural components,
requires revisiting this boundary rather than citing general combination as if
its hypotheses and proof had already been instantiated.

### 10.6 The supplied order-sorted paper is a different wrapper

The local `ACU-certification.pdf` is Hendrix and Meseguer's **Order-sorted
Equational Unification Revisited** (journal version, 2012). It wraps an unsorted
equational unification engine with rule-based sort-constraint processing. The
author-hosted version presents Intersection, Propagation, and Subsumption rules
for membership constraints and describes Maude/CiME integration.
[Author-hosted version](https://maude.cs.illinois.edu/papers/pdf/hendrix-meseguer-os-unify.pdf),
[journal DOI](https://doi.org/10.1016/j.entcs.2012.11.010).

It inspired the general external-engine-plus-rule-based-wrapper direction, but
**none of those three membership rules is the FINITE-SHARING or atom calculus
in this document**. Our contexts are many-sorted with fixed tags; there are no
subsort choices or membership refinements. More importantly, repairing the sort
information of an external unifier is different from proving that its proposed
unifier set exhausts all solutions. The paper is not an existing Lean-style
soundness/completeness checker for arbitrary external ACU answer sets.

### 10.7 SMTCoq: the trust architecture, not the ACU proof rules

Armand et al.'s **A Modular Integration of SAT/SMT Solvers to Coq through Proof
Witnesses** (CPP 2011) describes a modular certified checker for external solver
witnesses. It is the main architectural inspiration for separating expensive
search from trusted acceptance.
[Author-hosted paper](https://www-sop.inria.fr/marelle/Laurent.Thery/pub1.pdf).

Our proposed pipeline follows that skeptical principle:

```text
native engine proposes answers
→ untrusted certification search produces evidence
→ Lean validates evidence against the original semantic proposition.
```

The differences matter. Native Maude unifier output does not already include the
required completeness evidence. We must add a coverage derivation and factors,
not just parse the answers. The target is a finite symbolic representation of an
entire solution set, not solely a satisfiable/unsatisfiable formula. Also, our
prototype uses finite typed proof data and semantic replay; choosing a fully
reflective Boolean checker versus proof-term reconstruction remains a design
decision. SMTCoq's Coq checker is not code or an ACU calculus we have copied.

### 10.8 Proof-relevant unification: evidence without importing its metatheory

Cockx's **Dependent Pattern Matching and Proof-Relevant Unification** (2017),
Chapter 3, is related through evidence-producing rule transformations and their
composition. Its applications and correctness requirements concern dependent
pattern matching. E-unification appears as a possible extension, not a supplied
ACU completeness algorithm.
[Thesis](https://jesper.sikanda.be/files/thesis-final-digital.pdf).

We adopt neither its dependent-telescope infrastructure nor its stronger
requirements on proof-relevant equivalences. Our goal is propositional equality
of solution sets, with existential factor witnesses and possibly overlapping
answer families. We do not need invertible witnesses between all proof objects.
The connection is methodological; it is not the source of FINITE-SHARING and
does not discharge our search guarantee.

### 10.9 Disunification and complement methods: considered, not adopted

An alternative completeness formulation asks whether a solution outside every
proposed answer exists:

```text
exists ρ,
  E₀ρ holds
  and, for every i, there is NO β with ρ =B σᵢβ.
```

Refuting this formula would establish completeness. However, negating family
membership introduces quantification over substitution parameters. It is not
equivalent to adding a finite list of ordinary term disequalities with the
parameters left free.

Fernández's **AC Complement Problems: Satisfiability and Negation Elimination**
(1996) studies ground-instance complements modulo AC, with a rule-based
negation-elimination result for linear complement problems and additional
restricted nonlinear cases. This is directly related to that alternative
formulation, but its hypotheses do not yield our arbitrary-repetition ACU
coverage theorem automatically.
[Author's publication entry](https://nms.kcl.ac.uk/maribel.fernandez/allpapers.html).

Comon's **Unification et disunification : théorie et applications** (1988) is
broader background on equational-formula and disunification methods; it is not
claimed as the source of any named rule adopted here.
[Thesis record](https://theses.hal.science/tel-00331263v1).

No disequality, complement, or quantifier-elimination rule from those works is
currently part of this calculus. Positive complete reference families and
checked factorization establish coverage instead. We therefore do not claim
that a candidate answer set makes general disunification easy, nor that this
document implements a targeted complement/refutation algorithm.

### 10.10 Generalized rewrite theories: application motivation only

Meseguer's **Generalized Rewrite Theories and Coherence Completion** provides
the symbolic-execution background for the broader narrowing project. It studies
rewrite theories with background constraints and coherence/executability
conditions, rather than this unconstrained unifier-set replay problem.
[Paper](https://www.ideals.illinois.edu/items/105518/bitstreams/334027/data.pdf).

Its role here is motivation for a reliable structural unification component
inside later symbolic reasoning. No coherence-completion, constrained-narrowing,
or feasibility rule from that work is adopted in the present certificate
calculus. Neither its application results nor its executability assumptions
replace our coverage argument.

### 10.11 What can responsibly be claimed as different

The intended project-specific contribution is the combination of:

1. Registration of ordinary many-sorted user constructor datatypes, with checked
   structural semantics and no nontrivial per-model certification proof.
2. Untrusted native proposals plus rule-based, whole-family coverage certificates
   for a supported ACU modeling contract.
3. A rule-dump/replay interface whose accepted proposition states soundness and
   completeness of the proposed set against the existing native semantics.
4. Optional answer-guided early closure, backed by a finite complete fallback
   whose success argument does not depend on bounded experiments.

These are intended integration/certification contributions, not established
priority claims. General substitution composition, CSU factorization, skeptical
checking, proof-producing AC equality, and the finite-support foundation all have
precedents. A publication must compare the completed pipeline with the certified
AC algorithms and matching tactics above, not only with raw hand proofs.

In particular, we must not claim “the first certified AC/ACU unification system,”
“a new complete ACU algorithm,” or “native answers always make completeness
checking cheaper” on the basis of this note. The current defensible claim is an
explicit restricted calculus and an informal conditional reconstruction-success
argument; practical automatic replay, registration coverage, and performance
advantages remain implementation/evaluation obligations. Deferring the formal
Lean search-success proof does not change that distinction.

## Appendix A. Search guarantee and supporting arguments

This appendix addresses a DIFFERENT question from checking one certificate:
why should the prescribed strategy find a finite certificate for every legal
input with sound, symbolically complete supplied answers?

The arguments below describe the mathematical reference strategy, its
retained-worklist implementation audit, whole-vector matching, and the conditional
search-success claim. They are not premises silently trusted by the Lean checker.
The numeric finite-sharing component has Lean proofs; the full search/control
theorem remains informal. Individual accepted certificates are checked using
the rules of §4 and `exact_system`, whether or not search success has been formalized.

### A.1 Proof of finite-sharing exactness

This section proves the mathematical fact needed by the central rule. Counts
are used in the once-for-all argument, not as a problem-specific trusted
Diophantine solver.

#### Lemma A.1.1 — Bag normal form

For a fixed parameter context, a bag term modulo `B` is a finite multiset of:

1. singleton payload terms, identified by their payload equality; and
2. independent bag variables from that context.

Two bag terms are equal precisely when the multiplicities of these generators
agree. Free constructors at other sorts retain their heads and recursively
normalized arguments. This is the free constructor algebra with one free
commutative-monoid carrier. In native valuations there are no variable generators;
the bag generators are the actual singleton payload classes.

Proof outline: define normal forms recursively. At non-bag sorts retain a variable
or a free head with normalized arguments. At `Bag`, a variable contributes its
rigid generator, empty contributes nothing, singleton contributes its normalized
payload generator, and union adds the two multisets. Every generating equation
of `B` preserves this normal form, so congruence-generated equality implies equal
normal forms. Conversely, fix a total ordering of finite generator descriptions
and print each bag multiset as an ordered union. Structural induction, constructor
congruence, and ACU show that every term is equal to the printed representative
of its normal form. Equal normal forms therefore imply equality modulo `B`.
The argument is a characterization of the registered constructor quotient, not
an assumption that its native datatype has literal commutativity.

Including bag-variable generators is important: a symbolic proof must not
replace a fresh bag parameter by a fictitious singleton payload constructor.

#### Lemma A.1.2 — Minimal decomposition

Consider nonnegative integer vectors `(v₁,…,vᵣ,w₁,…,wₛ)` satisfying:

```text
sum aᵢvᵢ = sum bⱼwⱼ.
```

Every such vector is a finite sum of nonzero componentwise-minimal solution
vectors, or is zero with an empty decomposition.

Proof: choose a nonzero minimal subsolution below a nonzero vector, subtract it,
and repeat. Existence follows by choosing a solution of least total weight in
the finite box below that vector. Each subtraction strictly decreases the sum
of the coordinates. Subtraction preserves the balance equality. Therefore the
process ends. No effective search for this decomposition is needed at runtime.

#### Lemma A.1.3 — Opposite-pair bound

For a minimal nonzero solution `(v,w)` and every `i,j`:

```text
vᵢ ≤ bⱼ  OR  wⱼ ≤ aᵢ.
```

If both inequalities fail, the vector with `bⱼ` at coordinate `Xᵢ`, `aᵢ` at
coordinate `Yⱼ`, and zero elsewhere is a nonzero balanced proper subsolution.
This contradicts minimality.

#### Lemma A.1.4 — A minimal vector has a balanced support

Give each of the `aᵢ` rows labelled `Xᵢ` required row total `vᵢ`, and each of
the `bⱼ` columns labelled `Yⱼ` required column total `wⱼ`. The two total sums
agree, so a nonnegative integer matrix with these margins exists: successively
allocate each row across the remaining column capacities.

We turn this matrix into a zero/one matrix without changing any margin.
Suppose a cell in row `r` labelled `Xᵢ` and column `c` labelled `Yⱼ` has value
`A ≥ 2`. Lemma A.1.3 gives one of two cases.

**Case 1: `vᵢ ≤ bⱼ`.** Among the `bⱼ` columns with label `Yⱼ`, some column
`c'` has value zero in row `r`. Otherwise that part of the row would already
have total at least `bⱼ+1`, exceeding its required total `vᵢ`.

Columns `c` and `c'` have the same required total `wⱼ`. Since row `r` has more
in `c` than in `c'`, another row `r'` has values `C,D` there with `D>C`.
Perform this rectangle exchange:

```text
     c  c'                c    c'
r    A   0      →     r   A-1   1
r'   C   D            r'  C+1  D-1
```

All entries remain nonnegative, and each row and column sum is unchanged.
The change in the sum of squares of entries is:

```text
2(C-D-A+2) ≤ -2.
```

It strictly decreases because `A≥2` and `D≥C+1`.

**Case 2: `wⱼ ≤ aᵢ`.** Apply the same argument to the transposed matrix, using
the `aᵢ` rows with label `Xᵢ`.

The sum of squares is a natural number. Repeating exchanges therefore ends,
and it can end only when no cell exceeds one. The selected one-cells form a
balanced support with precisely the desired repeated-variable degrees. The
support is nonempty because the minimal vector is nonzero and the coefficients
are positive.

This argument establishes occurrence-level uniformity, not merely a capacity
bound on a coarser variable-pair allocation.

#### Proposition A.1.5 — Exact parameterization of a pure balance

Soundness: each selected cell contributes one occurrence to each side. Equal
degrees for equal row/column labels make repeated input-variable images agree.
Consequently every assignment to all `Z_S` satisfies the balance equation.

Completeness: fix any solution substitution. For each generator in its finite
bag normal forms, record its multiplicities in the active variable images.
This gives a balanced nonnegative vector. Decompose it by Lemma A.1.2 and represent
each minimal component by a support using Lemma A.1.4. Assign one copy of that
generator to the corresponding `Z_S` for each component. Multiple components
using the same support are combined in the same parameter bag. Summing the
degrees reconstructs the multiplicity of every generator in every input image.
Lemma A.1.1 therefore gives the required componentwise equality modulo `B`.
Passthrough parameters reconstruct every inactive variable independently.

This proves the exactness statement in FINITE-SHARING, including repeated
variables and symbolic parameter images. Zero-sided cases are immediate from
positivity: every active generator multiplicity must be zero.

### A.2 A finite strategy for a single bag equation

Define `SolveOneBag(e)` as the following rule-based procedure:

1. Flatten `e`; purify explicit singleton occurrences, retaining their equations.
2. Cancel common variable occurrences and construct the canonical support family.
3. Apply FINITE-SHARING once.
4. Process each retained singleton requirement using the exhaustive atom rules,
   propagating all bindings through every requirement and every image.
5. Solve generated free payload equations, rejecting genuine free contradictions.
6. Return all surviving composed substitutions, with unconstrained variables
   retained as parameters.

#### Proposition A.2.1 — Single-equation exactness

The returned list is finite. Every returned substitution is a symbolic unifier
of `e`, and every symbolic unifier of `e` factors through a returned member.

Proof: purification is exact; Proposition A.1.5 parameterizes the purified balance
exactly. The atom rules are an exhaustive characterization of each singleton
requirement. Free payload unification preserves all solutions and yields a most
general substitution or a proved contradiction. Compose these exact steps.

More explicitly, fix a symbolic unifier of the selected equation. Purification
extends it to the named singleton variables; finite sharing factors that extension
through the generated family. For the first singleton requirement, normal-form
multiplicities determine either its single displayed singleton or the unique
coefficient-one parameter contributing that singleton. The corresponding atom
branch is present and preserves the factor witness. Repeat for the remaining
requirements with the SAME witness, composing each binding. Finally factor its
payload assignment through the free solver's most general substitution. This
constructs one returned member through which the original unifier factors.
The reverse direction follows because every returned member satisfies the
balance and every retained requirement. No independent witness is chosen for
different occurrences of a shared parameter.

For termination: the grid has finitely many cell subsets; there are finitely
many retained requirements. Each atom-rule branch processes one requirement
and creates only payload equations. Processing later requirements does not
reintroduce earlier ones. Payload solving terminates and creates no bag equation
by stratification. Branch sizes may grow substantially, but every branching
factor and every branch length is finite.

This is not a repeated application of a mutation rule to fresh equations of the
same complexity. It has an explicit, finite internal schedule.

### A.3 Whole-problem reference search

#### A.3.1 The free phase

Apply the free rules to equations whose result sort is not `Bag`, postponing bag
equations. Propagate bindings through postponed equations and original images.
At completion the state is either dead or `⟨α ; P⟩`, where every equation in
`P` is a bag equation.

This phase terminates. One suitable measure, ignoring orientation as a separate
loop step, is lexicographic:

```text
(number of live non-bag variables,
 total term-node count of the remaining equation worklist).
```

A non-bag binding removes a live variable and introduces none. Decomposition
removes the two constructor heads; deletion removes an equation. Substitution
may increase the second component, but decreases the first. Use fixed variable
orientation and deterministic equation selection. The free occurs side condition
is legitimate by the contract argument in Section 4.1. Bag equations may be
created by configuration decomposition, but do not produce free configuration
equations in return.

#### A.3.2 The bag phase

After the free phase, run:

```text
SolveBags(α, []):
  return [α]

SolveBags(α, e :: P):
  result := []
  for every θ in SolveOneBag(e):
    append SolveBags(αθ, Pθ) to result
  return result
```

`SolveOneBag` acts on the complete current context, including passthrough
variables; its payload bindings are propagated through `α` and `P` as well.
The equations of `Pθ` still have bag result sort. Its length is exactly one less
than the pending list before the step. Payload solving cannot add bag equations.

#### Theorem A.3.3 — Finite reference CSU

For every finite `E₀` under the contract, this procedure terminates with a finite
reference list `Θ` such that:

```text
Sound(Θ) and Complete(Θ).
```

Proof: the free phase terminates and preserves the state's denotation. Induct on
the number of pending bag equations. The empty list represents all assignments
to the remaining parameters. For `e :: P`, Proposition A.2.1 yields finitely many
exact solution families `θ`. Substitution congruence gives:

```text
δ unifies (e :: P)
  iff
there exist θ in SolveOneBag(e) and η such that
  δ =B θη and η unifies Pθ.
```

The SAME `η` occurs in both conjuncts: this is the preservation of correlations.
Apply the induction hypothesis to each `Pθ`, then compose substitutions. This
proves coverage of every original-input unifier. Conversely, each composed
member solves `e` and the remaining equations, so it solves the whole problem.
Finiteness follows from finite branching and decreasing pending-list length.

An empty reference list means every branch ended with a proved contradiction.
It is not the consequence of an arbitrary search cutoff.

#### A.3.4 Retained-worklist implementation of the finite strategy

`CERTIFICATION-PRODUCER` retains equations for replay instead of physically
deleting every solved equation. Consequently, the length of its stored list is
NOT a termination measure. Its correspondence with Appendix A.2–A.3 is the following
phase argument. This is an informal implementation audit, not a Lean proof of
the Maude interpreter or a bounded-resource success guarantee.

**An original frontier** is a maximal bag-sort equation exposed by decomposing
matching free constructors in an input equation. For example,
`pair(P+[a], R+[b]) =B pair(Q+[a], S+[b])` has two frontiers. Defining equations
introduced by PURIFY, and requirements introduced by ATOM/ZERO, are instead
local obligations of the selected frontier.

1. **Free bindings cannot continue indefinitely.** `choose` traverses every
   stored equation and matching free-constructor field. A BIND removes one live
   variable; no rule introduces a non-bag variable. Therefore there are at most
   the original number of non-bag bindings along any branch. Free traversal
   itself is structural, not a rewriting loop that repeatedly reintroduces the
   same DECOMPOSE or ORIENT state. A clash or proper free occurrence closes the
   branch. Payloads cannot introduce bag equations by stratification.

2. **Between non-bag bindings, the original frontier structure is fixed.** Any
   unresolved configuration-variable binding would already be found by `choose`.
   Bag substitutions cannot introduce free configuration structure above a bag
   or inside its payload. There are finitely many frontier positions in the
   remaining finite free skeletons. Purification replaces one equation by one
   template; it does not duplicate that skeleton. It may name a singleton in a
   sibling field as well: this creates a retained defining equation, not another
   copy of that sibling frontier.

3. **Preparation is finite.** `prepareMore` replaces a chosen explicit singleton
   in the enclosing template by a fresh variable and retains its definition.
   The number of explicit singleton occurrences in that template strictly
   decreases. Replacing all identical occurrences at once is safe because one
   defining equation fixes their shared value. Preparation performs no bindings
   or sharing before it finishes. The selected balance's union/variable outer
   shape is preserved, so `prepareClean` reaches FINITE-SHARING rather than an
   unsupported preparation state.

4. **Sharing finishes that balance permanently.** `prepareSharing` cancels common
   variable occurrences and enumerates every balanced nonempty grid support.
   Its substitution makes the selected pure equation equal modulo B for ALL
   assignments of its parameters. Later substitutions preserve this equality.
   Thus `scanBag`, which skips normalized-equal equations and fields, never
   shares that frontier again. Fresh old-variable passthrough slots do not
   reactivate a solved equation. A zero-sided grid sends every active variable
   to empty and preserves all inactive variables.

5. **Local requirements do not start another sharing phase.** After sharing,
   each retained definition has the form `sum =B [payload]`. Substitution and
   flattening make each summand a variable or a singleton. ATOM creates EVERY
   occurrence choice; its children require each variable to equal that singleton
   or empty, and compare any explicit singletons through their free payloads.
   ZERO similarly requires every summand to be empty. These equations are solved
   by BIND, free payload processing, or NONEMPTY/CLASH; they do not require new
   PURIFY or FINITE-SHARING. Repeated occurrences keep the same variable: assigning
   it both singleton and empty closes that branch rather than dropping the case.
   Requirements are prepended; `scanBag` processes the first unresolved one.
   Solved requirements stay normalized-equal under all later substitutions.

6. **Every unresolved frontier has an applicable step.** At a bag sort the only
   heads are a variable, empty, singleton, and union. Variable binding or identity
   is handled by `choose`; a self-containing union is a balance, not free OCCURS.
   Singleton/singleton equations expose free payload equations. Singleton/empty
   closes by NONEMPTY. Union/singleton uses ATOM, union/empty uses ZERO, and the
   remaining union balances use preparation/sharing. A union already equal to
   its other side is skipped. This exhausts the contract's constructor shapes.

These observations give a finite hierarchical schedule. Partition a branch at
non-bag BIND steps; there are finitely many such partitions. Within a partition,
there are finitely many original frontiers. Each selected frontier has finite
preparation, at most one sharing step, and finite local requirement processing.
Bag BIND decreases the current finite scope between expansions; ATOM/ZERO adds
no variables. Every branching factor is finite. Hence the complete tree is
finite, even though the retained list and fresh bag scopes can grow.

Each completed frontier is preserved permanently under substitution. At a live
terminal state all equations normalize to identities, and the composed original
image vector is a symbolic unifier of the original problem. Completeness of the
SUPPLIED answer family gives a factor for that vector; the exhaustive matcher
of Appendix A.4.1 finds it. Checked early COVER may stop sooner. If the family is
empty, no such live terminal state can exist; all branches must close by proved
contradictions. Thus retained storage changes the evidence representation, not
the complete fallback of Theorem A.4.3.

The argument assumes unbounded execution of the finite enumerations, a correct
typed signature, and the stated stratification. Resource exhaustion is failure
to obtain a certificate, never a contradiction certificate. It does not assert
that arbitrary finite inputs fit the prototype's safety caps. The finite
conditional EARLY-COVER attempts described in Section 6 are now implemented;
stronger shortcut strategies remain optional. Neither is a prerequisite for
this fallback argument.

### A.4 Factor search and the answer-guided guarantee

#### Lemma A.4.1 — Complete finite whole-vector matching

For fixed finite substitutions `θ : X ⇒ Γ` and `σ : X ⇒ Λ`, one can decide
whether a factor `β : Λ ⇒ Γ` satisfies:

```text
θ(x) =B σ(x)β  for every x in X.
```

Rename contexts apart. Treat variables of `Γ` as fresh rigid symbols of their
sorts, including bag-sort symbols; only parameters of `Λ` are assignable.
Match the entire vector with one substitution environment.

At free constructors, match heads and recurse. At bag occurrences, flatten the
finite rigid subject. Every occurring bag-pattern variable must receive a subbag
of such a subject, including possibly empty. There are finitely many subbags,
including their possible multiplicities. Enumerate assignments, reconcile all
repeated occurrences and all vector fields, and check the resulting equalities.
Use canonical subbag representatives, not infinitely many raw parenthesizations.
Non-bag pattern variables match corresponding finite normalized subject subterms,
including configuration subterms; payload terms themselves use only free heads.
Every pattern parameter occurs somewhere in the vector after unused parameters
are removed.

This enumeration is finite and includes every possible factor: the nonnegative
bag multiplicities do not allow an assigned contribution outside the subject
to disappear. Free constructors similarly cannot hide extra terms. Equational
normalization checks each candidate, including unit collapse and repetitions.

Native Maude matching can propose the factor first. A bounded matcher that finds
none does not justify failure. The abstract guarantee uses the complete finite
matcher above as fallback; it is not conditional on an external process behaving
correctly or returning within a particular timeout.

##### Executable matching invariant

The producer implements this fallback with `allSorted`, `allArgs`, and `bagMatch`.
These match a **proposed-answer pattern** against the **rigid current image**;
they do not unify the two sides or instantiate current branch variables.
One partial parameter environment is threaded through the whole vector.
Its invariant is that an assigned parameter always denotes the same normalized
term in the current scope, including at repeated occurrences and other fields.

The complete cases are:

- A non-bag pattern variable receives the normalized subject term. A repeated
  occurrence must agree with its previous assignment.
- A free constructor pattern matches only the same subject head. `allArgs`
  recursively matches every corresponding field with the SAME environment;
  this includes bag fields inside free configuration constructors.
- An unassigned bag parameter receives each submultiset of the remaining finite
  subject, INCLUDING the empty one. A repeated assigned parameter removes exactly
  that multiset, with multiplicities, before matching the remaining pattern.
- A singleton pattern tries every subject singleton with the same head, recursively
  matches its free payload, and continues with that occurrence removed. A rigid
  subject bag variable is not a singleton and cannot be assigned by the matcher.
- Exhausting the pattern succeeds only when the subject is also exhausted.
  All vector components must succeed under one environment. A candidate factor
  is finally rechecked by normalization of every original input image.

For completeness, fix any factor extending the current partial environment.
At a free head its corresponding fields must match. At an unassigned bag
parameter its contribution is a submultiset of the remaining subject: with no
idempotence or absorption, no extra contribution can disappear. The partition
enumeration contains that submultiset. At a singleton some matching subject
occurrence must exist; the occurrence enumeration includes it. These choices
retain the fixed factor and reduce to smaller matching problems. Thus induction
over the remaining pattern occurrences and fields yields a successful branch.
Assignments can be replaced by their canonical normal forms without changing
the factor modulo B.

For finiteness, each bag has finitely many occurrence subsets. Recursive matching
consumes a pattern occurrence or descends to strict constructor fields; stored
assignments are only inspected/removed, not expanded into new pattern problems.
The finite lists of alternatives are combined across fields, not truncated.
There is no fixed arity, coefficient, or matcher-depth cutoff in this procedure.
This is an implementation-level informal argument, not a Lean search theorem.

Every answer parameter must occur in its image vector. The wrapper rejects
unused parameters instead of silently removing them from an already-fixed Σ:
doing the latter can change existential semantics when a parameter sort is empty.
Upstream normalization must remove them BEFORE fixing the certification goal.
Likewise, a process timeout is a failure to obtain evidence, never a proof that
there is no factor or unifier. Runtime safety caps do not provide a universal
bounded-time success guarantee.

#### Lemma A.4.2 — Finite equality evidence

If two open terms are equal modulo `B`, their finite normalized constructor
forms agree. Flattening, reordering, and removing units can be accompanied by
finite congruence/ACU equality traces. Thus factor matches and proposed-answer
soundness can be witnessed by finite checked equality data, not just Booleans.

#### Theorem A.4.3 — Search success for a correct proposed set

Assume the contract, finite `E₀`, and finite `Σ` with `Sound(Σ)` and
`Complete(Σ)`. The following reconstruction procedure terminates successfully:

`Σ` is supplied BEFORE this procedure starts. None of the steps below calls
native `unify` to obtain it. The internal reference family `Θ` is coverage
evidence for the supplied `Σ`, not a replacement answer set returned to Lean.

1. Construct checked equality traces establishing each proposed answer's soundness.
2. Obtain the finite reference derivation/list `Θ` by Appendix A.3.
3. For each `θ in Θ`, find a factor through some `σ in Σ` by Lemma A.4.1, and
   construct its equality evidence by Lemma A.4.2.
4. Combine reference completeness, the checked factors, and proposed soundness.

Proof: soundness traces exist by the premise and Lemma A.4.2. By Theorem A.3.3 each
`θ` is a symbolic unifier. The definition of `Complete(Σ)` therefore supplies a
factor through some answer. Complete matching finds one, and equality evidence
exists. There are finitely many reference members and proposed answers, and all
the searches just specified terminate. Aggregation yields the exact certificate.

If `Σ=[]`, its completeness implies that no reference leaf can be a symbolic
unifier; hence the exhaustive reference derivation has only dead branches.
Aggregation proves that the original problem has no solution.

The proof does not say “the reference and Maude answer lists look the same.”
Their lengths, orderings, parameter counts, and redundant families may differ.
Checked factorization of whole vectors is what relates them.

This baseline reconstructs a complete reference family before comparing answers.
Native proposals guide the factor search, but do not by themselves reduce the
reference unification work. The search-level acceleration is the optional
early-closure extension in Section 6, not this baseline alone.

#### Theorem A.4.4 — Accepted-certificate correctness (formerly Theorem 8.4)

Any well-checked reference derivation, factor list, and soundness traces establish
the native exactness proposition in Section 2, irrespective of the generator
that supplied them.

Proof: exact rule replacements establish reference completeness for native
valuations; factor equalities transport each reference witness into a proposed
answer witness; soundness traces give the reverse implication. Constructor
congruence preserves equations under componentwise modulo equality.

This theorem does NOT assume native Maude's completeness or soundness. Incorrect
proposals can cause reconstruction to fail but cannot make a valid checker prove
a false proposition. The search-success theorem is an external guarantee about
correct inputs, not an axiom used when checking an individual certificate.

### A.5 Is formalizing the search guarantee easy?

**No—not end to end. It is plausible and modular, but substantial proof work.**

The final theorem is relatively straightforward once the component results are
available: induction over the finite equation list, followed by symbolic CSU
factorization and matching completeness. The difficult formalization lies in:

1. Composing the proved typed finite-sharing replay with exhaustive equation
   processing; numeric rounding, computed-family exactness, native bag-image
   reconstruction, and the typed substitution replay rule are now proved.
2. Proving the free phase's termination and exactness with sorted substitution
   propagation through postponed bag equations. Typed BIND and whole-state
   propagation, scoped replacement extraction, automatic free-step selection,
   and proper free-occurrence rejection are proved/implemented. The repeated
   external driver and its informal audit exist; formalizing that exact control
   remains unfinished.
3. Composing the now-proved exhaustive singleton/zero replay rules with
   the now-proved PURIFY/BIND primitives, and proving single-bag solver exactness
   while tracking all parameter contexts and shared images.
4. Formalizing the implemented complete whole-vector matcher and its equality-trace
   construction, rather than assuming that a successful external query supplies it.
5. Connecting these constructive algorithms to certificate data and native replay.

The abstract declaration could eventually have the shape:

```text
reconstruct_complete:
  ModelingContract(signature, B) →
  Sound(E₀, Σ) → SymbolicallyComplete(E₀, Σ) →
  exists c, reconstruct(E₀, Σ) = success(c)
            and check(E₀, Σ, c) = accepted.
```

There should also be an unconditional checker theorem:

```text
check_sound:
  check(E₀, Σ, c) = accepted → NativeExactness(E₀, Σ).
```

Neither theorem needs a formal model of the native Maude implementation. Maude's
correctness is not part of the trusted checker; the success theorem quantifies
over any sound, symbolically complete finite proposed set.

An informal proof of the search guarantee is acceptable as an initial technical
report result, with Lean-checkable certificates providing a separate guarantee
for successful runs. Claiming the search guarantee itself is proved in Lean must
wait until the algorithm and all component proofs are actually completed.
