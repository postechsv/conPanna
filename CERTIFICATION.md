# A finite, answer-guided ACU certification calculus

Technical design note — 2026-10-05.

## 0. Purpose and status

The objective is a **search guarantee**, established mathematically before
implementing more Lean proof rules:

> For every finite constructor-unification problem under the contract below,
> and every finite sound, symbolically complete proposed answer set, a specified
> finite reconstruction procedure produces an exactness certificate.

The proposed answers may come from native Maude `unify`. Reconstruction checks
their soundness and proves their completeness; it does not trust their origin.
The guarantee is conditional on the actual properties of the proposed set, not
on the statement “Maude returned it.”

The certification input is the triple `(E₀, B, Σ)`: the original equation
system, its registered structural theory, and an ALREADY COMPUTED proposed
answer set. In the intended integration, Lean has obtained `Σ` from the earlier
native Maude unification call before certification begins. Certification does
not invoke native `unify` again, discover the requested answers, or replace `Σ`
by a different set. Its task is to construct evidence of exactness for that
fixed `Σ` against the fixed `E₀` and `B`.

“Certification search” means searching for that evidence, guided by the known
answers. It is hosted in Maude; Python constructs proof terms and Lean checks
them. Section 9 describes targeted early coverage, while Sections 6–8 supply
the complete fallback when those shortcuts cannot close a branch. The fallback
may repeat unification work, but this is not another native-answer acquisition
stage or a claim that the answers were unknown when certification started.

This document supplies definitions, informal inference rules, a complete fallback
strategy, and a mathematical sufficiency argument. It is a proposed technical
specification, **not an already formalized search theorem or an implemented
general solver**. Its key finite-sharing argument is proved below rather than
left as a conjectured property of mutation search.

Three results must remain distinct:

1. **Rule validity:** each checked transformation has its claimed semantic effect.
2. **Search success:** the specified strategy finds a finite certificate whenever
   the proposed set has the required properties.
3. **Implementation correctness:** the actual exporter, search program, parser,
   and replay mechanism implement that strategy and preserve the request.

Only the second is the central design question here. Establishing the second
requires mathematical arguments for the first, but does not require first
formalizing those arguments in Lean. A Lean checker will eventually need formal
rule-validity lemmas; it need not use a formal search-success theorem to accept
an individual certificate.

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

## 3. State invariant and proof judgement

A search state is:

```text
⟨α : X ⇒ Γ ; E over Γ⟩.
```

For any target context `Δ`, its represented original-input solutions are:

```text
Denote(α, E, Δ) =
  { ρ : X ⇒ Δ |
      exists δ : Γ ⇒ Δ,
      δ unifies E and ρ =B αδ on X }.
```

The initial state is `⟨identity ; E₀⟩`. Fresh-variable introduction, binding,
decomposition, and bag solving replace a state by states whose denotations have
exactly the same union. A dead branch has empty denotation.

The coverage judgement is:

```text
Σ ⊢ ⟨α ; E⟩ covered
```

meaning every solution represented by the state factors through some answer in
`Σ`. A coverage closure can prove inclusion without reproducing the state's
exact solution family. Checking `Sound(Σ)` separately then supplies the reverse
inclusion at the root.

## 4. Informal inference rules

In the displays, `E` means the entire remaining worklist. Every substitution is
applied both to `α` and to that entire worklist. Side conditions must be checked,
not accepted because an external dump asserts them.

### 4.1 Free constructor and substitution rules

```text
DELETE
  ⟨α ; t =B t, E⟩
  → ⟨α ; E⟩

ORIENT
  ⟨α ; t =B x, E⟩
  → ⟨α ; x =B t, E⟩
  where x is a variable; use a fixed orientation, not repeated flipping.

DECOMPOSE
  ⟨α ; f(s₁,…,sₖ) =B f(t₁,…,tₖ), E⟩
  → ⟨α ; s₁ =B t₁,…,sₖ =B tₖ, E⟩
  where f is a free constructor.

CLASH
  ⟨α ; f(…) =B g(…), E⟩ → dead
  where f and g are distinct free heads at the same non-Bag result sort.

BIND
  ⟨α ; x =B t, E⟩
  → ⟨α[x:=t] ; E[x:=t]⟩
  where x is not in t; remove x from the live parameter context.

FREE-OCCURS
  ⟨α ; x =B t, E⟩ → dead
  where x occurs strictly below only free constructors in t.
```

`BIND` is valid at any sort when its side condition holds. The mandatory free
phase uses it only at non-bag sorts; optional bag bindings may be shortcuts.
`DECOMPOSE` includes singleton injectivity, although the mandatory bag strategy
handles singleton equations in its dedicated phase.

The Lean replay now represents BIND by a typed context-removal table. Its
replacement term is scoped in the context with x removed, enforcing the
no-occurrence side condition structurally. This also gives a strict one-variable
decrease, without assuming sort distinctness or literal equality of bag trees.
The SAME generated substitution acts on every remaining equation and input image.

Do not apply `CLASH` to the raw roots `empty` and `union`, or an unrestricted
occurs failure to a bag variable. Unit collapse invalidates such inferences.

Under the contract, a strict occurrence of a non-bag variable in a same-sort
right-hand side cannot run through a bag. If its sort reaches bags, it cannot
also occur inside their payloads; otherwise the forbidden dependency cycle
would exist. If it is below bags, its right-hand side cannot contain bags at all.
Thus ordinary free occurs checking is legitimate in the free phase.

### 4.2 Bag normalization, cancellation, and purification

```text
NORMALIZE
  flatten unions and remove empty summands using ACU equality.

CANCEL
  ⟨α ; C + L =B C + R, E⟩
  → ⟨α ; L =B R, E⟩.

PURIFY
  replace an explicit singleton [t] in the selected bag equation by fresh A,
  and retain A =B [t] in a local singleton-requirement list D.
```

`CANCEL` follows from the free commutative-monoid representation of bags; it is
not justified in an arbitrary ACU algebra. Syntactically common occurrences can
be canceled without solving payload equations. Cancellation of additional
provably equal terms is an optional checked optimization.

`PURIFY` introduces an existentially quantified fresh bag variable. An original
solution extends by assigning `A := [t]`; a solution of the purified system
restricts to an original solution. Occurrence-by-occurrence fresh names are
allowed because all retained equations are subsequently enforced.

In the checked replay, the rewritten equation is a typed fresh-slot template.
Filling that slot with the named term computes the exact old equation. The
defining equation and lifted residual equations are all retained. The general
`Purification.exact` theorem proves both directions, modulo the existing native
relation. Automatic occurrence selection and once-only phase scheduling remain
separate from this checked primitive.

After cancellation, the pure selected equation is:

```text
a₁X₁ + … + aᵣXᵣ =B b₁Y₁ + … + bₛYₛ,                 (Balance)
```

where coefficients are positive, `kZ` denotes k repeated unions, and no active
variable occurs on both sides. Other live variables remain passthroughs.

### 4.3 FINITE-SHARING

Let `p = sum aᵢ` and `q = sum bⱼ`. Construct `p` occurrence rows and `q`
occurrence columns, labelled by their original variables.

A **support** is a nonempty subset of the `p*q` cells. It is balanced if:

- All rows labelled `Xᵢ` have the same degree `dᵢ(S)`.
- All columns labelled `Yⱼ` have the same degree `eⱼ(S)`.

The degree is the number of selected cells in that row or column. Let `H` be
the set of **all** balanced supports. Give each `S in H` one fresh bag parameter
`Z_S`. Define `θ` by:

```text
θ(Xᵢ) = sum over S in H of dᵢ(S) copies of Z_S
θ(Yⱼ) = sum over S in H of eⱼ(S) copies of Z_S.
```

Other live variables receive distinct same-sort passthrough parameters, retaining
all existing sharing. The rule is:

```text
FINITE-SHARING
  ⟨α ; Balance, D, E⟩
  → ⟨αθ ; Dθ, Eθ⟩.
```

It produces one parameterized family for the pure balance, not a branch for
each support. Different supports coexist as independent parameters; any of them
may be empty. No nonemptiness constraint is introduced.

The essential exactness lemma is:

```text
For every target context Δ and every δ over the old live variables,

  δ unifies Balance
    iff
  exists η over θ's parameters, δ =B θη on ALL old live variables.
```

If `p=0` or `q=0`, there are no nonempty supports. Every active variable is sent
to empty. If both sides cancel completely, there are no active variables and
all old variables pass through. Thus `X+Y =B X` leaves arbitrary `X` and forces
`Y=0`, whereas `X =B X` leaves arbitrary `X`.

### 4.4 Exhaustive singleton and zero rules

Normalize each equation of `Dθ`, composing earlier bag bindings. Combine repeated
occurrences of each still-live bag variable. Its left side then has form:

```text
[u₁] + … + [uₖ] + c₁Z₁ + … + cₗZₗ =B [t],
```

with distinct `Zᵢ`, positive coefficients, and no bags inside any payload.

```text
ATOM-MANY
  k ≥ 2 → dead.

ATOM-ONE
  k = 1 → bind every Zᵢ := 0 and retain u₁ =B t.

ATOM-CHOOSE
  k = 0 → for EACH j with cⱼ = 1, make a branch:
             Zⱼ := [t], every other Zᵢ := 0.
           If there is no such j, dead.

ZERO
  [u₁] + … + [uₖ] + c₁Z₁ + … + cₗZₗ =B 0:
    k > 0 → dead;
    k = 0 → bind every Zᵢ := 0.
```

These rules follow from multiplicity/cardinality: the target singleton has
exactly one occurrence, so exactly one coefficient-one contribution can supply
it. A coefficient-two parameter cannot supply half an element. Equal payloads
do not merge two occurrences because there is no idempotence.

The rules apply to the WHOLE state. For example, assigning `Z := [u]` in one
requirement changes `Z =B [v]` in another to `[u] =B [v]`, producing `u =B v`.
Solve all resulting payload equations with the free rules. They involve only
sorts below `Bag`, so they cannot generate bag equations.

### 4.5 COVER and soundness evidence

At a solved leaf `⟨θ ; []⟩`:

```text
COVER
  choose i and β such that θ =B σᵢβ on all original variables;
  check every component equality;
  conclude Σ ⊢ ⟨θ ; []⟩ covered.
```

Equality evidence uses reflexivity, symmetry, transitivity, constructor
congruence, and the registered ACU laws. Finite normalization can construct that
evidence for equal open terms.

Separately, construct such equality evidence for every equation in `E₀σᵢ` for
every proposed answer. This is `Sound(Σ)`, not an assumption silently inserted
into the Lean certificate.

A dead leaf requires an actual `CLASH`, `FREE-OCCURS`, `ATOM-MANY`, impossible
`ATOM-CHOOSE`, or `ZERO` contradiction. Failed matching, unsupported syntax, a
depth bound, or a redundant branch does not establish a dead leaf.

## 5. Proof of finite-sharing exactness

This section proves the mathematical fact needed by the central rule. Counts
are used in the once-for-all argument, not as a problem-specific trusted
Diophantine solver.

### Lemma 5.1 — Bag normal form

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

### Lemma 5.2 — Minimal decomposition

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

### Lemma 5.3 — Opposite-pair bound

For a minimal nonzero solution `(v,w)` and every `i,j`:

```text
vᵢ ≤ bⱼ  OR  wⱼ ≤ aᵢ.
```

If both inequalities fail, the vector with `bⱼ` at coordinate `Xᵢ`, `aᵢ` at
coordinate `Yⱼ`, and zero elsewhere is a nonzero balanced proper subsolution.
This contradicts minimality.

### Lemma 5.4 — A minimal vector has a balanced support

Give each of the `aᵢ` rows labelled `Xᵢ` required row total `vᵢ`, and each of
the `bⱼ` columns labelled `Yⱼ` required column total `wⱼ`. The two total sums
agree, so a nonnegative integer matrix with these margins exists: successively
allocate each row across the remaining column capacities.

We turn this matrix into a zero/one matrix without changing any margin.
Suppose a cell in row `r` labelled `Xᵢ` and column `c` labelled `Yⱼ` has value
`A ≥ 2`. Lemma 5.3 gives one of two cases.

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

### Proposition 5.5 — Exact parameterization of a pure balance

Soundness: each selected cell contributes one occurrence to each side. Equal
degrees for equal row/column labels make repeated input-variable images agree.
Consequently every assignment to all `Z_S` satisfies the balance equation.

Completeness: fix any solution substitution. For each generator in its finite
bag normal forms, record its multiplicities in the active variable images.
This gives a balanced nonnegative vector. Decompose it by Lemma 5.2 and represent
each minimal component by a support using Lemma 5.4. Assign one copy of that
generator to the corresponding `Z_S` for each component. Multiple components
using the same support are combined in the same parameter bag. Summing the
degrees reconstructs the multiplicity of every generator in every input image.
Lemma 5.1 therefore gives the required componentwise equality modulo `B`.
Passthrough parameters reconstruct every inactive variable independently.

This proves the exactness statement in FINITE-SHARING, including repeated
variables and symbolic parameter images. Zero-sided cases are immediate from
positivity: every active generator multiplicity must be zero.

## 6. A finite strategy for a single bag equation

Define `SolveOneBag(e)` as the following rule-based procedure:

1. Flatten `e`; purify explicit singleton occurrences, retaining their equations.
2. Cancel common variable occurrences and construct the canonical support family.
3. Apply FINITE-SHARING once.
4. Process each retained singleton requirement using the exhaustive atom rules,
   propagating all bindings through every requirement and every image.
5. Solve generated free payload equations, rejecting genuine free contradictions.
6. Return all surviving composed substitutions, with unconstrained variables
   retained as parameters.

### Proposition 6.1 — Single-equation exactness

The returned list is finite. Every returned substitution is a symbolic unifier
of `e`, and every symbolic unifier of `e` factors through a returned member.

Proof: purification is exact; Proposition 5.5 parameterizes the purified balance
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

## 7. Whole-problem reference search

### 7.1 The free phase

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

### 7.2 The bag phase

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

### Theorem 7.3 — Finite reference CSU

For every finite `E₀` under the contract, this procedure terminates with a finite
reference list `Θ` such that:

```text
Sound(Θ) and Complete(Θ).
```

Proof: the free phase terminates and preserves the state's denotation. Induct on
the number of pending bag equations. The empty list represents all assignments
to the remaining parameters. For `e :: P`, Proposition 6.1 yields finitely many
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

### 7.4 Retained-worklist implementation of the finite strategy

`CERTIFICATION-PRODUCER` retains equations for replay instead of physically
deleting every solved equation. Consequently, the length of its stored list is
NOT a termination measure. Its correspondence with Sections 6–7 is the following
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
of Section 8.1 finds it. Checked early COVER may stop sooner. If the family is
empty, no such live terminal state can exist; all branches must close by proved
contradictions. Thus retained storage changes the evidence representation, not
the complete fallback of Theorem 8.3.

The argument assumes unbounded execution of the finite enumerations, a correct
typed signature, and the stated stratification. Resource exhaustion is failure
to obtain a certificate, never a contradiction certificate. It does not assert
that arbitrary finite inputs fit the prototype's safety caps. General conditional
EARLY-COVER and further sharing optimizations remain optional improvements;
they are not prerequisites for this fallback argument.

## 8. Factor search and the answer-guided guarantee

### Lemma 8.1 — Complete finite whole-vector matching

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

#### Executable matching invariant

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

### Lemma 8.2 — Finite equality evidence

If two open terms are equal modulo `B`, their finite normalized constructor
forms agree. Flattening, reordering, and removing units can be accompanied by
finite congruence/ACU equality traces. Thus factor matches and proposed-answer
soundness can be witnessed by finite checked equality data, not just Booleans.

### Theorem 8.3 — Search success for a correct proposed set

Assume the contract, finite `E₀`, and finite `Σ` with `Sound(Σ)` and
`Complete(Σ)`. The following reconstruction procedure terminates successfully:

`Σ` is supplied BEFORE this procedure starts. None of the steps below calls
native `unify` to obtain it. The internal reference family `Θ` is coverage
evidence for the supplied `Σ`, not a replacement answer set returned to Lean.

1. Construct checked equality traces establishing each proposed answer's soundness.
2. Obtain the finite reference derivation/list `Θ` by Section 7.
3. For each `θ in Θ`, find a factor through some `σ in Σ` by Lemma 8.1, and
   construct its equality evidence by Lemma 8.2.
4. Combine reference completeness, the checked factors, and proposed soundness.

Proof: soundness traces exist by the premise and Lemma 8.2. By Theorem 7.3 each
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
early-closure extension in Section 9, not this baseline alone.

### Theorem 8.4 — Accepted-certificate correctness

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

## 9. Where native answers can accelerate search

The targeted search receives the same already known `Σ` as Section 8. At each
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

There is no general claim that proposed answers avoid reconstructing a complete
reference derivation in the worst case. They provide genuine checked early
closure opportunities; a uniform speedup is a separate question.

### 9.1 Concrete efficiency benefit and its limits

The target is a coverage proof, not rediscovery of the proposed answers. Once
EARLY-COVER proves that EVERY solution of a current branch factors through an
answer, that branch needs no further unification splits. This can save both
search and the corresponding exhaustive certificate subtree. Merely prioritizing
the choices suggested by an answer would not suffice: unexplored alternatives
would still need coverage evidence.

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
mechanism, but no measured speedup, general complexity improvement, or fully
implemented targeted reconstruction engine is claimed yet.

## 10. Example with two necessary families

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

## 11. Dumps, exhaustiveness, and cost

A suitable rule dump records:

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
answers upstream. Section 12.1 describes the implemented evidence boundary;
the Maude implementation itself is not verified in Lean. Raw rule traces must contain enough context and
branch information for replay; a successful rewrite path alone is not a complete
proof of exhaustiveness.

## 12. Existing Lean work and formalization difficulty

### 12.1 What already exists

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
General search remains unimplemented. These rule-validity proofs alone do not
establish that an automatic reconstruction procedure always succeeds.

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
- `Replay.lean`: typed certificate data, acceptance, and generated profiles.
- `Frontend.lean`: semantic-independent loading of closed rule evidence.

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
singleton/zero, purification, sharing, and whole-vector factor rules. Section 7.4
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
python3 certification_compiler.py --build
python3 certification_compiler.py --demo
CONPANNA_CERT_STRESS=1 python3 certification_compiler.py --demo
CONPANNA_CERT_NEGATIVES=1 python3 certification_compiler.py --demo
python3 -B -m unittest discover -s tests -v
```

The first command precompiles the backend; the second reuses cached modules,
calls Maude, saves its trace/proof under `.lake/build/certification`, and checks
the final theorem. A built project dependency environment is required.
Compilation and subprocesses are sequential and resource-limited.

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

The expanded producer has ATOM with two BIND/BIND/COVER children. At the native
surface, each branch's equalities already state those binding assignments;
the witness N:=n supplies COVER. Comments record this grouping and the different
branch order. This is a correspondence of proof rules and branches, not literal
identity of serialized proof trees. The manual theorem calls neither producer,
parser, generated-proof loader, nor certification tactic. The automated theorem
only unfolds representation data after the generated certificate is checked.

The optional negative suite corrupts freshly produced binding evidence after
checking an unmodified control. A wrong successor must fail at its transition
node; scope errors, admissions, duplicate/unsupported node declarations, and a
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

Those are useful ingredients, NOT a formal proof of Theorem 7.3 or 8.3. The finite
whole-vector matcher is implemented and has the informal invariant/coverage
argument in §8.1. The retained-worklist scheduler now has the informal
progress/exhaustiveness audit in §7.4; their combined FORMAL search-success
theorem remains open. Successful examples alone establish neither argument.
The retained semantic mutation/split rules are useful derived steps, not a
complete fallback algorithm or a replacement for the finite-sharing theorem.

### 12.2 Is formalizing the search guarantee easy?

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

### 12.3 Design verdict and next gate

Under the stated one-bag stratified contract, the argument above gives a credible
finite complete calculus and a conditional reconstruction-success argument. Its
reasoning does not depend on variable-linearity restrictions or finitely many
hand-picked examples. It is not a proof of general mixed-theory combination, an
efficiency result, or a formal verification of the implementation. The prototype
implements the finite fallback, with the retained-storage audit in §7.4 and
independently kernel-checked evidence for successful runs.

The remaining gates are formalizing the search/control guarantee if desired,
reducing certificates with optional conditional EARLY-COVER, and extending the
modeling contract with a separate combination argument. The prototype's safety
timeouts do not replace the finite complete schedule or justify contradiction.
Completing every Lean search meta-theorem before using the scientific prototype
is optional; silently replacing the strategy by bounded case-by-case search is
not. Narrowing integration is outside this document's present implementation.

## 13. References and attribution boundaries

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

## 14. Related work, rule provenance, and differences

### 14.1 How to read the attribution

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

### 14.2 Rule-by-rule provenance

| Rule or mechanism in this document | Provenance | Adaptation and limits of the claim |
| --- | --- | --- |
| `DELETE`, `ORIENT`, `DECOMPOSE`, `CLASH`, `BIND` (§4.1) | Reused free first-order unification transformations; Martelli–Montanari, §2. | Sorted contexts, modulo equality, and postponed bag equations are our setting. Raw free-head clash is not used on ACU roots. These are not new rules. |
| `FREE-OCCURS` (§4.1) | Reused free occurs checking, with an equational guard. | Its use is restricted to free-constructor cycles. Stratification justifies the mandatory non-bag phase. Ordinary syntactic occurs checking is deliberately not used for bag cycles. |
| Equality evidence and `NORMALIZE` (§4.2, §8.2) | Reused equational logic and standard ACU normalization. | Reconstructed evidence targets the registered relation. Neither normalization nor proof-producing equality checking is claimed novel; certified AC reasoning already exists (§14.4). |
| `CANCEL` (§4.2) | Standard flattened AC cancellation; it already appears in Stickel's AC algorithm. | Our justification uses the constructor-generated free bag algebra, including empty remainders. It is not valid merely from assuming an arbitrary ACU interpretation. |
| `MULTIPLICITY-CANCEL` (§9) | Derived from equality of generator multiplicities in a free commutative monoid. | Used as a general checked shortcut; no claim that the algebraic fact is new or that it is the cited papers' specific trace rule. |
| `PURIFY` (§4.2) | Inspired by standard variable abstraction/purification in equational unification and theory combination. | We name singleton terms and retain their equations. We do not import the entire Baader–Schulz combination algorithm or its general combination theorem (§14.5). |
| `FINITE-SHARING` (§4.3) | Adapted from Boudet–Contejean's finite-support theorem and occurrence-sharing treatment of nonlinear AC equations. | We collect all balanced supports into one parameterized pure-balance family, allow empty parameters, and later enforce singleton requirements. This is not a literal copy of their mutation/merge/pruning algorithm. |
| Minimal decomposition and opposite-pair bound (§5.2–§5.3) | Standard nonnegative-balance arguments; the pair bound is part of the reasoning behind Boudet–Contejean's Theorem 2. | Internal completeness arguments, not a separate runtime Diophantine solver or per-problem arithmetic certificate. No novelty claim. |
| Rectangle rounding (§5.4) | Our explicit proof organization for the required finite-support property. | It makes repeated occurrence degrees explicit. We claim neither a new finite-support theorem nor priority for this matrix argument. |
| `ATOM-MANY`, `ATOM-ONE`, `ATOM-CHOOSE`, `ZERO` (§4.4) | Derived from free-bag multiplicities and singleton injectivity. | The exact branching formulation is tailored to the three-constructor fragment. These are elementary ACU consequences, not rules taken from an order-sorted membership calculus. |
| Shared substitution propagation and composition (§4.1, §7) | Reused substitution composition and complete-unifier-set reasoning. | The finite free/bag/payload schedule is justified by our stratification, not a claim about arbitrary interacting theories. |
| `COVER` and whole-vector factorization (§4.5, §8.1) | Reused instantiation preorder and the standard definition of a complete set of unifiers. | We make the factor a checked certificate object on every original input. Comparing complete vectors preserves correlations; the mathematical factorization principle is not new. |
| `EARLY-COVER` (§9) | Project-specific proposed control, built from standard factorization and checked consequence derivations. | It can avoid expanding a branch when coverage is already proved. This is not a claimed new general subsumption theorem, nor a guarantee that native answers always accelerate reconstruction. |
| Proposed-answer soundness plus coverage aggregation (§8.4) | Reused logical inclusion in both directions; architecturally inspired by skeptical external-solver certification, notably SMTCoq. | The target is exactness of a symbolic unifier set over registered constructor semantics, rather than a SAT/SMT result. The native solver remains outside the trust boundary. |
| Exhaustive sharing/atom dumps (§11) | Standard explicit case-tree certification, organized for the proposed calculus. | Both branches or checked alternatives must be accounted for. A positive native computation trace alone is not completeness evidence. The wire format is still future work. |

### 14.3 Classical AC unification and the nonlinear sharing foundation

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

### 14.4 Existing certified AC algorithms and proof-assistant tactics

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
set or the composition argument of §7. Its rules are related work, not the rules
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

### 14.5 Purification and combination of equational theories

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

### 14.6 The supplied order-sorted paper is a different wrapper

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

### 14.7 SMTCoq: the trust architecture, not the ACU proof rules

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

### 14.8 Proof-relevant unification: evidence without importing its metatheory

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

### 14.9 Disunification and complement methods: considered, not adopted

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

### 14.10 Generalized rewrite theories: application motivation only

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

### 14.11 What can responsibly be claimed as different

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
