# Unification Derivation Format (UDF), version 1

A text format for certificates of **completeness** of a set of unifiers modulo free
constructors and associative-commutative operators with identity (ACU). A derivation
proves the judgment

    ⟨α ; E⟩ ⊩ Σ        every solution of the pending equations E, mapped through α,
                       is an instance of some unifier in Σ

for the initial state ⟨id ; E₀⟩ of a problem E₀. It is meant to be produced by a
unification tool (here: Maude, instrumented with `MAUDE_UNIFICATION_TRACE`) and checked
by an independent checker (here: Lean). A producer is untrusted: every step carries the
data its rule needs, and the checker verifies the rule's side conditions. The design
follows the step structure of SMT proof formats (Alethe, CPC): numbered steps, each
naming a rule, its arguments, and the steps it depends on.

Files use the extension `.deriv`.

## 1. Lexical structure and terms

A file is a sequence of s-expressions. Atoms are symbols (any token without
whitespace, parentheses or `"`), natural numbers, and the symbol `inf`. Comments run
from `;` to the end of the line.

Terms:

    term ::= var                       a declared variable
           | const                     a declared constant
           | (op term ...)             a free constructor applied to arguments
           | (op term term ...)        an ACU operator: flattened, any order, ≥ 2 arguments
           | id-op                     the identity of an ACU operator (declared constant)

The checker compares terms modulo ACU (flattening, permutation, identity).

## 2. File structure

    file ::= (udf 1)
             (signature decl ...)
             (problem (= term term) ...)
             [(answers answer ...)]
             step ...

    decl ::= (sort name)
           | (subsort name name)
           | (op name (sort ...) sort)               free constructor
           | (acu name sort identity)                ACU operator with its identity constant
           | (var name sort)

    answer ::= (unifier name (binders (var sort) ...) (bind var term) ...)

`answers` is present when the derivation certifies a given set of unifiers; when it is
absent, the claimed set is the set of leaves of the derivation (§4, `leaf`). With
`answers`, every leaf of the derivation is closed by `cover`: the leaves may be more
numerous than the answers (some leaves being instances of others), and the claim is that
every unifier is an instance of an answer.

## 3. Steps and states

    step ::= (step id rule arg ... :premises (id ...))

A state is a pair ⟨α ; E⟩ of a substitution and a list of pending equations. States are
**not** written in the file: the checker computes the state of each step from its parent
and the parent's rule. The root step `s0` has state ⟨id ; E₀⟩ with E₀ the `problem`
equations in order. Each rule determines the states of its premises, listed in order in
`:premises`. (A producer may add `:state` to a step for readability; checkers ignore it.)

Equations are addressed by their position in the current E, starting at 0.

## 4. Rules

Notation: E = e₀, …, eₙ₋₁; `E∖i` removes eᵢ; `σE` applies a substitution.

| Rule | Arguments | Applies to | Premises | Checker obligation |
|---|---|---|---|---|
| `delete` | `:eq i` | eᵢ is `t = t` | ⟨α ; E∖i⟩ | the two sides are equal modulo ACU |
| `decomp` | `:eq i` | eᵢ is `f(s₁…sₖ) = f(t₁…tₖ)`, f free | ⟨α ; s₁=t₁, …, sₖ=tₖ, E∖i⟩ | same free constructor |
| `clash` | `:eq i` | eᵢ is `f(…) = g(…)`, f ≠ g free | none (closed) | different free constructors |
| `occurs` | `:eq i` | eᵢ is `V = t`, V occurs in t, t not V | none (closed) | the occurrence is under a free constructor |
| `elim` | `:eq i :var V` | eᵢ is `V = t` or `t = V`, V not in t | ⟨[V↦t]∘α ; [V↦t](E∖i)⟩ | V does not occur in t; t has V's sort |
| `ground` | `:eq i` | eᵢ is `s = t`, both ground | none (closed) | s and t differ modulo ACU |
| `acu-solve` | see §5 | equations eᵢ (i in `:eqs`) with top operator f | one per selection | §5 |
| `leaf` | | E is empty | none | — (α is a claimed unifier) |
| `cover` | `:answer name :witness ((var term) ...)` | E is empty | none | α = β∘σ modulo ACU, for the named answer σ and witness β |

`occurs` is restricted to occurrences under a free constructor: inside an ACU operator a
variable can still be solved (by `acu-solve`). `elim` respects sorts: a variable of an
element sort (a strict subsort of an ACU sort) is not bound to a sum; such an equation is
solved by `acu-solve`, where the variable is an alien.

## 5. `acu-solve`

    (step id acu-solve
       :op f                                   the ACU operator
       :eqs (i ...)                            the equations it solves, all with top f or a variable side
       :unknowns (u₁ ... uₘ)                   the maximal non-f subterms of those equations
       :bounds (b₁ ... bₘ)                     inf for a variable of sort f, 1 otherwise ("alien")
       [:cover (c₁ ... cₘ)]                    1 if uⱼ must receive an element; default: 1 exactly for aliens
       :rows ((c₁ ... cₘ) ...)                 one per equation: occurrences left minus right
       :basis ((v₁ ... vₘ) ...)                minimal nonzero solutions of the rows within the bounds
       :selections ((sel (k ...) :fresh (Z ...)) ...)   one per premise, by basis position
       :premises (id ...))

Version 1 covers ACU operators with an identity: then every alien-free vector can be taken
(its fresh variable may be the identity), which is what makes the maximal selections
complete. AC operators without identity are out of its scope.

Unknowns with bound `inf` are the variables of sort f ("bag variables"); unknowns with
bound 1 are aliens: non-variable terms, and variables of a strict subsort of f (single
elements). A bag variable is one unknown. An alien term may label several unknowns: each
then stands for some of the term's occurrences (a producer with lazy bindings, like
Maude, keeps w(N) and w(M) apart after binding N to M). An alien may also be cancelled
when it occurs on both sides. The rows say which unknown takes which occurrences (§5,
obligation 1).

Two aliens *clash* when both are non-variable terms with different top symbols: no
element equals both.

`:cover` is reserved for AC operators (no identity), where every bag variable must
receive an element. Version 1 accepts only its default.

**Selections.** A selection S is a set of basis positions. It is *legal* if every alien
lies in exactly one selected vector (Σ_{k∈S} v_k[j] = 1 for each alien j), and it
*includes every alien-free vector*. The legal selections are exactly the maximal ones;
`:selections` must list all of them, in any order, each with a fresh variable for each of
its alien-free vectors (in order of their positions). The basis may be empty; then the
only legal selection, if no alien needs covering, is the empty one, which maps every bag
variable to the identity.

**Premise of a selection S.** For each selected alien-free vector v_k, its fresh variable
Z_k stands for a multiset; for each selected vector v_k with aliens A_k = {u_j : v_k[j] = 1},
the representative r_k is the first alien of A_k. The substitution θ_S maps each bag
variable u_j to

    θ_S(u_j) = ⋃_{k∈S, A_k=∅} v_k[j] · Z_k  ∪  ⋃_{k∈S, A_k≠∅} v_k[j] · {r_k}

and the premise is

    ⟨θ_S∘α ; (u = r_k for u ∈ A_k, u ≠ r_k, k ∈ S),  θ_S(E∖eqs)⟩

Version 1 requires that no alien contains a bag variable of the system, so θ_S leaves the
aliens and these pending equations unchanged. (In the models so far, aliens lie under a
free constructor of another sort, and hold variables of other operators.)

so aliens selected together become pending equations, solved by the free rules.

**Checker obligations.**

1. *Rows.* For each equation and each term t, the coefficients of the unknowns labelled
   t sum to the occurrences of t, left minus right (modulo ACU flattening); a bag
   variable labels one unknown; and every unknown with a nonzero coefficient is a
   summand of its equation.
2. *Basis vectors are solutions.* Each `v_k` solves every row and respects the bounds.
3. *Basis completeness (clash-free).* Every nonzero vector within the bounds that solves
   every row and has no two clashing aliens is componentwise above some basis vector.
   (A closed Presburger formula.)
4. *Selections.* The listed selections are exactly the legal selections.

Obligations 1, 2 and 4 are finite computations; 3 is the only quantified one.

**Why it is sound** (every solution of the conclusion reaches a premise). For a solution
ρ and each element x, the vector of copies of x in each unknown under ρ solves the rows
(by obligation 1, the rows add up the occurrences correctly however they are shared
among unknowns) and respects the bounds (an alien is one element). Its aliens all equal
x, so no two of them clash. By 3, it is above a basis vector; subtracting it leaves a
smaller clash-free solution, so it decomposes into a sum of basis vectors, whose alien
parts partition the aliens equal to x. Collecting over all x gives a legal selection S,
with Z_k the multiset of the x whose decomposition uses v_k (with multiplicity), and the
aliens of each selected alien vector equal to one x. (The detailed argument, with the
Lean rule, is in documentation/acu-solve-design.md.)

## 6. Example

The equation  R ∪ {f({a} ∪ X)} ∪ {f(Y)} = S ∪ T ∪ {f({a} ∪ W)}  over multisets of baskets,
with fruits a, b inside the baskets (documentation/worked-example.html):

    (udf 1)
    (signature
      (sort Fruit) (sort Fruits) (subsort Fruit Fruits)
      (sort Basket) (sort Baskets) (subsort Basket Baskets)
      (op a () Fruit) (op b () Fruit) (op f (Fruits) Basket)
      (acu u Fruits none) (acu v Baskets nil)
      (var X Fruits) (var Y Fruits) (var W Fruits)
      (var R Baskets) (var S Baskets) (var T Baskets))
    (problem (= (v R (f (u a X)) (f Y)) (v S T (f (u a W)))))

    (step s0 acu-solve :op v :eqs (0)
       :unknowns (S T (f (u a W)) R (f Y) (f (u a X)))
       :bounds   (inf inf 1 inf 1 1)
       :rows     ((-1 -1 -1 1 1 1))
       :basis    ((1 0 0 0 0 1) (1 0 0 0 1 0) (0 1 0 0 0 1) (0 1 0 0 1 0)   ; A or B into S or T
                  (0 0 1 1 0 0)                                           ; C from R
                  (1 0 0 1 0 0) (0 1 0 1 0 0)                             ; R∩S, R∩T
                  (0 0 1 0 0 1) (0 0 1 0 1 0))                            ; C with A, C with B
       :selections ((sel (0 1 4 5 6) :fresh (Z1 Z2))  (sel (0 3 4 5 6) :fresh (Z1 Z2))
                    (sel (2 1 4 5 6) :fresh (Z1 Z2))  (sel (2 3 4 5 6) :fresh (Z1 Z2))
                    (sel (1 7 5 6) :fresh (Z1 Z2))    (sel (3 7 5 6) :fresh (Z1 Z2))
                    (sel (0 8 5 6) :fresh (Z1 Z2))    (sel (2 8 5 6) :fresh (Z1 Z2)))
       :premises (s1 s2 s3 s4 s5 s7 s9 s11))
    (step s1 leaf :premises ())
    (step s2 leaf :premises ())
    (step s3 leaf :premises ())
    (step s4 leaf :premises ())
    ; selection (1 7 5 6): B into S, and A, C together: pending  f({a} ∪ X) = f({a} ∪ W)
    (step s5 decomp :eq 0 :premises (s6))
    (step s6 acu-solve :op u :eqs (0)
       :unknowns (X W) :bounds (inf inf) :rows ((1 -1))          ; a cancelled
       :basis ((1 1)) :selections ((sel (0) :fresh (Z3))) :premises (s6a))
    (step s6a leaf :premises ())
    (step s7 decomp :eq 0 :premises (s8))
    (step s8 acu-solve :op u :eqs (0) :unknowns (X W) :bounds (inf inf) :rows ((1 -1))
       :basis ((1 1)) :selections ((sel (0) :fresh (Z3))) :premises (s8a))
    (step s8a leaf :premises ())
    ; selections (0 8 5 6), (2 8 5 6): A into S or T, and B, C together: pending  f(Y) = f({a} ∪ W)
    (step s9 decomp :eq 0 :premises (s10))
    (step s10 elim :eq 0 :var Y :premises (s10a))
    (step s10a leaf :premises ())
    (step s11 decomp :eq 0 :premises (s12))
    (step s12 elim :eq 0 :var Y :premises (s12a))
    (step s12a leaf :premises ())

The eight leaves are the eight most general unifiers: four with A and B each in S or T
(and C taken from R), two with A = C and B in S or T, two with B = C and A in S or T.

## 7. Relation to the producer and the checker

- **Producer (Maude).** `MAUDE_UNIFICATION_TRACE` makes Maude print one event per
  inference step; `producer/tools/trace_tree.py` rebuilds the search tree, and
  `producer/tools/trace_to_udf.py` extracts the derivation. It keeps only the maximal
  selections (Maude also enumerates non-maximal ones, for order-sorted reasons), undoes
  Maude's purification of aliens by fresh variables, and reads each basis from Maude
  (Maude leaves out vectors with clashing aliens, hence obligation 3's form). The answers
  are Maude's filtered unifiers, and each leaf is covered by one. Any other unification
  tool can produce UDF by reporting the same steps.
- **Checker (Lean).** Each rule is a theorem proved once; the checker reads the file,
  computes the states, applies the rule theorems as terms, and discharges the obligations
  (§4, §5), by local reflection where they are computations.

## 8. Versioning

`(udf 1)` is this document. Additions that a version-1 checker can ignore (new optional
keyword arguments) keep the version; new rules or changed semantics increment it.
