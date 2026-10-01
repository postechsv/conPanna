# TODO

## Short-term goal: certified constrained narrowing

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

- ONE active Lean experiment: `certification2.lean`. Start with
  `IndexedExample.wrapped_two_unifiers` near the bottom.
- General library code, automatic registration, and the single main
  user proof are clearly separated. Superseded experimental Lean files were
  removed; do not add more intermediate files without a concrete need.
- Primitive ACU certificate replay, capture-safe elimination, indexed constructor
  semantics, wrapper inversion, and the two-unifier native example are proved
  without admissions. Rejection/capture regression checks are retained.
- Registration needs syntactic sort/symbol tables, quoting/round trips and
  existing law witnesses—not user freeness, reflection or unification proofs.
  `certify_structural T for Conf` now generates it for one ACU datatype with
  nullary atoms and a free unary state wrapper. Put the annotation beside T's
  declaration. Unsupported signatures are rejected explicitly.
- The indexed relation has a proved map INTO existing Structural.EqMod, not an
  equivalence with all old derivations. Indexed signatures, native registration,
  and the forward bridge now live in conPanna.Structural. `=[T.certified]` opts
  into indexed equality; `=[T]` and existing narrowing retain their semantics.
- `certification2.maude` is unchanged: a scripted object-level derivation with
  both unifiers in one result. No complete search strategy/trace importer yet.
- Next: extend automatic registration and the generic checker bridge to multiple
  sorts and payload constructors needed by Bakery, then migrate structural rule/
  pattern semantics and narrowing to certified theories. The explicit indexed
  path is transitional, not a reason to build two independent narrowing engines.
  Core changes were authorized; keep reporting semantic migration boundaries.
- Repeated-variable search/termination and checking complexity remain research
  tasks; successful finite certificate checks do not establish a full algorithm.

### Deferred until the prototype is stable

- Automatic Lean-to-Maude model translation/module dumping for certification.
- Automatic trace parsing, certificate transport, and proof-interface integration.
- Native registration/faithfulness automation and constrained-narrowing lifting.
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
