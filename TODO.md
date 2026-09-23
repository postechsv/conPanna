# TODO

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
