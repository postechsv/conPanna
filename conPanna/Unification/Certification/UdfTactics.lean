import conPanna.Unification.Certification.Tactics
import conPanna.Unification.Certification.AcuSolve

/-!
Thin tactics for the obligations of ACU-SOLVE on a system (`acu_solve`), as generated from
a UDF derivation by `udf_certify`. Like Tactics.lean, they do no search: every rule and
datum is fixed by the derivation. The vectors of `acu_solve` are given with explicit sizes,
so `Fin.castAdd`/`Fin.natAdd` at numerals and the vector entries evaluate by simprocs.
-/

namespace Unification.Certification

/-- Unfold and evaluate ACU-SOLVE's data: the substitution `θ_S`, the pending equations,
the rows in `side` form, sums and copies, vector entries at numerals. -/
syntax "udf_eval" (" [" Lean.Parser.Tactic.simpLemma,* "]")? (Lean.Parser.Tactic.location)? :
  tactic
macro_rules
  | `(tactic| udf_eval $[$loc:location]?) => `(tactic| udf_eval [] $[$loc:location]?)
  | `(tactic| udf_eval [$xs,*] $[$loc:location]?) => `(tactic|
      simp only [Eqs, State.start, unifiedBy, List.foldr_cons, List.foldr_nil, and_true,
        List.take_succ_cons, List.take_zero,
        Basis.theta, Basis.pending, System.Holds, side, sum, copies, Function.comp_apply, id_eq,
        List.ofFn_succ, List.ofFn_zero, List.flatten_cons, List.flatten_nil, List.nil_append,
        List.cons_append, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
        Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ,
        Matrix.head_cons, Fin.reduceCastAdd, Fin.reduceNatAdd, Fin.reduceSucc, Fin.isValue,
        Fin.succ_zero_eq_one, Fin.succ_one_eq_two,
        ne_eq, one_ne_zero, not_false_eq_true, not_true_eq_false, and_true, true_and, and_false,
        false_and, Bool.false_eq_true, ↓reduceIte, Fin.reduceEq, Fin.reduceNe,
        copies_zero, copies_one, ACU.plus_unit, ACU.unit_plus, $xs,*] $[$loc:location]?)

open Lean Meta Elab Tactic in
/-- Equations of bags from equations of bags, with cancellation: compare the number of
copies of an arbitrary element `e` on each side (`omega`, each count of a variable or a
singleton an unknown). Used where the rows of a system drop what both sides share. -/
elab "udf_cancel" : tactic => withMainContext do
  evalTactic (← `(tactic| (
    try casesm* _ ∧ _
    repeat' refine And.intro ?_ ?_
    all_goals (simp only [ACU.eq_iff, Multiset.ext] at *; intro e))))
  for goal in ← getGoals do
    goal.withContext do
      let mut specs : Array (TSyntax `tactic) := #[]
      for d in ← getLCtx do
        if d.isImplementationDetail then continue
        if (← instantiateMVars d.type).isForall then
          let h := mkIdent d.userName
          specs := specs.push (← `(tactic| try specialize $h:ident e))
      setGoals [goal]
      for t in specs do evalTactic t
      evalTactic (← `(tactic| (
        simp only [ACU.toMultiset_plus, ACU.toMultiset_elem, ACU.toMultiset_unit,
          toMultiset_copies, Multiset.count_add, Multiset.count_nsmul, Multiset.count_zero,
          smul_eq_mul] at *
        omega)))

/-- Evaluate list bookkeeping in the goal's state: `pick`'s reordering, `acu_solve_take`'s
`take`/`drop`, the pending equations of a selection. -/
macro "udf_list" : tactic => `(tactic|
  try simp only [List.getElem_cons_succ, List.getElem_cons_zero, List.eraseIdx_cons_succ,
    List.eraseIdx_cons_zero, List.drop_succ_cons, List.drop_zero, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append, Basis.pending, List.ofFn_succ, List.ofFn_zero,
    List.flatten_cons, List.flatten_nil, List.singleton_append, Matrix.cons_val,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ, Fin.reduceNatAdd,
    Fin.reduceSucc, Fin.isValue, Fin.succ_zero_eq_one, ne_eq, one_ne_zero, not_false_eq_true,
    not_true_eq_false, and_true, true_and, and_false, false_and, Bool.false_eq_true,
    ↓reduceIte, Fin.reduceEq, Fin.reduceNe])

/-- Close the goal from `h` after evaluating ACU-SOLVE's data in both, modulo AC. Used for
the rows of a system (`heq`) and to restate a premise's equations (`restate`). -/
macro "udf_from " h:ident : tactic => `(tactic| (
  try udf_eval at $h:ident ⊢
  all_goals first
    | exact $h
    | (acu_types; acu_ac at $h:ident ⊢; all_goals acu_from $h)
    | udf_cancel))

/-- The closed Presburger formulas of `Basis.Valid` (S3′), once the count vector is split
into named components. -/
macro "udf_arith" : tactic => `(tactic| (
  simp only [System.Admissible, Below, dot, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, IsEmpty.forall_iff, List.ofFn_succ, List.ofFn_zero,
    List.sum_cons, List.sum_nil, Fin.forall_fin_succ, Fin.exists_fin_succ, IsEmpty.exists_iff,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_one, Matrix.cons_val,
    Fin.isValue, Fin.reduceNatAdd, Fin.reduceSucc, Fin.cast_eq_self, Matrix.cons_val_fin_one,
    and_true, true_and, one_mul, zero_mul, add_zero, zero_add] at *
  omega))

/-- S3′, split by alien patterns: the unfolding of `udf_arith`, without its `omega`. -/
macro "udf_s3_unfold" : tactic => `(tactic| (
  simp only [System.Admissible, Below, dot, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, IsEmpty.forall_iff, List.ofFn_succ, List.ofFn_zero,
    List.sum_cons, List.sum_nil, Fin.forall_fin_succ, Fin.exists_fin_succ, IsEmpty.exists_iff,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_one, Matrix.cons_val,
    Fin.isValue, Fin.reduceNatAdd, Fin.reduceSucc, Fin.cast_eq_self, Matrix.cons_val_fin_one,
    and_true, true_and, one_mul, zero_mul, add_zero, zero_add] at *))

/-- One alien pattern of S3′ (the alien columns fixed to 0 or 1): evaluate the numerals,
which drops the basis vectors that do not fit and the clashing cases, then `omega` on the
bag columns. -/
macro "udf_s3_case" : tactic => `(tactic| (
  (try simp only [zero_le, le_refl, Nat.not_succ_le_zero, mul_one, mul_zero, one_mul,
    zero_mul, add_zero, zero_add, true_and, and_true, false_and, and_false, true_or, or_true,
    false_or, or_false, ne_eq, not_true_eq_false, not_false_eq_true, Nat.reduceLeDiff,
    Nat.reduceAdd, Nat.reduceMul] at *)
  all_goals omega))

/-- Clashing aliens differ: for each listed pair, different constructors once the alien
vector is evaluated. -/
macro "udf_clash" : tactic => `(tactic| (
  simp only [List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true]
  try constructorm* _ ∧ _
  all_goals simp only [Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_succ, Fin.isValue, Fin.succ_zero_eq_one, ne_eq, reduceCtorEq,
    not_false_eq_true]))

/-- COVER after ACU-SOLVE: the equality of tuples, with `θ_S` evaluated. -/
macro "udf_cover" : tactic => `(tactic| (
  show _ = _
  udf_eval [Prod.mk.injEq]
  try constructorm* _ ∧ _
  all_goals (acu_types; first | rfl | ac_rfl | (acu_ac; done))))

end Unification.Certification
