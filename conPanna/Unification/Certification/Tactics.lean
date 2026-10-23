import conPanna.Unification.Certification.Calculus
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-!
Thin helper tactics that close the routine obligations of compiled certificates.
They do no search over the calculus: a certificate fixes every rule and datum,
and these tactics only check equalities and closed Presburger formulas.
-/

namespace Unification.Certification

/-- A free step (DECOMP, ELIM): split the pending conjunction, substitute solved
variables, and close by constructor injectivity. Extra lemmas unfold the problem. -/
syntax "acu_free" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| acu_free) => `(tactic| acu_free [])
  | `(tactic| acu_free [$xs,*]) => `(tactic| (
      try simp only [State.start, unifiedBy, theta, sum, copies, Function.comp_apply,
        List.ofFn_succ, List.ofFn_zero, List.foldr_cons, List.foldr_nil, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_succ, Matrix.head_cons, Fin.succ_zero_eq_one,
        copies_zero, copies_one, ACU.plus_unit, ACU.unit_plus, $xs,*] at *
      -- cheap first: after substitution the goal is often a hypothesis or reflexive
      try (casesm* _ ∧ _; try subst_vars; first | rfl | assumption |
        (constructor <;> first | rfl | assumption); done)
      iterate 2 (
        try casesm* _ ∧ _
        try subst_vars
        try simp_all)
      try ac_nf at *
      try assumption
      try simp_all))

/-- The bag equation of SOLVE, read off a proof `h` of it: unfold the coefficient
form `side`, normalize modulo ACU, compare. -/
macro "acu_side " h:term : tactic => `(tactic| (
  have hb := $h
  simp only [theta, Function.comp_apply, side, sum, copies, List.ofFn_succ, List.ofFn_zero, List.foldr_cons, List.foldr_nil,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ, Matrix.head_cons,
    Fin.succ_zero_eq_one, ACU.plus_unit, ACU.unit_plus] at hb ⊢
  try ac_nf at hb ⊢
  try exact hb))

/-- The remaining equations after SOLVE, read off a proof `h` of them: SOLVE's answer
`θ_π` may occur anywhere in them (e.g. inside a constructor), so evaluate it and normalize
modulo ACU on both sides before comparing. -/
macro "acu_rest " h:term : tactic => `(tactic| (
  have hb := $h
  try simp only [theta, Function.comp_apply, sum, copies, List.ofFn_succ, List.ofFn_zero,
    List.foldr_cons, List.foldr_nil, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_succ, Matrix.head_cons, Fin.succ_zero_eq_one, copies_zero, copies_one, ACU.plus_unit,
    ACU.unit_plus] at hb ⊢
  try ac_nf at hb ⊢
  try exact hb))

set_option hygiene false in
/-- Distinctness of incompatible alien classes: by constructor disjointness,
recorded disequations, or arithmetic. Cheap cases first; the bag equations `h` of the
SOLVE step are not needed for distinctness, and simplifying them can be very costly, so
they are dropped before `simp_all` (the full context is the last resort). -/
macro "acu_distinct" : tactic => `(tactic| (
  intro c c' hcc hcp
  fin_cases c <;> fin_cases c' <;>
    first
      | exact absurd rfl hcc
      | (simp at hcp; done)
      | (simp [theta, sum, copies, ACU.plus_unit, ACU.unit_plus]; done)
      | (clear h; simp_all [theta, sum, copies, ACU.plus_unit, ACU.unit_plus]; done)
      -- the disequation recorded the other way round (`fin_cases` gives both orders):
      -- flip the goal rather than rewrite with `eq_comm`, which is costly
      | (clear h; refine Ne.symm ?_; simp_all [theta, sum, copies, ACU.plus_unit, ACU.unit_plus];
         done)
      | (clear h; simp_all [theta, sum, copies, ACU.plus_unit, ACU.unit_plus, eq_comm]; done)
      | (simp_all [theta, sum, copies, ACU.plus_unit, ACU.unit_plus]; done)
      | (simp_all [theta, sum, copies, ACU.plus_unit, ACU.unit_plus, eq_comm]; done)
      | (simp_all [theta, sum, copies, ACU.plus_unit, ACU.unit_plus]; omega)))

/-- S2 over the listed cliques: one closed Presburger formula per clique. -/
macro "acu_cliques" : tactic => `(tactic| (
  simp only [List.forall_mem_cons, List.forall_mem_nil, and_true, List.not_mem_nil, false_imp_iff,
    forall_const, implies_true]
  repeat' constructor
  all_goals (
    intro v hv
    simp_all [dot, Below, prodL, vsum, List.ofFn_succ, Fin.forall_fin_succ, Fin.exists_fin_succ]
    try omega)))

/-- S3: every nonzero homogeneous solution lies above a basis vector. -/
macro "acu_basis" : tactic => `(tactic| (
  intro v hv hne
  simp_all [dot, Below, List.ofFn_succ, Fin.forall_fin_succ, Fin.exists_fin_succ]
  try omega))

/-- The equality checked by COVER, once fresh variables are named. -/
macro "acu_cover" : tactic => `(tactic| (
  show _ = _
  first
    -- cheap first: evaluate the answer, then compare modulo AC
    | (simp only [State.start, theta, sum, copies, Function.comp_apply, List.ofFn_succ,
        List.ofFn_zero, List.foldr_cons, List.foldr_nil, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_succ, Matrix.head_cons, Fin.succ_zero_eq_one,
        copies_zero, copies_one, Prod.mk.injEq, ACU.plus_unit, ACU.unit_plus]
       try constructorm* _ ∧ _
       all_goals ac_rfl)
    | (simp [State.start, theta, sum, copies, List.ofFn_succ, ACU.plus_unit, ACU.unit_plus]
       try constructorm* _ ∧ _
       all_goals ac_rfl)))

open Lean Meta Elab Tactic in
/-- Restate a goal `s ⊩ U` with the state in direct form. Each step's state is the previous
state composed with the step's substitution, so without this a late step unfolds the whole
stack. Unfolds `Function.comp` and the `State` fields, then reduces beta, projections and
tuple matches; the new goal is definitionally equal. -/
elab "checkpoint" : tactic => liftMetaTactic1 fun goal => do
  let ty ← deltaExpand (← instantiateMVars (← goal.getType)) fun n =>
    n == ``Function.comp || n == ``State.α || n == ``State.E || n == ``State.D
  let ty ← Meta.transform ty (post := fun e => do
    if e.isLambda || e.isForall || e.isMData then return .done e
    let e' ← whnfCore e
    return if e' == e then .done e else .visit e')
  some <$> goal.replaceTargetDefEq ty

end Unification.Certification
