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
        ACU.plus_unit, ACU.unit_plus, $xs,*] at *
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

/-- Distinctness of incompatible alien classes: by constructor disjointness,
recorded disequations, or arithmetic. -/
macro "acu_distinct" : tactic => `(tactic| (
  intro c c' hcc hcp
  fin_cases c <;> fin_cases c' <;>
    first
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
  simp [State.start, theta, sum, copies, List.ofFn_succ, ACU.plus_unit, ACU.unit_plus]
  try constructorm* _ ∧ _
  all_goals ac_rfl))

end Unification.Certification
