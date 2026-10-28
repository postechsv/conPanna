import conPanna.Unification.Certification.Calculus
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-!
Thin helper tactics that close the routine obligations of compiled certificates.
They do no search over the calculus: a certificate fixes every rule and datum,
and these tactics only check equalities and closed Presburger formulas.
-/

namespace Unification.Certification

/-- CLASH (and OCCURS, DISTINCT), and ELIM after SOLVE: split the pending equations,
evaluate SOLVE's answers, substitute solved variables, and close by constructor
injectivity and disjointness, modulo AC. Extra lemmas unfold the problem. -/
syntax "acu_free" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| acu_free) => `(tactic| acu_free [])
  | `(tactic| acu_free [$xs,*]) => `(tactic| (
      try simp only [Eqs, State.start, unifiedBy, theta, sum, copies, Function.comp_apply,
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

set_option hygiene false in
/-- DECOMP `f(s₁,…,sₙ) = f(t₁,…,tₙ)`, from the first equation `h`: by the constructor's injectivity
lemma `f.injEq`, given with the lemmas that unfold the problem (successor `n + 1` is
built in). Arguments that are bags are compared modulo AC. -/
syntax "acu_decomp" " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| acu_decomp [$xs,*]) => `(tactic| (
      simp only [Eqs, List.foldr_cons, List.foldr_nil, and_true, unifiedBy, Nat.add_right_cancel_iff,
        $xs,*] at h ⊢
      first
        | exact h
        | (ac_nf at h ⊢ <;> exact h)))

set_option hygiene false in
/-- ELIM `V = t`, from the first equation `h`: substitute it, then the valuation is
the image of the smaller one. The lemmas unfold the problem, for an ELIM on it. After
SOLVE, `h` may contain SOLVE's answer `θ_π`: then it is evaluated and compared modulo AC
(`acu_free`). -/
syntax "acu_elim" " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| acu_elim [$xs,*]) => `(tactic| (
      first
        | (subst h; rfl)
        | (simp only [unifiedBy, $xs,*] at h; subst h; rfl)
        | acu_free [$xs,*]))

/-- The bag equation of SOLVE, read off a proof `h` of it: unfold the coefficient
form `side`, normalize modulo ACU, compare. -/
macro "acu_side " h:term : tactic => `(tactic| (
  have hb := $h
  simp only [BagEq.Holds, theta, Function.comp_apply, side, sum, copies, List.ofFn_succ, List.ofFn_zero, List.foldr_cons, List.foldr_nil,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ, Matrix.head_cons,
    Fin.succ_zero_eq_one, ACU.plus_unit, ACU.unit_plus] at hb ⊢
  try ac_nf at hb ⊢
  try exact hb))

set_option hygiene false in
/-- Distinctness of incompatible alien classes: by constructor disjointness,
recorded disequations, or arithmetic. Cheap cases first; the pending equations `h` are
rarely needed for distinctness, and simplifying them can be very costly, so they are
dropped before `simp_all` (the full context is the last resort). -/
macro "acu_distinct" : tactic => `(tactic| (
  intro c c' hcc hcp
  fin_cases c <;> fin_cases c' <;>
    first
      | exact absurd rfl hcc
      | (simp [BagEq.cp] at hcp; done)
      | (simp [Eqs, theta, sum, copies, ACU.plus_unit, ACU.unit_plus]; done)
      | (clear h; simp_all [Eqs, BagEq.cp, theta, sum, copies, ACU.plus_unit, ACU.unit_plus]; done)
      -- the disequation recorded the other way round (`fin_cases` gives both orders):
      -- flip the goal rather than rewrite with `eq_comm`, which is costly
      | (clear h; refine Ne.symm ?_; simp_all [Eqs, BagEq.cp, theta, sum, copies, ACU.plus_unit, ACU.unit_plus];
         done)
      | (clear h; simp_all [Eqs, BagEq.cp, theta, sum, copies, ACU.plus_unit, ACU.unit_plus, eq_comm]; done)
      | (simp_all [Eqs, BagEq.cp, theta, sum, copies, ACU.plus_unit, ACU.unit_plus]; done)
      | (simp_all [Eqs, BagEq.cp, theta, sum, copies, ACU.plus_unit, ACU.unit_plus, eq_comm]; done)
      | (simp_all [Eqs, BagEq.cp, theta, sum, copies, ACU.plus_unit, ACU.unit_plus]; omega)))

/-- The premises of SOLVE, one per choice `π`: name the choice in each. -/
macro "acu_branches" : tactic => `(tactic| (
  intro π hπ
  simp [choices] at hπ
  all_goals try casesm* _ ∨ _
  all_goals subst_vars))

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
stack. Unfolds `State.subst`, `Function.comp`, the list operations of the rules and the
fields of states and SOLVE's data, then reduces beta, tuple matches and projections of
tuples (`(a, b).1`), also under binders: the pending equations are functions, and are
substituted at every ELIM and SOLVE. The new goal is definitionally equal. -/
elab "checkpoint" : tactic => liftMetaTactic1 fun goal => do
  let ty ← deltaExpand (← instantiateMVars (← goal.getType)) fun n =>
    n == ``State.subst || n == ``State.start || n == ``Function.comp ||
    n == ``State.α || n == ``State.E || n == ``State.D ||
    n == ``Split.glue || n == ``SolveData.B ||
    n == ``List.map || n == ``HAppend.hAppend || n == ``Append.append ||
    n == ``instHAppendOfAppend || n == ``List.instAppend || n == ``List.append
  let ty ← Meta.transform ty (post := fun e => do
    if e.isMData then return .done e
    let e' ← whnfCore e
    if e' != e then return .visit e'
    -- a structure projection applied to a constructor, e.g. `(a, b).1`; not class
    -- projections such as `HAdd.hAdd`, which would unfold `+`
    if let .const n _ := e.getAppFn then
      if let some info ← getProjectionFnInfo? n then
        unless info.fromClass do
          if let some e' ← unfoldDefinition? e then
            let e' ← whnfCore e'
            unless e'.isProj do return .visit e'
    return .done e)
  some <$> goal.replaceTargetDefEq ty

end Unification.Certification
