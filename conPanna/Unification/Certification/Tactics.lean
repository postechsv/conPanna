import conPanna.Unification.Certification.Calculus
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-!
Thin helper tactics that close the routine obligations of compiled certificates.
They do no search over the calculus: a certificate fixes every rule and datum,
and these tactics only check equalities and closed Presburger formulas.
-/

namespace Unification.Certification

/-! ## Normalization

Every term-level obligation of a certificate is an equation or disequation between
terms built from the problem, SOLVE's answers `θ_π` and the free constructors, compared
modulo ACU. `acu_eval` unfolds the certificate's definitions and evaluates `θ_π`
completely (sums, copies, vector entries at any index); `acu_norm` then normalizes
modulo AC. The step tactics below try a cheap closing step first and fall back to
`acu_norm`. -/

/-- Unfold the certificate's definitions and evaluate SOLVE's answers. Extra lemmas
unfold the problem or name a constructor's injectivity. -/
syntax "acu_eval" (" [" Lean.Parser.Tactic.simpLemma,* "]")? (Lean.Parser.Tactic.location)? :
  tactic
macro_rules
  | `(tactic| acu_eval $[$loc:location]?) => `(tactic| acu_eval [] $[$loc:location]?)
  | `(tactic| acu_eval [$xs,*] $[$loc:location]?) => `(tactic|
      simp only [Eqs, State.start, unifiedBy, BagEq.Holds, side, theta, sum, copies,
        Function.comp_apply, List.ofFn_succ, List.ofFn_zero, List.foldr_cons, List.foldr_nil,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ, Matrix.cons_val,
        Matrix.head_cons, Fin.succ_zero_eq_one, Fin.isValue, Fin.reduceFinMk, Fin.zero_eta, Fin.mk_one,
        copies_zero, copies_one,
        ACU.plus_unit, ACU.unit_plus, $xs,*] $[$loc:location]?)

open Lean Meta Elab Tactic in
/-- Unfold type abbreviations such as `abbrev Bag := ACU Elem`, down to `ACU`, in the goal
and the hypotheses. The AC tactics compare operations syntactically: `+` at type `Bag` and
`+` at type `ACU Elem` (the type of SOLVE's answers) would count as two operations. -/
elab "acu_types" : tactic => withMainContext do
  let env ← getEnv
  let abbrevType (n : Name) : Bool := n != ``ACU &&
    getReducibilityStatusCore env n == .reducible &&
    match env.find? n with
    | some (.defnInfo d) => d.type.getForallBody.isSort
    | _ => false
  let unfold (e : Expr) : MetaM Expr := do deltaExpand (← instantiateMVars e) abbrevType
  let mut goal ← getMainGoal
  for d in ← getLCtx do
    unless d.isImplementationDetail do
      let ty ← unfold d.type
      if ty != d.type then goal ← goal.replaceLocalDeclDefEq d.fvarId ty
  goal ← goal.replaceTargetDefEq (← unfold (← goal.getType))
  replaceMainGoal [goal]

/-- Normalize modulo AC, inside out: one `ac_nf` pass orders a bag of boxes before the bags
inside the boxes are normalized (`box({b} + {a})` and `box({a} + {b})` count as different
elements), so a second pass orders it again. -/
syntax "acu_ac" (Lean.Parser.Tactic.location)? : tactic
macro_rules
  | `(tactic| acu_ac $[$loc:location]?) => `(tactic| (
      try ac_nf $[$loc:location]?
      all_goals try ac_nf $[$loc:location]?))

/-- `acu_eval`, then normalize modulo AC. -/
syntax "acu_norm" (" [" Lean.Parser.Tactic.simpLemma,* "]")? (Lean.Parser.Tactic.location)? :
  tactic
macro_rules
  | `(tactic| acu_norm $[$loc:location]?) => `(tactic| acu_norm [] $[$loc:location]?)
  | `(tactic| acu_norm [$xs,*] $[$loc:location]?) => `(tactic| (
      try acu_eval [$xs,*] $[$loc:location]?
      all_goals (acu_types; acu_ac $[$loc:location]?)))

/-- Close the goal from `h` when both are the same equation (or disequation) modulo AC,
in either orientation. Each side is related to its counterpart by `ac_rfl`, which orders
the two terms together; normalizing goal and hypothesis separately (`ac_nf`) can order
the elements of a nested bag differently. -/
macro "acu_bridge " h:term : tactic => `(tactic| first
  | exact $h
  | exact Eq.trans (by ac_rfl) (Eq.trans $h (by ac_rfl))
  | exact Eq.trans (by ac_rfl) (Eq.trans (Eq.symm $h) (by ac_rfl))
  | exact fun he => $h (Eq.trans (by ac_rfl) (Eq.trans he (by ac_rfl)))
  | exact fun he => $h (Eq.trans (by ac_rfl) (Eq.trans (Eq.symm he) (by ac_rfl))))

/-- Close the goal, or each conjunct of it, from `h` or one of its conjuncts, modulo AC
(`acu_bridge`). -/
syntax "acu_from " term : tactic
macro_rules
  | `(tactic| acu_from $h) => `(tactic| first
      | acu_bridge $h
      | (refine And.intro ?_ ?_ <;> acu_from $h)
      -- recurse only into a conjunction: check `h` is one first, or a failing case recurses
      | (have _ := And.left $h; acu_from (And.left $h))
      | (have _ := And.right $h; acu_from (And.right $h)))

/-! ## Step obligations -/

/-- An equation of tuples of terms, compared component-wise modulo ACU once SOLVE's
answers are evaluated. -/
macro "acu_eq" : tactic => `(tactic| (
  try acu_eval [Prod.mk.injEq]
  try constructorm* _ ∧ _
  all_goals (acu_types; first | ac_rfl | (acu_ac; done))))

/-- CLASH (and OCCURS, DISTINCT): the pending constraints are contradictory. Split them,
substitute solved variables, and close by constructor injectivity and disjointness,
modulo AC. Extra lemmas unfold the problem. Also the last resort of ELIM. -/
syntax "acu_free" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| acu_free) => `(tactic| acu_free [])
  | `(tactic| acu_free [$xs,*]) => `(tactic| (
      try acu_eval [$xs,*] at *
      -- cheap first: after substitution the goal is often a hypothesis or reflexive
      try (casesm* _ ∧ _; try subst_vars; first | rfl | assumption |
        (constructor <;> first | rfl | assumption); done)
      iterate 2 (
        try casesm* _ ∧ _
        try subst_vars
        try simp_all)
      try acu_types
      try acu_ac at *
      try assumption
      try simp_all))

set_option hygiene false in
/-- DECOMP `f(s₁,…,sₙ) = f(t₁,…,tₙ)`, from the first equation `h`: by the constructor's
injectivity lemma `f.injEq`, given with the lemmas that unfold the problem (successor
`n + 1` and singleton bags `{s} = {t}` are built in). Arguments are compared modulo ACU. -/
syntax "acu_decomp" " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| acu_decomp [$xs,*]) => `(tactic| (
      simp only [Eqs, List.foldr_cons, List.foldr_nil, and_true, unifiedBy, Nat.add_right_cancel_iff,
        ACU.elem_inj, $xs,*] at h ⊢
      first
        | exact h
        | (try acu_eval [ACU.elem_inj, $xs,*] at h ⊢
           all_goals (acu_types; acu_ac at h ⊢)
           all_goals acu_from h)))

set_option hygiene false in
/-- ELIM `V = t`, from the first equation `h`: substitute it, then the valuation is
the image of the smaller one. The lemmas unfold the problem, for an ELIM on it. After
SOLVE, `h` may contain SOLVE's answer `θ_π`: it is evaluated first, and the images are
compared modulo ACU. -/
syntax "acu_elim" " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| acu_elim [$xs,*]) => `(tactic| (
      first
        | (subst h; rfl)
        | (simp only [unifiedBy, $xs,*] at h; subst h; rfl)
        | (acu_norm [$xs,*] at h; subst h; acu_eq)
        | acu_free [$xs,*]))

/-- The bag equation of SOLVE, read off a proof `h` of it: unfold the coefficient
form `side`, normalize modulo ACU, compare. -/
macro "acu_side " h:term : tactic => `(tactic| (
  have hb := $h
  try acu_eval at hb ⊢
  all_goals (acu_types; acu_ac at hb ⊢)
  all_goals acu_from hb))

set_option hygiene false in
/-- Distinctness of incompatible aliens: by constructor disjointness, or by a recorded
disequation (`hD`) in either orientation, modulo ACU; arithmetic as the last resort.
The pending equations `h` are rarely needed for distinctness, and simplifying them can be
very costly, so they are dropped first. -/
macro "acu_distinct" : tactic => `(tactic| (
  intro c c' hcc hcp
  fin_cases c <;> fin_cases c' <;>
    first
      | exact absurd rfl hcc
      | (simp [BagEq.cp] at hcp; done)
      -- different constructors, possibly under singleton bags (`{a} = {c} ↔ a = c`)
      | (simp [Eqs, theta, sum, copies, ACU.plus_unit, ACU.unit_plus, ACU.elem_inj]; done)
      | (clear h; (try acu_eval at hD ⊢); all_goals (acu_types; acu_ac at hD ⊢)
         all_goals acu_from hD)
      | (simp_all [Eqs, BagEq.cp, theta, sum, copies, ACU.plus_unit, ACU.unit_plus, eq_comm]; done)
      | (simp_all [Eqs, BagEq.cp, theta, sum, copies, ACU.plus_unit, ACU.unit_plus]; omega)))

/-- The premises of SOLVE, one per choice `π`: name the choice in each. -/
macro "acu_branches" : tactic => `(tactic| (
  intro π hπ
  simp [choices] at hπ
  all_goals try casesm* _ ∨ _
  all_goals subst_vars))

/-- S2 over the listed cliques: one closed Presburger formula per clique. The count
equation is simplified in place, not used to rewrite the goal (`simp_all` can loop on an
equation such as `v₀ + v₁ = 2 * v₀ + v₁`). -/
macro "acu_cliques" : tactic => `(tactic| (
  simp only [List.forall_mem_cons, List.forall_mem_nil, and_true, List.not_mem_nil, false_imp_iff,
    forall_const, implies_true]
  repeat' constructor
  all_goals (
    -- a trivially true count equation is already gone from the goal
    intro v; try intro hv
    try simp [dot, Below, prodL, vsum, List.ofFn_succ, Fin.forall_fin_succ, Fin.exists_fin_succ]
      at *
    all_goals omega)))

/-- S3: every nonzero homogeneous solution lies above a basis vector. Simplified in place,
as in `acu_cliques`. -/
macro "acu_basis" : tactic => `(tactic| (
  intro v; try intro hv; try intro hne
  try simp [dot, Below, List.ofFn_succ, Fin.forall_fin_succ, Fin.exists_fin_succ] at *
  all_goals omega))

/-- The equality checked by COVER, once fresh variables are named. -/
macro "acu_cover" : tactic => `(tactic| (
  show _ = _
  acu_eq))

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
