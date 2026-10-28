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

/-- Close the goal by `h` or one of its conjuncts as it stands, in either orientation: once
goal and hypothesis are normalized, this finds the matching disequation without `ac_rfl`. -/
syntax "acu_find " term : tactic
macro_rules
  | `(tactic| acu_find $h) => `(tactic| first
      | exact $h
      | exact Ne.symm $h
      | exact Eq.symm $h
      | (have _ := And.left $h; acu_find (And.left $h))
      | (have _ := And.right $h; acu_find (And.right $h)))

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

open Lean in
/-- The elements `e` of the singletons `{e}` in a first-order term. -/
partial def singletons (t : Expr) : Array Expr :=
  let inner := t.getAppArgs.foldl (fun acc a => acc ++ singletons a) #[]
  if t.isAppOfArity ``Singleton.singleton 4 then inner.push t.appArg! else inner

open Lean Meta Elab Tactic in
/-- Distinctness by counting, for a goal `s ≠ t`: assume `s = t`, strip equal
constructors (`injection`), and for some element `e` occurring as `{e}`, the copies of
`e` on the two sides differ (`omega`, with each variable's count as an unknown). Proves
e.g. `box({b}) ≠ box({b} + {b})` and `{a} + Z₁ + Z₂ ≠ {b} + Z₁`, which no recorded
disequation or constructor clash gives. -/
elab "acu_count" : tactic => withMainContext do
  evalTactic (← `(tactic| (intro he; repeat' injection he with he)))
  for goal in ← getGoals do
    goal.withContext do
      -- the equations between bags left by `injection`, and the elements in them
      let mut found := false
      for d in ← getLCtx do
        if found || d.isImplementationDetail then continue
        let ty ← instantiateMVars d.type
        let some (_, lhs, rhs) := ty.eq? | continue
        let elems := singletons lhs ++ singletons rhs
        let h ← Term.exprToSyntax d.toExpr
        for e in elems do
          if found then break
          let es ← Term.exprToSyntax e
          let saved ← saveState
          try
            setGoals [goal]
            evalTactic (← `(tactic| (
              have hc := congrArg (fun Z => @Multiset.count _ (Classical.decEq _) $es (ACU.toMultiset Z)) $h
              simp only [ACU.toMultiset_plus, ACU.toMultiset_elem, ACU.toMultiset_unit,
                Multiset.count_add, Multiset.count_singleton, Multiset.count_zero,
                reduceCtorEq, ↓reduceIte, if_true, if_false] at hc
              omega)))
            found := true
          catch _ => restoreState saved
      unless found do throwError "acu_count: no element whose copies differ"
  setGoals []

set_option hygiene false in
/-- Distinctness of incompatible aliens, one goal per pair: by a recorded disequation (`hD`)
in either orientation, by different constructors, or by counting copies of an element,
all modulo ACU; `simp_all` with arithmetic as the last resort. The disequations are
normalized once, before the split into pairs; cheap checks come first. The pending equations `h` are rarely needed
for distinctness, and simplifying them can be very costly, so the cheap paths drop them. -/
macro "acu_distinct" : tactic => `(tactic| (
  intro c c' hcc hcp
  try acu_eval at hD
  try (acu_types; acu_ac at hD)
  -- normalizing may already close the goal: the disequations contradict each other
  all_goals fin_cases c <;> fin_cases c' <;>
    first
      | exact absurd rfl hcc
      -- a compatible pair: nothing to prove (a closed Boolean computation)
      | exact absurd hcp (by decide)
      -- different constructors, possibly under singleton bags (`{a} = {c} ↔ a = c`)
      | (simp [Eqs, theta, sum, copies, ACU.plus_unit, ACU.unit_plus, ACU.elem_inj]; done)
      -- a recorded disequation
      | (clear h; (try acu_eval at ⊢); all_goals (acu_types; acu_ac)
         all_goals first | acu_find hD | acu_from hD)
      -- a different number of copies of some element
      | (clear h; (try acu_eval at ⊢); acu_count)
      | (simp_all [Eqs, BagEq.cp, theta, sum, copies, ACU.plus_unit, ACU.unit_plus, eq_comm]; done)
      | (simp_all [Eqs, BagEq.cp, theta, sum, copies, ACU.plus_unit, ACU.unit_plus]; omega)))

/-- The premises of SOLVE, one per choice `π`: name the choice in each. -/
macro "acu_branches" : tactic => `(tactic| (
  intro π hπ
  simp [choices] at hπ
  all_goals try casesm* _ ∨ _
  all_goals subst_vars))

/-- A closed Presburger obligation of SOLVE (S2, S3) about a count vector `v`: unfold the
dot products, the picks and the vector entries (an explicit lemma list, which is much
cheaper than the default simp set, kept as fallback), then `omega`. Simplified in place,
not by `simp_all`, which can loop on an equation such as `v₀ + v₁ = 2 * v₀ + v₁`. -/
macro "acu_arith" : tactic => `(tactic| first
  | ((try simp only [dot, Below, prodL, vsum, Nat.succ_eq_add_one, zero_add, Nat.reduceAdd,
        List.ofFn_succ, List.ofFn_zero, Fin.isValue, Fin.cast_eq_self, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_succ, Matrix.cons_val_fin_one, Matrix.cons_val,
        Fin.succ_zero_eq_one, one_mul, zero_mul, List.sum_cons, List.sum_nil, add_zero,
        List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false,
        Fin.forall_fin_succ, Fin.exists_fin_succ, IsEmpty.forall_iff, IsEmpty.exists_iff,
        and_true, true_and, exists_eq_or_imp, zero_le, ↓existsAndEq] at *)
     all_goals omega)
  | ((try simp [dot, Below, prodL, vsum, List.ofFn_succ, Fin.forall_fin_succ, Fin.exists_fin_succ]
        at *)
     all_goals omega))

/-- S2 over the listed cliques: one closed Presburger formula per clique. The list is split
by applying `List.forall_mem_cons` (rewriting the whole statement with it is far costlier). -/
macro "acu_cliques" : tactic => `(tactic| (
  repeat' (first
    | exact List.forall_mem_nil _
    | refine List.forall_mem_cons.2 ⟨?_, ?_⟩)
  all_goals (
    -- a trivially true count equation is already gone from the goal
    intro v; try intro hv
    acu_arith)))

/-- S3: every nonzero homogeneous solution lies above a basis vector. -/
macro "acu_basis" : tactic => `(tactic| (
  intro v; try intro hv; try intro hne
  acu_arith))

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
