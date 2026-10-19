import conPanna.Narrowing.Narrowing
import conPanna.Unification.Tactics.maudeUnify
import conPanna.Later

/-!
The narrowing tactic `narrow`, and `drop_empty`, which it uses and which is also useful
on its own (after further simplification of a post).
-/

/-! ## Dropping empty patches
A patch whose condition is `False` holds for no state. `drop_empty at h` removes such
patches from the post of `h : isPost R S P`: the shorter list is a different term but
holds for the same states, so `isPost` carries over (`isPost_of_holds_iff`). -/

-- should appear near isPost at core.lean
-- used by drop_empty tactic
theorem Expresso.isPost_of_holds_iff {α : Type _} {R : Expresso.System α}
    {S P Q : Expresso.Pattern α} (h : Expresso.isPost R S P)
    (e : ∀ s, P.holds s ↔ Q.holds s) : Expresso.isPost R S Q :=
  ⟨fun a b ha hs => (e b).1 (h.1 a b ha hs), fun b hb => h.2 b ((e b).2 hb)⟩

open Lean Meta Elab Tactic in
/-- Remove the patches with condition `False` from the post of `h : isPost R S P`. -/
elab "drop_empty" " at " h:ident : tactic => withMainContext do
  let ty ← instantiateMVars (← getLocalDeclFromUserName h.getId).type
  unless ty.isAppOfArity ``Expresso.isPost 4 do
    throwError "drop_empty: {h} is not `isPost R S P`"
  let some (T, ps) := ty.appArg!.listLit? | throwError "drop_empty: the post is not a list"
  -- `Patch.bind fun x => { state := …, cond := False }`
  let empty (p : Expr) : Bool := p.isAppOfArity ``Expresso.Patch.bind 3 &&
    match p.appArg! with
    | .lam _ _ b _ => b.isAppOfArity ``Expresso.PatchBody.mk 3 && b.appArg!.isConstOf ``False
    | _ => false
  let keep := ps.filter (!empty ·)
  if keep.length == ps.length then return
  let Q ← Term.exprToSyntax (← mkListLit T keep)
  evalTactic (← `(tactic| replace $h:ident := Expresso.isPost_of_holds_iff $h:ident (Q := $Q)
    (fun _ => by simp only [Expresso.Pattern.holds_cons, Expresso.Pattern.holds_nil,
      Expresso.Patch.holds, Expresso.PatchBody.holds, and_false, exists_false, false_or])))

namespace NarrowTactic

/-! ## `narrow`
One narrowing step as one tactic (illustrated step by step in the Bakery example,
`examples/Bakery/bakery_pf_uncertain.lean`):

  `narrow R from S using [lemmas] as post hpost`

1. `maude_unify`: the unifier table `Us` for every (rule, patch) cell;
2. `certifyPost_R_P R S Us`, with every certificate deferred (`later`);
3. the post computed (the narrowing definitions and those of `R`, `S` and their
   elements unfolded) and simplified with `lemmas` plus a base set, on the post only;
4. `drop_empty`;
5. each remaining patch named `<theorem>.<post>_i` (a definition, so the context stays
   short), with `post`, its definition `post_eq : [post_1, …] = post`, and
   `hpost : isPost R S post`. `unfold <theorem>.post_i at post_eq` shows a patch. -/

open Lean Meta Elab Tactic in
/-- The elements of a list literal, after unfolding. -/
partial def listElems (l : Expr) : MetaM (List Expr) := do
  let l ← whnf l
  if l.isAppOfArity ``List.cons 3 then return l.appFn!.appArg! :: (← listElems l.appArg!)
  return []

syntax (name := narrowTac) "narrow " term " from " term
  (" using " "[" term,* "]")? (" as " ident ident)? : tactic

open Lean Meta Elab Tactic Expresso Narrowing in
@[tactic narrowTac] def evalNarrow : Tactic := fun stx => withMainContext do
  let `(tactic| narrow $Rs from $Ss $[using [$ls,*]]? $[as $pn $hn]?) := stx
    | throwUnsupportedSyntax
  let postId := pn.getD (mkIdent `post)
  let hId := hn.getD (mkIdent `hpost)
  let R ← Term.elabTerm Rs none
  let S ← Term.elabTerm Ss none
  let α := (← whnf (← whnf (← inferType R)).appArg!).appArg!
  -- 1. the unifiers
  let st ← Dumper.model α
  Dumper.write st
  let Us ← MaudeUnify.forSystem st (mkConst ``PUnit.unit [mkLevelSucc (← getLevel α)]) R S
  -- 2. the post, every certificate deferred
  let cert ← mkFreshExprSyntheticOpaqueMVar (← mkAppM ``certificates_R_P #[R, S, Us])
  let main ← getMainGoal
  setGoals [cert.mvarId!]
  evalTactic (← `(tactic| (
    simp only [certificates_R_P, certificates_r_P, certificates_r_p]
    repeat' (first | exact trivial | constructor)
    all_goals later)))
  setGoals [main]
  let h ← mkAppM ``certifyPost_R_P #[R, S, Us, ← instantiateMVars cert]
  let (_, main) ← (← main.assert hId.getId (← inferType h) h).intro1P
  replaceMainGoal [main]
  -- 3. compute the post (unfold), then simplify it
  let mut defs : Array (TSyntax ``Lean.Parser.Tactic.simpLemma) := #[]
  for e in [R, S] ++ (← listElems R) ++ (← listElems S) do
    if let some c := e.getAppFn.constName? then
      unless c == ``List.cons || c == ``List.nil do
        defs := defs.push (← `(Lean.Parser.Tactic.simpLemma| $(mkIdent c):ident))
  evalTactic (← `(tactic| conv at $hId:ident =>
    arg 3
    simp only [post_R_P, post_r_P, post_r_p, List.map, post_r_p_u, List.cons_append,
      List.nil_append, List.append_nil, $defs,*]))
  -- simplify with the given lemmas plus the logic ones (theory and domain lemmas come
  -- from the caller)
  let lemmas ← ((ls.map (·.getElems)).getD #[]).mapM fun t =>
    `(Lean.Parser.Tactic.simpLemma| $t:term)
  evalTactic (← `(tactic| try (conv at $hId:ident =>
    arg 3
    simp [and_true, or_imp, forall_and, $lemmas,*])))
  -- 4. drop the patches with condition `False`
  evalTactic (← `(tactic| drop_empty at $hId:ident))
  -- 5. name the patches `<theorem>.<post>_i`; `post` with its defining equation
  withMainContext do
    let some decl := (← getLCtx).findFromUserName? hId.getId | throwError "narrow: lost {hId}"
    let hty ← instantiateMVars decl.type
    let some (T, ps) := hty.appArg!.listLit?
      | throwError "narrow: the post is not a list{indentExpr hty}"
    let base := (← Term.getDeclName?).getD `narrow
    let mut names : Array Expr := #[]
    for (p, i) in ps.zipIdx do
      let n := base ++ .mkSimple s!"{postId.getId.eraseMacroScopes}_{i + 1}"
      names := names.push (← mkAuxDefinition n T p (compile := false))
    -- state `hpost` with the names (the same statement, by unfolding), then abstract the list
    let postList ← mkListLit T names.toList
    let main ← (← getMainGoal).replaceLocalDeclDefEq decl.fvarId
      (mkAppN hty.getAppFn (hty.getAppArgs.set! 3 postList))
    replaceMainGoal [main]
    let postVal ← Term.exprToSyntax postList
    let eqId := mkIdent (.mkSimple s!"{postId.getId.eraseMacroScopes}_eq")
    evalTactic (← `(tactic| generalize $eqId:ident : $postVal = $postId:ident at $hId:ident))

end NarrowTactic
