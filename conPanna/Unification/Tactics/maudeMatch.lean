import conPanna.Unification.Tactics.maudeAdapter
import conPanna.Subsumption

/-!
`maude_match b` (or `maude_match b k`) proves that a patch `a` lands in the target
patch `b`, up to the condition. On a goal `∃ b' ∈ B, subsumes [a] [b']` it

1. picks `b` and proves `b ∈ B`;
2. asks `producer/tools/match.py` to match `b`'s state against `a`'s, modulo the
   dumped model (`a`'s variables stay fixed), taking the `k`-th match (default first);
3. decodes the match into `σ` (`a`'s variables ↦ `b`'s) and applies
   `Subsumption.subsumes_of_match σ`, closing the state equation;
4. leaves the condition implication: `hc : cond of a at x ⊢ cond of b at σ x`.

The user names the target: matching alone cannot tell which target's condition holds.
Nothing here is trusted: `σ` is data, and Lean checks the state equation.
-/

namespace MaudeMatch

open Lean Meta Elab Tactic MaudeAdapter

/-- The Python side, relative to the project root. -/
def tool : System.FilePath := "producer/tools/match.py"

/-- The elements of a list literal. -/
partial def listElems (l : Expr) : MetaM (List Expr) := do
  let l ← whnf l
  if l.isAppOfArity ``List.nil 1 then return []
  if l.isAppOfArity ``List.cons 3 then return l.appFn!.appArg! :: (← listElems l.appArg!)
  throwError "maude_match: {l} is not a list of patches"

/-- Prove `b ∈ B` for a list `B` one of whose elements is `b` (up to unfolding). -/
def proveMem (goal : MVarId) : MetaM Unit := goal.withContext do
  let ty ← whnfR (← instantiateMVars (← goal.getType))
  let some (B, b) := (do
      guard (ty.isAppOfArity ``Membership.mem 5)
      pure (ty.getArg! 3, ty.getArg! 4)) | throwError "maude_match: expected a membership goal"
  let es ← listElems B
  let some i ← es.toArray.findIdxM? (isDefEq · b) | throwError "maude_match: {b} is not in{indentExpr B}"
  -- `b ∈ e₀ :: … :: eᵢ :: rest` by `head`, then `tail` i times
  let rec rest : Nat → Expr → MetaM Expr
    | 0, l => return l
    | n + 1, l => do rest n (← whnf l).appArg!
  let mut pf ← mkAppOptM ``List.Mem.head #[none, es[i]!, (← whnf (← rest i B)).appArg!]
  for j in (List.range i).reverse do
    pf ← mkAppM ``List.Mem.tail #[es[j]!, pf]
  unless ← isDefEq (← inferType pf) ty do throwError "maude_match: membership proof failed"
  goal.assign pf

/-- `σ` for `subsumes [a] [b]` from the `k`-th Maude match, and `b` in `bind` form. -/
def matchSigma (st : Dumper.State) (a b : Expr) (k : Nat) : MetaM (Expr × Expr) := do
  let bw ← whnf b
  openPatch "Y" b fun _ shapeB ys ynames _ stateB =>
  openPatch "X" a fun A shapeA xs xnames _ stateA => do
    let reply ← callTool tool (Json.mkObj [
      ("model", .str ((← Dumper.outPath) / "ctor.maude").toString),
      ("problems", .arr #[Json.mkObj [("pattern", ← encodeTerm st ynames stateB),
        ("subject", ← encodeTerm st xnames stateA)]])])
    let ms := (← IO.ofExcept (reply.getObjValAs? (Array (Array Json)) "matches"))[0]!
    if ms.isEmpty then throwError "maude_match: the state of{indentExpr b}\ndoes not match{indentExpr stateA}"
    let some m := ms[k]? | throwError "maude_match: only {ms.size} matches"
    let lookup (n : String) : Option Expr := (xs.findIdx? fun x => xnames x.fvarId! == some n).map (xs[·]!)
    let vals ← ys.toList.mapM fun y => do
      let n := (ynames y.fvarId!).get!
      let .ok t := m.getObjVal? n
        | throwError "maude_match: {n} of the target is not determined by the state"
      decodeTerm st lookup t (← inferType y)
    let body ← shapeB.tuple vals
    let σ ← withLocalDeclD `x A fun x => do
      mkLambdaFVars #[x] (body.replaceFVars xs (← shapeA.projections x).toArray)
    return (σ, bw)

syntax (name := maudeMatch) "maude_match " term (ppSpace num)? : tactic

@[tactic maudeMatch] def evalMaudeMatch : Tactic := fun stx => withMainContext do
  let b := stx[1]
  let k := if stx[2].isNone then 0 else stx[2][0].isNatLit?.getD 1 - 1
  evalTactic (← `(tactic| refine ⟨$(⟨b⟩), ?mem, ?sub⟩))
  let gs ← getGoals  -- [mem, sub]
  proveMem (gs[0]!)
  let sub := gs[1]!
  setGoals [sub]
  sub.withContext do
    let ty ← instantiateMVars (← sub.getType)
    unless ty.isAppOfArity ``Expresso.subsumes 3 do
      throwError "maude_match: expected `subsumes [a] [b]`"
    let some (_, [a]) := ty.getArg! 1 |>.listLit? | throwError "maude_match: expected one source patch"
    let some (T, [bE]) := ty.getArg! 2 |>.listLit? | throwError "maude_match: expected one target patch"
    let st ← Dumper.model (← whnf (← inferType a)).appArg!
    Dumper.write st
    let (σ, bw) ← matchSigma st a bE k
    -- `b` in `bind` form, so the lemma applies
    let goal ← sub.replaceTargetDefEq (mkAppN ty.getAppFn #[ty.getArg! 0, ty.getArg! 1,
      ← mkListLit T [bw]])
    setGoals [goal]
    let σs ← Term.exprToSyntax σ
    -- `x` and `hc` are for the user (unhygienic)
    let (x, hc) := (mkIdent `x, mkIdent `hc)
    evalTactic (← `(tactic| refine Subsumption.subsumes_of_match $σs fun $x $hc => ⟨?_, ?_⟩))
    -- the state equation
    evalTactic (← `(tactic| first
      | rfl
      | (dsimp only; first
          | rfl
          | ac_rfl
          | (simp only [ACU.plus_unit, ACU.unit_plus]; done)
          | (simp only [ACU.plus_unit, ACU.unit_plus]; ac_rfl))
      | fail "maude_match: could not close the state equation"))
    evalTactic (← `(tactic| try dsimp only at $hc:ident ⊢))

end MaudeMatch
