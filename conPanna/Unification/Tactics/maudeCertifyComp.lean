import conPanna.Unification.Tactics.maudeAdapter
import conPanna.Unification.Certification.Tactics

/-!
`maude_certify_comp` proves a goal `complete P U`: the unifiers `U` cover every
solution of the problem `P`. It works on any such goal, e.g. a cell
`complete (mayFire r p) U` inside a narrowing proof, or a standalone theorem.

1. The goal is restated in literal form (definitionally equal): `P` as
   `Problem.bind fun γ => (lhs, rhs)` and `U` as a list of `Unifier.bind fun z => γ`,
   both over the constructor terms they unfold to. The proof then names nothing of
   the user's (no `problem`, `answers`, rule or pattern definitions).
2. Problem and unifiers are encoded (`maudeAdapter.lean`) and sent to
   `producer/tools/certify.py`: the producer derives a certificate for exactly
   these unifiers (no unification), and the compiler turns it into proof steps.
3. The steps are elaborated against the goal. Nothing outside Lean is trusted.
-/

namespace MaudeCertifyComp

open Lean Meta Elab Tactic Unification MaudeAdapter

/-- The Python side, relative to the project root. -/
def tool : System.FilePath := "producer/tools/certify.py"

/-- The elements of a list literal. -/
partial def listElems (l : Expr) : MetaM (List Expr) := do
  let l ← whnf l
  if l.isAppOfArity ``List.nil 1 then return []
  if l.isAppOfArity ``List.cons 3 then return l.appFn!.appArg! :: (← listElems l.appArg!)
  throwError "maude_certify_comp: {l} is not a list of unifiers"

/-- The literal form of goal `complete P U`, and the request for `certify.py`. -/
def prepare (st : Dumper.State) (ty : Expr) : MetaM (Expr × Json) := do
  let #[α, Γ, P, U] := ty.getAppArgs
    | throwError "maude_certify_comp: the goal is not `complete P U`"
  let elemTy := (← whnf (← inferType U)).appArg!
  openProblem P fun shape xs names lhs rhs => do
    let ns := (List.range xs.size).map (s!"X{· + 1}")
    let P' ← withLocalDeclD `γ Γ fun γ => do
      let body := (← mkAppM ``Prod.mk #[lhs, rhs]).replaceFVars xs (← shape.projections γ).toArray
      mkAppOptM ``Problem.bind #[α, Γ, ← mkLambdaFVars #[γ] body]
    let us ← listElems U
    let us' ← us.mapM fun u => openUnifier shape u fun binder zs images => do
      let A := (← whnf u).appFn!.appArg!
      withLocalDeclD `z A fun z => do
        let body := (← shape.tuple images).replaceFVars zs (← binder.projections z).toArray
        mkAppOptM ``Unifier.bind #[Γ, A, ← mkLambdaFVars #[z] body]
    let vars ← xs.mapIdxM fun i x => do
      let sort ← sortOfType st (← inferType x)
      return Json.mkObj [("name", .str s!"X{i + 1}"), ("sort", .str sort)]
    let request := Json.mkObj [
      ("model", .str ((← Dumper.outPath) / "ctor.maude").toString),
      ("vars", .arr vars), ("shape", shape.toJson ns),
      ("lhs", ← encodeTerm st names lhs), ("rhs", ← encodeTerm st names rhs),
      ("answers", .arr (← us.toArray.mapM (encodeUnifier st shape ns)))]
    return (mkAppN ty.getAppFn #[α, Γ, P', ← mkListLit elemTy us'], request)

/-- Prove a goal `complete P U` with a certificate derived by Maude. -/
elab "maude_certify_comp" : tactic => withMainContext do
  let goal ← getMainGoal
  let ty ← zetaReduce (← instantiateMVars (← goal.getType))
  unless ty.isAppOfArity ``Unification.complete 4 do
    throwError "maude_certify_comp: the goal is not `complete P U`"
  let st ← Dumper.model ty.getAppArgs[0]!
  Dumper.write st
  let (target, request) ← prepare st ty
  unless ← isDefEq ty target do
    throwError "maude_certify_comp: could not restate the goal in literal form{indentExpr target}"
  let goal ← goal.replaceTargetDefEq target
  let reply ← callTool tool request
  let script ← IO.ofExcept (reply.getObjValAs? String "script")
  -- generated steps use fixed unfolding hints, some unused at a given step
  let text := "set_option linter.unusedSimpArgs false in\n" ++
    "open Unification Unification.Certification in by\n" ++
    "\n".intercalate ((script.splitOn "\n").map ("  " ++ ·))
  let stx ← IO.ofExcept (Parser.runParserCategory (← getEnv) `term text)
  -- The parsed steps carry positions in `text`, not in the user's file: re-anchor them at
  -- this tactic call (errors point here), and record no editor info for them (otherwise
  -- the editor highlights unrelated parts of the file).
  let info := SourceInfo.fromRef (← getRef)
  let stx := stx.rewriteBottomUp (·.setInfo info)
  replaceMainGoal [goal]
  goal.withContext do
    let pf ← withEnableInfoTree false <| elabTermEnsuringType stx (← goal.getType)
    goal.assign pf
  replaceMainGoal []

end MaudeCertifyComp
