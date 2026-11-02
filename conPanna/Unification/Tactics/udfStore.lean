import conPanna.Unification.Tactics.maudeAdapter
import conPanna.Unification.Certification.UdfTactics
import conPanna.Unification.LaterAx

/-!
Completeness certificates kept from narrowing to certification.

When `narrow` unifies a cell, the instrumented Maude also returns the cell's completeness
certificate (a UDF derivation). It is stored under the claim's key, a hash of the claim
`complete P U` in literal form (the request `prepare` builds, with the
model named by its file); the obligation stating the same claim later finds it by the same
key, so certification needs no Maude call. Certificates are untrusted data: a missing,
stale or wrong one makes certification fail or fall back, never succeed wrongly.
-/

namespace UdfStore

open Lean Meta Elab Tactic Unification MaudeAdapter

/-- The elements of a list literal. -/
partial def listElems (l : Expr) : MetaM (List Expr) := do
  let l ← whnf l
  if l.isAppOfArity ``List.nil 1 then return []
  if l.isAppOfArity ``List.cons 3 then return l.appFn!.appArg! :: (← listElems l.appArg!)
  throwError "udf: {l} is not a list of unifiers"

/-- The literal form of goal `complete P U`, and its request (`producer/tools/udf.py`). -/
def prepare (st : Dumper.State) (ty : Expr) : MetaM (Expr × Json) := do
  let #[α, Γ, P, U] := ty.getAppArgs
    | throwError "udf: the goal is not `complete P U`"
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
      ("model", .str (← Dumper.modelPath st).toString),
      ("vars", .arr vars), ("shape", shape.toJson ns),
      ("lhs", ← encodeTerm st names lhs), ("rhs", ← encodeTerm st names rhs),
      ("answers", .arr (← us.toArray.mapM (encodeUnifier st shape ns)))]
    return (mkAppN ty.getAppFn #[α, Γ, P', ← mkListLit elemTy us'], request)

/-- The claim `ty = complete P U` in literal form, its request, and its key. -/
def claim (st : Dumper.State) (ty : Expr) : MetaM (Expr × Json × String) := do
  let (target, request) ← prepare st ty
  let model := ((request.getObjValAs? String "model").toOption.getD "")
  let name := (System.FilePath.mk model).fileName.getD model
  let key := toString (hash (request.setObjVal! "model" (.str name)).compress)
  return (target, request, key)

def path (key : String) : CoreM System.FilePath :=
  return (← Dumper.outPath) / "udf" / s!"{key}.udf"

def store (key text : String) : CoreM Unit := do
  let p ← path key
  if let some d := p.parent then IO.FS.createDirAll d
  IO.FS.writeFile p text

def load? (key : String) : CoreM (Option String) := do
  let p ← path key
  if ← p.pathExists then return some (← IO.FS.readFile p) else return none

/-- Close a certificate goal of narrowing: `complete P U` by `laterAx key P U`,
`sound P U` by `laterSoundAx P U`, anything else like `later`. -/
elab "later_claim" : tactic => withMainContext do
  let goal ← getMainGoal
  let ty ← zetaReduce (← instantiateMVars (← goal.getType))
  if ty.hasFVar then
    throwError "later_claim: the statement depends on local variables{indentExpr ty}"
  if ty.isAppOfArity ``Unification.complete 4 then
    let st ← Dumper.model ty.getAppArgs[0]!
    let (_, _, key) ← claim st ty
    goal.assign (← mkAppM ``laterAx #[mkStrLit key, ty.getArg! 2, ty.getArg! 3])
  else if ty.isAppOfArity ``Unification.sound 4 then
    goal.assign (← mkAppM ``laterSoundAx #[ty.getArg! 2, ty.getArg! 3])
  else
    goal.assign (← mkSorry ty false)
  replaceMainGoal []

end UdfStore
