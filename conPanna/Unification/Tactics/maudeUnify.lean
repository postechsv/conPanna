import conPanna.Unification.Tactics.maudeAdapter
import conPanna.Narrowing.Narrowing

/-!
`maude_unify` closes a goal `unifiers_R_P R P` with the unifiers Maude computes.

For every (rule, patch) cell of `R` and `P` it encodes the cell's problem
`mayFire r p` (`maudeAdapter.lean`), asks `producer/tools/unify.py` for all
unifiers, and decodes each into `Unifier.bind fun x => γ`. So the problem Maude
solves is exactly the one later certified (`certificates_r_p`). Nothing here is
trusted: the unifiers are data.
-/

namespace MaudeUnify

open Lean Meta Elab Tactic Expresso Narrowing Unification MaudeAdapter

/-- The Python side, relative to the project root. -/
def tool : System.FilePath := "producer/tools/unify.py"

variable (st : Dumper.State)

/-- The unifiers of problem `P : Problem α Γ`, as a list of `Unifier Γ`. -/
def unifiersOf (P : Expr) : MetaM Expr := do
  let Γ := (← whnfR (← inferType P)).appArg!
  let v ← getDecLevel Γ
  let elemTy := mkApp (mkConst ``Unifier [v, v]) Γ
  encodeProblem st P fun shape xs names lhs rhs => do
    let reply ← callTool tool (Json.mkObj [
      ("model", .str ((← Dumper.outPath) / "ctor.maude").toString),
      ("problems", .arr #[Json.mkObj [("lhs", lhs), ("rhs", rhs)]])])
    let substs := (← IO.ofExcept (reply.getObjValAs? (Array (Array Json)) "unifiers"))[0]!
    let us ← substs.mapM fun sub => do
      -- the unifier's variables: Maude's fresh #n, and originals the substitution leaves free
      let mut fresh : Array (String × Expr) := #[]
      let .ok obj := sub.getObj? | throwError "maude_unify: bad substitution {sub}"
      for (n, s) in obj.toList.flatMap (varsOf ·.2) do
        unless fresh.any (·.1 == n) do fresh := fresh.push (n, (← sortInfo st s).type)
      for x in xs do
        let n := (names x.fvarId!).get!
        if (sub.getObjVal? n).toOption.isNone then fresh := fresh.push (n, ← inferType x)
      let vars := fresh.qsort (·.1 < ·.1)
      withLocalDeclsD (vars.map fun (n, t) => (n.toName, fun _ => pure t)) fun zs => do
        let lookup (n : String) : Option Expr := (vars.findIdx? (·.1 == n)).map (zs[·]!)
        let vals ← xs.toList.mapM fun x => do
          let n := (names x.fvarId!).get!
          match sub.getObjVal? n with
          | .ok t => decodeTerm st lookup t (← inferType x)
          | .error _ => return (lookup n).get!
        let body ← shape.tuple vals
        let Z ← tupleType (← zs.toList.mapM inferType)
        withLocalDeclD `x Z fun z => do
          let projs ← (List.range zs.size).mapM fun i => proj z i zs.size
          let body := body.replaceFVars zs projs.toArray
          mkAppOptM ``Unifier.bind #[Γ, Z, ← mkLambdaFVars #[z] body]
    mkListLit elemTy us.toList

/-- A value of `unifiers_R_P R P`: for each rule of `R` (a list), for each patch of
`P` (a list), the unifiers of that cell; `unit` closes each list. -/
partial def forSystem (unit : Expr) (R P : Expr) : MetaM Expr := do
  let R ← whnf R
  if R.isAppOfArity ``List.nil 1 then return unit
  if R.isAppOfArity ``List.cons 3 then
    return ← mkAppM ``Prod.mk #[← forRule unit R.appFn!.appArg! P, ← forSystem unit R.appArg! P]
  throwError "maude_unify: cannot read the system {R}"
where
  forRule (unit r P : Expr) : MetaM Expr := do
    let P ← whnf P
    if P.isAppOfArity ``List.nil 1 then return unit
    if P.isAppOfArity ``List.cons 3 then
      return ← mkAppM ``Prod.mk
        #[← unifiersOf st (← mkAppM ``mayFire #[r, P.appFn!.appArg!]), ← forRule unit r P.appArg!]
    throwError "maude_unify: cannot read the pattern {P}"

/-- Close a goal `unifiers_R_P R P` with the unifiers Maude computes for every cell. -/
elab "maude_unify" : tactic => withMainContext do
  let goal ← getMainGoal
  let ty ← instantiateMVars (← goal.getType)
  unless ty.isAppOfArity ``unifiers_R_P 3 do
    throwError "maude_unify: the goal is not `unifiers_R_P R P`"
  let α := ty.getArg! 0
  let st ← Dumper.model α
  Dumper.write st
  let unit := mkConst ``PUnit.unit [mkLevelSucc (← getLevel α)]
  let v ← forSystem st unit (ty.getArg! 1) (ty.getArg! 2)
  unless ← isDefEq (← inferType v) ty do
    throwError "maude_unify: built a value of the wrong type{indentExpr (← inferType v)}"
  goal.assign v
  replaceMainGoal []

end MaudeUnify
