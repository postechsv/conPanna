import Tiny.conPanna.Dumper
import Tiny.conPanna.Narrowing.Narrowing

/-!
`maude_unify` closes a goal `unifiers_R_P R P` with the unifiers Maude computes.

For every (rule, patch) cell of `R` and `P` it instantiates both binders with fresh
variables, translates `r.lhs =? p.state` into the dumped model `CTOR` (see
`Dumper.lean`), asks `producer/tools/unify.py` for all unifiers, and translates them
back into `Unifier.bind fun x => (rule tuple, patch tuple)`.

States of rules and patterns are constructor terms: constructors of the model, `0`,
`n + k` and numerals on `Nat`, and `∅`, `{a}`, `+` on ACU sorts. Anything else is
rejected. Nothing here is trusted: the unifiers are data, certified separately
(`certificates_R_P`).
-/

namespace MaudeUnify

open Lean Meta Elab Tactic Expresso Narrowing Unification

/-- The Python side, relative to the project root. -/
def tool : System.FilePath := "producer/tools/unify.py"

variable (st : Dumper.State)

/-- The sort of a Lean type, up to reducible unfolding (`inferType` may unfold `abbrev`s). -/
def sortOfType (t : Expr) : MetaM String := do
  for s in st.sorts do
    if ← withReducible (isDefEq s.type t) then return s.name
  (Dumper.sortOf t).run' st

def sortInfo (s : String) : MetaM Dumper.Sort' := do
  let some i := st.sorts.find? (·.name == s) | throwError "maude_unify: unknown sort {s}"
  return i

private def natLit? (e : Expr) : Option Nat :=
  if let some n := e.rawNatLit? then some n
  else if e.isAppOfArity ``OfNat.ofNat 3 then e.appFn!.appArg!.rawNatLit?
  else none

private def succs (k : Nat) (t : Json) : Json :=
  k.repeat (fun t => Json.mkObj [("op", .str "s_"), ("sort", .str "Nat"), ("args", .arr #[t])]) t

/-- A constructor term as JSON (`unify.py`'s format); `names` names the variables. -/
partial def toJson (names : FVarId → Option String) (e : Expr) : MetaM Json := do
  let e ← instantiateMVars e
  let s ← sortOfType st (← inferType e)
  let node (op : String) (args : Array Json) : Json :=
    Json.mkObj [("op", .str op), ("sort", .str s), ("args", .arr args)]
  let go := toJson names
  if let .fvar id := e then
    let some n := names id | throwError "maude_unify: unexpected variable {e}"
    return Json.mkObj [("var", .str n), ("sort", .str s)]
  match (← sortInfo st s).kind with
  | .acu _ =>
    if e.isAppOfArity ``HAdd.hAdd 6 || e.isAppOfArity ``ACU.plus 3 then
      return node "__" #[← go e.appFn!.appArg!, ← go e.appArg!]
    if e.isAppOfArity ``Singleton.singleton 4 || e.isAppOfArity ``ACU.elem 2 then
      return ← go e.appArg!
    if e.isAppOfArity ``EmptyCollection.emptyCollection 2 || e.isAppOfArity ``ACU.unit 1 then
      return node "none" #[]
  | .nat =>
    if let some k := natLit? e then return succs k (node "0" #[])
    if e.isAppOfArity ``HAdd.hAdd 6 || e.isAppOfArity ``Nat.add 2 then
      if let some k := natLit? e.appArg! then return succs k (← go e.appFn!.appArg!)
    if e.isAppOfArity ``Nat.succ 1 then return succs 1 (← go e.appArg!)
    if e.isConstOf ``Nat.zero then return node "0" #[]
  | .bool =>
    if e.isConstOf ``Bool.true then return node "true" #[]
    if e.isConstOf ``Bool.false then return node "false" #[]
  | .ind _ =>
    if let some c := e.getAppFn.constName? then
      if let some op := st.ops.find? (·.origin == c.toString) then
        return node op.name (← e.getAppArgs.mapM go)
  let e' ← whnfR e
  if e' != e then return ← go e'
  throwError "maude_unify: {e} is not a constructor term"

/-- Strip a chain of `k` successors. -/
partial def peel (j : Json) (k : Nat) : Json × Nat :=
  match j.getObjValAs? String "op", j.getObjValAs? (Array Json) "args" with
  | .ok "s_", .ok #[a] => peel a (k + 1)
  | _, _ => (j, k)

/-- A JSON term from `unify.py` as a Lean term of type `T`; `vars` gives Maude's variables. -/
partial def ofJson (vars : String → Option Expr) (j : Json) (T : Expr) : MetaM Expr := do
  if let .ok n := j.getObjValAs? String "var" then
    let some x := vars n | throwError "maude_unify: unknown variable {n} in Maude's reply"
    return x
  let op ← IO.ofExcept (j.getObjValAs? String "op")
  let args ← IO.ofExcept (j.getObjValAs? (Array Json) "args")
  let s ← sortOfType st T
  match (← sortInfo st s).kind, op with
  | .acu _, "__" => mkAppM ``HAdd.hAdd #[← ofJson vars args[0]! T, ← ofJson vars args[1]! T]
  | .acu _, "none" => mkAppOptM ``EmptyCollection.emptyCollection #[T, none]
  | .acu e, _ =>
    let E := (← sortInfo st e).type
    mkAppOptM ``Singleton.singleton #[E, T, none, ← ofJson vars j E]
  | .nat, _ =>
    -- `s_` chains become `t + k`, or a numeral on `0`
    let (base, k) := peel j 0
    if base.getObjValAs? String "op" matches .ok "0" then return mkNatLit k
    let b ← ofJson vars base T
    if k == 0 then return b
    mkAppM ``HAdd.hAdd #[b, mkNatLit k]
  | .bool, "true" => return mkConst ``Bool.true
  | .bool, "false" => return mkConst ``Bool.false
  | .ind _, _ =>
    let some o := st.ops.find? (·.name == op) | throwError "maude_unify: unknown operator {op}"
    let mut f := mkConst o.origin.toName
    let mut fty ← inferType f
    for a in args do
      let .forallE _ dom body _ := fty | throwError "maude_unify: arity mismatch for {op}"
      let x ← ofJson vars a dom
      f := mkApp f x
      fty := body.instantiate1 x
    return f
  | _, _ => throwError "maude_unify: unexpected operator {op} at sort {s}"

/-- Component types of a binder type `A₁ × (A₂ × …)`. -/
partial def components (A : Expr) : MetaM (List Expr) := do
  let A' ← whnfR A
  if A'.isAppOfArity ``Prod 2 then return A'.appFn!.appArg! :: (← components A'.appArg!)
  return [A]

/-- The right-nested tuple of `xs`. -/
def tuple : List Expr → MetaM Expr
  | [] => return mkConst ``Unit.unit
  | [x] => return x
  | x :: xs => do mkAppM ``Prod.mk #[x, ← tuple xs]

/-- The `i`-th component of a right-nested tuple `z` with `n` components. -/
def proj (z : Expr) : Nat → Nat → MetaM Expr
  | _, 1 => return z
  | 0, _ => mkAppM ``Prod.fst #[z]
  | i + 1, n => do proj (← mkAppM ``Prod.snd #[z]) i (n - 1)

def runTool (problem : Json) : MetaM (Array Json) := do
  let root ← Dumper.projectRoot
  let out ← Dumper.outPath
  let req := out / "unify-request.json"
  IO.FS.writeFile req (Json.mkObj [("model", .str (out / "ctor.maude").toString),
    ("problems", .arr #[problem])]).compress
  let out ← IO.Process.output
    { cmd := "python3", args := #[(root / tool).toString, req.toString], cwd := root }
  unless out.exitCode == 0 do throwError "maude_unify: unify.py failed:\n{out.stderr}"
  let reply ← IO.ofExcept (Json.parse out.stdout)
  let all ← IO.ofExcept (reply.getObjValAs? (Array (Array Json)) "unifiers")
  return all[0]!

/-- The variables of a JSON term, with their sorts. -/
partial def varsOf (j : Json) : List (String × String) :=
  match j.getObjValAs? String "var", j.getObjValAs? String "sort" with
  | .ok n, .ok s => [(n, s)]
  | _, _ => match j.getObjValAs? (Array Json) "args" with
    | .ok args => args.toList.flatMap varsOf
    | .error _ => []

/-- The unifiers of one cell, as a value of `unifiers_r_p r p`. -/
def cell (r p : Expr) : MetaM Expr := do
  let rw ← whnf r
  let pw ← whnf p
  unless rw.isAppOfArity ``Rule.bind 3 && pw.isAppOfArity ``Patch.bind 3 do
    throwError "maude_unify: cannot read the binder of {r} or {p}"
  let (A, f) := (rw.appFn!.appArg!, rw.appArg!)
  let (B, g) := (pw.appFn!.appArg!, pw.appArg!)
  let elemTy ← do
    let t ← whnfR (← mkAppM ``unifiers_r_p #[r, p])
    pure t.appArg!
  let Γ ← mkAppM ``Prod #[A, B]
  let tsA ← components A
  let tsB ← components B
  let decls := (tsA.zipIdx.map fun (t, i) => (s!"r{i + 1}".toName, fun _ => pure t)) ++
    (tsB.zipIdx.map fun (t, i) => (s!"p{i + 1}".toName, fun _ => pure t))
  withLocalDeclsD decls.toArray fun vs => do
    let (xs, ys) := vs.toList.splitAt tsA.length
    let names (id : FVarId) : Option String :=
      (vs.findIdx? (· == .fvar id)).map fun i =>
        if i < tsA.length then s!"r{i + 1}" else s!"p{i + 1 - tsA.length}"
    let lhs ← mkAppM ``RuleBody.lhs #[mkApp f (← tuple xs)]
    let state ← mkAppM ``PatchBody.state #[mkApp g (← tuple ys)]
    let problem := Json.mkObj [("lhs", ← toJson st names lhs), ("rhs", ← toJson st names state)]
    let substs ← runTool problem
    let us ← substs.mapM fun sub => do
      -- Maude's fresh variables #n, and original variables the substitution leaves free
      let mut fresh : Array (String × Expr) := #[]
      for (n, t) in (← collectVars sub) do
        unless fresh.any (·.1 == n) do fresh := fresh.push (n, (← sortInfo st t).type)
      for (v, i) in vs.toList.zipIdx do
        let n := (names v.fvarId!).get!
        if (sub.getObjVal? n).toOption.isNone then fresh := fresh.push (n, ← inferType vs[i]!)
      let fresh' := fresh.qsort (·.1 < ·.1)
      withLocalDeclsD (fresh'.map fun (n, t) => (n.toName, fun _ => pure t)) fun zs => do
        let lookup (n : String) : Option Expr := (fresh'.findIdx? (·.1 == n)).map (zs[·]!)
        let val (x : Expr) : MetaM Expr := do
          let n := (names x.fvarId!).get!
          match sub.getObjVal? n with
          | .ok t => ofJson st lookup t (← inferType x)
          | .error _ => return (lookup n).get!
        let body ← mkAppM ``Prod.mk #[← tuple (← xs.mapM val), ← tuple (← ys.mapM val)]
        let Z ← if zs.isEmpty then pure (mkConst ``Unit) else
          mkProdTy (← zs.toList.mapM inferType)
        withLocalDeclD `x Z fun z => do
          let projs ← (List.range zs.size).mapM fun i => proj z i zs.size
          let body := body.replaceFVars zs projs.toArray
          mkAppOptM ``Unifier.bind #[Γ, Z, ← mkLambdaFVars #[z] body]
    mkListLit elemTy us.toList
where
  collectVars (sub : Json) : MetaM (List (String × String)) := do
    let .ok obj := sub.getObj? | return []
    return obj.toList.flatMap fun (_, t) => varsOf t
  mkProdTy : List Expr → MetaM Expr
    | [] => return mkConst ``Unit
    | [t] => return t
    | t :: ts => do mkAppM ``Prod #[t, ← mkProdTy ts]

/-- A value of `unifiers_R_P R P`, following the trees of `R` and `P`. -/
partial def forSystem (unit : Expr) (R P : Expr) : MetaM Expr := do
  let R ← whnf R
  if R.isAppOfArity ``System.empty 1 then return unit
  if R.isAppOfArity ``System.choice 3 then
    return ← mkAppM ``Prod.mk #[← forSystem unit R.appFn!.appArg! P, ← forSystem unit R.appArg! P]
  if R.isAppOfArity ``System.rule 2 then return ← forRule unit R.appArg! P
  throwError "maude_unify: cannot read the system {R}"
where
  forRule (unit r P : Expr) : MetaM Expr := do
    let P ← whnf P
    if P.isAppOfArity ``Pattern.bott 1 then return unit
    if P.isAppOfArity ``Pattern.disj 3 then
      return ← mkAppM ``Prod.mk #[← forRule unit r P.appFn!.appArg!, ← forRule unit r P.appArg!]
    if P.isAppOfArity ``Pattern.patch 2 then return ← cell st r P.appArg!
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
