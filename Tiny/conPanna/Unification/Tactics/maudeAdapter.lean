import Tiny.conPanna.Dumper
import Tiny.conPanna.Unification.Unification

/-!
The adapter between Lean goals and the producer's Maude tools: it encodes problems
and terms of the constructor model (`Dumper.lean`) as JSON terms, decodes Maude's
terms back into Lean, and runs a tool on a JSON request.

JSON terms are `{"var": name, "sort": S}` or `{"op": name, "sort": S, "args": [...]}`,
over the operator names of the dumped `CTOR`. Encodable terms are constructor terms:
constructors of the model, `0`, `n + k` and numerals on `Nat`, and `∅`, `{a}`, `+`
on ACU sorts. Nothing here is trusted: tools return data or proof text that Lean checks.
-/

namespace MaudeAdapter

open Lean Meta Unification

variable (st : Dumper.State)

/-- The sort of a Lean type, up to reducible unfolding (`inferType` may unfold `abbrev`s). -/
def sortOfType (t : Expr) : MetaM String := do
  for s in st.sorts do
    if ← withReducible (isDefEq s.type t) then return s.name
  (Dumper.sortOf t).run' st

def sortInfo (s : String) : MetaM Dumper.Sort' := do
  let some i := st.sorts.find? (·.name == s) | throwError "maude: unknown sort {s}"
  return i

/-! ## Terms -/

private def natLit? (e : Expr) : Option Nat :=
  if let some n := e.rawNatLit? then some n
  else if e.isAppOfArity ``OfNat.ofNat 3 then e.appFn!.appArg!.rawNatLit?
  else none

private def succs (k : Nat) (t : Json) : Json :=
  k.repeat (fun t => Json.mkObj [("op", .str "s_"), ("sort", .str "Nat"), ("args", .arr #[t])]) t

/-- A constructor term as a JSON term; `names` names its variables. -/
partial def encodeTerm (names : FVarId → Option String) (e : Expr) : MetaM Json := do
  let e ← instantiateMVars e
  let s ← sortOfType st (← inferType e)
  let node (op : String) (args : Array Json) : Json :=
    Json.mkObj [("op", .str op), ("sort", .str s), ("args", .arr args)]
  let go := encodeTerm names
  if let .fvar id := e then
    let some n := names id | throwError "maude: unexpected variable {e}"
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
  throwError "maude: {e} is not a constructor term"

/-- Strip a chain of `k` successors. -/
partial def peel (j : Json) (k : Nat) : Json × Nat :=
  match j.getObjValAs? String "op", j.getObjValAs? (Array Json) "args" with
  | .ok "s_", .ok #[a] => peel a (k + 1)
  | _, _ => (j, k)

/-- A JSON term as a Lean term of type `T`; `vars` gives its variables. -/
partial def decodeTerm (vars : String → Option Expr) (j : Json) (T : Expr) : MetaM Expr := do
  if let .ok n := j.getObjValAs? String "var" then
    let some x := vars n | throwError "maude: unknown variable {n} in a reply"
    return x
  let op ← IO.ofExcept (j.getObjValAs? String "op")
  let args ← IO.ofExcept (j.getObjValAs? (Array Json) "args")
  let s ← sortOfType st T
  match (← sortInfo st s).kind, op with
  | .acu _, "__" => mkAppM ``HAdd.hAdd #[← decodeTerm vars args[0]! T, ← decodeTerm vars args[1]! T]
  | .acu _, "none" => mkAppOptM ``EmptyCollection.emptyCollection #[T, none]
  | .acu e, _ =>
    let E := (← sortInfo st e).type
    mkAppOptM ``Singleton.singleton #[E, T, none, ← decodeTerm vars j E]
  | .nat, _ =>
    -- `s_` chains become `t + k`, or a numeral on `0`
    let (base, k) := peel j 0
    if base.getObjValAs? String "op" matches .ok "0" then return mkNatLit k
    let b ← decodeTerm vars base T
    if k == 0 then return b
    mkAppM ``HAdd.hAdd #[b, mkNatLit k]
  | .bool, "true" => return mkConst ``Bool.true
  | .bool, "false" => return mkConst ``Bool.false
  | .ind _, _ =>
    let some o := st.ops.find? (·.name == op) | throwError "maude: unknown operator {op}"
    let mut f := mkConst o.origin.toName
    let mut fty ← inferType f
    for a in args do
      let .forallE _ dom body _ := fty | throwError "maude: arity mismatch for {op}"
      let x ← decodeTerm vars a dom
      f := mkApp f x
      fty := body.instantiate1 x
    return f
  | _, _ => throwError "maude: unexpected operator {op} at sort {s}"

/-- The variables of a JSON term, with their sorts. -/
partial def varsOf (j : Json) : List (String × String) :=
  match j.getObjValAs? String "var", j.getObjValAs? String "sort" with
  | .ok n, .ok s => [(n, s)]
  | _, _ => match j.getObjValAs? (Array Json) "args" with
    | .ok args => args.toList.flatMap varsOf
    | .error _ => []

/-! ## Tuples
Variable contexts are nested tuples, e.g. `(Nat × Nat × ProcSet) × (Nat × ProcSet)`
for a (rule, patch) cell. A `Shape` records the nesting; its leaves are variables. -/

inductive Shape where
  | leaf (type : Expr)
  | pair (left right : Shape)

partial def shapeOf (T : Expr) : MetaM Shape := do
  let T' ← whnf T
  if T'.isAppOfArity ``Prod 2 then
    return .pair (← shapeOf T'.appFn!.appArg!) (← shapeOf T'.appArg!)
  return .leaf T

def Shape.leaves : Shape → List Expr
  | .leaf t => [t]
  | .pair l r => l.leaves ++ r.leaves

/-- The tuple of shape `s` with leaves `xs` (in order). -/
def Shape.tuple : Shape → List Expr → MetaM Expr
  | .leaf _, xs => return xs.head!
  | .pair l r, xs => do
    let n := l.leaves.length
    mkAppM ``Prod.mk #[← l.tuple (xs.take n), ← r.tuple (xs.drop n)]

/-- The right-nested tuple type of `ts`, `Unit` when empty. -/
def tupleType : List Expr → MetaM Expr
  | [] => return mkConst ``Unit
  | [t] => return t
  | t :: ts => do mkAppM ``Prod #[t, ← tupleType ts]

/-- The `i`-th component of a right-nested tuple `z` with `n` components. -/
def proj (z : Expr) : Nat → Nat → MetaM Expr
  | _, 1 => return z
  | 0, _ => mkAppM ``Prod.fst #[z]
  | i + 1, n => do proj (← mkAppM ``Prod.snd #[z]) i (n - 1)

/-! ## Problems -/

/-- Open a problem `P : Problem α Γ`: one fresh variable `X1, X2, …` per leaf of `Γ`,
and both sides encoded. `k` gets the shape of `Γ`, the variables, their names, and
the encoded sides. -/
def encodeProblem {β} [Inhabited β] (P : Expr) (k : Shape → Array Expr → (FVarId → Option String) →
    Json → Json → MetaM β) : MetaM β := do
  let Pw ← whnf P
  unless Pw.isAppOfArity ``Problem.bind 3 do throwError "maude: cannot read the problem {P}"
  let shape ← shapeOf Pw.appFn!.appArg!
  let decls := shape.leaves.toArray.mapIdx fun i t => (s!"X{i + 1}".toName, fun _ => pure t)
  withLocalDeclsD decls fun xs => do
    let names (id : FVarId) : Option String :=
      (xs.findIdx? (· == .fvar id)).map fun i => s!"X{i + 1}"
    let sides ← whnf (mkApp Pw.appArg! (← shape.tuple xs.toList))
    unless sides.isAppOfArity ``Prod.mk 4 do throwError "maude: cannot read the sides of {P}"
    k shape xs names (← encodeTerm st names sides.appFn!.appArg!) (← encodeTerm st names sides.appArg!)

/-! ## Tools -/

/-- Run producer tool `tool` (relative to the project root) on a JSON request. -/
def callTool (tool : System.FilePath) (request : Json) : MetaM Json := do
  let root ← Dumper.projectRoot
  let out ← Dumper.outPath
  let req := out / s!"{tool.fileStem.getD "tool"}-request.json"
  IO.FS.writeFile req request.compress
  let res ← IO.Process.output
    { cmd := "python3", args := #[(root / tool).toString, req.toString], cwd := root }
  unless res.exitCode == 0 do throwError "maude: {tool} failed:\n{res.stderr}"
  IO.ofExcept (Json.parse res.stdout)

end MaudeAdapter
