import conPanna.Dumper
import conPanna.Unification.Unification

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

/-- The components of a tuple `z` of shape `s`, as projections. -/
def Shape.projections : Shape → Expr → MetaM (List Expr)
  | .leaf _, z => return [z]
  | .pair l r, z => do
    return (← l.projections (← mkAppM ``Prod.fst #[z])) ++ (← r.projections (← mkAppM ``Prod.snd #[z]))

/-- The components of a value `e` of shape `s`, reducing it to tuples. -/
def Shape.split : Shape → Expr → MetaM (List Expr)
  | .leaf _, e => return [e]
  | .pair l r, e => do
    let e ← whnf e
    unless e.isAppOfArity ``Prod.mk 4 do throwError "maude: {e} is not a tuple"
    return (← l.split e.appFn!.appArg!) ++ (← r.split e.appArg!)

/-- The shape as JSON over `names`: a leaf's name, or a pair `[left, right]`. -/
def Shape.toJson : Shape → List String → Json
  | .leaf _, ns => .str ns.head!
  | .pair l r, ns => .arr #[l.toJson ns, r.toJson (ns.drop l.leaves.length)]

/-! ## Problems and unifiers -/

/-- Open a problem `P : Problem α Γ`: one fresh variable `X1, X2, …` per leaf of `Γ`.
`k` gets the shape of `Γ`, the variables, their names, and the two sides. -/
def openProblem {β} [Inhabited β] (P : Expr) (k : Shape → Array Expr → (FVarId → Option String) →
    Expr → Expr → MetaM β) : MetaM β := do
  let Pw ← whnf P
  unless Pw.isAppOfArity ``Problem.bind 3 do throwError "maude: cannot read the problem {P}"
  let shape ← shapeOf Pw.appFn!.appArg!
  let decls := shape.leaves.toArray.mapIdx fun i t => (s!"X{i + 1}".toName, fun _ => pure t)
  withLocalDeclsD decls fun xs => do
    let names (id : FVarId) : Option String :=
      (xs.findIdx? (· == .fvar id)).map fun i => s!"X{i + 1}"
    let sides ← whnf (mkApp Pw.appArg! (← shape.tuple xs.toList))
    unless sides.isAppOfArity ``Prod.mk 4 do throwError "maude: cannot read the sides of {P}"
    k shape xs names sides.appFn!.appArg! sides.appArg!

/-- `openProblem`, with both sides encoded. -/
def encodeProblem {β} [Inhabited β] (P : Expr) (k : Shape → Array Expr →
    (FVarId → Option String) → Json → Json → MetaM β) : MetaM β :=
  openProblem P fun shape xs names lhs rhs => do
    k shape xs names (← encodeTerm st names lhs) (← encodeTerm st names rhs)

/-- Open a unifier `u : Unifier Γ` of a problem whose context has shape `shape` and
variables named `names`: one fresh variable `#1, #2, …` per leaf of its binder. `k`
gets the binder's shape, its variables, and the images of the problem's variables. -/
def openUnifier {β} [Inhabited β] (shape : Shape) (u : Expr)
    (k : Shape → Array Expr → List Expr → MetaM β) : MetaM β := do
  let uw ← whnf u
  unless uw.isAppOfArity ``Unifier.bind 3 do throwError "maude: cannot read the unifier {u}"
  let binder ← shapeOf uw.appFn!.appArg!
  let decls := binder.leaves.toArray.mapIdx fun i t => (s!"#{i + 1}".toName, fun _ => pure t)
  withLocalDeclsD decls fun zs => do
    k binder zs (← shape.split (mkApp uw.appArg! (← binder.tuple zs.toList)))

/-- A unifier as JSON: `{"sub": {X_i: image}, "binder": shape over #1, #2, …}`. -/
def encodeUnifier (shape : Shape) (names : List String) (u : Expr) : MetaM Json :=
  openUnifier shape u fun binder zs images => do
    let zname (id : FVarId) : Option String :=
      (zs.findIdx? (· == .fvar id)).map fun i => s!"#{i + 1}"
    let sub ← (names.zip images).mapM fun (n, t) => return (n, ← encodeTerm st zname t)
    return Json.mkObj [("sub", Json.mkObj sub),
      ("binder", binder.toJson ((List.range binder.leaves.length).map (s!"#{· + 1}")))]

/-! ## Tools -/

/-- Run producer tool `tool` (relative to the project root) on a JSON request. Each call
has its own files `<tool>-<id>.*` in `outDir` (proofs are elaborated in parallel);
they are removed on success and kept on failure, for inspection. -/
def callTool (tool : System.FilePath) (request : Json) : MetaM Json := do
  let root ← Dumper.projectRoot
  let out ← Dumper.outPath
  let stem := s!"{tool.fileStem.getD "tool"}-{hash request.compress}-{← IO.monoNanosNow}"
  let req := out / s!"{stem}.json"
  IO.FS.writeFile req request.compress
  let res ← IO.Process.output
    { cmd := "python3", args := #[(root / tool).toString, req.toString], cwd := root }
  unless res.exitCode == 0 do
    throwError "maude: {tool} failed (files kept in {out / stem}.*):\n{res.stderr}"
  for ext in ["json", "maude", "deriv"] do
    let f := out / s!"{stem}.{ext}"
    if ← f.pathExists then IO.FS.removeFile f
  IO.ofExcept (Json.parse res.stdout)

end MaudeAdapter
