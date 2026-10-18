import Lean
import Tiny.Expresso.ACU

/-!
Dump the constructor model of a state type as the Maude module the certification
producer works in.

  `#dump_model Conf`  writes `ctor.maude` and `ctor.json` into `outDir` below.

`ctor.maude` holds a hardcoded prelude for `Nat` (when used) and `fmod CTOR`: one
sort per type reachable from the state type through constructor fields, and one
`ctor` operator per constructor. `ctor.json` is the name table the tools read:
each Maude operator's Lean counterpart, and the ACU sorts.

| Lean | Maude |
|---|---|
| `inductive T` / `structure T` (no parameters) | `sort T`, one `ctor` op per constructor; a structure's op is named `T` |
| `abbrev S := ACU E` | `sort S`, `subsort E < S`, `none : -> S`, `__ : S S -> S [assoc comm id: none]` |
| `Nat` | prelude `NAT-CTOR`: `0`, `s_` (Peano). Maude's built-in `NAT` is not used: its unification is incomplete, e.g. `X + 1 =? Y + 2` misses `X = 1, Y = 0` |
| `Bool` | Maude's built-in `Bool` (`true`, `false`), included by default |

Anything else (parameters, indices, `Prop` or function fields, an ACU sort whose
elements are bags, an unnamed `ACU E`) is rejected with the offending type named.
-/

namespace Dumper

/-- Where `#dump_model` writes, relative to the project root. The producer's tools
read the model from here; change it at will. -/
def outDir : System.FilePath := "producer/.cache"

open Lean Meta Elab Command

/-- One Maude sort of the model. -/
inductive Kind where
  | nat | bool
  | acu (elem : String)
  | ind (name : Name)

structure Sort' where
  name : String
  kind : Kind
  /-- The Lean type this sort stands for. -/
  type : Expr

structure Op where
  name : String
  args : List String
  result : String
  attrs : String := "ctor"
  /-- Lean counterpart; `{i}` is the i-th argument. -/
  lean : String
  /-- Lean declaration, for the comment in `ctor.maude`. -/
  origin : String := ""

structure State where
  sorts : Array Sort' := #[]
  ops : Array Op := #[]
  todo : Array Name := #[]

abbrev M := StateT State MetaM

private def maudeSafe (s : String) : Bool :=
  !s.isEmpty && s.all fun c => !c.isWhitespace && !"()[]{},.`\"".contains c

private def last : Name → String
  | .str _ s => s
  | n => n.toString

private def sortName (n : Name) : MetaM String := do
  let s := last n
  unless maudeSafe s do throwError "dump: type name {n} is not a valid Maude sort name"
  return s

/-- The Maude sort of a Lean type, registering it on first sight. -/
partial def sortOf (t : Expr) : M String := do
  let t := (← instantiateMVars t).cleanupAnnotations
  if t.isConstOf ``Nat then return (← add "Nat" .nat t)
  if t.isConstOf ``Bool then return (← add "Bool" .bool t)
  let some c := t.getAppFn.constName? | throwError "dump: unsupported type {t}"
  if c == ``ACU then throwError "dump: name the ACU sort with an abbrev, e.g. `abbrev S := {t}`"
  match (← getEnv).find? c with
  | some (.inductInfo info) =>
    unless info.numParams == 0 && info.numIndices == 0 && t.isConst do
      throwError "dump: {c} has parameters or indices"
    let s ← sortName c
    if !(← get).sorts.any (·.name == s) then
      modify fun st => { st with todo := st.todo.push c }
    add s (.ind c) t
  | some (.defnInfo info) =>
    unless t.isConst do throwError "dump: unsupported type {t}"
    let v := info.value
    if v.getAppFn.isConstOf ``ACU && v.getAppNumArgs == 1 then
      let e ← sortOf v.appArg!
      if (← get).sorts.any fun s => s.name == e && s.kind matches .acu _ then
        throwError "dump: {c} is a bag of bags; wrap the inner bag in a constructor"
      add (← sortName c) (.acu e) t
    else
      sortOf v
  | _ => throwError "dump: unsupported type {t}"
where
  add (s : String) (k : Kind) (t : Expr) : M String := do
    match (← get).sorts.find? (·.name == s) with
    | some _ => return s
    | none =>
      modify fun st => { st with sorts := st.sorts.push ⟨s, k, t⟩ }
      return s

/-- The constructors of an inductive type, as Maude operators. -/
def ctorsOf (c : Name) : M Unit := do
  let env ← getEnv
  let some (.inductInfo info) := env.find? c | unreachable!
  let s ← sortName c
  let isStruct := isStructure env c
  for k in info.ctors do
    let some (.ctorInfo ci) := env.find? k | unreachable!
    let args ← forallTelescope ci.type fun xs _ => xs.toList.mapM fun x => do
      let ty ← inferType x
      if (← isProp ty) || ty.isSort || ty.isForall then
        throwError "dump: field of {k} has unsupported type {ty}"
      return ty
    let args ← args.mapM sortOf
    let name := if isStruct then s else last k
    unless maudeSafe name do throwError "dump: constructor name {k} is not a valid Maude operator name"
    let op : Op := { name, args, result := s, lean := k.toString, origin := k.toString }
    modify fun st => { st with ops := st.ops.push op }

def collect (root : Expr) : M Unit := do
  discard <| sortOf root
  while true do
    let st ← get
    let some c := st.todo.back? | break
    set { st with todo := st.todo.pop }
    ctorsOf c

/-- Operators of the ACU sorts and the prelude; then check that names do not clash. -/
def finish : M Unit := do
  for s in (← get).sorts do
    match s.kind with
    | .acu _ =>
      let unit : Op := { name := "none", args := [], result := s.name, lean := "∅" }
      let union : Op := { name := "__", args := [s.name, s.name], result := s.name,
                          attrs := "ctor assoc comm id: none", lean := "{0} + {1}" }
      modify fun st => { st with ops := st.ops ++ #[unit, union] }
    | _ => pure ()
  let ops := (← get).ops
  for o in ops do
    if ops.any fun o' => o'.name == o.name && o'.result != o.result && o.name != "none" && o.name != "__" then
      throwError "dump: operator name {o.name} is used by two constructors ({o.origin})"
    if ["0", "s_", "true", "false", "none", "__"].contains o.name && o.origin != "" then
      throwError "dump: constructor {o.origin} clashes with a reserved Maude name"

def natPrelude : String := "fmod NAT-CTOR is
  sort Nat .
  op 0 : -> Nat [ctor] .
  op s_ : Nat -> Nat [ctor] .
endfm
"

def render (st : State) : String := Id.run do
  let sorts := st.sorts.filter fun s => !(s.kind matches .nat | .bool)
  let mut out := "*** Generated by #dump_model; the certification producer works in CTOR.\n\n"
  let usesNat := st.sorts.any (·.kind matches .nat)
  if usesNat then out := out ++ natPrelude ++ "\n"
  out := out ++ "fmod CTOR is\n"
  if usesNat then out := out ++ "  protecting NAT-CTOR .\n"
  out := out ++ s!"  sorts {" ".intercalate (sorts.map (·.name)).toList} .\n"
  for s in sorts do
    if let .acu e := s.kind then out := out ++ s!"  subsort {e} < {s.name} .\n"
  for o in st.ops do
    let sig := s!"{" ".intercalate o.args} -> {o.result}"
    let sig := if o.args.isEmpty then s!"-> {o.result}" else sig
    let note := if o.origin.isEmpty then "" else s!"   *** {o.origin}"
    out := out ++ s!"  op {o.name} : {sig} [{o.attrs}] .{note}\n"
  return out ++ "endfm\n"

private def jstr (s : String) : String := (Json.str s).compress

def table (st : State) : String := Id.run do
  let mut ops : Array (String × String) := #[]
  if st.sorts.any (·.kind matches .nat) then ops := ops ++ #[("0", "0"), ("s_", "({0} + 1)")]
  if st.sorts.any (·.kind matches .bool) then ops := ops ++ #[("true", "true"), ("false", "false")]
  for o in st.ops do
    if !(o.name == "none" || o.name == "__") then
      let lean := if o.args.isEmpty then o.lean else
        " ".intercalate (o.lean :: (List.range o.args.length).map fun i => s!"\{{i}}")
      ops := ops.push (o.name, lean)
  let bags := st.sorts.filterMap fun s => if s.kind matches .acu _ then some s.name else none
  let opsJ := ",\n".intercalate (ops.map fun (m, l) => s!"    {jstr m}: {jstr l}").toList
  let bagsJ := ", ".intercalate (bags.map fun b => s!"[{jstr b}, \"__\", \"none\"]").toList
  return s!"\{\n  \"module\": \"CTOR\",\n  \"ops\": \{\n{opsJ}\n  },\n  \"bags\": [{bagsJ}]\n}\n"

/-- The constructor model of state type `root`. -/
def model (root : Expr) : MetaM State := do
  let ((), st) ← (do collect root; finish).run {}
  return st

/-- The project root: the nearest directory above the current Lean file holding a
lakefile. Paths are anchored here, so the working directory does not matter (the
editor's Lean server need not run in the project root). -/
def projectRoot : CoreM System.FilePath := do
  let mut dir ← IO.FS.realPath (← getFileName)
  while true do
    let some parent := dir.parent | break
    dir := parent
    if (← (dir / "lakefile.toml").pathExists) || (← (dir / "lakefile.lean").pathExists) then
      return dir
  throwError "dump: no lakefile above {← getFileName}"

/-- The absolute output directory. -/
def outPath : CoreM System.FilePath := return (← projectRoot) / outDir

/-- Write `ctor.maude` and `ctor.json` into `outDir`. -/
def write (st : State) : CoreM Unit := do
  let out ← outPath
  IO.FS.createDirAll out
  -- atomically (write, then rename): Lean elaborates proofs in parallel, and
  -- concurrent tactics may write and read the model at the same time
  let tag := toString (← IO.monoNanosNow)
  for (name, text) in [("ctor.maude", render st), ("ctor.json", table st)] do
    let tmp := out / s!"{name}.{tag}.tmp"
    IO.FS.writeFile tmp text
    IO.FS.rename tmp (out / name)

/-- `#dump_model T`: write `ctor.maude` and `ctor.json` for state type `T` into `outDir`. -/
syntax (name := dumpModel) "#dump_model " term : command

@[command_elab dumpModel] def elabDumpModel : CommandElab
  | `(#dump_model $t) => do
    let st ← liftTermElabM do model (← Term.elabType t)
    liftCoreM (write st)
    logInfo m!"{render st}\nwrote {outDir / "ctor.maude"} and {outDir / "ctor.json"}"
  | _ => throwUnsupportedSyntax

end Dumper
