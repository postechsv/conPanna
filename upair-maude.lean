import conPanna.conPanna

open framework
open Structural

/- # Step 1 - Modeling UPair (Unordered Pairs)
  idle | waiting | critical
  pair x y = pair y x

  pair is commutative but not associative: nested pairs remain structurally distinct.

  Rules:

  request: pair idle X     → pair waiting X
  enter:   pair waiting idle → pair critical idle
  exit:    pair critical X → pair idle X
-/


/- Define constructor symbols. Separating `Status` from `Conf` ensures that a
symbolic process variable ranges only over process states, while `Conf` remains
a recursive Maude-style term language. -/
inductive Status where
  | idle
  | wait
  | crit
  deriving Repr

inductive Conf where
  | proc : Status → Conf
  | upair : Conf → Conf → Conf -- [comm]
  deriving Repr

-- register Conf as top-level sort for rewriting
instance : State Conf := ⟨⟩

-- register structural axioms
structural UPairTheory where
  comm Conf.upair


/-!
## Experimental Maude signature discovery

This stays local to the experiment.  The explicit root below is only a
diagnostic hook; a future unification backend will obtain the same type from
the unification problem.
-/

namespace MaudeExperiment

open Lean Meta Elab Command Term

structure ConstructorDecl where
  leanName : Name
  fields : Array Name
  result : Name

structure SortDecl where
  leanName : Name
  constructors : Array ConstructorDecl

private def shortName : Name → String
  | .str _ value => value
  | name => name.toString

private def inductiveNameOfType (type : Expr) : MetaM Name := do
  let type ← whnf type
  unless type.getAppArgs.isEmpty do
    throwError "parameterized or indexed sort is not supported: {type}"
  let .const name _ := type.getAppFn
    | throwError "expected an inductive sort, got: {type}"
  match (← getEnv).find? name with
  | some (.inductInfo _) => return name
  | _ => throwError "expected an inductive sort, got: {type}"

private def inspectConstructor (name : Name) : MetaM ConstructorDecl := do
  let info ← getConstInfoCtor name
  unless info.numParams == 0 do
    throwError "parameterized constructor is not supported: {name}"
  forallTelescopeReducing info.type fun arguments resultType => do
    unless arguments.size == info.numFields do
      throwError "unexpected constructor telescope for {name}"
    let mut fields := #[]
    for argument in arguments do
      let fieldType ← inferType argument
      if fieldType.hasFVar then
        throwError "dependent constructor field is not supported: {name}"
      fields := fields.push (← inductiveNameOfType fieldType)
    let result ← inductiveNameOfType resultType
    unless result == info.induct do
      throwError "unexpected constructor result for {name}"
    return { leanName := name, fields, result }

private def inspectSort (name : Name) : MetaM SortDecl := do
  let info ← getConstInfoInduct name
  unless info.numParams == 0 && info.numIndices == 0 do
    throwError "parameterized or indexed inductive sort is not supported: {name}"
  let mut constructors := #[]
  for constructorName in info.ctors do
    constructors := constructors.push
      (← inspectConstructor constructorName)
  return { leanName := name, constructors }

private partial def collectPending (pending : List Name)
    (visited : Array Name) (sorts : Array SortDecl) :
    MetaM (Array SortDecl) := do
  match pending with
  | [] => return sorts
  | name :: rest =>
      if visited.contains name then
        collectPending rest visited sorts
      else
        let sort ← inspectSort name
        let dependencies := sort.constructors.flatMap (·.fields)
        collectPending (rest ++ dependencies.toList)
          (visited.push name) (sorts.push sort)

def collectSignature (root : Expr) : MetaM (Array SortDecl) := do
  let rootName ← inductiveNameOfType root
  collectPending [rootName] #[] #[]

private def renderOperator (constructor : ConstructorDecl) : String :=
  let arguments := constructor.fields.toList.map shortName
  let domain := if arguments.isEmpty then "" else
    " " ++ String.intercalate " " arguments
  s!"  op {shortName constructor.leanName} :{domain} -> " ++
    s!"{shortName constructor.result} [ctor] ."

def renderModule (sorts : Array SortDecl) : String := Id.run do
  let mut lines := #["fmod LEAN-MODEL is"]
  for sort in sorts do
    lines := lines.push s!"  sort {shortName sort.leanName} ."
  lines := lines.push ""
  for sort in sorts do
    for constructor in sort.constructors do
      lines := lines.push (renderOperator constructor)
  lines := lines.push "endfm"
  return String.intercalate "\n" lines.toList

elab "#dump_maude_model " root:term : command => do
  liftTermElabM do
    let root ← elabType root
    let stateType ← mkAppM ``framework.State #[root]
    discard <| synthInstance stateType
    logInfo (renderModule (← collectSignature root))

end MaudeExperiment

#dump_maude_model Conf
