import conPanna.Certification.Semantics
import conPanna.Certification.Parser

/-!
# Certification client: metadata, export and external coordination
This module owns generated syntactic profiles, request serialization and the
Python process boundary. The certifier receives FIXED (E₀, B, Σ); produce does
not rerun native unification. Parser.lean loads the returned proof against the
independently fixed goal. No mathematical proof rule is introduced here.
-/

/- Generate/check metadata from the already registered constructor signature.
The one-stratified-bag contract is checked syntactically; this command supplies
no semantic assumptions and creates no problem-specific certification lemma. -/
open Lean Meta Elab Command in
elab "derive_direct_profile " name:ident " for " theory:ident : command => do
  let (theoryName, sortName, symbolName, symbolNames, zeroHeads, addHeads, rigidSorts) ← liftTermElabM do
    let t ← Term.elabTerm theory (some (mkConst ``Structural.CertifiedTheory))
    let some theoryName := t.constName?
      | throwError "expected a named certified theory"
    let sorts ← whnf (← mkAppM ``Structural.CertifiedTheory.Sorts #[t])
    let some sortName := sorts.constName?
      | throwError "expected a generated finite sort datatype"
    let sig ← mkAppM ``Structural.CertifiedTheory.signature #[t]
    let symbol ← whnf (← mkAppM ``Structural.Indexed.Signature.Symbol #[sig])
    let some symbolName := symbol.getAppFn.constName?
      | throwError "expected a generated constructor datatype"
    let symbolInfo ← getConstInfoInduct symbolName
    let operations ← whnf (← mkAppM ``Structural.Indexed.Signature.ACUOp #[sig])
    let some opName := operations.getAppFn.constName?
      | throwError "expected a generated ACU operator datatype"
    let opInfo ← getConstInfoInduct opName
    unless opInfo.ctors.length == 1 do
      throwError "certification contract requires exactly one ACU bag fragment"
    let mut zeros := #[]
    let mut adds := #[]
    let mut resultSorts := #[]
    for op in opInfo.ctors do
      let info ← getConstInfoCtor op
      unless info.numFields == 0 && info.numParams == 0 do
        throwError "ACU operator identifiers must be nullary"
      let opExpr := mkConst op
      let resultType ← whnf (← inferType opExpr)
      let sort := resultType.getAppArgs.back!
      if resultSorts.contains sort then
        throwError "direct prototype requires at most one ACU operator per sort"
      resultSorts := resultSorts.push sort
      let zero ← whnf (← mkAppM ``Structural.Indexed.Signature.zero #[sig, opExpr])
      let add ← whnf (← mkAppM ``Structural.Indexed.Signature.add #[sig, opExpr])
      let some zeroName := zero.constName? | throwError "unit must be a constructor"
      let some addName := add.constName? | throwError "operation must be a constructor"
      zeros := zeros.push (zeroName, op)
      adds := adds.push (addName, op)
    -- Dependency analysis is purely syntactic. Starting with ACU result sorts,
    -- propagate non-rigidity backwards through ALL constructor arguments.
    -- In particular a free Conf constructor containing a bag is not rigid.
    let mut tags : Array Name := #[]
    let mut dependencies : Array (Expr × Array Expr) := #[]
    let mut bagPayloads : Array Expr := #[]
    for symbol in symbolInfo.ctors do
      let info ← getConstInfoCtor symbol
      unless info.numFields == 0 && info.numParams == 0 do
        throwError "constructor identifiers must be nullary"
      let ty ← whnf info.type
      let args := ty.getAppArgs
      unless args.size == 2 do throwError "expected argument-sort and result-sort indices"
      let output ← whnf args[1]!
      let mut inputs := #[]
      let mut inputList := args[0]!
      while true do
        let cell ← whnf inputList
        if cell.getAppFn.constName? == some ``List.nil then break
        unless cell.getAppFn.constName? == some ``List.cons do
          throwError "expected a finite list of constructor argument sorts"
        let fields := cell.getAppArgs
        inputs := inputs.push (← whnf fields[1]!)
        inputList := fields[2]!
      dependencies := dependencies.push (output, inputs)
      if resultSorts.contains output &&
          !(zeros.any (·.1 == symbol)) && !(adds.any (·.1 == symbol)) then
        unless inputs.size == 1 do
          throwError "bag fragment requires a unary singleton constructor"
        bagPayloads := bagPayloads.push inputs[0]!
      for tag in #[output] ++ inputs do
        let some tagName := tag.constName? | throwError "sort tags must be nullary constructors"
        unless tags.contains tagName do tags := tags.push tagName
    let mut blocked := resultSorts
    for _ in [:tags.size] do
      for (output, inputs) in dependencies do
        if inputs.any blocked.contains && !blocked.contains output then
          blocked := blocked.push output
    unless bagPayloads.size == 1 do
      throwError "bag fragment must contain only unit, operation, and one singleton"
    if blocked.contains bagPayloads[0]! then
      throwError "singleton payload must not contain the ACU bag sort"
    return (theoryName, sortName, symbolName, symbolInfo.ctors, zeros, adds,
      tags.map fun tag => (tag, !blocked.contains (mkConst tag)))
  let q (n : Name) := "_root_." ++ n.toString
  let signature := "(Structural.CertifiedTheory.signature " ++ q theoryName ++ ")"
  let branches := symbolNames.map fun symbol =>
    let rhs := match zeroHeads.find? (·.1 == symbol) with
      | some (_, op) => "DirectCertification.HeadView.zero (sig := " ++ signature ++ ") " ++ q op
      | none => match addHeads.find? (·.1 == symbol) with
        | some (_, op) => "DirectCertification.HeadView.add (sig := " ++ signature ++ ") " ++ q op
        | none => "DirectCertification.HeadView.atom (sig := " ++ signature ++ ") _"
    "    | " ++ q symbol ++ " => " ++ rhs
  let rigidBranches := rigidSorts.map fun (tag, rigid) =>
    "    | " ++ q tag ++ " => " ++ (if rigid then "true" else "false")
  let codeBranches := symbolNames.toArray.mapIdx fun i symbol =>
    "    | " ++ q symbol ++ " => " ++ toString i
  let source := "def " ++ name.getId.toString ++
    " : DirectCertification.Profile " ++ signature ++ " where\n" ++
    "  view := fun f => match f with\n" ++ String.intercalate "\n" branches ++
    "\n  view_zero := by intro s op; cases op <;> rfl" ++
    "\n  view_add := by intro s op; cases op <;> rfl" ++
    "\n  unique := by intro s a b; cases a <;> cases b <;> rfl" ++
    "\n  code := fun f => match f with\n" ++ String.intercalate "\n" codeBranches.toList ++
    "\n  rigid := fun s => match s with\n" ++ String.intercalate "\n" rigidBranches.toList ++
    "\n  rigid_args := by intro ss s f h; cases f <;> simp_all [DirectCertification.AllRigid]" ++
    "\n  rigid_no_acu := by intro s op; cases op <;> rfl"
  match Parser.runParserCategory (← getEnv) `command source with
  | .ok stx => elabCommand stx
  | .error e => throwError "generated profile syntax: {e}"
  -- Serialize the registered signature once. Names do not choose algorithms:
  -- only finite sort/head codes and registered free/zero/add roles are exported.
  let sortTags := (← getConstInfoInduct sortName).ctors.toArray
  let mut schema : Array Lean.Json := #[]
  for i in [:symbolNames.length] do
    let symbol := symbolNames[i]!
    let (inputs, output) ← liftTermElabM do
      let ty ← whnf (← getConstInfoCtor symbol).type
      let args := ty.getAppArgs
      let output ← whnf args[1]!
      let mut inputs := #[]
      let mut rest := args[0]!
      while true do
        let cell ← whnf rest
        if cell.getAppFn.constName? == some ``List.nil then break
        let fields := cell.getAppArgs
        inputs := inputs.push (← whnf fields[1]!)
        rest := fields[2]!
      return (inputs, output)
    let tagCode := fun (e : Expr) => (sortTags.findIdx? (fun n => e.constName? == some n)).getD sortTags.size
    let role := if zeroHeads.any (·.1 == symbol) then "zero"
      else if addHeads.any (·.1 == symbol) then "add" else "free"
    schema := schema.push (Lean.Json.mkObj [("id", toJson i),
      ("inputs", toJson (inputs.map tagCode)), ("output", toJson (tagCode output)),
      ("role", toJson role)])
  let text := (Lean.Json.arr schema).compress
  let schemaSource := "def " ++ name.getId.toString ++ "_signature : Lean.Json := " ++
    "(Lean.Json.parse " ++ (Lean.Json.str text).compress ++ ").toOption.get!"
  match Parser.runParserCategory (← getEnv) `command schemaSource with
  | .ok stx => elabCommand stx
  | .error e => throwError "generated signature syntax: {e}"
  -- Forward existing decidable metadata through opaque registration projections.
  -- This is generated here, not a new user registration obligation.
  for source in [
      "def " ++ name.getId.toString ++ "_sortCode : " ++ q sortName ++ " → Nat := fun s => match s with\n" ++
        String.intercalate "\n" ((← getConstInfoInduct sortName).ctors.toArray.mapIdx
          (fun i tag => "  | " ++ q tag ++ " => " ++ toString i)).toList,
      "local instance " ++ name.getId.toString ++ "_decidableSorts : DecidableEq (" ++
        q theoryName ++ ".Sorts) := inferInstanceAs (DecidableEq " ++ q sortName ++ ")",
      "local instance " ++ name.getId.toString ++ "_decidableSymbols : ∀ ss s, DecidableEq (" ++
        signature ++ ".Symbol ss s) := fun ss s => inferInstanceAs (DecidableEq (" ++
        q symbolName ++ " ss s))"] do
    match Parser.runParserCategory (← getEnv) `command source with
    | .ok stx => elabCommand stx
    | .error e => throwError "generated decidable metadata syntax: {e}"

namespace DirectCertification

open Structural.Indexed

variable {Sorts : Type} {sig : Signature Sorts}

namespace Substitution

namespace Worklist

def closeAction [DecidableEq Sorts] {profile : Profile sig} {inputs Γ}
    {proposed : List (Answer sig inputs)} {images : Terms sig Γ inputs}
    {eqs : List (Problem sig Γ)} {s a b} (action : FreePhase.Action profile (s := s) a b)
    (selected : Derives profile eqs a b) : Option (Complete profile proposed images eqs) :=
  match action with
  | .occurs v rhs path => some (.occurs v rhs path selected)
  | .clash f g hf hg different a b => some (.clash f g hf hg different a b selected)
  | .orient action => closeAction action (.symm selected)
  | _ => none

def closeFree [DecidableEq Sorts] [∀ ss s, DecidableEq (sig.Symbol ss s)]
    (profile : Profile sig) {inputs Γ} (proposed : List (Answer sig inputs))
    (images : Terms sig Γ inputs) (eqs : List (Problem sig Γ)) (index : Fin eqs.length) :
    Option (Complete profile proposed images eqs) :=
  closeAction (FreePhase.classify profile (eqs.get index).left (eqs.get index).right) (.hyp index)

end Worklist

namespace LeanReady

open Lean Meta Elab Term

def variableIndex {Γ : List Sorts} {s : Sorts} : Variable Γ s → Nat
  | .here => 0
  | .there v => variableIndex v + 1

mutual
  def termJson (profile : Profile sig) {Γ s} : Term sig Γ s → Json
    | .var v => Json.mkObj [("var", toJson (variableIndex v))]
    | .app f args => Json.mkObj [("app", toJson (profile.code f)), ("args", termsJson profile args)]
  def termsJson (profile : Profile sig) {Γ ss} : Terms sig Γ ss → Json
    | .nil => toJson ([] : List Json)
    | .cons a rest => match termsJson profile rest with
      | .arr xs => .arr (#[termJson profile a] ++ xs)
      | _ => .null -- unreachable: the recursive result is always an array
end

def requestJson (profile : Profile sig) (sortCode : Sorts → Nat) {inputs}
    (eqs : List (Problem sig inputs)) (proposed : List (Answer sig inputs))
    (problemName answerName : String) (signature : Json := .null) : Json :=
  Json.mkObj [("aggregate", toJson "system"), ("problem", toJson problemName),
    ("answers", toJson answerName), ("signature", signature), ("scope", toJson (inputs.map sortCode)),
    ("eqs", toJson (eqs.map fun p => Json.mkObj [
      ("sort", toJson (sortCode p.sort)), ("left", termJson profile p.left),
      ("right", termJson profile p.right)])),
    ("proposed", toJson (proposed.map fun p => Json.mkObj [
      ("parameters", toJson (p.parameters.map sortCode)),
      ("images", termsJson profile p.images)]))]

def produce (request : Json) (compiler : System.FilePath := "certifier/certifier.py") : IO String := do
  let out ← IO.Process.output { cmd := "python3", args := #[compiler.toString, "--certify"] }
    (some request.compress)
  unless out.exitCode == 0 do
    throw (IO.userError s!"certificate producer failed: {out.stderr}")
  pure out.stdout

/-- Optional native-answer coordinator, used by the standalone demo.
This acquires native answers upstream, then certifies that frozen family behind
one Python exchange. The fixed-answer produce entry point stays separate. -/
def coordinate (constructors : System.FilePath) (query : String) (cache : System.FilePath)
    (compiler : System.FilePath := "certifier/certifier.py") : IO String := do
  let out ← IO.Process.output { cmd := "python3", args := #[compiler.toString,
    "--ctor", constructors.toString, "--unify", query, "--out", cache.toString] }
  unless out.exitCode == 0 do
    throw (IO.userError s!"certificate coordinator failed: {out.stderr}")
  pure out.stdout

end LeanReady

end Substitution

end DirectCertification
