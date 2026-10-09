import Lean

/-!
# Certificate parsing and typed proof construction
Python supplies a dependency-ordered bundle of surface rule applications.
This module owns JSON and Lean term parsing, name management, elaboration and
closedness checks. It imports only Lean: no search, semantics or process calls.
The host independently fixes the final semantic goal. Typed intermediate DATA
and rule evidence are checked declarations, never generated axioms or sorries.
-/
namespace DirectCertification.Substitution.LeanReady

open Lean Meta Elab Term

/-- Preparation happens in elaboration, outside kernel reduction. The caller
fixes the proposition independently of the dump. No holes/sorry are accepted. -/
private def parseProofSyntax (dump : String) : TermElabM Syntax := do
  match Parser.runParserCategory (← getEnv) `term dump with
  | .ok stx => pure stx
  | .error message => throwError "invalid prepared certificate: {message}"

private def checkClosed (expected proof : Expr) (debug : Bool := false) : TermElabM (Expr × Expr) := do
  if debug then
    let pending := (← get).pendingMVars
    IO.eprintln s!"Root pending obligations: {pending.length}"
    for mvar in pending.take 6 do
      if let some decl ← getSyntheticMVarDecl? mvar then
        IO.eprintln s!"Pending syntax: {decl.stx.getKind}, assigned: {← mvar.isAssigned}"
  synthesizeSyntheticMVarsNoPostponing
  if debug then IO.eprintln "Root synthetic obligations resolved"
  let expected ← instantiateMVars expected
  let proof ← instantiateMVars proof
  if debug then IO.eprintln "Root metavariables instantiated"
  if expected.hasMVar || proof.hasMVar || expected.hasFVar || proof.hasFVar then
    throwError "prepared certificate is not closed"
  if expected.hasSorry || proof.hasSorry then
    throwError "prepared certificate contains sorry"
  if debug then IO.eprintln "Root closure/admission checks complete"
  pure (expected, proof)

private partial def renameSteps (renames : Array (Name × Name)) : Syntax → Syntax
  | s@(.ident _ _ n _) => match renames.find? (·.1 == n) with
    | some p => mkIdent p.2
    | none => s
  | .node info kind args => .node info kind (args.map (renameSteps renames))
  | s => s

private def prepareStep (renames : Array (Name × Name)) (step : Json) :
    TermElabM (Name × Name) := withCurrHeartbeats do
  let read (key : String) : TermElabM String := match step.getObjValAs? String key with
    | .ok s => pure s
    | .error e => throwError "certificate step: {e}"
  let old := (← read "name").toName
  if renames.any (·.1 == old) then throwError "duplicate certificate step name"
  let typeSyntax := renameSteps renames (← parseProofSyntax (← read "type"))
  let valueSyntax := renameSteps renames (← parseProofSyntax (← read "value"))
  let expected ← elabType typeSyntax
  let proof ← elabTermEnsuringType valueSyntax (some expected)
  let (type, proof) ← checkClosed expected proof
  -- Keep rule labels in generated names, so #print can follow the replay rather
  -- than showing a uniformly anonymous sequence. Labels affect no proof type.
  let label := (step.getObjValAs? String "rule").toOption.getD old.toString
  let name ← mkFreshUserName (Name.mkSimple ("_certification_" ++ label))
  match (step.getObjValAs? String "kind").toOption with
  | some "data" =>
    addDecl (.defnDecl { name := name, levelParams := [], type := type, value := proof, hints := .abbrev, safety := .safe })
  | none =>
    addDecl (.opaqueDecl { name := name, levelParams := [], type := type, value := proof, isUnsafe := false })
  | _ => throwError "unsupported certificate node kind"
  pure (old, name)

private def prepareBatch (renames : Array (Name × Name)) (steps : Array Json) :
    TermElabM (Array (Name × Name)) := withoutModifyingMCtx do
  let mut names := renames
  for step in steps do
    let pair ← try prepareStep names step catch e =>
      let label := (step.getObjValAs? String "rule").toOption.getD
        ((step.getObjValAs? String "name").toOption.getD "unnamed")
      throwError "certificate node {label}: {e.toMessageData}"
    names := names.push pair
  pure names

/-- Check a finite proof DAG step-by-step. The producer cannot declare axioms,
overwrite names, or choose the final goal. Every internal declaration is a closed
kernel-checked definition of equality/completeness evidence or syntactic DATA, freshly named here; no
intermediate Lean FILE is created. Definitions have values, never axiom bodies.
Types/values are ordinary applications of the same equality rules as nested
replay. This avoids elaborating hundreds of dependent steps in one local context.
-/
private def prepareSteps (bundle : Json) : TermElabM Syntax := do
  let steps ← match bundle.getObjValAs? (Array Json) "steps" with
    | .ok xs => pure xs
    | .error e => throwError "certificate steps: {e}"
  let mut renames : Array (Name × Name) := #[]
  let mut remaining := steps
  while !remaining.isEmpty do
    -- Bound temporary elaboration state, but reuse the reduction cache WITHIN
    -- each batch. This is housekeeping, not a search bound: all nodes are checked.
    renames ← prepareBatch renames (remaining.extract 0 50)
    remaining := remaining.extract 50 remaining.size
    if (← IO.getEnv "CONPANNA_CERT_DEBUG") == some "1" then
      IO.eprintln s!"Checked {renames.size}/{steps.size} certificate steps"
  let body ← match bundle.getObjValAs? String "proof" with
    | .ok s => pure s
    | .error e => throwError "certificate proof: {e}"
  logInfo m!"Kernel-checked {steps.size} generated rule steps"
  withCurrHeartbeats do
    pure (renameSteps renames (← parseProofSyntax body))

private def prepare (expectedSyntax : Syntax) (parseAction : TermElabM Syntax) : TermElabM (Expr × Expr) :=
  withoutErrToSorry <| withEnableInfoTree false do
    -- Generated proof text has no user source positions. Retaining an infoview
    -- snapshot for every internal application needlessly retains whole states.
    let started ← IO.monoMsNow
    let stx ← parseAction
    let parsed ← IO.monoMsNow
    if (← IO.getEnv "CONPANNA_CERT_DEBUG") == some "1" then IO.eprintln "Certificate steps and root syntax prepared"
    withCurrHeartbeats do
      let expected ← elabType expectedSyntax
      if (← IO.getEnv "CONPANNA_CERT_DEBUG") == some "1" then IO.eprintln "Fixed semantic goal prepared"
      let proof ← elabTermEnsuringType stx (some expected)
      if (← IO.getEnv "CONPANNA_CERT_DEBUG") == some "1" then IO.eprintln "Root proof elaborated"
      let (expected, proof) ← checkClosed expected proof
        ((← IO.getEnv "CONPANNA_CERT_DEBUG") == some "1")
      let elaborated ← IO.monoMsNow
      logInfo m!"Rule preparation/checking: {parsed - started} ms; root elaboration: {elaborated - parsed} ms"
      pure (expected, proof)

/-- Load an already decoded proof bundle. No compress/reparse round trip. -/
def prepareBundle (expectedSyntax : Syntax) (bundle : Json) : TermElabM (Expr × Expr) :=
  prepare expectedSyntax do
    unless (bundle.getObjValAs? String "format").toOption == some "rule-bundle-v1" do
      throwError "unsupported certificate bundle"
    prepareSteps bundle

/-- Fixed-answer entry point. Raw proof text remains supported for handwritten
regression fixtures; production uses the rule-bundle-v1 surface proof format. -/
def prepareProof (expectedSyntax : Syntax) (dump : String) : TermElabM (Expr × Expr) :=
  match Json.parse dump with
  | .ok bundle => prepareBundle expectedSyntax bundle
  | .error _ => prepare expectedSyntax (parseProofSyntax dump)

/-- Decode a coordinated reply and install its checked answer DATA.
The caller fixes the answer type/name, then fixes the original-problem goal
independently and passes the returned bundle to prepareBundle. The request field
from Python is NEVER used to select or replace the semantic goal. -/
def prepareCoordinatorAnswers (answerTypeSyntax : Syntax) (answerName : Name)
    (dump : String) : TermElabM Json := withoutErrToSorry do
  let result ← match Json.parse dump with
    | .ok value => pure value
    | .error message => throwError "coordinator reply: {message}"
  unless (result.getObjValAs? String "format").toOption == some "coordinated-certificate-v1" do
    throwError "unsupported coordinator reply"
  let bundle ← match result.getObjVal? "certificate" with
    | .ok value => pure value
    | .error message => throwError "coordinator certificate: {message}"
  let answerText ← match result.getObjValAs? String "answer_value" with
    | .ok value => pure value
    | .error message => throwError "coordinator answer data: {message}"
  let answerType ← elabType answerTypeSyntax
  let answerValue ← elabTermEnsuringType (← parseProofSyntax answerText) (some answerType)
  let (type, value) ← checkClosed answerType answerValue
  addDecl (.defnDecl {
    name := answerName, levelParams := [], type := type, value := value,
    hints := .abbrev, safety := .safe })
  pure bundle

end DirectCertification.Substitution.LeanReady
