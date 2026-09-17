import conPanna.Narrowing

open framework
open Structural

/-!
# Optional Maude backend

This module translates structural Lean signatures and symbolic equations to
Maude, parses complete unifier sets back into solver-neutral certificates, and
reuses the ordinary narrowing materializer and certification interface.

Set `CONPANNA_MAUDE` to override the executable name or path. By default the
backend runs `maude` from `PATH`.
-/

namespace Maude

open Lean Meta Elab Command Term Tactic

structure ConstructorDecl where
  leanName : Name
  fields : Array Name
  result : Name

structure SortDecl where
  leanName : Name
  constructors : Array ConstructorDecl

inductive OperatorLaw where
  | commutative
  | associative
  | identity (element : Name)

structure OperatorDecl where
  leanName : Name
  laws : Array OperatorLaw

/-- A symbolic Lean argument together with its typed Maude name. -/
structure MaudeVariable where
  expression : Expr
  leanName : Name
  maudeName : String
  sort : Name

/-- Constructor terms accepted by the generated Maude signature. -/
inductive MaudeTerm where
  | variable (name : String) (sort : Name)
  | application (constructor result : Name) (arguments : Array MaudeTerm)

structure TranslatedPattern where
  term : MaudeTerm
  variables : Array MaudeVariable

structure MaudeBinding where
  domain : MaudeVariable
  image : MaudeTerm

structure MaudeUnifier where
  index : Nat
  bindings : Array MaudeBinding

structure BasisVariable where
  name : String
  sort : Name

inductive RawMaudeTerm where
  | atom (name : String) (sort? : Option String := none)
  | application (name : String) (arguments : Array RawMaudeTerm)

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

private def findConstructor? (sorts : Array SortDecl) (name : Name) :
    Option ConstructorDecl := Id.run do
  for sort in sorts do
    if let some constructor := sort.constructors.find? (·.leanName == name) then
      return some constructor
  return none

private def findVariable? (variables : Array MaudeVariable) (expression : Expr) :
    Option MaudeVariable :=
  variables.find? fun entry => entry.expression == expression

private partial def translateTerm (sorts : Array SortDecl)
    (variables : Array MaudeVariable) (expression : Expr) : MetaM MaudeTerm := do
  let expression ← instantiateMVars expression
  if let some entry := findVariable? variables expression then
    return .variable entry.maudeName entry.sort
  let expression ← withTransparency .all <| whnf expression
  if let some entry := findVariable? variables expression then
    return .variable entry.maudeName entry.sort
  let some constructorName := expression.getAppFn.constName?
    | throwError "unsupported Maude term: {expression}"
  let some constructor := findConstructor? sorts constructorName
    | throwError "term head is not a constructor in the generated signature: {constructorName}"
  let arguments := expression.getAppArgs
  unless arguments.size == constructor.fields.size do
    throwError "unexpected constructor arity for {constructorName}"
  let mut translated := #[]
  for argument in arguments do
    translated := translated.push
      (← translateTerm sorts variables argument)
  return .application constructor.leanName constructor.result translated

private def makeVariables (stem : String)
    (pattern : Unification.Problem.SaturatedPattern) :
    MetaM (Array MaudeVariable) := do
  let mut variables := #[]
  for index in [:pattern.arguments.size] do
    let expression := pattern.arguments[index]!
    let sort ← inductiveNameOfType (← inferType expression)
    variables := variables.push {
      expression
      leanName := pattern.argumentNames[index]!
      maudeName := s!"{stem}{index + 1}"
      sort
    }
  return variables

def translatePattern (sorts : Array SortDecl) (stem : String)
    (pattern : Unification.Problem.SaturatedPattern) :
    MetaM TranslatedPattern := do
  let variables ← makeVariables stem pattern
  return {
    term := ← translateTerm sorts variables pattern.application
    variables
  }

partial def MaudeTerm.render : MaudeTerm → String
  | .variable name sort => s!"{name}:{shortName sort}"
  | .application constructor _ arguments =>
      if arguments.isEmpty then
        shortName constructor
      else
        let rendered := arguments.toList.map MaudeTerm.render
        s!"{shortName constructor}({String.intercalate ", " rendered})"

private partial def skipWhitespace : List Char → List Char
  | character :: rest =>
      if character.isWhitespace then skipWhitespace rest
      else character :: rest
  | [] => []

private def isDelimiter (character : Char) : Bool :=
  character.isWhitespace ||
    character == '(' || character == ')' ||
    character == ',' || character == ':'

private def takeToken (input : List Char) : String × List Char :=
  let (token, rest) := input.span fun character => !isDelimiter character
  (String.mk token, rest)

private partial def parseRawTerm (input : List Char) :
    Except String (RawMaudeTerm × List Char) := do
  let input := skipWhitespace input
  let (name, rest) := takeToken input
  if name.isEmpty then
    throw "expected a Maude term"
  match skipWhitespace rest with
  | ':' :: rest =>
      let (sort, rest) := takeToken (skipWhitespace rest)
      if sort.isEmpty then
        throw s!"expected a sort after `{name}:`"
      return (.atom name (some sort), rest)
  | '(' :: rest =>
      let (arguments, rest) ← parseRawArguments rest #[]
      return (.application name arguments, rest)
  | rest => return (.atom name none, rest)
where
  parseRawArguments (input : List Char) (arguments : Array RawMaudeTerm) :
      Except String (Array RawMaudeTerm × List Char) := do
    match skipWhitespace input with
    | ')' :: rest => return (arguments, rest)
    | input =>
        let (argument, rest) ← parseRawTerm input
        match skipWhitespace rest with
        | ',' :: rest => parseRawArguments rest (arguments.push argument)
        | ')' :: rest => return (arguments.push argument, rest)
        | _ => throw "expected `,` or `)` in a Maude term"

private def parseRawTermFully (input : String) : Except String RawMaudeTerm := do
  let (term, rest) ← parseRawTerm input.toList
  unless (skipWhitespace rest).isEmpty do
    throw s!"unexpected text after Maude term `{input}`"
  return term

private def resolveSort (sorts : Array SortDecl) (name : String) :
    Except String Name := do
  let candidates := sorts.filter fun sort => shortName sort.leanName == name
  match candidates.toList with
  | [sort] => return sort.leanName
  | [] => throw s!"unknown Maude sort `{name}`"
  | _ => throw s!"ambiguous Maude sort `{name}`"

private def checkExpectedSort (expected? : Option Name) (actual : Name) :
    Except String Unit := do
  if let some expected := expected? then
    unless expected == actual do
      throw s!"expected a term of sort `{shortName expected}`, got `{shortName actual}`"

private def isFreshVariable (name : String) : Bool :=
  name.startsWith "#" || name.startsWith "%"

private partial def resolveRawTerm (sorts : Array SortDecl)
    (variables : Array MaudeVariable) (expected? : Option Name) :
    RawMaudeTerm → Except String MaudeTerm
  | .atom name (some sortName) => do
      let sort ← resolveSort sorts sortName
      checkExpectedSort expected? sort
      match variables.find? (·.maudeName == name) with
      | some entry =>
          unless entry.sort == sort do
            throw s!"Maude changed the sort of input variable `{name}`"
          return .variable name sort
      | none =>
          unless isFreshVariable name do
            throw s!"unknown Maude variable `{name}`"
          return .variable name sort
  | .atom name none => do
      let candidates := sorts.flatMap (·.constructors) |>.filter fun constructor =>
        shortName constructor.leanName == name && constructor.fields.isEmpty &&
          expected?.all (· == constructor.result)
      match candidates.toList with
      | [constructor] =>
          return .application constructor.leanName constructor.result #[]
      | [] => throw s!"unknown nullary Maude constructor `{name}`"
      | _ => throw s!"ambiguous nullary Maude constructor `{name}`"
  | .application name arguments => do
      let candidates := sorts.flatMap (·.constructors) |>.filter fun constructor =>
        shortName constructor.leanName == name &&
          constructor.fields.size == arguments.size &&
          expected?.all (· == constructor.result)
      let constructor ← match candidates.toList with
        | [constructor] => pure constructor
        | [] => throw s!"unknown Maude constructor application `{name}`"
        | _ => throw s!"ambiguous Maude constructor application `{name}`"
      let mut resolved := #[]
      for (argument, field) in arguments.zip constructor.fields do
        resolved := resolved.push
          (← resolveRawTerm sorts variables (some field) argument)
      return .application constructor.leanName constructor.result resolved

private def parseBinding (sorts : Array SortDecl)
    (variables : Array MaudeVariable) (line : String) :
    Except String MaudeBinding := do
  let parts := line.splitOn " --> "
  let [domainText, imageText] := parts
    | throw s!"malformed Maude substitution line `{line}`"
  let domainTerm ← parseRawTermFully domainText.trim
  let (.atom domainName (some domainSortName)) := domainTerm
    | throw s!"expected a typed variable before `-->` in `{line}`"
  let some domain := variables.find? (·.maudeName == domainName)
    | throw s!"Maude returned an unknown domain variable `{domainName}`"
  let domainSort ← resolveSort sorts domainSortName
  unless domain.sort == domainSort do
    throw s!"Maude changed the sort of domain variable `{domainName}`"
  let imageRaw ← parseRawTermFully imageText.trim
  let image ← resolveRawTerm sorts variables (some domain.sort) imageRaw
  return { domain, image }

def parseUnifiers (sorts : Array SortDecl)
    (variables : Array MaudeVariable) (output : String) :
    Except String (Array MaudeUnifier) := do
  let mut unifiers := #[]
  let mut current? : Option MaudeUnifier := none
  let mut sawNoUnifier := false
  for rawLine in output.splitOn "\n" do
    let line := rawLine.trim
    if line.startsWith "Unifier " then
      if let some current := current? then
        unifiers := unifiers.push current
      let some index := (line.drop 8).trim.toNat?
        | throw s!"malformed Maude unifier heading `{line}`"
      current? := some { index, bindings := #[] }
    else if (line.splitOn " --> ").length > 1 then
      let some current := current?
        | throw s!"Maude returned a substitution outside a unifier block: `{line}`"
      let binding ← parseBinding sorts variables line
      current? := some { current with
        bindings := current.bindings.push binding }
    else if line == "No unifier." then
      sawNoUnifier := true
  if let some current := current? then
    unifiers := unifiers.push current
  if unifiers.isEmpty && !sawNoUnifier then
    throw "Maude output contained neither a unifier nor `No unifier.`"
  return unifiers

def parseMatchers (sorts : Array SortDecl)
    (variables : Array MaudeVariable) (output : String) :
    Except String (Array MaudeUnifier) := do
  let mut matchers := #[]
  let mut current? : Option MaudeUnifier := none
  let mut sawNoMatch := false
  for rawLine in output.splitOn "\n" do
    let line := rawLine.trim
    if line.startsWith "Matcher " then
      if let some current := current? then
        matchers := matchers.push current
      let some index := (line.drop 8).trim.toNat?
        | throw s!"malformed Maude matcher heading `{line}`"
      current? := some { index, bindings := #[] }
    else if (line.splitOn " --> ").length > 1 then
      let some current := current?
        | throw s!"Maude returned a substitution outside a matcher block: `{line}`"
      let binding ← parseBinding sorts variables line
      current? := some { current with
        bindings := current.bindings.push binding }
    else if line == "No match." then
      sawNoMatch := true
  if let some current := current? then
    matchers := matchers.push current
  if matchers.isEmpty && !sawNoMatch then
    throw "Maude output contained neither a matcher nor `No match.`"
  return matchers

private def sameBasisVariable (left right : BasisVariable) : Bool :=
  left.name == right.name && left.sort == right.sort

private partial def collectBasisVariables (term : MaudeTerm)
    (basis : Array BasisVariable := #[]) : Array BasisVariable :=
  match term with
  | .variable name sort =>
      let entry := { name, sort }
      if basis.any (sameBasisVariable entry) then basis else basis.push entry
  | .application _ _ arguments =>
      arguments.foldl (fun basis argument =>
        collectBasisVariables argument basis) basis

private def imageOf (unifier : MaudeUnifier)
    (input : MaudeVariable) : MaudeTerm :=
  match unifier.bindings.find? fun binding =>
      binding.domain.maudeName == input.maudeName with
  | some binding => binding.image
  | none => .variable input.maudeName input.sort

private partial def withBasisExpressions {α : Type}
    (basis : Array BasisVariable) (index : Nat) (expressions : Array Expr)
    (continuation : Array Expr → MetaM α) : MetaM α := do
  if _h : index < basis.size then
    let type ← mkConstWithFreshMVarLevels basis[index].sort
    withLocalDeclD (Name.mkSimple s!"u{index + 1}") type fun expression =>
      withBasisExpressions basis (index + 1) (expressions.push expression)
        continuation
  else
    continuation expressions

private partial def maudeTermToExpr (basis : Array BasisVariable)
    (basisExpressions : Array Expr) : MaudeTerm → MetaM Expr
  | .variable name sort =>
      match basis.findIdx? fun entry => entry.name == name && entry.sort == sort with
      | some index => return basisExpressions[index]!
      | none => throwError "Maude variable `{name}:{shortName sort}` is not in the unifier basis"
  | .application constructor _ arguments => do
      let operation ← mkConstWithFreshMVarLevels constructor
      let mut translated := #[]
      for argument in arguments do
        translated := translated.push
          (← maudeTermToExpr basis basisExpressions argument)
      return mkAppN operation translated

private partial def maudeTermToFixedExpr (variables : Array MaudeVariable) :
    MaudeTerm → MetaM Expr
  | .variable name sort =>
      match variables.find? fun entry =>
          entry.maudeName == name && entry.sort == sort with
      | some entry => return entry.expression
      | none => throwError
          "Maude matcher introduced unsupported variable `{name}:{shortName sort}`"
  | .application constructor _ arguments => do
      let operation ← mkConstWithFreshMVarLevels constructor
      let mut translated := #[]
      for argument in arguments do
        translated := translated.push
          (← maudeTermToFixedExpr variables argument)
      return mkAppN operation translated

private partial def collectMVars (expression : Expr)
    (result : Array MVarId := #[]) : Array MVarId :=
  match expression with
  | .mvar mvarId =>
      if result.contains mvarId then result else result.push mvarId
  | .app function argument =>
      collectMVars argument (collectMVars function result)
  | .lam _ type body _ | .forallE _ type body _ =>
      collectMVars body (collectMVars type result)
  | .letE _ type value body _ =>
      collectMVars body (collectMVars value (collectMVars type result))
  | .mdata _ body | .proj _ _ body => collectMVars body result
  | _ => result

private partial def collectFVars (expression : Expr)
    (result : Array FVarId := #[]) : Array FVarId :=
  match expression with
  | .fvar fvarId =>
      if result.contains fvarId then result else result.push fvarId
  | .app function argument =>
      collectFVars argument (collectFVars function result)
  | .lam _ type body _ | .forallE _ type body _ =>
      collectFVars body (collectFVars type result)
  | .letE _ type value body _ =>
      collectFVars body (collectFVars value (collectFVars type result))
  | .mdata _ body | .proj _ _ body => collectFVars body result
  | _ => result

private def variablesForMVars (stem : String) (ids : Array MVarId) :
    MetaM (Array MaudeVariable) := do
  let mut variables := #[]
  for index in [:ids.size] do
    let expression := mkMVar ids[index]!
    let type ← inferType expression
    let sort ← try
      inductiveNameOfType type
    catch error =>
      throwError m!"unsupported Maude match variable {expression} : {type}\n{error.toMessageData}"
    variables := variables.push {
      expression
      leanName := Name.mkSimple s!"target{index + 1}"
      maudeName := s!"{stem}{index + 1}"
      sort
    }
  return variables

private def variablesForFVars (stem : String) (ids : Array FVarId) :
    MetaM (Array MaudeVariable) := do
  let mut variables := #[]
  for index in [:ids.size] do
    let expression := mkFVar ids[index]!
    let declaration ← ids[index]!.getDecl
    variables := variables.push {
      expression
      leanName := declaration.userName
      maudeName := s!"{stem}{index + 1}"
      sort := ← inductiveNameOfType (← inferType expression)
    }
  return variables

private def matcherToCandidate (variables targets : Array MaudeVariable)
    (matcher : MaudeUnifier) : MetaM Narrowing.Subsumption.MatchCandidate := do
  let mut assignments := #[]
  for target in targets do
    let some binding := matcher.bindings.find? fun binding =>
        binding.domain.maudeName == target.maudeName
      | continue
    let value ← maudeTermToFixedExpr variables binding.image
    if value.hasExprMVar then
      throwError "Maude matcher returned a target variable in a match image"
    let .mvar metavariable := target.expression
      | throwError "internal Maude matcher target is not a metavariable"
    assignments := assignments.push { metavariable, value }
  return { assignments }

private def unifierToAlternative (inputs : Array MaudeVariable)
    (unifier : MaudeUnifier) : MetaM Unification.Certificate.Alternative := do
  let images := inputs.map (imageOf unifier)
  let basis := images.foldl (fun basis image =>
    collectBasisVariables image basis) #[]
  let mut basisTypes := #[]
  for entry in basis do
    basisTypes := basisTypes.push (← mkConstWithFreshMVarLevels entry.sort)
  let images ← withBasisExpressions basis 0 #[] fun basisExpressions => do
    let mut expressions := #[]
    for image in images do
      let body ← maudeTermToExpr basis basisExpressions image
      expressions := expressions.push (← mkLambdaFVars basisExpressions body)
    return expressions
  return { basisTypes, images }

def toSolutionSet (inputs : Array MaudeVariable)
    (unifiers : Array MaudeUnifier) :
    MetaM Unification.Certificate.SolutionSet := do
  let mut alternatives := #[]
  for unifier in unifiers do
    alternatives := alternatives.push
      (← unifierToAlternative inputs unifier)
  return { alternatives }

private def renderTranslatedPattern (translation : TranslatedPattern) : String :=
  let mappings := translation.variables.toList.map fun entry =>
    s!"  {entry.maudeName}:{shortName entry.sort} ← {entry.leanName}"
  let mappingBlock := if mappings.isEmpty then "" else
    "\nvariables:\n" ++ String.intercalate "\n" mappings
  "term: " ++ translation.term.render ++ mappingBlock

private def constantName (description : String) (expression : Expr) :
    MetaM Name := do
  let expression ← withTransparency .all <| whnf expression
  let .const name _ := expression
    | throwError "expected {description} to be a constant, got: {expression}"
  return name

private partial def inspectLaws (laws : Expr)
    (result : Array OperatorLaw := #[]) : MetaM (Array OperatorLaw) := do
  let laws ← withTransparency .all <| whnf laws
  let arguments := laws.getAppArgs
  if laws.getAppFn.isConstOf ``List.nil then
    return result
  unless laws.getAppFn.isConstOf ``List.cons && arguments.size >= 3 do
    throwError "could not reduce structural operator laws"
  let law ← withTransparency .all <|
    whnf arguments[arguments.size - 2]!
  let tail := arguments[arguments.size - 1]!
  if law.getAppFn.isConstOf ``Structural.OperatorLaw.commutative then
    inspectLaws tail (result.push .commutative)
  else if law.getAppFn.isConstOf ``Structural.OperatorLaw.associative then
    inspectLaws tail (result.push .associative)
  else if law.getAppFn.isConstOf ``Structural.OperatorLaw.identity then
    let element ← constantName "identity element" law.getAppArgs.back!
    inspectLaws tail (result.push (.identity element))
  else
    throwError "unsupported structural operator law: {law}"

private partial def inspectSymbols (symbols : Expr)
    (result : Array OperatorDecl := #[]) : MetaM (Array OperatorDecl) := do
  let symbols ← withTransparency .all <| whnf symbols
  let arguments := symbols.getAppArgs
  if symbols.getAppFn.isConstOf ``List.nil then
    return result
  unless symbols.getAppFn.isConstOf ``List.cons && arguments.size >= 3 do
    throwError "could not reduce structural theory symbols"
  let symbol := arguments[arguments.size - 2]!
  let tail := arguments[arguments.size - 1]!
  let operation ← mkAppM ``Structural.Symbol.operation #[symbol]
  let operationName ← constantName "registered operation" operation
  let laws ← mkAppM ``Structural.Symbol.laws #[symbol]
  inspectSymbols tail (result.push {
    leanName := operationName
    laws := ← inspectLaws laws
  })

def inspectTheory (theory : Expr) : MetaM (Array OperatorDecl) := do
  inspectSymbols (← mkAppM ``Structural.Theory.symbols #[theory])

private def renderLaw : OperatorLaw → String
  | .commutative => "comm"
  | .associative => "assoc"
  | .identity element => s!"id: {shortName element}"

private def renderOperator (operators : Array OperatorDecl)
    (constructor : ConstructorDecl) : String :=
  let arguments := constructor.fields.toList.map shortName
  let domain := if arguments.isEmpty then "" else
    " " ++ String.intercalate " " arguments
  let laws := match operators.find? (·.leanName == constructor.leanName) with
    | some operation => operation.laws.toList.map renderLaw
    | none => []
  let attributes := String.intercalate " " ("ctor" :: laws)
  s!"  op {shortName constructor.leanName} :{domain} -> " ++
    s!"{shortName constructor.result} [{attributes}] ."

def renderModule (sorts : Array SortDecl)
    (operators : Array OperatorDecl) : String := Id.run do
  let mut lines := #["fmod LEAN-MODEL is"]
  for sort in sorts do
    lines := lines.push s!"  sort {shortName sort.leanName} ."
  lines := lines.push ""
  for sort in sorts do
    for constructor in sort.constructors do
      lines := lines.push (renderOperator operators constructor)
  lines := lines.push "endfm"
  return String.intercalate "\n" lines.toList

private def elaborateModule (rootSyntax theorySyntax : Syntax) :
    TermElabM String := do
  let root ← elabType rootSyntax
  let stateType ← mkAppM ``framework.State #[root]
  discard <| synthInstance stateType
  let theoryType ← mkConstWithFreshMVarLevels ``Structural.Theory
  let theory ← elabTerm theorySyntax (some theoryType)
  return renderModule
    (← collectSignature root) (← inspectTheory theory)

private def elaboratePatternTranslation (patternSyntax rootSyntax : Syntax) :
    TermElabM String := do
  let root ← elabType rootSyntax
  let stateType ← mkAppM ``framework.State #[root]
  discard <| synthInstance stateType
  let sorts ← collectSignature root
  let pattern ← elabTerm patternSyntax none
  let pattern ← Unification.Problem.saturatePattern pattern
  return renderTranslatedPattern
    (← translatePattern sorts "X" pattern)

private def patternResultType
    (pattern : Unification.Problem.SaturatedPattern) : MetaM Expr := do
  withTransparency .all <| whnf (← inferType pattern.application)

def maudeExecutable : IO String := do
  return (← IO.getEnv "CONPANNA_MAUDE").getD "maude"

def runMaude (moduleText query : String) : IO String := do
  let input := "set include BOOL off .\n" ++
    moduleText ++ "\n\n" ++ query ++ "\nquit\n"
  let executable ← maudeExecutable
  let output ← IO.Process.output {
    cmd := executable
    args := #["-no-banner"]
  } (some input)
  if output.exitCode != 0 then
    throw <| IO.userError (
      s!"Maude failed with exit code {output.exitCode}\n" ++
      s!"stdout:\n{output.stdout}\nstderr:\n{output.stderr}")
  unless output.stderr.trim.isEmpty do
    throw <| IO.userError s!"Maude wrote to stderr:\n{output.stderr}"
  if (output.stdout.splitOn "Warning:").length > 1 then
    throw <| IO.userError s!"Maude reported a warning:\n{output.stdout}"
  return output.stdout

private def solveWithMaude (sorts : Array SortDecl) (moduleText : String)
    (problem : Unification.Problem.Input) :
    MetaM Unification.Certificate.SolutionSet := do
  let left ← translatePattern sorts "L" problem.lhs
  let right ← translatePattern sorts "R" problem.rhs
  let query :=
    "unify in LEAN-MODEL : " ++
    left.term.render ++ " =? " ++ right.term.render ++ " ."
  let output ← MonadLiftT.monadLift
    (runMaude moduleText query : IO String)
  let inputs := left.variables ++ right.variables
  let unifiers ← ofExcept <| parseUnifiers sorts inputs output
  toSolutionSet inputs unifiers

private def matchWithMaude (sorts : Array SortDecl) (moduleText : String)
    (pattern subject : Expr) :
    MetaM (Array Narrowing.Subsumption.MatchCandidate) := do
  let pattern ← withTransparency .all <| whnf (← instantiateMVars pattern)
  let subject ← withTransparency .all <| whnf (← instantiateMVars subject)
  let targets ← variablesForMVars "T" (collectMVars pattern)
  let fixed ← variablesForFVars "S" (collectFVars subject)
  let variables := targets ++ fixed
  let patternTerm ← translateTerm sorts variables pattern
  let subjectTerm ← translateTerm sorts variables subject
  let query :=
    "match in LEAN-MODEL : " ++ patternTerm.render ++
    " <=? " ++ subjectTerm.render ++ " ."
  let output ← MonadLiftT.monadLift
    (runMaude moduleText query : IO String)
  let matchers ← ofExcept <| parseMatchers sorts variables output
  matchers.mapM (matcherToCandidate variables targets)

/-- Solve one library unification problem through the external Maude process. -/
def solveStructuralTheory (theory : Expr)
    (problem : Unification.Problem.Input) :
    MetaM Unification.Certificate.SolutionSet := do
  let root ← patternResultType problem.lhs
  let rightRoot ← patternResultType problem.rhs
  unless ← isDefEq root rightRoot do
    throwError "Maude unification requires patterns with the same result type"
  let stateType ← mkAppM ``framework.State #[root]
  discard <| synthInstance stateType
  let sorts ← collectSignature root
  let moduleText := renderModule sorts (← inspectTheory theory)
  solveWithMaude sorts moduleText problem

/-- Find directional matches of a target atom against a fixed source atom. -/
def matchStructuralTheory (theory pattern subject : Expr) :
    MetaM (Array Narrowing.Subsumption.MatchCandidate) := do
  let root ← withTransparency .all <| whnf (← inferType pattern)
  let subjectRoot ← withTransparency .all <| whnf (← inferType subject)
  if root.isForall then
    throwError m!"Maude received a non-atomic match pattern:\n  {pattern}\nwith type:\n  {root}\nsubject:\n  {subject}"
  unless ← isDefEq root subjectRoot do
    throwError "Maude matching requires terms with the same type"
  let stateType ← mkAppM ``framework.State #[root]
  discard <| synthInstance stateType
  let sorts ← collectSignature root
  let moduleText := renderModule sorts (← inspectTheory theory)
  matchWithMaude sorts moduleText pattern subject

initialize
  Unification.registerStructuralTheorySolver solveStructuralTheory

initialize
  Narrowing.Subsumption.registerStructuralMatcher matchStructuralTheory

def dumpModelCommand (rootSyntax theorySyntax : Syntax) : TermElabM Unit := do
  logInfo (← elaborateModule rootSyntax theorySyntax)

def dumpTermCommand (patternSyntax rootSyntax : Syntax) : TermElabM Unit := do
  logInfo (← elaboratePatternTranslation patternSyntax rootSyntax)

end Maude

elab "#dump_maude_model " root:term " mod " theory:term : command => do
  Lean.Elab.Command.liftTermElabM <|
    Maude.dumpModelCommand root.raw theory.raw

elab "#dump_maude_term " pattern:term " from " root:term : command => do
  Lean.Elab.Command.liftTermElabM <|
    Maude.dumpTermCommand pattern.raw root.raw
