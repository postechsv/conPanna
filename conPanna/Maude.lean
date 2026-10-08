import conPanna.Narrowing

open framework
open Structural

/-!
# Optional Maude backend

This module translates structural Lean signatures and symbolic equations to
Maude and parses candidate substitutions into solver-neutral data. Built-in
`unify` output is not a proof of completeness. Certification dump commands export
free syntax, native signature data and a request for the object-level calculus;
their replies still need a parser and kernel replay before narrowing can use them.

Set `CONPANNA_MAUDE` to override the executable name or path. Otherwise the
backend searches `PATH`, then the conventional `$HOME/Maude/maude` installation.
The fallback also works when an editor does not inherit the shell's `PATH`.
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
  deriving BEq

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
  if let .lit (.natVal value) := expression then
    unless (findConstructor? sorts ``Nat.zero).isSome &&
        (findConstructor? sorts ``Nat.succ).isSome do
      throwError "Nat literals require Nat in the generated signature"
    let mut term := MaudeTerm.application ``Nat.zero ``Nat #[]
    for _ in [:value] do
      term := .application ``Nat.succ ``Nat #[term]
    return term
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
  if let some executable ← IO.getEnv "CONPANNA_MAUDE" then
    if executable.isEmpty then
      throw <| IO.userError "CONPANNA_MAUDE is empty; set it to the Maude executable name or absolute path."
    return executable
  let filename := if System.Platform.isWindows then "maude.exe" else "maude"
  let searchPath := System.SearchPath.parse ((← IO.getEnv "PATH").getD "")
  for directory in searchPath do
    let executable := directory / filename
    if (← executable.pathExists) && !(← executable.isDir) then
      return executable.toString
  let homeVariable := if System.Platform.isWindows then "USERPROFILE" else "HOME"
  if let some userDirectory ← IO.getEnv homeVariable then
    let executable := System.FilePath.mk userDirectory / "Maude" / filename
    if (← executable.pathExists) && !(← executable.isDir) then
      return executable.toString
  throw <| IO.userError
    "Maude executable not found. Set CONPANNA_MAUDE to its absolute path, add Maude to PATH, or install it in your home directory's Maude folder."

def runMaude (moduleText query : String) : IO String := do
  -- Keep associative output binary, matching the registered constructor arity.
  -- This changes printing only, not Maude's ACU search or term semantics.
  let input := "set include BOOL off .\nset print flat off .\n" ++
    moduleText ++ "\n\n" ++ query ++ "\nquit\n"
  let executable ← maudeExecutable
  let output ← try
    IO.Process.output { cmd := executable, args := #["-no-banner"] } (some input)
  catch error =>
    throw <| IO.userError s!"Cannot start Maude executable '{executable}': {error}"
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

/-- Native directional matching on translated constructor terms. Subject
variables are fixed by Maude matching. A free tuple constructor may frame several
images in one query, preserving correlations between all pattern variables.
Returned substitutions are untrusted candidates, not semantic certificates. -/
def matchTranslated (sorts : Array SortDecl) (moduleText : String)
    (variables : Array MaudeVariable) (pattern subject : MaudeTerm) :
    IO (Array MaudeUnifier) := do
  let query := "match in LEAN-MODEL : " ++ pattern.render ++
    " <=? " ++ subject.render ++ " ."
  let output ← runMaude moduleText query
  IO.ofExcept <| parseMatchers sorts variables output

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
  let matchers ← matchTranslated sorts moduleText variables patternTerm subjectTerm
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

/-! Certification exports free syntax and law DATA. Native Maude ACU attributes
and built-in `unify` belong only to the candidate path above. -/
namespace Certification

structure Signature where
  sorts : Array SortDecl
  bag : Name
  add : Name
  zero : Name

private partial def containsBag (sorts : Array SortDecl) (bag : Name)
    (seen : List Name) (sort : Name) : Bool :=
  if sort == bag then true
  else if seen.contains sort then false
  else match sorts.find? (·.leanName == sort) with
    | none => false
    | some decl => decl.constructors.any fun ctor =>
        ctor.fields.any (containsBag sorts bag (sort :: seen))

private def inspect (root theory : Expr) : MetaM Signature := do
  let sorts ← collectSignature root
  let operators ← inspectTheory theory
  let [operation] := operators.toList
    | throwError "certification currently requires exactly one ACU operator"
  let some add := findConstructor? sorts operation.leanName
    | throwError "certification operator is outside the native signature"
  let mut isComm := false
  let mut isAssoc := false
  let mut units : Array Name := #[]
  for law in operation.laws do
    match law with
    | .commutative => isComm := true
    | .associative => isAssoc := true
    | .identity unit => units := units.push unit
  let [unit] := units.toList
    | throwError "certification requires one unit constructor"
  unless isComm && isAssoc && add.fields == #[add.result, add.result] do
    throwError "certification requires a binary ACU constructor"
  let some zero := findConstructor? sorts unit
    | throwError "certification unit is outside the native signature"
  unless zero.fields.isEmpty && zero.result == add.result do
    throwError "certification requires a nullary unit at the ACU sort"
  for sort in sorts do
    for ctor in sort.constructors do
      if ctor.result == add.result && ctor.leanName != add.leanName then
        if ctor.fields.any (containsBag sorts add.result []) then
          throwError "certification does not support ACU terms nested inside payloads"
  return { sorts, bag := add.result, add := add.leanName, zero := unit }

private def constructors (sig : Signature) : Array ConstructorDecl :=
  sig.sorts.flatMap (·.constructors)

private def sortId (sig : Signature) (name : Name) : MetaM Nat := do
  let some index := sig.sorts.findIdx? (·.leanName == name)
    | throwError "sort is outside the certification signature: {name}"
  return index

private def constructorId (sig : Signature) (name : Name) : MetaM Nat := do
  let some index := (constructors sig).findIdx? (·.leanName == name)
    | throwError "constructor is outside the certification signature: {name}"
  return index

private def list (nil cons : String) (items : Array String) : String :=
  items.foldr (fun item rest => s!"{cons}({item}, {rest})") nil

/-- Qualified identities and argument sorts bind later replies to the exact
native signature. IDs are local to this packet, not generated Lean Tag indices. -/
def renderSchema (sig : Signature) : MetaM String := do
  let sorts := sig.sorts.mapIdx fun i sort =>
    s!"nativeSort({i}, {sort.leanName.toString.quote})"
  let ctors ← (constructors sig).mapIdxM fun i ctor => do
    let fields ← ctor.fields.mapM (fun s => return toString (← sortId sig s))
    return s!"nativeCtor({i}, {ctor.leanName.toString.quote}, " ++
      s!"{← sortId sig ctor.result}, {list "nNil" "nCons" fields})"
  return s!"schema({list "sNil" "sCons" sorts}, {list "cNil" "cCons" ctors}, " ++
    s!"{← sortId sig sig.bag}, {← constructorId sig sig.add}, " ++
    s!"{← constructorId sig sig.zero})"

def renderModule (sig : Signature) : MetaM String := do
  return "load conPanna/maude-cert2.maude\n\n" ++
    "mod LEAN-CERTIFICATION-MODEL is\n  protecting CERT2-PROTOCOL .\n" ++
    s!"  op nativeSignature : -> Schema .\n  eq nativeSignature = {← renderSchema sig} .\nendm"

private partial def ground : MaudeTerm → Bool
  | .variable .. => false
  | .application _ _ args => args.all ground

/-- Project through matching free constructors. Other fields must be identical
ground syntax; payload variables and multiple changing fields fail explicitly. -/
private partial def project (sig : Signature) (a b : MaudeTerm) :
    MetaM (Array Nat × MaudeTerm × MaudeTerm) := do
  let resultSort : MaudeTerm → Name
    | .variable _ s | .application _ s _ => s
  unless resultSort a == resultSort b do
    throwError "certification equation has mismatched sorts"
  if resultSort a == sig.bag then return (#[], a, b)
  let .application f _ aa := a
    | throwError "certification cannot project through a free-sort variable"
  let .application g _ bb := b
    | throwError "certification cannot project through a free-sort variable"
  unless f == g && aa.size == bb.size do
    throwError "certification constructor mismatch is not supported yet"
  let changing := aa.zip bb |>.mapIdx (fun i (a, b) => (i, a, b))
    |>.filter (fun (_, a, b) => !(ground a && ground b && a == b))
  let [(index, a, b)] := changing.toList
    | throwError "certification projection requires exactly one non-ground or changing field"
  let (path, a, b) ← project sig a b
  return (#[index] ++ path, a, b)

private partial def nativeTerm (sig : Signature) (variables : Array MaudeVariable) :
    MaudeTerm → MetaM String
  | .variable name sort => do
      let some index := variables.findIdx? (·.maudeName == name)
        | throwError "unknown certification variable: {name}"
      return s!"v({index}, {← sortId sig sort})"
  | .application ctor _ args => do
      let args ← args.mapM (nativeTerm sig variables)
      return s!"node({← constructorId sig ctor}, {list "tNil" "tCons" args})"

private partial def portableTerm (sig : Signature) (variables : Array MaudeVariable)
    (term : MaudeTerm) (atoms : Array MaudeTerm) : MetaM (String × Array MaudeTerm) := do
  match term with
  | .variable name sort =>
      unless sort == sig.bag do
        throwError "certification payload variables are not supported yet"
      let some index := variables.findIdx? (·.maudeName == name)
        | throwError "unknown certification variable: {name}"
      return (s!"var({index})", atoms)
  | .application ctor result args =>
      unless result == sig.bag do
        throwError "expected a certification term at the ACU sort"
      if ctor == sig.zero then return ("zero", atoms)
      if ctor == sig.add then
        let #[a, b] := args | throwError "unexpected ACU constructor arity"
        let (a, atoms) ← portableTerm sig variables a atoms
        let (b, atoms) ← portableTerm sig variables b atoms
        return (s!"add({a}, {b})", atoms)
      unless ground term do
        throwError "certification payload variables are not supported yet"
      if let some index := atoms.findIdx? (· == term) then
        return (s!"atom({index})", atoms)
      return (s!"atom({atoms.size})", atoms.push term)

private def isOverlap (sig : Signature) (a b : MaudeTerm) : Bool :=
  match a, b with
  | .application f _ #[.variable x _, .variable y _],
      .application g _ #[atom@(.application h _ _), .variable z _] =>
      f == sig.add && g == sig.add && h != sig.add && h != sig.zero &&
        ground atom && x != y && x != z && y != z
  | _, _ => false

/-- `request` is the exact request text, with the schema expanded, that a reply
must echo. `script` is the runnable Maude input containing that request. -/
structure Query where
  request : String
  script : String

/-- Native input, sorted variables, ground-atom dictionary and projection path
remain in the request. The portable formula alone is not its identity. -/
def renderQuery (sig : Signature) (problem : Unification.Problem.Input) : MetaM Query := do
  let lhs ← translatePattern sig.sorts "L" problem.lhs
  let rhs ← translatePattern sig.sorts "R" problem.rhs
  let variables := lhs.variables ++ rhs.variables
  let (path, nativeA, nativeB) ← project sig lhs.term rhs.term
  let (a, atoms) ← portableTerm sig variables nativeA #[]
  let (b, atoms) ← portableTerm sig variables nativeB atoms
  unless variables.size == 3 && variables.all (·.sort == sig.bag) &&
      isOverlap sig nativeA nativeB do
    throwError "certification search currently supports only X+Y = ground-atom+Z"
  let declarations ← variables.mapIdxM fun i v => do
    return s!"nativeVar({i}, {← sortId sig v.sort}, {v.maudeName.quote})"
  let dictionary ← atoms.mapIdxM fun i atom => do
    return s!"nativeAtom({i}, {← nativeTerm sig variables atom})"
  let fields := s!"{list "vNil" "vCons" declarations}, {list "aNil" "aCons" dictionary}, " ++
    s!"{← nativeTerm sig variables lhs.term}, {← nativeTerm sig variables rhs.term}, " ++
    s!"{list "nNil" "nCons" (path.map toString)}, eqn({a}, {b}))"
  return {
    request := s!"request(1, {← renderSchema sig}, " ++ fields
    script := (← renderModule sig) ++
      "\n\nsmod LEAN-CERTIFICATION-QUERY is\n" ++
      "  protecting LEAN-CERTIFICATION-MODEL .\n  protecting CERT2-SEARCH .\n" ++
      "  op nativeQuery : -> Request .\n" ++
      s!"  eq nativeQuery = request(1, nativeSignature, {fields} .\nendsm\n\n" ++
      "srew [1] in LEAN-CERTIFICATION-QUERY : query(nativeQuery) using certifyOverlap .\nquit\n" }

def exportQuery (root theory : Expr) (problem : Unification.Problem.Input) : MetaM Query := do
  renderQuery (← inspect root theory) problem

/-! Untrusted reply syntax. Parsing only recovers first-order DATA; it proves
nothing. Callers must compare the echoed request and replay the certificate. -/

inductive Node where
  | num (value : Nat)
  | str (value : String)
  | app (head : String) (args : Array Node)
  deriving Repr, BEq, Inhabited

private partial def parseNodeAt (s : Array Char) (i : Nat) : Except String (Node × Nat) := do
  let skip (i : Nat) := Id.run do
    let mut i := i
    while s.getD i 'x' |>.isWhitespace do i := i + 1
    return i
  let span (p : Char → Bool) (i : Nat) := Id.run do
    let mut j := i
    while j < s.size && p s[j]! do j := j + 1
    return (String.mk (s.extract i j).toList, j)
  let i := skip i
  if i ≥ s.size then throw "malformed or truncated Maude reply"
  let c := s[i]!
  if c.isDigit then
    let (digits, j) := span Char.isDigit i
    return (.num digits.toNat!, j)
  if c == '"' then
    let (body, j) := span (fun c => c != '"' && c != '\\') (i + 1)
    unless s.getD j ' ' == '"' do throw "unsupported or unterminated string in Maude reply"
    return (.str body, j + 1)
  let (head, j) := span Char.isAlphanum i
  if head.isEmpty then throw s!"unexpected character in Maude reply: {c}"
  let mut j := skip j
  unless s.getD j ' ' == '(' do return (.app head #[], j)
  let mut args := #[]
  repeat
    let (arg, k) ← parseNodeAt s (j + 1)
    args := args.push arg
    j := skip k
    if s.getD j ' ' == ',' then continue
    unless s.getD j ' ' == ')' do throw "malformed or truncated Maude reply"
    break
  return (.app head args, j + 1)

/-- Parse one complete term; trailing text is rejected. -/
def parseNode (text : String) : Except String Node := do
  let chars := text.toList.toArray
  let (node, i) ← parseNodeAt chars 0
  unless chars.extract i chars.size |>.all Char.isWhitespace do
    throw "trailing text after Maude term"
  return node

/-- Exactly one `result Reply:` term, followed only by Maude's exit message.
No result, a different sort or truncation is an error, never an empty family. -/
def parseReply (stdout : String) : Except String Node := do
  let [_, after] := stdout.splitOn "result Reply:"
    | throw "expected exactly one Maude Reply result"
  let [term, rest] := after.splitOn "Bye."
    | throw "Maude reply is not followed by its exit message"
  unless rest.trim.isEmpty do throw "unexpected text after Maude exit"
  parseNode term

private def elaborateSignature (rootSyntax theorySyntax : Syntax) : TermElabM Signature := do
  let root ← elabType rootSyntax
  discard <| synthInstance (← mkAppM ``framework.State #[root])
  let theory ← elabTerm theorySyntax (some (← mkConstWithFreshMVarLevels ``Structural.Theory))
  inspect root theory

def dumpModelCommand (rootSyntax theorySyntax : Syntax) : TermElabM Unit := do
  logInfo (← renderModule (← elaborateSignature rootSyntax theorySyntax))

def dumpQueryCommand (lhs rhs root theory : Syntax) : TermElabM Unit := do
  let sig ← elaborateSignature root theory
  let left ← Unification.Problem.saturatePattern (← elabTerm lhs none)
  let right ← Unification.Problem.saturatePattern (← elabTerm rhs none)
  logInfo (← renderQuery sig { lhs := left, rhs := right }).script

end Certification

end Maude

elab "#dump_maude_model " root:term " mod " theory:term : command => do
  Lean.Elab.Command.liftTermElabM <|
    Maude.dumpModelCommand root.raw theory.raw

elab "#dump_maude_term " pattern:term " from " root:term : command => do
  Lean.Elab.Command.liftTermElabM <|
    Maude.dumpTermCommand pattern.raw root.raw

elab "#dump_maude_model " "certification " root:term " mod " theory:term : command => do
  Lean.Elab.Command.liftTermElabM <|
    Maude.Certification.dumpModelCommand root.raw theory.raw

elab "#dump_maude_query " "certification " lhs:term " =? " rhs:term " from " root:term
    " mod " theory:term : command => do
  Lean.Elab.Command.liftTermElabM <|
    Maude.Certification.dumpQueryCommand lhs.raw rhs.raw root.raw theory.raw
