import conPanna.Unification
import conPanna.StructuralSemantics

open Lean Meta Elab Term Tactic
open framework framework.Patterns


/-
`Narrowing` is an adapter around the generic unification API.  It extracts the
structural equation between a rule LHS and a source-pattern term, delegates
that equation to a backend, and reconnects the candidate substitutions to the
rule RHS and both constraints.
-/
namespace Narrowing


/-
`Narrowing.Problem` projects a rule closure and constrained source closure,
saturates their shared variables once, and forms the structural equation
`rule.lhs = source.term` consumed by unification.
-/
namespace Problem

/-- A rule closure whose binders were saturated together exactly once. -/
structure SaturatedRule where
  value : Expr
  closure : Unification.Problem.SaturatedPattern
  lhs : Expr
  rhs : Expr
  requires : Expr

/-- A constrained pattern closure saturated exactly once. -/
structure SaturatedConstrainedPattern where
  value : Expr
  closure : Unification.Problem.SaturatedPattern
  term : Expr
  requires : Expr

/-- Everything needed for one atomic structural narrowing problem. -/
structure Input where
  rule : SaturatedRule
  source : SaturatedConstrainedPattern
  unification : Unification.Problem.Input

/-- The atomic problems obtained by decomposing one finite source pattern. -/
structure PatternInput where
  stateType : Expr
  sources : Array Expr
  branches : Array Input

private def project (projection : Name) (value : Expr) : MetaM Expr := do
  withTransparency .all <| whnf (← mkAppM projection #[value])

def saturateRule (rule : Expr) : MetaM SaturatedRule := do
  let closure ← Unification.Problem.saturatePattern rule
  let application ← withTransparency .all <| whnf closure.application
  try
    return {
      value := rule
      closure
      lhs := ← project ``framework.Rules.RuleBody.lhs application
      rhs := ← project ``framework.Rules.RuleBody.rhs application
      requires := ← project ``framework.Rules.RuleBody.requires application
    }
  catch _ =>
    throwError "`narrow` expects a closure returning `RuleBody`"

def saturateSource (source : Expr) : MetaM SaturatedConstrainedPattern := do
  let closure ← Unification.Problem.saturatePattern source
  let application ← withTransparency .all <| whnf closure.application
  try
    return {
      value := source
      closure
      term := ← project ``framework.Patterns.APattBody.term application
      requires := ← project ``framework.Patterns.APattBody.requires application
    }
  catch _ =>
    throwError "`narrow` expects a closure returning `APattBody`"

/-- Form the backend problem `rule.lhs = source.term`. -/
def ofTerms (rule source : Expr) : MetaM Input := do
  let rule ← saturateRule rule
  let source ← saturateSource source
  let lhs : Unification.Problem.SaturatedPattern := {
    rule.closure with application := rule.lhs
  }
  let rhs : Unification.Problem.SaturatedPattern := {
    source.closure with application := source.term
  }
  return { rule, source, unification := { lhs, rhs } }

/--
Expose the atomic leaves of a finite pattern built from `Disjunction`,
`EmptyPattern`, and constrained-pattern closures.
-/
partial def atomicSources (source : Expr) : MetaM (Array Expr) := do
  let reduced ← withTransparency .all <| whnf source
  let arguments := reduced.getAppArgs
  if reduced.getAppFn.isConstOf ``framework.Patterns.Disjunction.mk then
    unless arguments.size >= 2 do
      throwError "malformed source-pattern disjunction"
    let left ← atomicSources arguments[arguments.size - 2]!
    let right ← atomicSources arguments[arguments.size - 1]!
    return left ++ right
  if reduced.getAppFn.isConstOf ``framework.Patterns.EmptyPattern.empty then
    return #[]
  return #[source]

/-- Decompose a finite source pattern and form one problem per atomic leaf. -/
def ofPattern (rule source : Expr) : MetaM PatternInput := do
  let typeRule ← saturateRule rule
  let stateType ← inferType typeRule.lhs
  let sources ← atomicSources source
  let mut branches := #[]
  for atomicSource in sources do
    try
      branches := branches.push (← ofTerms rule atomicSource)
    catch _ =>
      throwError
        "`narrow` expects a finite pattern built from `APattBody` closures, `Disjunction`, and `EmptyPattern`"
  return { stateType, sources, branches }

def symbolicArguments (problem : Input) : Array Expr :=
  Unification.Problem.symbolicArguments problem.unification

end Problem


namespace Goal

/-!
`Goal` recognizes the semantic goal shapes manipulated by narrowing-side
automation. It extracts user objects without deciding how their propositions
will be proved.
-/

/-- The two user objects encoded in a `Subsumes` target. -/
structure SubsumptionInput where
  source : Expr
  target : Expr
  theory? : Option Expr := none

def ofSubsumesType (type : Expr) : MetaM SubsumptionInput := do
  let type ← instantiateMVars type
  let arguments := type.getAppArgs
  if type.getAppFn.isConstOf ``framework.Patterns.Subsumes &&
      arguments.size >= 2 then
    return {
      source := arguments[arguments.size - 2]!
      target := arguments[arguments.size - 1]!
    }
  if type.getAppFn.isConstOf ``framework.Patterns.SubsumesMod &&
      arguments.size >= 3 then
    return {
      source := arguments[arguments.size - 2]!
      target := arguments[arguments.size - 1]!
      theory? := some arguments[0]!
    }
  throwError
    "`subsume` expects a goal of the form `source ⊑ target` or `source ⊑[theory] target`"

end Goal


namespace Backend

/-!
`Backend` is the narrow bridge from a narrowing problem to the common
unification solution-set format. Theory-specific dispatch can later replace
this free-only bridge without affecting successor construction.
-/

/--
The backend bridge. Without a theory it preserves free narrowing; with a
structural theory it uses the declared commutative operations. Backend-private
evidence is erased here, so materialization remains solver-neutral.
-/
def solve (problem : Problem.Input) (theory? : Option Expr := none) :
    MetaM Unification.Certificate.SolutionSet := do
  match theory? with
  | none =>
      let output ← Unification.Free.solve problem.unification
      return { alternatives := output.candidates.map (·.alternative) }
  | some theory =>
      Unification.solveStructuralTheory theory problem.unification

/-- One unifier together with the source branch from which it was computed. -/
structure BranchAlternative where
  problem : Problem.Input
  alternative : Unification.Certificate.Alternative

/-- One atomic source branch and its complete computed solution set. -/
structure BranchSolution where
  problem : Problem.Input
  solutionSet : Unification.Certificate.SolutionSet

/-- Branch-local solution sets together with their flattened alternatives. -/
structure PatternSolution where
  branches : Array BranchSolution
  alternatives : Array BranchAlternative

/-- Solve every atomic branch and retain both completeness boundaries. -/
def solvePatternDetailed (input : Problem.PatternInput)
    (theory? : Option Expr := none) : MetaM PatternSolution := do
  let mut branches := #[]
  let mut alternatives := #[]
  for problem in input.branches do
    let solutionSet ← solve problem theory?
    branches := branches.push { problem, solutionSet }
    for alternative in solutionSet.alternatives do
      alternatives := alternatives.push { problem, alternative }
  return { branches, alternatives }

/-- Solve every atomic branch while retaining its branch-local substitutions. -/
def solvePattern (input : Problem.PatternInput) (theory? : Option Expr := none) :
    MetaM (Array BranchAlternative) := do
  return (← solvePatternDetailed input theory?).alternatives

end Backend


namespace Materialization

/-!
`Materialization` turns each substitution alternative into a constrained
successor by applying it to the rule RHS and both conditions, then combines
all successors into the generated post pattern.
-/

/-- A generated post together with its concrete (possibly heterogeneous) type. -/
structure Post where
  type : Expr
  value : Expr

private partial def withBasisVariables
    {α : Type}
    (types : Array Expr) (index : Nat) (variables : Array Expr)
    (continuation : Array Expr → MetaM α) : MetaM α := do
  if _h : index < types.size then
    withLocalDeclD (Name.mkSimple s!"u{index + 1}") types[index]!
      fun basisVariable =>
        withBasisVariables types (index + 1) (variables.push basisVariable)
          continuation
  else
    continuation variables

private def projections (problem : Problem.Input)
    (alternative : Unification.Certificate.Alternative)
    (basis : Array Expr) : MetaM (Expr × Expr × Expr) := do
  let mut images := #[]
  for image in alternative.images do
    images := images.push (← whnf
      (Unification.Certificate.instantiateImage image basis))
  let ruleCount := problem.rule.closure.arguments.size
  let sourceCount := problem.source.closure.arguments.size
  unless images.size == ruleCount + sourceCount do
    throwError "a narrowing alternative has the wrong number of images"
  let ruleArguments := images.extract 0 ruleCount
  let sourceArguments := images.extract ruleCount images.size
  let ruleValue ← withTransparency .all <|
    whnf (mkAppN problem.rule.value ruleArguments)
  let sourceValue ← withTransparency .all <|
    whnf (mkAppN problem.source.value sourceArguments)
  let rhs ← withTransparency .all <|
    whnf (← mkAppM ``framework.Rules.RuleBody.rhs #[ruleValue])
  let ruleRequires ← withTransparency .all <|
    whnf (← mkAppM ``framework.Rules.RuleBody.requires #[ruleValue])
  let sourceRequires ← withTransparency .all <|
    whnf (← mkAppM ``framework.Patterns.APattBody.requires #[sourceValue])
  return (rhs, sourceRequires, ruleRequires)

/-- Turn one backend alternative into its constrained successor closure. -/
def successor (problem : Problem.Input)
    (alternative : Unification.Certificate.Alternative) : MetaM Expr := do
  withBasisVariables alternative.basisTypes 0 #[] fun basis => do
    let (rhs, sourceRequires, ruleRequires) ←
      projections problem alternative basis
    let requires ← mkAppM ``And #[sourceRequires, ruleRequires]
    let body ← mkAppM ``framework.Patterns.APattBody.mk #[rhs, requires]
    mkLambdaFVars basis body

private def empty (stateType : Expr) : MetaM Expr := do
  let .sort (.succ level) ← whnf (← inferType stateType)
    | throwError "the narrowing state is not a type"
  return mkApp
    (mkConst ``framework.Patterns.EmptyPattern.empty [level]) stateType

private def disjoin (left right : Expr) : MetaM Expr :=
  mkAppM ``framework.Patterns.Disjunction.mk #[left, right]

/--
Materialize every MGU as an atomic successor and combine the successors into
the complete `Pattern` post.  The free backend yields zero or one successor;
the fold already supports a future multi-unifier backend.
-/
def post (stateType : Expr)
    (alternatives : Array Backend.BranchAlternative) : MetaM Post := do
  let value ← if alternatives.isEmpty then
      empty stateType
    else
      let some last := alternatives.back?
        | throwError "nonempty narrowing result unexpectedly had no last alternative"
      let mut value ← successor last.problem last.alternative
      for alternative in alternatives.toList.dropLast.reverse do
        value ← disjoin
          (← successor alternative.problem alternative.alternative) value
      pure value
  return { type := ← inferType value, value }

end Materialization


namespace Closure

/-!
`Closure` discovers which user definitions should be unfolded while replaying
semantic proofs. It is proof-support machinery and does not participate in
unification or successor computation.
-/

/--
Find the definition, if any, that directly supplies a rule or pattern closure.
For example, both `advance` and `fun x y => advance x y` select `advance`.
Record constructors and fully inline closures need no extra unfolding lemma.
-/
private partial def closureDefinition? (expression : Expr) : Option Name :=
  match expression.consumeMData with
  | .lam _ _ body _ => closureDefinition? body
  | .letE _ _ _ body _ => closureDefinition? body
  | expression =>
      match expression.getAppFn with
      | .const name _ => some name
      | _ => none

def unfoldingDefinitions (expressions : Array Expr) : CoreM (Array Name) := do
  let environment ← getEnv
  let mut result := #[]
  for expression in expressions do
    let some name := closureDefinition? expression | continue
    let isDefinition := match environment.find? name with
      | some (.defnInfo _) | some (.opaqueInfo _) => true
      | _ => false
    if isDefinition && !result.contains name then
      result := result.push name
  return result

end Closure


namespace Certification

/-!
`Certification` proves that a materialized post is exactly the semantic
one-step image. This obligation is separate from structural unifier
certification because it also accounts for rule RHSs and constraints.
-/

/--
Certify that the materialized post is the complete one-step image.  This
prototype replays free constructor reasoning with `simp` and `grind`; an AC
backend can replace this namespace with certificate replay for its theory.
-/
def prove (ref : Syntax) (unfoldingExpressions : Array Expr)
    (ruleSyntax sourceSyntax : TSyntax `term) (postIdent : Ident) :
    TacticM Ident := do
  let narrowingIdent ←
    Unification.Exposure.freshVisibleIdent ref `narrowing
  let unfoldNames ← Closure.unfoldingDefinitions unfoldingExpressions
  let unfoldSimps ← unfoldNames.mapM fun name =>
    `(Parser.Tactic.simpLemma| $(mkIdent name):ident)
  try
    evalTactic (← `(tactic|
      have $narrowingIdent:ident :
          framework.Rules.NarrowsTo
            $ruleSyntax $sourceSyntax ($postIdent:term) := by
        simp only [framework.Rules.NarrowsTo,
          framework.Rules.postImage_disjunction,
          framework.Patterns.Pattern.semantics,
          $postIdent:term, $unfoldSimps,*]
        simp [framework.Rules.postImage,
          framework.Patterns.Pattern.semantics,
          framework.Patterns.APatt.semantics,
          framework.Rules.AtRule.semantics,
          $unfoldSimps,*] <;>
          grind))
  catch exception =>
    throwErrorAt ref m!"failed to certify the generated narrowing post:\n{exception.toMessageData}"
  return narrowingIdent

private def conjunction (propositions : Array Expr) : MetaM Expr := do
  if propositions.isEmpty then
    return mkConst ``True
  let mut result := propositions[propositions.size - 1]!
  for proposition in propositions.toList.dropLast.reverse do
    result ← mkAppM ``And #[proposition, result]
  return result

/-- One completeness proposition per atomic source branch. -/
def completenessBundleType (theory : Expr)
    (branches : Array Backend.BranchSolution) : MetaM (Array Expr × Expr) := do
  let mut propositions := #[]
  for branch in branches do
    propositions := propositions.push
      (← Unification.ModCertificate.completenessType theory
        branch.problem.unification branch.solutionSet)
  return (propositions, ← conjunction propositions)

private def splitConjunction (propositions : Array Expr) (proof : Expr) :
    MetaM (Array Expr) := do
  if propositions.isEmpty then
    return #[]
  if propositions.size == 1 then
    return #[proof]
  let mut result := #[]
  let mut remaining := proof
  for _ in [:propositions.size - 1] do
    result := result.push (← mkAppM ``And.left #[remaining])
    remaining ← mkAppM ``And.right #[remaining]
  return result.push remaining

/--
Lift atomic unification completeness into a `mapsIntoMod` proof. The lifting
is generic; solver-specific reasoning is confined to the supplied proofs.
-/
def proveMapsInto (ref : Syntax) (rule source : Expr)
    (sourceBranches : Array Expr)
    (ruleSyntax sourceSyntax theorySyntax : TSyntax `term)
    (postIdent : Ident) (propositions : Array Expr) (bundleProof : Expr) :
    TacticM Ident := do
  let proofs ← splitConjunction propositions bundleProof
  let goal ← getMainGoal
  let mapsIntoName ← goal.withContext do
    return (← getLCtx).getUnusedName `mapsInto
  let mapsIntoIdent := mkIdentFrom ref mapsIntoName
  let unfoldNames ← Closure.unfoldingDefinitions
    (#[rule, source] ++ sourceBranches)
  let unfoldSimps ← unfoldNames.mapM fun name =>
    `(Parser.Tactic.simpLemma| $(mkIdent name):ident)

  let mapsIntoTypeSyntax ← `(term|
    framework.Rules.mapsIntoMod $theorySyntax
      $ruleSyntax $sourceSyntax ($postIdent:term))
  let mapsIntoType ← goal.withContext do
    Tactic.elabTerm mapsIntoTypeSyntax.raw none

  -- Prove a function from the atomic completeness certificates to maps-into,
  -- then apply it immediately.  The certificates remain scoped to this proof
  -- instead of leaking into the user's subsumption continuation.
  let mut liftingType := mapsIntoType
  for offset in [:propositions.size] do
    let i := propositions.size - offset - 1
    liftingType := .forallE
      (Name.mkSimple s!"unificationCompleteness{i + 1}")
      propositions[i]! liftingType .default
  let liftingProof ← goal.withContext do
    mkFreshExprMVar (some liftingType)
  let mut liftingGoal := liftingProof.mvarId!
  for _ in propositions do
    let (_, nextGoal) ← liftingGoal.withContext liftingGoal.intro1P
    liftingGoal := nextGoal
  setGoals [liftingGoal]
  try
    evalTactic (← `(tactic|
      simp only [framework.Rules.mapsIntoMod,
        framework.Patterns.PatternMod.semantics,
        framework.Patterns.APattMod.semantics,
        framework.Rules.AtRuleMod.semantics,
        $postIdent:ident, $unfoldSimps,*] <;>
        grind [Structural.EqMod.trans, Structural.EqMod.symm]))
  catch exception =>
    setGoals [goal]
    throwErrorAt ref m!"failed to lift unification completeness into maps-into:\n{exception.toMessageData}"

  setGoals [goal]
  let mapsIntoProof ← goal.withContext do
    let liftingProof ← instantiateMVars liftingProof
    return mkAppN liftingProof proofs
  let (_, goal) ← goal.withContext do
    goal.note mapsIntoName mapsIntoProof (some mapsIntoType)
  setGoals [goal]
  return mapsIntoIdent

end Certification


namespace Tactic

/-!
`Narrowing.Tactic` connects post computation to the existential decomposition
created by `mapsInto_via_narrowing`. It binds the generated `post` and leaves
only semantic subsumption to the surrounding proof.
-/

private def ensureDecompositionGoal (goal : MVarId) : MetaM Unit := do
  let type ← whnf (← goal.getType)
  unless type.getAppFn.isConstOf ``Exists do
    throwError "`narrow` expects the post goal from `apply mapsInto_via_narrowing`"

private def bindPost (ref : Syntax) (post : Materialization.Post) :
    TacticM Ident := do
  let goal ← getMainGoal
  let name ← goal.withContext do
    return (← getLCtx).getUnusedName `post
  let goal ← goal.define name post.type post.value
  let (_, goal) ← goal.intro1P
  setGoals [goal]
  return mkIdentFrom ref name

/--
Generate and bind the exact one-step post, then fill the post and narrowing
parts of the explicit decomposition.  Only subsumption remains.
-/
def run (ref : Syntax) (ruleSyntax sourceSyntax : TSyntax `term) : TacticM Unit := do
  let initialGoal ← getMainGoal
  let (rule, source, sourceBranches, generatedPost) ← initialGoal.withContext do
    ensureDecompositionGoal initialGoal
    let rule ← Tactic.elabTerm ruleSyntax.raw none
    let source ← Tactic.elabTerm sourceSyntax.raw none
    let problem ← Problem.ofPattern rule source
    let alternatives ← Backend.solvePattern problem
    let generatedPost ← Materialization.post problem.stateType alternatives
    return (rule, source, problem.sources, generatedPost)

  let postIdent ← bindPost ref generatedPost
  let narrowingIdent ← Certification.prove ref
    (#[rule, source] ++ sourceBranches)
    ruleSyntax sourceSyntax postIdent

  evalTactic (← `(tactic|
    refine ⟨_, inferInstance, $postIdent:term,
      $narrowingIdent:term, ?_⟩))

/--
Run theory-indexed narrowing, accept one completeness certificate per atomic
unification problem, and leave subsumption as the ordinary proof continuation.
-/
def runModCertified (ref : Syntax)
    (ruleSyntax sourceSyntax theorySyntax certificateSyntax : TSyntax `term) :
    TacticM Unit := do
  let initialGoal ← getMainGoal
  let (rule, source, sourceBranches, generatedPost,
      propositions, bundleType) ← initialGoal.withContext do
    ensureDecompositionGoal initialGoal
    let rule ← Tactic.elabTerm ruleSyntax.raw none
    let source ← Tactic.elabTerm sourceSyntax.raw none
    let theoryType ← mkConstWithFreshMVarLevels ``Structural.Theory
    let theory ← Tactic.elabTerm theorySyntax.raw (some theoryType)
    let problem ← Problem.ofPattern rule source
    let solution ← Backend.solvePatternDetailed problem (some theory)
    let generatedPost ←
      Materialization.post problem.stateType solution.alternatives
    let (propositions, bundleType) ←
      Certification.completenessBundleType theory solution.branches
    return (rule, source, problem.sources, generatedPost,
      propositions, bundleType)

  let bundleProof ← initialGoal.withContext do
    Lean.Elab.Tactic.elabTermEnsuringType certificateSyntax.raw
      (some bundleType)
  let postIdent ← bindPost ref generatedPost
  let mapsIntoIdent ← Certification.proveMapsInto ref rule source
    sourceBranches ruleSyntax sourceSyntax theorySyntax postIdent propositions
    bundleProof

  evalTactic (← `(tactic|
    refine ⟨_, inferInstance, $postIdent:term, $mapsIntoIdent:term, ?_⟩))

end Tactic


namespace Subsumption

/-!
`Subsumption` is the current lightweight prover for the residual inclusion
between the generated post and the user's target pattern. Its semantic goal
is stable even if stronger constraint automation replaces this prototype.
-/

/-- One assignment proposed by an external structural matcher. -/
structure MatchAssignment where
  metavariable : MVarId
  value : Expr

/-- One directional match of a target atom against a source atom. -/
structure MatchCandidate where
  assignments : Array MatchAssignment

/-- A pluggable directional matcher for structural terms. -/
abbrev StructuralMatcher :=
  Expr → Expr → Expr → MetaM (Array MatchCandidate)

initialize structuralMatcherRef :
    IO.Ref (Option StructuralMatcher) ← IO.mkRef none

/-- Register an optional external matcher used only to find existential witnesses. -/
def registerStructuralMatcher (matcher : StructuralMatcher) : IO Unit :=
  structuralMatcherRef.set (some matcher)

private def externalMatches (theory pattern subject : Expr) :
    MetaM (Array MatchCandidate) := do
  let some matcher ← structuralMatcherRef.get
    | throwError "the Maude matcher is enabled but `conPanna.Maude` is not imported"
  matcher theory pattern subject

namespace Structural

private structure ACUOperator where
  operation : Expr
  identity : Expr

private partial def identityDeclarations (declarations : Expr) : MetaM (Array ACUOperator) := do
  let declarations ← withTransparency .all <| whnf declarations
  let arguments := declarations.getAppArgs
  if declarations.getAppFn.isConstOf ``List.nil then
    return #[]
  unless declarations.getAppFn.isConstOf ``List.cons && arguments.size >= 3 do
    throwError "could not reduce structural identity declarations"
  let declaration := arguments[arguments.size - 2]!
  let tail := arguments[arguments.size - 1]!
  let remaining ← identityDeclarations tail
  let operation ← withTransparency .all <|
    whnf (← mkAppM ``_root_.Structural.IdentityDeclaration.operation #[declaration])
  let identity ← withTransparency .all <|
    whnf (← mkAppM ``_root_.Structural.IdentityDeclaration.element #[declaration])
  return remaining.push { operation, identity }

private def acuOperators (theory : Expr) : MetaM (Array ACUOperator) := do
  identityDeclarations (← mkAppM ``_root_.Structural.Theory.identities #[theory])

private partial def mvarCount : Expr → Nat
  | .mvar _ => 1
  | .app function argument => mvarCount function + mvarCount argument
  | .lam _ type body _ | .forallE _ type body _ =>
      mvarCount type + mvarCount body
  | .letE _ type value body _ =>
      mvarCount type + mvarCount value + mvarCount body
  | .mdata _ expression | .proj _ _ expression => mvarCount expression
  | _ => 0

private partial def normalize (theory : Expr) (acu : ACUOperator)
    (expression : Expr) : MetaM (List Expr × Expr) := do
  let expression ← instantiateMVars expression
  if !expression.hasExprMVar &&
      (← withoutModifyingState <| isDefEq expression acu.identity) then
    return ([], ← mkAppM ``_root_.Structural.EqMod.reflAt #[theory, expression])
  let exposed ← withTransparency .reducible <| whnf expression
  match exposed with
  | .app (.app operation left) right =>
      if ← withoutModifyingState <| isDefEq operation acu.operation then
        let (leftAtoms, leftProof) ← normalize theory acu left
        let (rightAtoms, rightProof) ← normalize theory acu right
        let congruence ← mkAppM ``_root_.Structural.EqMod.congrAt
          #[theory, acu.operation, leftProof, rightProof]
        let leftList ← mkListLit (← inferType acu.identity) leftAtoms
        let rightList ← mkListLit (← inferType acu.identity) rightAtoms
        let append ← mkAppM ``_root_.Structural.EqMod.foldOperation_append
          #[theory, acu.operation, acu.identity, leftList, rightList]
        return (leftAtoms ++ rightAtoms,
          ← mkAppM ``_root_.Structural.EqMod.transAt
            #[theory, congruence, append])
  | _ => pure ()
  let identityInstance ← synthInstance (← mkAppM
    ``_root_.Structural.HasIdentity #[theory, acu.operation, acu.identity])
  let identityRight ← mkAppOptM
    ``_root_.Structural.EqMod.identityRightAt
    #[some theory, none, some acu.operation, some acu.identity,
      some expression, some identityInstance]
  return ([expression], ← mkAppM ``_root_.Structural.EqMod.symmAt
    #[theory, identityRight])

private def swapAt (elementType : Expr) (values : Array Expr) (index : Nat) :
    MetaM (Array Expr × Expr) := do
  let left := values[index - 1]!
  let right := values[index]!
  let tail := values.toList.drop (index + 1)
  let tailExpression ← mkListLit elementType tail
  let mut proof ← mkAppM ``List.Perm.swap #[right, left, tailExpression]
  for prefixValue in (values.toList.take (index - 1)).reverse do
    proof ← mkAppM ``List.Perm.cons #[prefixValue, proof]
  let mut swapped := values
  swapped := swapped.set! (index - 1) right
  swapped := swapped.set! index left
  return (swapped, proof)

private partial def permutationProof (elementType : Expr)
    (left right : Array Expr) : MetaM Expr := do
  unless left.size == right.size do
    throwError "ACU normal forms have different sizes"
  if left.isEmpty then
    let empty ← mkListLit elementType []
    return ← mkAppM ``List.Perm.refl #[empty]
  let target := right[0]!
  let mut matchIndex? : Option Nat := none
  for preferRigid in [true, false] do
    for index in [:left.size] do
      if matchIndex?.isNone &&
          (!left[index]!.hasExprMVar == preferRigid) then
        if ← isDefEq left[index]! target then
          matchIndex? := some index
  let some matchIndex := matchIndex?
    | throwError "ACU normal forms contain different atoms"
  let mut current := left
  let originalList ← mkListLit elementType left.toList
  let mut frontProof ← mkAppM ``List.Perm.refl #[originalList]
  for offset in [:matchIndex] do
    let index := matchIndex - offset
    let (next, swapProof) ← swapAt elementType current index
    frontProof ← mkAppM ``List.Perm.trans #[frontProof, swapProof]
    current := next
  let tailProof ← permutationProof elementType
    (current.extract 1 current.size) (right.extract 1 right.size)
  let restProof ← mkAppM ``List.Perm.cons #[target, tailProof]
  return ← mkAppM ``List.Perm.trans #[frontProof, restProof]

private def proveACU (theory left right : Expr) : MetaM Expr := do
  for acu in ← acuOperators theory do
    let saved ← saveState
    try
      let (leftAtoms, leftProof) ← normalize theory acu left
      let (rightAtoms, rightProof) ← normalize theory acu right
      let elementType ← inferType acu.identity
      let permutation ← permutationProof elementType
        leftAtoms.toArray rightAtoms.toArray
      let permutationProof ← mkAppM
        ``_root_.Structural.EqMod.foldOperation_perm
        #[theory, acu.operation, acu.identity, permutation]
      let reverseRight ← mkAppM ``_root_.Structural.EqMod.symmAt
        #[theory, rightProof]
      return ← mkAppM ``_root_.Structural.EqMod.transAt #[theory,
        leftProof, ← mkAppM ``_root_.Structural.EqMod.transAt
          #[theory, permutationProof, reverseRight]]
    catch _ =>
      restoreState saved
  throwError "the terms are not equal modulo a registered ACU operation"

private partial def proveEqMod (theory left right : Expr) : MetaM Expr := do
  let left ← instantiateMVars left
  let right ← instantiateMVars right
  if ← isDefEq left right then
    return ← mkAppM ``_root_.Structural.EqMod.reflAt #[theory, left]

  let left ← withTransparency .all <| whnf left
  let right ← withTransparency .all <| whnf right
  let leftArguments := left.getAppArgs
  let rightArguments := right.getAppArgs
  let mut constructorFailure? : Option MessageData := none
  if leftArguments.size == rightArguments.size then
    let saved ← saveState
    try
      unless ← withoutModifyingState <|
          isDefEq left.getAppFn right.getAppFn do
        throwError "different constructor heads"
      let constructorInstance ← synthInstance (← mkAppM
        ``_root_.Structural.HasConstructor #[theory, left.getAppFn])
      let mut order := (Array.range leftArguments.size).toList
      order := order.mergeSort fun first second =>
        mvarCount leftArguments[first]! + mvarCount rightArguments[first]! <
        mvarCount leftArguments[second]! + mvarCount rightArguments[second]!
      let mut proofs : Array (Option Expr) :=
        Array.replicate leftArguments.size none
      for index in order do
        proofs := proofs.set! index (some (← proveEqMod theory
          leftArguments[index]! rightArguments[index]!))
      let mut congruence ← mkAppOptM
        ``_root_.Structural.ConstructorCongruence.headAt
        #[some theory, none, some left.getAppFn, some constructorInstance]
      for proof in proofs do
        congruence ← mkAppM
          ``_root_.Structural.ConstructorCongruence.appAt
          #[theory, congruence, proof.get!]
      return ← mkAppM ``_root_.Structural.EqMod.constructorAt
        #[theory, congruence]
    catch error =>
      constructorFailure? := some error.toMessageData
      restoreState saved
  try
    proveACU theory left right
  catch error =>
    match constructorFailure? with
    | some constructorFailure =>
        throwError m!"constructor congruence failed:\n{constructorFailure}\nstructural normalization failed:\n{error.toMessageData}"
    | none => throw error

private def eqModParts? (type : Expr) : MetaM (Option (Expr × Expr × Expr)) := do
  let type ← withTransparency .reducible <| whnf (← instantiateMVars type)
  let arguments := type.getAppArgs
  unless type.getAppFn.isConstOf ``_root_.Structural.EqMod &&
      arguments.size >= 3 do
    return none
  return some (arguments[0]!, arguments[arguments.size - 2]!,
    arguments[arguments.size - 1]!)

private def proveMatchedEqMod (theory pattern subject : Expr) : MetaM Expr := do
  unless (← getOptions).getBool `conPanna.unification.useMaude false do
    return ← proveEqMod theory pattern subject
  for candidate in ← externalMatches theory pattern subject do
    let saved ← saveState
    try
      for assignment in candidate.assignments do
        assignment.metavariable.assign assignment.value
      return ← proveEqMod theory pattern subject
    catch _ => restoreState saved
  throwError "no external match passed Lean's structural-equality check"

private def proveEqModGoal (goal : MVarId) : MetaM Unit := goal.withContext do
  let some (theory, left, right) ← eqModParts? (← goal.getType)
    | throwError "not a structural equality goal"
  let saved ← saveState
  try
    goal.assign (← proveEqMod theory left right)
    return
  catch _ =>
    restoreState saved

  for declaration in ← getLCtx do
    let some (hypTheory, hypLeft, hypRight) ← eqModParts? declaration.type
      | continue
    unless ← withoutModifyingState <| isDefEq theory hypTheory do continue
    if ← withoutModifyingState <| isDefEq right hypRight then
      let saved ← saveState
      try
        let initialProof ← proveMatchedEqMod theory left hypLeft
        goal.assign (← mkAppM ``_root_.Structural.EqMod.transAt
          #[theory, initialProof, mkFVar declaration.fvarId])
        return
      catch _ => restoreState saved
    if ← withoutModifyingState <| isDefEq right hypLeft then
      let saved ← saveState
      try
        let initialProof ← proveMatchedEqMod theory left hypRight
        let reversed ← mkAppM ``_root_.Structural.EqMod.symmAt
          #[theory, mkFVar declaration.fvarId]
        goal.assign (← mkAppM ``_root_.Structural.EqMod.transAt
          #[theory, initialProof, reversed])
        return
      catch _ => restoreState saved
  throwError m!"could not prove structural equality modulo the registered theory:\n  {left}\n  {right}"

private def decomposableHypothesis? (type : Expr) : MetaM Bool := do
  let type ← withTransparency .reducible <| whnf type
  let head := type.getAppFn
  return head.isConstOf ``And || head.isConstOf ``Or ||
    head.isConstOf ``Exists || head.isConstOf ``False

private partial def solve (goal : MVarId) : MetaM Unit := goal.withContext do
  let target ← withTransparency .reducible <| whnf (← goal.getType)

  for declaration in ← getLCtx do
    if ← isDefEq declaration.type target then
      goal.assign (mkFVar declaration.fvarId)
      return

  if target.isForall then
    let (_, next) ← goal.intro1P
    solve next
    return

  for declaration in ← getLCtx do
    if ← decomposableHypothesis? declaration.type then
      let branches ← goal.cases declaration.fvarId
      for branch in branches do
        solve branch.mvarId
      return

  let head := target.getAppFn
  if head.isConstOf ``True then
    goal.assign (mkConst ``True.intro)
    return
  if head.isConstOf ``And then
    let subgoals ← goal.apply (mkConst ``And.intro)
    for subgoal in subgoals do solve subgoal
    return
  if head.isConstOf ``Exists then
    let arguments := target.getAppArgs
    let witness ← mkFreshExprMVar (some arguments[0]!)
    let body ← whnf (mkApp arguments[1]! witness)
    let proof ← mkFreshExprMVar (some body)
    goal.assign (← mkAppOptM ``Exists.intro
      #[some arguments[0]!, some arguments[1]!, some witness, some proof])
    solve proof.mvarId!
    return
  if head.isConstOf ``Or then
    let mut failures := #[]
    for lemma in [``Or.inl, ``Or.inr] do
      let saved ← saveState
      try
        let [subgoal] ← goal.apply (mkConst lemma)
          | throwError "unexpected disjunction subgoals"
        solve subgoal
        return
      catch error =>
        failures := failures.push error.toMessageData
        restoreState saved
    throwError m!"no target disjunct subsumes this post branch\n{MessageData.joinSep failures.toList (m!"\n")}"
  if (← eqModParts? target).isSome then
    proveEqModGoal goal
    return
  throwError m!"`subsume` could not close {target}"

/-- Prove one fully instantiated equality modulo the registered theory. -/
def runRfl : TacticM Unit := do
  let goal ← getMainGoal
  let proof ← goal.withContext do
    let some (theory, left, right) ← eqModParts? (← goal.getType)
      | throwError "`structural_rfl` expects an equality-modulo-theory goal"
    proveEqMod theory left right
  goal.assign proof
  replaceMainGoal []

end Structural

private partial def splitModDisjunctions (goal : MVarId) :
    MetaM (Array MVarId) := goal.withContext do
  let input ← Goal.ofSubsumesType (← goal.getType)
  let some _ := input.theory? | return #[goal]
  let source ← withTransparency .all <| whnf input.source
  if source.getAppFn.isConstOf ``framework.Patterns.Disjunction.mk then
    let lemma ← mkConstWithFreshMVarLevels
      ``framework.Patterns.disjunction_subsumes_mod
    let subgoals ← goal.apply
      lemma
    let mut leaves := #[]
    for subgoal in subgoals do
      leaves := leaves ++ (← splitModDisjunctions subgoal)
    return leaves
  return #[goal]

private def unfoldingNames (input : Goal.SubsumptionInput) :
    MetaM (Array Name) := do
  let sourceBranches ← Problem.atomicSources input.source
  let targetBranches ← Problem.atomicSources input.target
  Closure.unfoldingDefinitions
    (#[input.source, input.target] ++ sourceBranches ++ targetBranches)

/-- Leave one pattern-level subsumption goal for each atomic source branch. -/
def cases : TacticM Unit := do
  let goal ← getMainGoal
  let input ← goal.withContext do
    Goal.ofSubsumesType (← goal.getType)
  match input.theory? with
  | none =>
      let unfoldNames ← goal.withContext <| unfoldingNames input
      let unfoldSimps ← unfoldNames.mapM fun name =>
        `(Parser.Tactic.simpLemma| $(mkIdent name):ident)
      evalTactic (← `(tactic|
        simp [framework.Patterns.Subsumes,
          framework.Patterns.Pattern.semantics,
          framework.Patterns.APatt.semantics,
          $unfoldSimps,*] <;>
          grind))
  | some _ =>
      let mut branches := #[]
      for goal in ← getGoals do
        branches := branches ++ (← splitModDisjunctions goal)
      setGoals branches.toList

/-- Prove one atomic residual inclusion. -/
def atom : TacticM Unit := do
  let goal ← getMainGoal
  let input ← goal.withContext do
    Goal.ofSubsumesType (← goal.getType)
  let unfoldNames ← goal.withContext <| unfoldingNames input
  let unfoldSimps ← unfoldNames.mapM fun name =>
    `(Parser.Tactic.simpLemma| $(mkIdent name):ident)
  match input.theory? with
  | none =>
      evalTactic (← `(tactic|
        simp [framework.Patterns.Subsumes,
          framework.Patterns.Pattern.semantics,
          framework.Patterns.APatt.semantics,
          $unfoldSimps,*] <;>
          grind))
  | some _ =>
      evalTactic (← `(tactic|
        simp only [framework.Patterns.SubsumesMod,
          framework.Patterns.PatternMod.semantics,
          framework.Patterns.APattMod.semantics,
          $unfoldSimps,*]))
      let goals ← getGoals
      for goal in goals do
        goal.withContext <| Structural.solve goal
      setGoals []

/-- Simplify and prove the residual semantic inclusion between patterns. -/
def run : TacticM Unit := do
  cases
  let goals ← getGoals
  for goal in goals do
    setGoals [goal]
    atom
  setGoals []

end Subsumption

/-- Compute and display a narrowing post without opening a proof goal. -/
elab "#narrow " rule:term " from " source:term : command => do
  Lean.Elab.Command.liftTermElabM do
    let rule ← Term.elabTerm rule none
    let source ← Term.elabTerm source none
    let problem ← Problem.ofPattern rule source
    let alternatives ← Backend.solvePattern problem
    let post ← Materialization.post problem.stateType alternatives
    logInfo m!"post: {post.value}\ntype: {post.type}"

/-- Compute and display a narrowing post modulo a structural theory. -/
elab "#narrow " rule:term " from " source:term " mod " theory:term : command => do
  Lean.Elab.Command.liftTermElabM do
    let rule ← Term.elabTerm rule none
    let source ← Term.elabTerm source none
    let theoryType ← mkConstWithFreshMVarLevels ``Structural.Theory
    let theory ← Term.elabTerm theory (some theoryType)
    let problem ← Problem.ofPattern rule source
    let alternatives ← Backend.solvePattern problem (some theory)
    let post ← Materialization.post problem.stateType alternatives
    logInfo m!"post: {post.value}\ntype: {post.type}"

/-- Generate the post and certify one constrained narrowing phase. -/
elab "narrow " rule:term " against " source:term : tactic =>
  Narrowing.Tactic.run rule.raw rule source

/--
Generate a theory-indexed post, certify it with the nested term, and leave
subsumption as the proof continuation.
-/
elab "narrow " rule:term " from " source:term " mod " theory:term
    " := " certificate:term : tactic =>
  Narrowing.Tactic.runModCertified rule.raw rule source theory certificate

/-- Prove the residual pattern-subsumption phase. -/
elab "subsume" : tactic =>
  Narrowing.Subsumption.run

/-- Expose one residual goal per atomic post branch. -/
elab "subsume_cases" : tactic =>
  Narrowing.Subsumption.cases

/-- Prove one atomic residual goal, using the registered matcher for witnesses. -/
elab "subsume_atom" : tactic =>
  Narrowing.Subsumption.atom

/-- Prove an instantiated structural equality without searching for witnesses. -/
elab "structural_rfl" : tactic =>
  Narrowing.Subsumption.Structural.runRfl

end Narrowing
