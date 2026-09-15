import conPanna.Unification

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

def ofSubsumesType (type : Expr) : MetaM SubsumptionInput := do
  let type ← instantiateMVars type
  let arguments := type.getAppArgs
  unless type.getAppFn.isConstOf ``framework.Patterns.Subsumes &&
      arguments.size >= 2 do
    throwError "`subsume` expects a goal of the form `source ⊑ target`"
  return {
    source := arguments[arguments.size - 2]!
    target := arguments[arguments.size - 1]!
  }

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

/-- Solve every atomic branch while retaining its branch-local substitutions. -/
def solvePattern (input : Problem.PatternInput) (theory? : Option Expr := none) :
    MetaM (Array BranchAlternative) := do
  let mut results := #[]
  for problem in input.branches do
    let solutionSet ← solve problem theory?
    for alternative in solutionSet.alternatives do
      results := results.push { problem, alternative }
  return results

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

end Tactic


namespace Subsumption

/-!
`Subsumption` is the current lightweight prover for the residual inclusion
between the generated post and the user's target pattern. Its semantic goal
is stable even if stronger constraint automation replaces this prototype.
-/

/-- Simplify and prove the residual semantic inclusion between patterns. -/
def run : TacticM Unit := do
  let goal ← getMainGoal
  let input ← goal.withContext do
    Goal.ofSubsumesType (← goal.getType)
  let sourceBranches ← goal.withContext do
    Problem.atomicSources input.source
  let targetBranches ← goal.withContext do
    Problem.atomicSources input.target
  let unfoldNames ← Closure.unfoldingDefinitions
    (#[input.source, input.target] ++ sourceBranches ++ targetBranches)
  let unfoldSimps ← unfoldNames.mapM fun name =>
    `(Parser.Tactic.simpLemma| $(mkIdent name):ident)
  evalTactic (← `(tactic|
    simp [framework.Patterns.Subsumes,
      framework.Patterns.Pattern.semantics,
      framework.Patterns.APatt.semantics,
      $unfoldSimps,*] <;>
      grind))

end Subsumption

/-- Compute and display a narrowing post without opening a proof goal. -/
elab "#narrow " rule:term " against " source:term : command => do
  Lean.Elab.Command.liftTermElabM do
    let rule ← Term.elabTerm rule none
    let source ← Term.elabTerm source none
    let problem ← Problem.ofPattern rule source
    let alternatives ← Backend.solvePattern problem
    let post ← Materialization.post problem.stateType alternatives
    logInfo m!"post: {post.value}\ntype: {post.type}"

/-- Compute and display a narrowing post modulo a structural theory. -/
elab "#narrow " rule:term " against " source:term " in " theory:term : command => do
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

/-- Prove the residual pattern-subsumption phase. -/
elab "subsume" : tactic =>
  Narrowing.Subsumption.run

end Narrowing
