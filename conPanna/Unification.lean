import Expresso.Expresso
import conPanna.Structural
/-!
# Equational theories

A `Theory` is the declarative equality component shared by unification,
narrowing, and rewriting. It records term-forming symbols and proof-carrying
structural laws, but it does not choose an algorithm or contain rewrite rules.
Those are responsibilities of clients and of a future executable module.
-/
namespace Theory

universe u

/--
A structural algebraic law attached to the exact operation it describes.
Indexing by the operation prevents registering a proof about one symbol as a
law of another. Absence or combinations of laws are later classified as free,
A, C, AC, and related unification fragments.
-/
inductive OperatorLaw : {operationType : Type u} →
    (operation : operationType) → Type (u + 1) where
  | commutative {α : Type u} {operation : α → α → α}
      (proof : ∀ left right, operation left right = operation right left) :
      OperatorLaw operation
  | associative {α : Type u} {operation : α → α → α}
      (proof : ∀ first second third,
        operation (operation first second) third =
          operation first (operation second third)) :
      OperatorLaw operation

namespace OperatorLaw

/-!
Convenience constructors in this namespace turn standard Lean algebraic
instances into the proof-carrying laws stored by a theory.
-/

def commutativeOfInstance {α : Type u} (operation : α → α → α)
    [Std.Commutative operation] : OperatorLaw operation :=
  .commutative Std.Commutative.comm

def associativeOfInstance {α : Type u} (operation : α → α → α)
    [Std.Associative operation] : OperatorLaw operation :=
  .associative Std.Associative.assoc

end OperatorLaw

/-- One symbol of any arity; its complete signature is its inferred Lean type. -/
structure Symbol where
  {operationType : Type u}
  operation : operationType
  laws : List (OperatorLaw operation) := []

/-- Uniform declaration constructor for nullary through arbitrary-arity symbols. -/
def Symbol.declare {operationType : Type u} (operation : operationType)
    (laws : List (OperatorLaw operation) := []) : Symbol where
  operation := operation
  laws := laws

end Theory

universe theory_u

/-- The symbol signature and structural equality laws of a theory. -/
structure Theory where
  symbols : List (Theory.Symbol.{theory_u}) := []





open Lean Meta Elab Term Tactic
open framework framework.Patterns

/-
# Unification

Unification begins with semantic intersection of two pattern denotations and
computationally explains that intersection by a sound, complete set of
factorizing substitutions. The namespace separates semantic judgments,
solver-neutral certificates, theory-specific backends, and proof-state UI.
-/
namespace Unification

universe u v w

/- ## Unifiability -/

/- atomic unifiability (non-empty intersection) -/
def Unifiable {α : Type u} {P : Type v} {Q : Type w}
    [State α] [APatt α P] [APatt α Q]
    (p : P) (q : Q) : Prop :=
  ∃ state, APatt.semantics p state ∧ APatt.semantics q state

infix:50 " ⋈ " => Unifiable

/- unifiability modulo equational theory -/
def UnifiableIn {α : Type u} {P : Type v} {Q : Type w}
    [State α] [APatt α P] [APatt α Q]
    (_theory : Theory) (left : P) (right : Q) : Prop :=
  Unifiable left right

notation:50 left " ⋈[" theory "] " right =>
  UnifiableIn theory left right


/-
`Problem` defines a way to represent patterns as meta expressions
`ofUnifiableType` is the main functionality
-/
-- TODO: move this as part of Pattern?
namespace Problem

/- transform patterns into meta objects. lambda binders get unwrapped. -/
-- rename: APattMeta
/- e.g., λx1. λx2. f x1 x2 is turned into: -/
structure SaturatedPattern where
  application : Expr -- e.g., f ?x1 ?x2
  arguments : Array Expr -- e.g., [?x1, ?x2]
  argumentNames : Array Name -- e.g., [x1, x2]

/- encodes the equation p1 = p2 for two patterns -/
-- rename: APattMetaEq
structure Input where
  theory? : Option Expr := none
  lhs : SaturatedPattern
  rhs : SaturatedPattern

def visibleName (fallback : String) (name : Name) : Name :=
  if name.isAnonymous then Name.mkSimple fallback else name.eraseMacroScopes

/- Saturate all explicit arguments of a pattern closure. -/
-- rename: APatt2Meta
def saturatePattern (pattern : Expr) : MetaM SaturatedPattern := do
  let type ← inferType pattern
  let (arguments, binderInfos, _) ← forallMetaTelescopeReducing type
  unless binderInfos.all fun info => info == .default do
    throwError "`unify` only supports explicit pattern arguments"
  let mut argumentNames := #[]
  for argument in arguments do
    let decl ← argument.mvarId!.getDecl
    argumentNames := argumentNames.push decl.userName.eraseMacroScopes
  return {
    application := mkAppN pattern arguments
    arguments
    argumentNames
  }

/- turns object level unification hypothesis into meta-level APattMetaEq-/
/-- Extract the optional theory and two patterns from a unifiability proposition. -/
def ofUnifiableType (type : Expr) : MetaM Input := do
  let type ← instantiateMVars type
  let arguments := type.getAppArgs
  let isDefault := type.getAppFn.isConstOf ``Unification.Unifiable
  let isTheoryIndexed :=
    type.getAppFn.isConstOf ``Unification.UnifiableIn
  unless (isDefault && arguments.size >= 2) ||
      (isTheoryIndexed && arguments.size >= 3) do
    throwError "expected a hypothesis of the form `p ⋈ q`"
  let lhs ← saturatePattern arguments[arguments.size - 2]!
  let rhs ← saturatePattern arguments[arguments.size - 1]!
  let theory? := if isTheoryIndexed then
      some arguments[arguments.size - 3]!
    else
      none
  return { theory?, lhs, rhs }

def argumentCount (problem : Input) : Nat :=
  problem.lhs.arguments.size + problem.rhs.arguments.size

def symbolicArguments (problem : Input) : Array Expr :=
  problem.lhs.arguments ++ problem.rhs.arguments

end Problem


/-
`Dispatch` interprets a declarative `Theory` only far enough to choose a
unification algorithm. It owns no symbols or laws: other reasoning procedures
may interpret the same theory through their own dispatch layers.

`backend` is the main functionality
(determines which backend algorithm to use given a theory)
-/
namespace Dispatch

inductive Backend where
  | free
  | c

/-- Read the structural-law kinds attached to one declared symbol. -/
private partial def scanLaws (laws : Expr)
    (foundAssociative foundCommutative : Bool) : MetaM (Bool × Bool) := do
  let laws ← withTransparency .all <| whnf laws
  let arguments := laws.getAppArgs
  if laws.getAppFn.isConstOf ``List.nil then
    return (foundAssociative, foundCommutative)
  unless laws.getAppFn.isConstOf ``List.cons && arguments.size >= 3 do
    throwError "could not reduce a symbol's structural-law declarations"
  let lawExpr := arguments[arguments.size - 2]!
  let tail := arguments[arguments.size - 1]!
  let lawExpr ← withTransparency .all <| whnf lawExpr
  let isAssociative :=
    lawExpr.getAppFn.isConstOf ``Theory.OperatorLaw.associative
  let isCommutative :=
    lawExpr.getAppFn.isConstOf ``Theory.OperatorLaw.commutative
  unless isAssociative || isCommutative do
    throwError "the theory contains an unrecognized structural law"
  scanLaws tail (foundAssociative || isAssociative)
    (foundCommutative || isCommutative)

/-- Select a prototype backend from an arbitrary-arity symbol list. -/
private partial def scanSymbols (symbols : Expr) (foundC : Bool) : MetaM Backend := do
  let symbols ← withTransparency .all <| whnf symbols
  let arguments := symbols.getAppArgs
  if symbols.getAppFn.isConstOf ``List.nil then
    return if foundC then .c else .free
  unless symbols.getAppFn.isConstOf ``List.cons && arguments.size >= 3 do
    throwError "could not reduce the theory's symbol declarations"
  let symbol := arguments[arguments.size - 2]!
  let tail := arguments[arguments.size - 1]!
  let laws ← mkAppM ``Theory.Symbol.laws #[symbol]
  let (hasAssociative, hasCommutative) ← scanLaws laws false false
  if hasAssociative && hasCommutative then
    throwError "the AC backend is not implemented in this prototype"
  if hasAssociative then
    throwError "the associative-unification backend is not implemented in this prototype"
  let foundC := foundC || hasCommutative
  scanSymbols tail foundC

def backend (theory : Expr) : MetaM Backend := do
  let symbols ← mkAppM ``Theory.symbols #[theory]
  scanSymbols symbols false

end Dispatch


namespace StructuralDispatch

inductive Backend where
  | free
  | c

private partial def scanLaws (laws : Expr)
    (foundAssociative foundCommutative foundIdentity : Bool) :
    MetaM (Bool × Bool × Bool) := do
  let laws ← withTransparency .all <| whnf laws
  let arguments := laws.getAppArgs
  if laws.getAppFn.isConstOf ``List.nil then
    return (foundAssociative, foundCommutative, foundIdentity)
  unless laws.getAppFn.isConstOf ``List.cons && arguments.size >= 3 do
    throwError "could not reduce a structural symbol's law declarations"
  let law ← withTransparency .all <|
    whnf arguments[arguments.size - 2]!
  let isAssociative :=
    law.getAppFn.isConstOf ``Structural.OperatorLaw.associative
  let isCommutative :=
    law.getAppFn.isConstOf ``Structural.OperatorLaw.commutative
  let isIdentity :=
    law.getAppFn.isConstOf ``Structural.OperatorLaw.identity
  unless isAssociative || isCommutative || isIdentity do
    throwError "the structural theory contains an unrecognized law"
  scanLaws arguments[arguments.size - 1]!
    (foundAssociative || isAssociative)
    (foundCommutative || isCommutative)
    (foundIdentity || isIdentity)

private partial def scanSymbols (symbols : Expr) (foundC : Bool) :
    MetaM Backend := do
  let symbols ← withTransparency .all <| whnf symbols
  let arguments := symbols.getAppArgs
  if symbols.getAppFn.isConstOf ``List.nil then
    return if foundC then .c else .free
  unless symbols.getAppFn.isConstOf ``List.cons && arguments.size >= 3 do
    throwError "could not reduce a structural theory's symbol declarations"
  let symbol := arguments[arguments.size - 2]!
  let laws ← mkAppM ``Structural.Symbol.laws #[symbol]
  let (hasAssociative, hasCommutative, hasIdentity) ←
    scanLaws laws false false false
  if hasAssociative || hasIdentity then
    throwError "only free and commutative structural narrowing are implemented"
  scanSymbols arguments[arguments.size - 1]!
    (foundC || hasCommutative)

/-- Select the implemented backend from a declarative structural theory. -/
def backend (theory : Expr) : MetaM Backend := do
  let symbols ← mkAppM ``Structural.Theory.symbols #[theory]
  scanSymbols symbols false

end StructuralDispatch


/-
`Certificate` is the solver-neutral contract between computation and proof.
It represents residual freedom with explicit basis variables and separately
records candidate data, soundness, completeness, and concrete factorization.

`solutionSetType` is the main functionality
-/
namespace Certificate



/-
A solver-neutral unifier branch.

Each `image` is a lambda over all `basisTypes`.  Consequently this structure
contains no metavariables owned by a particular backend.  An AC backend can
return several values of this type; the free backend returns at most one.

(example)
alternative ∃ u1, x1 = f(u1, c) ∧ x2 = c ∧ y1 = u1.
for problem f(x1, x2) = f(f(y1, c), c):

basisTypes = [Conf]
images = [
  fun u1 => f u1 c,    -- image of x1
  fun u1 => c,         -- image of x2
  fun u1 => u1         -- image of y1
]
-/
structure Alternative where -- = one unifier
  basisTypes : Array Expr
  images : Array Expr
  deriving Inhabited

/-- The common result shape for unitary and multi-unifier backends. -/
structure SolutionSet where -- = set of unifiers
  alternatives : Array Alternative

/-- A branch together with a kernel-checked proof of its factorization. -/
structure ProvenAlternative where
  alternative : Alternative
  proposition : Expr
  proof : Expr

/--
A computed solution set whose alternatives have each been checked to be
actual unifiers.  Soundness is backend-independent data even when the tactic
used to construct the proofs is theory-specific.
-/
structure SoundSolutionSet where
  solutionSet : SolutionSet
  soundnessPropositions : Array Expr
  soundnessProofs : Array Expr

/--
A sound solution set together with a user-supplied proof that every unifier
factors through one of its alternatives.
-/
structure ExactSolutionSet extends SoundSolutionSet where
  completenessProposition : Expr
  completenessProof : Expr

/-- A checked factorization disjunction specialized to one semantic witness. -/
structure ProvenSolutionSet where
  solutionSet : SolutionSet
  branchPropositions : Array Expr
  proposition : Expr
  proof : Expr

private def mkAndAll (propositions : Array Expr) : MetaM Expr := do
  let mut result := Lean.mkConst ``True
  for proposition in propositions.toList.reverse do
    result ← mkAppM ``And #[proposition, result]
  return result

private def mkExistsOne (variableExpr body : Expr) : MetaM Expr := do
  let predicate ← mkLambdaFVars #[variableExpr] body
  mkAppM ``Exists #[predicate]

private def mkExistsOver (variables : Array Expr) (body : Expr) : MetaM Expr := do
  let mut result := body
  for variableExpr in variables.toList.reverse do
    result ← mkExistsOne variableExpr result
  return result

private def mkOrAll (propositions : Array Expr) : MetaM Expr := do
  if propositions.isEmpty then
    return Lean.mkConst ``False
  let mut result := propositions[propositions.size - 1]!
  for proposition in propositions.toList.dropLast.reverse do
    result ← mkAppM ``Or #[proposition, result]
  return result

private partial def withBasisVariables
    {α : Type}
    (types : Array Expr) (index : Nat) (variables : Array Expr)
    (continuation : Array Expr → MetaM α) : MetaM α := do
  if _h : index < types.size then
    withLocalDeclD (Name.mkSimple s!"u{index + 1}") types[index]!
      fun variableExpr =>
        withBasisVariables types (index + 1) (variables.push variableExpr)
          continuation
  else
    continuation variables

/-- Instantiate one substitution image at concrete basis values. -/
def instantiateImage (image : Expr) (basis : Array Expr) : Expr :=
  mkAppN image basis

/--
Turn a branch into its public logical meaning:

`∃ u₁ ... uₖ, x₁ = image₁ u ∧ ... ∧ xₙ = imageₙ u ∧ True`.
-/
def factorizationType
    (alternative : Alternative) (actualArguments : Array Expr) : MetaM Expr := do
  unless alternative.images.size == actualArguments.size do
    throwError "a unification branch has the wrong number of substitution images"
  withBasisVariables alternative.basisTypes 0 #[] fun basis => do
    let mut equations := #[]
    for i in [:actualArguments.size] do
      let image ← whnf (instantiateImage alternative.images[i]! basis)
      equations := equations.push (← mkEq actualArguments[i]! image)
    let body ← mkAndAll equations
    mkExistsOver basis body

/-- Build the disjunction represented by an entire solver result. -/
def solutionSetType
    (solutionSet : SolutionSet) (actualArguments : Array Expr) : MetaM
      (Array Expr × Expr) := do
  let mut branches := #[]
  for alternative in solutionSet.alternatives do
    branches := branches.push (← factorizationType alternative actualArguments)
  return (branches, ← mkOrAll branches)

end Certificate





namespace Free

/-!
`Free` is the native free first-order backend. It asks Lean's unifier for a
candidate, abstracts residual metavariables into an explicit basis, and
returns solver-neutral substitution images without proving completeness.
-/

/-- A free-backend candidate represented through the common alternative interface. -/
structure Candidate where
  alternative : Certificate.Alternative
  deriving Inhabited

structure Output where
  candidates : Array Candidate := #[]

private def replaceResiduals
    (template : Expr) (residuals : Array MVarId)
    (basis : Array Expr) : Expr :=
  template.replace fun subterm =>
    match subterm with
    | .mvar id =>
        match residuals.idxOf? id with
        | some i => basis[i]?
        | none => none
    | _ => none

private partial def withBasisVariables
    {α : Type}
    (types : Array Expr) (index : Nat) (variables : Array Expr)
    (continuation : Array Expr → MetaM α) : MetaM α := do
  if _h : index < types.size then
    withLocalDeclD (Name.mkSimple s!"u{index + 1}") types[index]!
      fun variableExpr =>
        withBasisVariables types (index + 1) (variables.push variableExpr)
          continuation
  else
    continuation variables

/--
Compute the unique MGU for a free first-order problem with Lean's native
unifier.  Residual native metavariables are abstracted immediately into lambda
bound basis variables; they never cross this backend boundary.
-/
def solve (problem : Problem.Input) : MetaM Output := do
  unless ← isDefEq problem.lhs.application problem.rhs.application do
    return {}

  let symbolicArguments := Problem.symbolicArguments problem
  let mut templates := #[]
  let mut residuals := #[]
  for argument in symbolicArguments do
    let template ← instantiateMVars argument
    templates := templates.push template
    for residual in ← getMVars template do
      unless residuals.contains residual do
        residuals := residuals.push residual

  let mut basisTypes := #[]
  for residual in residuals do
    let some _originalIndex := symbolicArguments.findIdx? fun argument =>
        argument.isMVar && argument.mvarId! == residual
      | throwError "native unification introduced an unexpected metavariable"
    let type ← instantiateMVars (← residual.getType)
    unless (← getMVars type).isEmpty do
      throwError "dependent basis types are outside the supported free fragment"
    basisTypes := basisTypes.push type

  let images ← withBasisVariables basisTypes 0 #[] fun basis => do
    let mut images := #[]
    for template in templates do
      let body := replaceResiduals template residuals basis
      unless (← getMVars body).isEmpty do
        throwError "native unification left an unabstracted metavariable"
      images := images.push (← mkLambdaFVars basis body)
    return images

  return { candidates := #[{
      alternative := { basisTypes, images }
    }] }

private partial def collectEqualityLeaves
    (proof : Expr) (result : Array Expr := #[]) : MetaM (Array Expr) := do
  let type ← whnf (← inferType proof)
  if type.eq?.isSome then
    return result.push proof
  let arguments := type.getAppArgs
  if type.getAppFn.isConstOf ``And && arguments.size == 2 then
    let left ← mkAppM ``And.left #[proof]
    let right ← mkAppM ``And.right #[proof]
    let result ← collectEqualityLeaves left result
    collectEqualityLeaves right result
  else
    return result

private def noteSizeEquation (goal : MVarId) (equality : Expr) : MetaM MVarId :=
    goal.withContext do
  let equalityType ← whnf (← inferType equality)
  let some (type, _, _) := equalityType.eq?
    | return goal
  try
    let sizeFunction ← withLocalDeclD `_unifySizeArgument type fun argument => do
      let size ← mkAppM ``SizeOf.sizeOf #[argument]
      mkLambdaFVars #[argument] size
    let sizeEquality ← mkAppM ``congrArg #[sizeFunction, equality]
    let sizeEqualityType ← inferType sizeEquality
    let name := (← getLCtx).getUnusedName `_unifySizeEq
    let (_, goal) ← goal.note name sizeEquality (some sizeEqualityType)
    return goal
  catch _ =>
    -- Constructor clashes do not need `SizeOf`.  An occurs-check cycle does;
    -- if its state type has no `SizeOf` instance, the final certification step
    -- reports that this input is outside the currently supported fragment.
    return goal

/--
Optional automation for a zero-result completeness goal. `simp_all` proves
direct constructor clashes. For occurs-check cycles, every constructor
equation is also mapped through `sizeOf`; generated inductive `SizeOf`
equations reduce to inconsistent natural-number constraints checked by
`omega`.
-/
def certifyFailureGoal : TacticM Unit := do
  evalTactic (← `(tactic| simp_all))
  if (← getGoals).isEmpty then
    return

  let mut goal ← getMainGoal
  let equalityProofs ← goal.withContext do
    let mut equalityProofs := #[]
    for declaration in ← getLCtx do
      if declaration.isImplementationDetail then
        continue
      equalityProofs ← collectEqualityLeaves (mkFVar declaration.fvarId)
        equalityProofs
    return equalityProofs
  for equality in equalityProofs do
    goal ← noteSizeEquation goal equality
  setGoals [goal]

  try
    evalTactic (← `(tactic| solve | (simp_all <;> omega)))
  catch _ =>
    throwError
      "free unification found no solution, but could not certify the contradiction"


end Free



/-!
The C backend is deliberately an adapter around the free backend. It expands
the right-hand term into every orientation permitted by registered
`C.Operator`s, invokes native free unification independently on each
orientation, and returns the resulting finite candidate set through the
common `Certificate` interface.
-/
namespace C

/--
A binary operation that is free modulo commutativity.

`Std.Commutative op` supplies the equation used to justify swapped terms.
`eq_iff` is the constructor-decomposition principle needed to prove that the
two orientations are complete.  Commutativity alone would not be sufficient:
for example, a constant operation is commutative but has many extra equations.
-/
class Operator {α : Type u} (op : α → α → α) extends Std.Commutative op where
  eq_iff (a b c d : α) :
    op a b = op c d ↔ (a = c ∧ b = d) ∨ (a = d ∧ b = c)


abbrev Candidate := Free.Candidate

structure Output where
  candidates : Array Candidate := #[]

private def operatorInstance? (operation : Expr) : MetaM (Option Expr) := do
  try
    return some (← synthInstance (← mkAppM ``Operator #[operation]))
  catch _ =>
    return none

private abbrev IsCommutativeOperator := Expr → MetaM Bool

private partial def structuralLawsContainComm (laws : Expr) : MetaM Bool := do
  let laws ← withTransparency .all <| whnf laws
  let arguments := laws.getAppArgs
  if laws.getAppFn.isConstOf ``List.nil then
    return false
  unless laws.getAppFn.isConstOf ``List.cons && arguments.size >= 3 do
    throwError "could not reduce a structural symbol's law declarations"
  let law ← withTransparency .all <|
    whnf arguments[arguments.size - 2]!
  if law.getAppFn.isConstOf ``Structural.OperatorLaw.commutative then
    return true
  structuralLawsContainComm arguments[arguments.size - 1]!

/-- Extract the operations declared commutative in a structural theory. -/
private partial def structuralCommutativeOperations (symbols : Expr) :
    MetaM (Array Expr) := do
  let symbols ← withTransparency .all <| whnf symbols
  let arguments := symbols.getAppArgs
  if symbols.getAppFn.isConstOf ``List.nil then
    return #[]
  unless symbols.getAppFn.isConstOf ``List.cons && arguments.size >= 3 do
    throwError "could not reduce a structural theory's symbol declarations"
  let symbol := arguments[arguments.size - 2]!
  let tail := arguments[arguments.size - 1]!
  let remaining ← structuralCommutativeOperations tail
  let laws ← mkAppM ``Structural.Symbol.laws #[symbol]
  unless ← structuralLawsContainComm laws do
    return remaining
  let operation ← withTransparency .all <|
    whnf (← mkAppM ``Structural.Symbol.operation #[symbol])
  return remaining.push operation

private def isRegisteredOperation (operations : Array Expr)
    (operation : Expr) : MetaM Bool := do
  for registered in operations do
    if ← withoutModifyingState <| isDefEq registered operation then
      return true
  return false

private def pushUniqueExpr (expressions : Array Expr) (expression : Expr) :
    Array Expr :=
  if expressions.any fun existing => existing == expression then
    expressions
  else
    expressions.push expression

/--
Expose definitions until either a registered C operation or a rigid term is
visible.  Registered defined functions are kept opaque at their application
head so their user-supplied theory is not lost by unfolding.
-/
private partial def exposeHeadWith (isOperator : IsCommutativeOperator)
    (expression : Expr) : MetaM Expr := do
  let expression := expression.consumeMData
  match expression with
  | .app (.app operation _) _ =>
      if ← isOperator operation then
        return expression
  | _ => pure ()
  let reduced ← withTransparency .all <| whnf expression
  if reduced == expression then
    return expression
  exposeHeadWith isOperator reduced

partial def exposeHead (expression : Expr) : MetaM Expr :=
  exposeHeadWith
    (fun operation => return (← operatorInstance? operation).isSome) expression

/-- Enumerate all terms obtained by independently swapping registered C nodes. -/
private partial def orientationsWith (isOperator : IsCommutativeOperator)
    (expression : Expr) : MetaM (Array Expr) := do
  let expression ← exposeHeadWith isOperator expression
  match expression with
  | .app (.app operation left) right =>
      if ← isOperator operation then
        let leftOrientations ← orientationsWith isOperator left
        let rightOrientations ← orientationsWith isOperator right
        let mut result := #[]
        for left in leftOrientations do
          for right in rightOrientations do
            result := pushUniqueExpr result (mkApp2 operation left right)
            result := pushUniqueExpr result (mkApp2 operation right left)
        return result
  | _ => pure ()

  -- A C node may occur below an otherwise free application.
  let mut applications := #[expression.getAppFn]
  for argument in expression.getAppArgs do
    let argumentOrientations ← orientationsWith isOperator argument
    let mut next := #[]
    for application in applications do
      for orientedArgument in argumentOrientations do
        next := pushUniqueExpr next (mkApp application orientedArgument)
    applications := next
  return applications

private def sameAlternative
    (left right : Certificate.Alternative) : Bool :=
  left.basisTypes == right.basisTypes && left.images == right.images

private def pushUniqueCandidate
    (candidates : Array Candidate) (candidate : Candidate) : Array Candidate :=
  if candidates.any fun existing =>
      sameAlternative existing.alternative candidate.alternative then
    candidates
  else
    candidates.push candidate

/--
Compute a finite candidate set of C-unifiers by reducing each C orientation to
the free solver. `withoutModifyingState` is essential:
native unification may assign the saturated metavariables, and every
orientation must start from the same untouched problem.
-/
private def solveWith (isOperator : IsCommutativeOperator)
    (problem : Problem.Input) : MetaM Output := do
  let rhsOrientations ← orientationsWith isOperator problem.rhs.application
  let mut candidates := #[]
  for rhs in rhsOrientations do
    let output ← withoutModifyingState do
      Free.solve {
        lhs := problem.lhs
        rhs := { problem.rhs with application := rhs }
      }
    for candidate in output.candidates do
      candidates := pushUniqueCandidate candidates candidate
  return { candidates }

def solve (problem : Problem.Input) : MetaM Output :=
  solveWith
    (fun operation => return (← operatorInstance? operation).isSome) problem

/-- Compute C-unifiers using operation declarations from `Structural.Theory`. -/
def solveStructural (theory : Expr) (problem : Problem.Input) : MetaM Output := do
  let symbols ← mkAppM ``Structural.Theory.symbols #[theory]
  let operations ← structuralCommutativeOperations symbols
  solveWith (isRegisteredOperation operations) problem

private def eqModRefl (theory value : Expr) : MetaM Expr :=
  mkAppM ``Structural.EqMod.reflAt #[theory, value]

private partial def proveEqModWith (operations : Array Expr)
    (theory left right : Expr) : MetaM Expr := do
  if ← withoutModifyingState <| isDefEq left right then
    return ← eqModRefl theory left

  let left ← exposeHeadWith (isRegisteredOperation operations) left
  let right ← exposeHeadWith (isRegisteredOperation operations) right
  let leftHead := left.getAppFn
  let rightHead := right.getAppFn
  let leftArguments := left.getAppArgs
  let rightArguments := right.getAppArgs
  unless leftArguments.size == rightArguments.size &&
      (← withoutModifyingState <| isDefEq leftHead rightHead) do
    throwError "terms are not equivalent modulo the registered C theory"

  let proveArguments (targets : Array Expr) : MetaM Expr := do
    let mut currentArguments := leftArguments
    let mut currentTerm := left
    let mut proof ← eqModRefl theory left
    for i in [:currentArguments.size] do
      let argumentProof ←
        proveEqModWith operations theory currentArguments[i]! targets[i]!
      let argumentType ← inferType currentArguments[i]!
      let (function, nextTerm) ← withLocalDeclD `_eqModArgument argumentType
        fun argument => do
          let nextArguments := currentArguments.set! i argument
          let body := mkAppN leftHead nextArguments
          return (← mkLambdaFVars #[argument] body,
            mkAppN leftHead (currentArguments.set! i targets[i]!))
      let step ← mkAppM ``Structural.EqMod.congrAt
        #[theory, function, argumentProof]
      proof ← mkAppM ``Structural.EqMod.transAt #[theory, proof, step]
      currentArguments := currentArguments.set! i targets[i]!
      currentTerm := nextTerm
    unless ← withoutModifyingState <| isDefEq currentTerm (mkAppN leftHead targets) do
      throwError "failed to construct a congruence certificate"
    return proof

  try
    return ← proveArguments rightArguments
  catch _ => pure ()

  unless leftArguments.size == 2 &&
      (← isRegisteredOperation operations leftHead) do
    throwError "terms are not equivalent modulo the registered C theory"
  let swappedTargets := #[rightArguments[1]!, rightArguments[0]!]
  let congruence ← proveArguments swappedTargets
  let commutativity ← mkAppM ``Structural.EqMod.commAt
    #[theory, leftHead, rightArguments[1]!, rightArguments[0]!]
  mkAppM ``Structural.EqMod.transAt #[theory, congruence, commutativity]

/-- Construct a kernel-checkable `EqMod` proof for a registered C equation. -/
def proveEqModStructural (theory left right : Expr) : MetaM Expr := do
  let symbols ← mkAppM ``Structural.Theory.symbols #[theory]
  let operations ← structuralCommutativeOperations symbols
  proveEqModWith operations theory left right

end C


/-- Run the backend selected by a declarative structural theory. -/
def solveStructuralTheory (theory : Expr) (problem : Problem.Input) :
    MetaM Certificate.SolutionSet := do
  match ← StructuralDispatch.backend theory with
  | .free =>
      let output ← Free.solve problem
      return { alternatives := output.candidates.map (·.alternative) }
  | .c =>
      let output ← C.solveStructural theory problem
      return { alternatives := output.candidates.map (·.alternative) }


namespace ModCertificate

private def instantiateApplication (pattern : Problem.SaturatedPattern)
    (arguments : Array Expr) : Expr :=
  pattern.application.replace fun subterm =>
    match subterm with
    | .mvar id =>
        match pattern.arguments.findIdx? fun argument =>
            argument.isMVar && argument.mvarId! == id with
        | some index => arguments[index]?
        | none => none
    | _ => none

private partial def withBasisVariables
    {α : Type} (types : Array Expr) (index : Nat) (variables : Array Expr)
    (continuation : Array Expr → MetaM α) : MetaM α := do
  if _h : index < types.size then
    withLocalDeclD (Name.mkSimple s!"u{index + 1}") types[index]!
      fun basisVariable =>
        withBasisVariables types (index + 1) (variables.push basisVariable)
          continuation
  else
    continuation variables

/--
Construct the candidate-specific soundness certificate
`∀ basis, EqMod theory (lhs σ) (rhs σ)`.
-/
def proveSoundness (theory : Expr) (problem : Problem.Input)
    (alternative : Certificate.Alternative) : MetaM Expr :=
  withBasisVariables alternative.basisTypes 0 #[] fun basis => do
    let mut images := #[]
    for image in alternative.images do
      images := images.push (← whnf
        (Certificate.instantiateImage image basis))
    let lhsCount := problem.lhs.arguments.size
    unless images.size == lhsCount + problem.rhs.arguments.size do
      throwError "a structural unifier has the wrong number of images"
    let lhs ← withTransparency .all <| whnf
      (instantiateApplication problem.lhs (images.extract 0 lhsCount))
    let rhs ← withTransparency .all <| whnf
      (instantiateApplication problem.rhs (images.extract lhsCount images.size))
    let proof ← C.proveEqModStructural theory lhs rhs
    mkLambdaFVars basis proof

end ModCertificate


namespace Inspect

private def formatAlternative (problem : Problem.Input)
    (alternative : Certificate.Alternative) (index : Nat) : MetaM MessageData := do
  let names := problem.lhs.argumentNames ++ problem.rhs.argumentNames
  let lhsCount := problem.lhs.argumentNames.size
  let mut message := m!"unifier {index + 1}:"
  for i in [:alternative.images.size] do
    let fallback := if i < lhsCount then s!"x{i + 1}" else s!"y{i - lhsCount + 1}"
    let name := Problem.visibleName fallback names[i]!
    let side := if i < lhsCount then "left" else "right"
    let image ← whnf alternative.images[i]!
    message := m!"{message}\n  {side}.{name} ↦ {image}"
  return message

/-- Display a structural unification solution set without opening a proof. -/
def structuralUnifiers (left right theory : Expr) : MetaM MessageData := do
  let lhs ← Problem.saturatePattern left
  let rhs ← Problem.saturatePattern right
  let problem : Problem.Input := { theory? := some theory, lhs, rhs }
  let solutionSet ← solveStructuralTheory theory problem
  if solutionSet.alternatives.isEmpty then
    return m!"no unifier"
  let mut message := m!""
  for i in [:solutionSet.alternatives.size] do
    let alternative ← formatAlternative problem solutionSet.alternatives[i]! i
    message := if i == 0 then alternative else m!"{message}\n{alternative}"
  return message

end Inspect


namespace Exposure

/-!
`Exposure` is the proof-state view of a certified solution set. It introduces
stable basis names and factorization equations for users; it is unrelated to
the equational `Theory` that selected the solver.
-/

def freshVisibleIdent (ref : Syntax) (base : Name) : TacticM Ident := do
  let goal ← getMainGoal
  let name ← goal.withContext do
    return (← getLCtx).getUnusedName base
  return mkIdentFrom ref name

private def singleCases (goal : MVarId) (hypothesis : FVarId) : MetaM
    (MVarId × Array FVarId) := do
  let subgoals ← goal.cases hypothesis
  let [subgoal] := subgoals.toList
    | throwError "unexpected branching while exposing a unifier certificate"
  let fields := subgoal.fields.filterMap fun
    | .fvar id => some id
    | _ => none
  return (subgoal.mvarId, fields)

/-- Open one proven branch on a specified goal. -/
private def exposeAlternativeAt
    (goal : MVarId) (proven : Certificate.ProvenAlternative) : MetaM MVarId := do
  let factorizationName ← goal.withContext do
    return (← getLCtx).getUnusedName `_unifyFactorization
  let (factorizationId, goal) ← goal.withContext do
    goal.note factorizationName proven.proof (some proven.proposition)

  let mut goal := goal
  let mut bodyId := factorizationId
  for i in [:proven.alternative.basisTypes.size] do
    let (nextGoal, fields) ← goal.withContext do singleCases goal bodyId
    unless fields.size >= 2 do
      throwError "malformed existential unifier certificate"
    let basisName ← nextGoal.withContext do
      return (← getLCtx).getUnusedName (Name.mkSimple s!"u{i + 1}")
    goal ← nextGoal.rename fields[0]! basisName
    bodyId := fields[fields.size - 1]!

  for i in [:proven.alternative.images.size] do
    let (nextGoal, fields) ← goal.withContext do singleCases goal bodyId
    unless fields.size >= 2 do
      throwError "malformed conjunction in unifier certificate"
    let equationName ← nextGoal.withContext do
      return (← getLCtx).getUnusedName (Name.mkSimple s!"h{i + 1}")
    goal ← nextGoal.rename fields[0]! equationName
    bodyId := fields[fields.size - 1]!

  -- The conjunction has a final `True`, used to make the zero-argument case
  -- uniform.  It is an implementation detail and is removed here.
  goal ← goal.clear bodyId
  return goal

private partial def exposeAlternativesAt
    (goal : MVarId) (hypothesis : FVarId)
    (proven : Certificate.ProvenSolutionSet) (index : Nat) : MetaM (List MVarId) := do
  let remaining := proven.solutionSet.alternatives.size - index
  if remaining == 1 then
    let goal ← exposeAlternativeAt goal {
      alternative := proven.solutionSet.alternatives[index]!
      proposition := proven.branchPropositions[index]!
      proof := mkFVar hypothesis
    }
    return [goal]

  let subgoals ← goal.cases hypothesis
  let [left, right] := subgoals.toList
    | throwError "malformed disjunction in unification result certificate"
  let some leftProof := left.fields.back?
    | throwError "failed to expose a unifier branch"
  let some rightProof := right.fields.back?
    | throwError "failed to expose the remaining unifier branches"
  let .fvar leftProof := leftProof
    | throwError "failed to expose a unifier branch"
  let .fvar rightProof := rightProof
    | throwError "failed to expose the remaining unifier branches"
  let leftGoal ← exposeAlternativeAt left.mvarId {
    alternative := proven.solutionSet.alternatives[index]!
    proposition := proven.branchPropositions[index]!
    proof := mkFVar leftProof
  }
  let rightGoals ← exposeAlternativesAt right.mvarId rightProof proven (index + 1)
  return leftGoal :: rightGoals

/--
Open a complete solver result into the stable public interface.  One branch
creates one goal; several alternatives create several goals.  Every goal has
basis variables `u1`, `u2`, ... followed by equations `h1`, `h2`, ... in
original-argument order.  An empty result closes the goal by contradiction.
-/
def expose (proven : Certificate.ProvenSolutionSet) : TacticM Unit := do
  let goal ← getMainGoal
  match proven.solutionSet.alternatives.size with
  | 0 =>
      let falseName ← goal.withContext do
        return (← getLCtx).getUnusedName `_unifyImpossible
      let (_, goal) ← goal.withContext do
        goal.note falseName proven.proof (some proven.proposition)
      setGoals [goal]
      evalTactic (← `(tactic| contradiction))
  | 1 =>
      let goal ← exposeAlternativeAt goal {
        alternative := proven.solutionSet.alternatives[0]!
        proposition := proven.branchPropositions[0]!
        proof := proven.proof
      }
      setGoals [goal]
  | _ =>
      let disjunctionName ← goal.withContext do
        return (← getLCtx).getUnusedName `_unifyAlternatives
      let (disjunctionId, goal) ← goal.withContext do
        goal.note disjunctionName proven.proof (some proven.proposition)
      let goals ← goal.withContext do
        exposeAlternativesAt goal disjunctionId proven 0
      setGoals goals

end Exposure



/-
`Tactic` orchestrates the complete user command: parse the semantic problem,
run a selected backend, check candidate soundness, emit completeness, and use
`Exposure` to open the certified alternatives. It is the main replaceable
frontend/backend boundary.
-/
namespace Tactic

private structure SemanticWitnesses where
  actualArguments : Array Expr
  stateId : FVarId
  lhsSemanticsId : FVarId
  rhsSemanticsId : FVarId
  equalityId : FVarId

private def instantiateSaturatedApplication
    (pattern : Problem.SaturatedPattern) (arguments : Array Expr) : Expr :=
  pattern.application.replace fun subterm =>
    match subterm with
    | .mvar id =>
        match pattern.arguments.findIdx? fun argument =>
            argument.isMVar && argument.mvarId! == id with
        | some index => arguments[index]?
        | none => none
    | _ => none

private def instantiateOriginalArguments
    (expression : Expr) (originals replacements : Array Expr) : Expr :=
  expression.replace fun subterm =>
    match subterm with
    | .mvar id =>
        match originals.findIdx? fun original =>
            original.isMVar && original.mvarId! == id with
        | some index => replacements[index]?
        | none => none
    | _ => none

private partial def withOriginalArguments
    {α : Type}
    (problem : Problem.Input) (index : Nat) (arguments : Array Expr)
    (continuation : Array Expr → MetaM α) : MetaM α := do
  let originals := Problem.symbolicArguments problem
  if _h : index < originals.size then
    let original := originals[index]!
    let type ← inferType original
    let type := instantiateOriginalArguments type originals arguments
    let names := problem.lhs.argumentNames ++ problem.rhs.argumentNames
    let name := Problem.visibleName s!"x{index + 1}" names[index]!
    withLocalDeclD name type fun argument =>
      withOriginalArguments problem (index + 1) (arguments.push argument)
        continuation
  else
    continuation arguments

private partial def withBasisArguments
    {α : Type}
    (types : Array Expr) (index : Nat) (arguments : Array Expr)
    (continuation : Array Expr → MetaM α) : MetaM α := do
  if _h : index < types.size then
    withLocalDeclD (Name.mkSimple s!"u{index + 1}") types[index]!
      fun argument =>
        withBasisArguments types (index + 1) (arguments.push argument)
          continuation
  else
    continuation arguments

private def equationType
    (problem : Problem.Input) (arguments : Array Expr) : MetaM Expr := do
  unless arguments.size == Problem.argumentCount problem do
    throwError "a unification certificate has the wrong number of arguments"
  let lhsArguments := arguments.extract 0 problem.lhs.arguments.size
  let rhsArguments := arguments.extract problem.lhs.arguments.size arguments.size
  let lhs ← C.exposeHead
    (instantiateSaturatedApplication problem.lhs lhsArguments)
  let rhs ← C.exposeHead
    (instantiateSaturatedApplication problem.rhs rhsArguments)
  mkEq lhs rhs

/-- State that every actual unifier factors through a returned alternative. -/
private def completenessType
    (problem : Problem.Input) (solutionSet : Certificate.SolutionSet) : MetaM Expr :=
  withOriginalArguments problem 0 #[] fun arguments => do
    let equation ← equationType problem arguments
    let (_, factorization) ←
      Certificate.solutionSetType solutionSet arguments
    let body ← mkArrow equation factorization
    mkForallFVars arguments body

/-- State that every basis instance of one returned alternative is a unifier. -/
private def soundnessType
    (problem : Problem.Input) (alternative : Certificate.Alternative) : MetaM Expr :=
  withBasisArguments alternative.basisTypes 0 #[] fun basis => do
    let mut images := #[]
    for image in alternative.images do
      images := images.push (← whnf
        (Certificate.instantiateImage image basis))
    let equation ← equationType problem images
    mkForallFVars basis equation

private def proveSoundness
    (ref : Syntax) (problem : Problem.Input)
    (solutionSet : Certificate.SolutionSet) (hypothesisId : FVarId) : TacticM
      Certificate.SoundSolutionSet := do
  let originalGoal ← getMainGoal
  let mut propositions := #[]
  let mut proofs := #[]
  for alternative in solutionSet.alternatives do
    let proposition ← originalGoal.withContext do
      soundnessType problem alternative
    let proof ← originalGoal.withContext do
      mkFreshExprMVar (some proposition)
    let soundnessGoal ← proof.mvarId!.clear hypothesisId
    replaceMainGoal [soundnessGoal]
    try
      evalTactic (← `(tactic|
        intros <;> simp_all [C.Operator.eq_iff] <;> grind))
    catch exception =>
      throwErrorAt ref m!"failed to certify a computed unifier's soundness:\n{exception.toMessageData}"
    unless ← proof.mvarId!.isAssigned do
      throwErrorAt ref "failed to construct a unifier soundness proof"
    propositions := propositions.push proposition
    proofs := proofs.push (← instantiateMVars proof)
    setGoals [originalGoal]
  return {
    solutionSet
    soundnessPropositions := propositions
    soundnessProofs := proofs
  }

private def exposeSemantics
    (ref : Syntax) (h : Ident) (problem : Problem.Input) : TacticM
      SemanticWitnesses := do
  let stateIdent ← Exposure.freshVisibleIdent ref `_unifyState
  let lhsIdent ← Exposure.freshVisibleIdent ref `_unifyLhs
  let rhsIdent ← Exposure.freshVisibleIdent ref `_unifyRhs
  evalTactic (← `(tactic|
    rcases ($h:term) with
      ⟨$stateIdent:ident, $lhsIdent:ident, $rhsIdent:ident⟩))

  let mut actualIdents := #[]
  for i in [:problem.lhs.arguments.size] do
    let base := Problem.visibleName s!"x{i + 1}"
      problem.lhs.argumentNames[i]!
    let argumentIdent ← Exposure.freshVisibleIdent ref base
    evalTactic (← `(tactic|
      rcases ($lhsIdent:term) with ⟨$argumentIdent:ident, $lhsIdent:ident⟩))
    actualIdents := actualIdents.push argumentIdent
  for i in [:problem.rhs.arguments.size] do
    let base := Problem.visibleName s!"y{i + 1}"
      problem.rhs.argumentNames[i]!
    let argumentIdent ← Exposure.freshVisibleIdent ref base
    evalTactic (← `(tactic|
      rcases ($rhsIdent:term) with ⟨$argumentIdent:ident, $rhsIdent:ident⟩))
    actualIdents := actualIdents.push argumentIdent

  let actualIds ← actualIdents.mapM getFVarId
  let actualArguments := actualIds.map mkFVar
  let lhsSemanticsId ← getFVarId lhsIdent
  let rhsSemanticsId ← getFVarId rhsIdent

  -- Compose both equalities with the shared semantic state, then unfold the
  -- pattern bodies.  This equality is the kernel-checked input to certification.
  let goal ← getMainGoal
  let equalityName ← goal.withContext do
    return (← getLCtx).getUnusedName `_unifyEq
  let (equalityType, equalityProof) ← goal.withContext do
    let rhsSymm ← mkAppM ``Eq.symm #[mkFVar rhsSemanticsId]
    let proof ← mkAppM ``Eq.trans #[mkFVar lhsSemanticsId, rhsSymm]
    let proofType ← whnf (← inferType proof)
    unless proofType.eq?.isSome do
      throwError "malformed atomic-pattern semantics"
    let lhsArguments := actualArguments.extract 0 problem.lhs.arguments.size
    let rhsArguments := actualArguments.extract problem.lhs.arguments.size
      actualArguments.size
    -- Rebuild the equation from the saturated closures instead of reading its
    -- sides back from `proof`.  The latter may already have unfolded a
    -- reducible registered operation while reducing `APatt.semantics`.
    let lhs ← C.exposeHead
      (instantiateSaturatedApplication problem.lhs lhsArguments)
    let rhs ← C.exposeHead
      (instantiateSaturatedApplication problem.rhs rhsArguments)
    return (← mkEq lhs rhs, proof)
  let (equalityId, goal) ← goal.withContext do
    goal.note equalityName equalityProof (some equalityType)
  setGoals [goal]

  return {
    actualArguments
    stateId := ← getFVarId stateIdent
    lhsSemanticsId
    rhsSemanticsId
    equalityId
  }

private def clearSemantics (witnesses : SemanticWitnesses) : TacticM Unit := do
  let mut clearedGoals := #[]
  for goal in ← getGoals do
    let goal ← goal.clear witnesses.equalityId
    let goal ← goal.clear witnesses.lhsSemanticsId
    let goal ← goal.clear witnesses.rhsSemanticsId
    let goal ← goal.clear witnesses.stateId
    clearedGoals := clearedGoals.push goal
  setGoals clearedGoals.toList

/--
Shared frontend/backend boundary.  A backend computes alternatives; their
soundness is checked immediately, while completeness becomes an explicit
user-level proof goal.  Result goals depend on that completeness certificate.
-/
private def runWith {Output : Type}
    (solve : Problem.Input → MetaM Output)
    (solutions : Output → Certificate.SolutionSet)
    (ref : Syntax) (h : Ident) : TacticM Unit := do
  let hypothesisId ← getFVarId h
  let hypothesisType ← instantiateMVars (← hypothesisId.getType)
  let initialGoal ← getMainGoal
  let (problem, output) ← initialGoal.withContext do
    let problem ← Problem.ofUnifiableType hypothesisType
    let output ← solve problem
    return (problem, output)

  let sound ← proveSoundness ref problem (solutions output) hypothesisId
  let completenessProposition ← initialGoal.withContext do
    completenessType problem sound.solutionSet
  let completenessName ← initialGoal.withContext do
    return (← getLCtx).getUnusedName `completeness
  let completenessValue ← initialGoal.withContext do
    mkFreshExprMVar (some completenessProposition)
  let completenessGoal ← completenessValue.mvarId!.clear hypothesisId
  completenessGoal.setTag `completeness
  let continuationGoal ← initialGoal.withContext do
    initialGoal.assert completenessName completenessProposition completenessValue
  let (completenessId, continuationGoal) ← continuationGoal.withContext do
    continuationGoal.intro1P
  let completenessProof := mkFVar completenessId

  setGoals [continuationGoal]
  let witnesses ← exposeSemantics ref h problem
  let goal ← getMainGoal
  let (branchPropositions, proposition, proof) ← goal.withContext do
    let (branchPropositions, proposition) ←
      Certificate.solutionSetType sound.solutionSet witnesses.actualArguments
    let specialized := mkAppN completenessProof witnesses.actualArguments
    let proof := mkApp specialized (mkFVar witnesses.equalityId)
    let proofType ← inferType proof
    unless ← isDefEq proofType proposition do
      throwError "the completeness certificate does not match the computed solution set"
    return (branchPropositions, proposition, proof)
  let exact : Certificate.ExactSolutionSet := {
    sound with
    completenessProposition
    completenessProof
  }
  let proven : Certificate.ProvenSolutionSet := {
    solutionSet := exact.solutionSet
    branchPropositions
    proposition
    proof
  }
  Exposure.expose proven
  clearSemantics witnesses
  let resultGoals ← getGoals
  setGoals (completenessGoal :: resultGoals)

/-- Compute a free solution set and expose completeness plus result goals. -/
def run (ref : Syntax) (h : Ident) : TacticM Unit :=
  runWith Free.solve
    (fun output => {
      alternatives := output.candidates.map (·.alternative)
    })
    ref h

/-- Compute a C solution set and expose completeness plus result goals. -/
def runC (ref : Syntax) (h : Ident) : TacticM Unit :=
  runWith C.solve
    (fun output => {
      alternatives := output.candidates.map (·.alternative)
    })
    ref h

/--
Resolve an explicit equational theory from an indexed unifiability hypothesis
and dispatch to the prototype backend selected by its structural laws.
-/
def runIn (ref : Syntax) (h : Ident) (theorySyntax : TSyntax `term) :
    TacticM Unit := do
  let hypothesisId ← getFVarId h
  let hypothesisType ← instantiateMVars (← hypothesisId.getType)
  let goal ← getMainGoal
  let problem ← goal.withContext do
    Problem.ofUnifiableType hypothesisType
  let some declaredTheory := problem.theory?
    | throwErrorAt h "`unify ... in ...` requires a hypothesis `p ⋈[T] q`"
  let requestedTheory ← goal.withContext do
    Term.elabTerm theorySyntax.raw
      (some (← inferType declaredTheory))
  let theoriesMatch ← goal.withContext do
    withoutModifyingState
      (isDefEq requestedTheory declaredTheory)
  unless theoriesMatch do
    throwErrorAt theorySyntax
      "the requested theory does not match the theory in the hypothesis"
  match ← goal.withContext do
      Dispatch.backend requestedTheory with
  | .free => run ref h
  | .c => runC ref h

end Tactic


namespace Completeness

/-!
`Completeness` provides optional automation for the ordinary proof obligation
emitted by `unify`. It does not belong to a solver and may be replaced by a
manual proof or a theory-specific certificate checker.
-/

/--
Optional user-level automation for the completeness goal emitted by `unify`.
The goal remains an ordinary proposition: users may replace this tactic with
any manual, theory-specific, or externally checked proof.
-/
def run : TacticM Unit := do
  evalTactic (← `(tactic| intros))
  try
    evalTactic (← `(tactic|
      solve | (simp_all <;> grind)))
  catch _ => pure ()
  if (← getGoals).isEmpty then
    return
  try
    evalTactic (← `(tactic|
      solve | (simp_all [C.Operator.eq_iff] <;> grind)))
  catch _ => pure ()
  if (← getGoals).isEmpty then
    return
  Free.certifyFailureGoal

end Completeness


/-- Compute and display unifiers modulo a declarative structural theory. -/
elab "#unify " left:term " with " right:term " in " theory:term : command => do
  Lean.Elab.Command.liftTermElabM do
    let left ← Term.elabTerm left none
    let right ← Term.elabTerm right none
    let theoryType ← mkConstWithFreshMVarLevels ``Structural.Theory
    let theory ← Term.elabTerm theory (some theoryType)
    logInfo (← Inspect.structuralUnifiers left right theory)


/--
Compute the free first-order solution set for `h`, check candidate soundness,
and expose completeness followed by one result goal per candidate.
-/
elab "unify " h:ident : tactic =>
  Unification.Tactic.run h.raw h

/--
Compute all candidates modulo registered free commutative operations, check
their soundness, and expose completeness followed by the result goals.
-/
elab "c_unify " h:ident : tactic =>
  Unification.Tactic.runC h.raw h

/-- Unify using the equational theory explicitly named by the user. -/
elab "unify " h:ident " in " theory:term : tactic =>
  Unification.Tactic.runIn h.raw h theory

/-- Attempt to discharge the explicit completeness goal emitted by `unify`. -/
elab "unify_complete" : tactic =>
  Unification.Completeness.run


end Unification


