import Expresso.Expresso

/-! Indexed, capture-free syntax and compact display for atomic pattern closures. -/

register_option conPanna.pp.compactPatterns : Bool := {
  defValue := true
  descr := "Display atomic patterns with compact `%`-bound notation"
}

namespace conPanna.PatternPretty

open Lean Lean.Meta Lean.PrettyPrinter.Delaborator Lean.PrettyPrinter.Delaborator.SubExpr

/-- An argument of the enclosing atomic-pattern closure, indexed outermost first. -/
syntax:71 "%" num : term

/-- Compact display of an atomic pattern's term and constraint. -/
syntax:max "⟦" term:51 " ∣ " term "⟧" : term

/-- Resolve `%i` against the binders opened from a pattern closure. -/
def replacePatternVariables (stx : Syntax) (variables : Array Expr) :
    Lean.Elab.Term.TermElabM Syntax :=
  stx.replaceM fun stx => do
    match stx with
    | `(term| ⟦$_ ∣ $_⟧) => return some stx
    | `(term| %$index:num) =>
        let i := index.getNat
        let some binder := variables[i]?
          | throwError "pattern variable %{i} is out of range ({variables.size} binders)"
        return some (← Lean.Elab.Term.exprToSyntax binder).raw
    | _ => return none

/-- Elaborate `%i` directly to a fresh local binder, then close the ordinary lambda. -/
elab_rules : term <= expectedType?
  | `(⟦$value ∣ $condition⟧) => do
      let expectedType := expectedType?
      Lean.Meta.forallTelescope expectedType fun variables bodyType => do
        let value ← replacePatternVariables value.raw variables
        let condition ← replacePatternVariables condition.raw variables
        let value : Term := ⟨value⟩
        let condition : Term := ⟨condition⟩
        let body ← Lean.Elab.Term.elabTerm
          (← `({ term := $value, requires := $condition })) (some bodyType)
        Lean.Meta.mkLambdaFVars variables body

private partial def hasAtomicPatternBody (expression : Expr) : Bool :=
  match expression with
  | .lam _ _ body _ => hasAtomicPatternBody body
  | .mdata _ body => hasAtomicPatternBody body
  | body => body.getAppFn.isConstOf ``framework.Patterns.APattBody.mk

private partial def containsBinderName (stx : Syntax) (names : Array Name) : Bool :=
  if stx.isIdent && names.contains stx.getId then true
  else stx.getArgs.any (containsBinderName · names)

/-- A shadowed printed name cannot be safely converted by syntactic rewriting. -/
private partial def shadowsPatternBinder (stx : Syntax) (names : Array Name) : Bool :=
  let kind := stx.getKind
  let unsupportedLocalBinder := kind == ``Lean.Parser.Term.«let» ||
    kind == ``Lean.Parser.Term.«have» ||
    kind == ``Lean.Parser.Term.«let_fun» ||
    kind == ``Lean.Parser.Term.«let_delayed» ||
    kind == ``Lean.Parser.Term.«let_tmp» ||
    kind == ``Lean.Parser.Term.«haveI» ||
    kind == ``Lean.Parser.Term.«letI» ||
    kind == ``Lean.Parser.Term.«match» ||
    kind == ``Lean.Parser.Term.matchExpr ||
    kind == ``Lean.Parser.Term.«do»
  if unsupportedLocalBinder then true else
  let bindsName := kind == ``Lean.Parser.Term.forall ||
    kind == `Lean.«term∀__,_» || kind == ``Lean.Parser.Term.fun
  if bindsName && (stx.getArgs[1]?.any (containsBinderName · names)) then true
  else stx.getArgs.any (shadowsPatternBinder · names)

/-- Render a closure returning `APattBody` without its explicit lambdas. -/
@[delab lam]
def delabAtomicPatternClosure : Delab := do
  unless (← getOptions).getBool `conPanna.pp.compactPatterns true do
    failure
  let expression ← getExpr
  unless hasAtomicPatternBody expression do
    failure
  let closureSyntax ← delabLam
  match closureSyntax with
  | `(fun $binders* ↦ $body:term) => do
      let names := binders.filterMap fun binder =>
        if binder.raw.isIdent then some binder.raw.getId else none
      unless names.size == binders.size do failure
      if shadowsPatternBinder body.raw names then failure
      let rewritten ← body.raw.replaceM fun stx => do
        if stx.isIdent then
          if let some index := names.toList.idxOf? stx.getId then
            let indexSyntax : TSyntax `num := ⟨Syntax.mkNumLit (toString index)⟩
            let indexed ← `(term| %$indexSyntax:num)
            return some (← `(term| ($indexed))).raw
        return none
      return ⟨rewritten⟩
  | _ => failure

/-- Render the body itself in term-and-condition notation. -/
@[app_delab framework.Patterns.APattBody.mk]
def delabAPattBody : Delab := do
  unless (← getOptions).getBool `conPanna.pp.compactPatterns true do
    failure
  let term ← withNaryArg 1 delab
  let condition ← withNaryArg 2 delab
  `(⟦$term ∣ $condition⟧)

end conPanna.PatternPretty
