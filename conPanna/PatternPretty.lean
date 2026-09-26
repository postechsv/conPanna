import Expresso.Expresso

/-! Compact display for atomic pattern closures. This changes printing only. -/

register_option conPanna.pp.compactPatterns : Bool := {
  defValue := true
  descr := "Display atomic patterns with compact `%`-bound notation"
}

namespace conPanna.PatternPretty

open Lean Lean.Meta Lean.PrettyPrinter.Delaborator Lean.PrettyPrinter.Delaborator.SubExpr

/-- Display-only marker for a variable bound by the enclosing atomic pattern. -/
syntax:max "%" ident : term

/-- Compact display of an atomic pattern's term and constraint. -/
syntax:max "⟦" term:51 " ∣ " term "⟧" : term

macro_rules
  | `(⟦$term ∣ $condition⟧) =>
      `({ term := $term, requires := $condition })

private partial def hasAtomicPatternBody (expression : Expr) : Bool :=
  match expression with
  | .lam _ _ body _ => hasAtomicPatternBody body
  | .mdata _ body => hasAtomicPatternBody body
  | body => body.getAppFn.isConstOf ``framework.Patterns.APattBody.mk

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
      let rewritten ← body.raw.replaceM fun stx => do
        if stx.isIdent && names.contains stx.getId then
          return some (← `(term| %$(mkIdent stx.getId)))
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
