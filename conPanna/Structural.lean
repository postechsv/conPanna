import Lean

/-!
A prototype declarative interface for Maude-style structural equations.
Unlike `Theory.OperatorLaw`, these declarations are data intended to drive a
future equality-modulo-theory layer; they do not assert that raw Lean
constructors are equal.
-/
namespace Structural

universe u

/-- A structural equation attached to the operation it governs. -/
inductive OperatorLaw : {operationType : Type u} →
    (operation : operationType) → Type (u + 1) where
  | commutative {α β : Type u} {operation : α → α → β} :
      OperatorLaw operation
  | associative {α : Type u} {operation : α → α → α} :
      OperatorLaw operation
  | identity {α : Type u} {operation : α → α → α} (element : α) :
      OperatorLaw operation

/-- One symbol together with the equations declared for that symbol. -/
structure Symbol where
  {operationType : Type u}
  operation : operationType
  laws : List (OperatorLaw operation) := []

def Symbol.declare {operationType : Type u} (operation : operationType)
    (laws : List (OperatorLaw operation) := []) : Symbol where
  operation := operation
  laws := laws

/-- A collection of independently classified structural symbols. -/
structure Theory where
  symbols : List (Symbol.{u}) := []

end Structural


open Lean Elab Command

declare_syntax_cat structuralLaw

namespace Structural

scoped syntax "comm " term : structuralLaw
scoped syntax "assoc " term : structuralLaw
scoped syntax "id " term:max term : structuralLaw

end Structural

open scoped Structural

/-- Declare a named collection of Maude-style structural equations. -/
syntax (name := structuralCommand)
  "structural " ident " where" ppLine structuralLaw* : command

private structure StructuralGroup where
  operation : TSyntax `term
  laws : Array (TSyntax `term)
  deriving Inhabited

private def addStructuralLaw (groups : Array StructuralGroup)
    (operation law : TSyntax `term) : Array StructuralGroup := Id.run do
  let mut groups := groups
  for index in [:groups.size] do
    if groups[index]!.operation.raw == operation.raw then
      let group := groups[index]!
      groups := groups.set! index { group with laws := group.laws.push law }
      return groups
  return groups.push { operation, laws := #[law] }

elab_rules : command
  | `(structural $name:ident where $laws:structuralLaw*) => do
      let mut groups : Array StructuralGroup := #[]
      for law in laws do
        match law with
        | `(structuralLaw| comm $operation:term) =>
            let declaration ← `(term| Structural.OperatorLaw.commutative)
            groups := addStructuralLaw groups operation declaration
        | `(structuralLaw| assoc $operation:term) =>
            let declaration ← `(term| Structural.OperatorLaw.associative)
            groups := addStructuralLaw groups operation declaration
        | `(structuralLaw| id $operation:term $element:term) =>
            let declaration ← `(term| Structural.OperatorLaw.identity $element)
            groups := addStructuralLaw groups operation declaration
        | _ => throwUnsupportedSyntax

      let mut symbols : Array (TSyntax `term) := #[]
      for group in groups do
        let declaration ← `(term|
          Structural.Symbol.declare $(group.operation) [$(group.laws),*])
        symbols := symbols.push declaration
      let symbolList ← `(term| [$symbols,*])
      elabCommand (← `(command|
        def $name : Structural.Theory where
          symbols := $symbolList))
