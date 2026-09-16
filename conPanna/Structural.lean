import Lean

/-!
A prototype declarative interface for Maude-style structural equations.
Unlike `Theory.OperatorLaw`, these declarations generate witnesses consumed by
`EqMod`; they do not assert that raw Lean constructors are equal.
-/
namespace Structural

universe u

/-- A structural equation attached to the operation it governs. -/
inductive OperatorLaw : {operationType : Type u} →
    (operation : operationType) → Type (u + 1) where
  | commutative {α : Type u} {operation : α → α → α} :
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
structure CommutativeDeclaration where
  {carrier : Type u}
  operation : carrier → carrier → carrier

def CommutativeDeclaration.declare {α : Type u}
    (operation : α → α → α) : CommutativeDeclaration where
  operation := operation

structure AssociativeDeclaration where
  {carrier : Type u}
  operation : carrier → carrier → carrier

def AssociativeDeclaration.declare {α : Type u}
    (operation : α → α → α) : AssociativeDeclaration where
  operation := operation

structure IdentityDeclaration where
  {carrier : Type u}
  operation : carrier → carrier → carrier
  element : carrier

def IdentityDeclaration.declare {α : Type u}
    (operation : α → α → α) (element : α) : IdentityDeclaration where
  operation := operation
  element := element

structure Theory where
  symbols : List (Symbol.{u}) := []
  commutative : List (CommutativeDeclaration.{u}) := []
  associative : List (AssociativeDeclaration.{u}) := []
  identities : List (IdentityDeclaration.{u}) := []

/-- Proof-level evidence that a binary operation belongs to a theory. -/
class HasSymbol (theory : Theory.{u}) {α : Type u}
    (operation : α → α → α) where
  declaration : Symbol.{u}
  member : declaration ∈ theory.symbols
  operation_eq : HEq declaration.operation operation

/-- Proof-level evidence that a theory declares an operation commutative. -/
class HasComm (theory : Theory.{u}) {α : Type u}
    (operation : α → α → α) where
  declaration : CommutativeDeclaration.{u}
  member : declaration ∈ theory.commutative
  operation_eq : HEq declaration.operation operation

/-- Proof-level evidence that a theory declares an operation associative. -/
class HasAssoc (theory : Theory.{u}) {α : Type u}
    (operation : α → α → α) where
  declaration : AssociativeDeclaration.{u}
  member : declaration ∈ theory.associative
  operation_eq : HEq declaration.operation operation

/-- Proof-level evidence that a theory declares a two-sided identity. -/
class HasIdentity (theory : Theory.{u}) {α : Type u}
    (operation : α → α → α) (element : α) where
  declaration : IdentityDeclaration.{u}
  member : declaration ∈ theory.identities
  operation_eq : HEq declaration.operation operation
  element_eq : HEq declaration.element element

/-- Internal injectivity evidence for a free binary constructor. -/
class FreeBinary {α : Type u} (operation : α → α → α) where
  operation_eq_iff : ∀ a b c d,
    operation a b = operation c d ↔ a = c ∧ b = d

/--
Internal evidence that a theory consists of one free commutative constructor.
The `structural` command derives this evidence for the C fragment; users do not
prove constructor injectivity or theory-membership facts themselves.
-/
class ConstructorCTheory (theory : Theory.{u}) {α : Type u}
    (operation : outParam (α → α → α)) extends FreeBinary operation where
  symbol : HasSymbol theory operation
  commEvidence : HasComm theory operation
  symbol_unique : ∀ {β : Type u} (candidate : β → β → β),
    [HasSymbol theory candidate] → HEq candidate operation
  comm_unique : ∀ {β : Type u} (candidate : β → β → β),
    [HasComm theory candidate] → HEq candidate operation
  no_assoc : ∀ {β : Type u} (candidate : β → β → β),
    [HasAssoc theory candidate] → False
  no_identity : ∀ {β : Type u} (candidate : β → β → β) (element : β),
    [HasIdentity theory candidate element] → False

/-- Recursive equality for a free binary constructor modulo commutativity. -/
inductive CEquiv {α : Type u} (operation : α → α → α) : α → α → Prop where
  | ofEq {left right : α} : left = right → CEquiv operation left right
  | direct {a b c d : α} :
      CEquiv operation a c → CEquiv operation b d →
        CEquiv operation (operation a b) (operation c d)
  | swapped {a b c d : α} :
      CEquiv operation a d → CEquiv operation b c →
        CEquiv operation (operation a b) (operation c d)

namespace CEquiv

theorem refl {α : Type u} {operation : α → α → α} (value : α) :
    CEquiv operation value value :=
  .ofEq rfl

theorem symm {α : Type u} {operation : α → α → α}
    {left right : α} (equation : CEquiv operation left right) :
    CEquiv operation right left := by
  induction equation with
  | ofEq equality => exact .ofEq equality.symm
  | direct _ _ ihLeft ihRight => exact .direct ihLeft ihRight
  | swapped _ _ ihLeft ihRight => exact .swapped ihRight ihLeft

theorem trans {α : Type u} {operation : α → α → α} [FreeBinary operation]
    {first second third : α}
    (left : CEquiv operation first second)
    (right : CEquiv operation second third) :
    CEquiv operation first third := by
  induction left generalizing third with
  | ofEq equality =>
      cases equality
      exact right
  | @direct a b c d leftFirst leftSecond ihFirst ihSecond =>
      generalize middleEquality : operation c d = middle at right
      cases right with
      | ofEq equality =>
          cases equality
          cases middleEquality
          exact .direct leftFirst leftSecond
      | @direct e f g h rightFirst rightSecond =>
          have parts := (FreeBinary.operation_eq_iff c d e f).mp
            middleEquality
          rcases parts with ⟨rfl, rfl⟩
          exact .direct (ihFirst rightFirst) (ihSecond rightSecond)
      | @swapped e f g h rightFirst rightSecond =>
          have parts := (FreeBinary.operation_eq_iff c d e f).mp
            middleEquality
          rcases parts with ⟨rfl, rfl⟩
          exact .swapped (ihFirst rightFirst) (ihSecond rightSecond)
  | @swapped a b c d leftFirst leftSecond ihFirst ihSecond =>
      generalize middleEquality : operation c d = middle at right
      cases right with
      | ofEq equality =>
          cases equality
          cases middleEquality
          exact .swapped leftFirst leftSecond
      | @direct e f g h rightFirst rightSecond =>
          have parts := (FreeBinary.operation_eq_iff c d e f).mp
            middleEquality
          rcases parts with ⟨rfl, rfl⟩
          exact .swapped (ihFirst rightSecond) (ihSecond rightFirst)
      | @swapped e f g h rightFirst rightSecond =>
          have parts := (FreeBinary.operation_eq_iff c d e f).mp
            middleEquality
          rcases parts with ⟨rfl, rfl⟩
          exact .direct (ihFirst rightSecond) (ihSecond rightFirst)

/-- Away from the registered constructor, C equality is ordinary equality. -/
theorem eq_of_left_not_operation {α : Type u} {operation : α → α → α}
    {left right : α} (notOperation : ∀ a b, left ≠ operation a b)
    (equation : CEquiv operation left right) : left = right := by
  cases equation with
  | ofEq equality => exact equality
  | direct => exact (notOperation _ _ rfl).elim
  | swapped => exact (notOperation _ _ rfl).elim

end CEquiv

/--
Equality generated by native Lean equality, congruence under registered binary
symbols, and the structural laws registered in `theory`. In particular, a raw
constructor can be treated as commutative here without asserting an impossible
equality between distinct constructor trees.
-/
inductive EqMod (theory : Theory.{u}) : {α : Type u} → α → α → Prop where
  | ofEq {α : Type u} {left right : α} (equality : left = right) :
      EqMod theory left right
  | symm {α : Type u} {left right : α} :
      EqMod theory left right → EqMod theory right left
  | trans {α : Type u} {first second third : α} :
      EqMod theory first second → EqMod theory second third →
        EqMod theory first third
  | congr {α : Type u} (operation : α → α → α)
      [HasSymbol theory operation]
      {left left' right right' : α} :
      EqMod theory left left' → EqMod theory right right' →
        EqMod theory (operation left right) (operation left' right')
  | comm {α : Type u} (operation : α → α → α)
      [HasComm theory operation] (left right : α) :
      EqMod theory (operation left right) (operation right left)
  | assoc {α : Type u} (operation : α → α → α)
      [HasAssoc theory operation] (first second third : α) :
      EqMod theory (operation (operation first second) third)
        (operation first (operation second third))
  | identityLeft {α : Type u} (operation : α → α → α) (element value : α)
      [HasIdentity theory operation element] :
      EqMod theory (operation element value) value
  | identityRight {α : Type u} (operation : α → α → α) (element value : α)
      [HasIdentity theory operation element] :
      EqMod theory (operation value element) value

notation:50 left:50 " =[" theory "] " right:51 =>
  EqMod theory left right

namespace EqMod

theorem reflAt (theory : Theory.{u}) {α : Type u} (value : α) :
    EqMod theory value value :=
  .ofEq rfl

theorem transAt (theory : Theory.{u}) {α : Type u}
    {first second third : α} :
    EqMod theory first second → EqMod theory second third →
      EqMod theory first third :=
  .trans

theorem congrAt (theory : Theory.{u}) {α : Type u}
    (operation : α → α → α) [HasSymbol theory operation]
    {left left' right right' : α} :
    EqMod theory left left' → EqMod theory right right' →
      EqMod theory (operation left right) (operation left' right') :=
  .congr operation

theorem commAt (theory : Theory.{u}) {α : Type u}
    (operation : α → α → α) [HasComm theory operation]
    (left right : α) :
    EqMod theory (operation left right) (operation right left) :=
  .comm operation left right

/-- For a registered free C constructor, `EqMod` is precisely recursive C equality. -/
theorem iff_cEquiv {theory : Theory.{u}} {α : Type u}
    (operation : α → α → α) [ConstructorCTheory theory operation]
    {left right : α} :
    EqMod theory left right ↔ CEquiv operation left right := by
  letI : HasSymbol theory operation := ConstructorCTheory.symbol
  letI : HasComm theory operation := ConstructorCTheory.commEvidence
  constructor
  · intro equation
    induction equation with
    | ofEq equality => exact .ofEq equality
    | symm _ ih => exact ih.symm
    | trans _ _ ihLeft ihRight => exact ihLeft.trans ihRight
    | congr candidate _ _ ihLeft ihRight =>
        have operationEquality :=
          ConstructorCTheory.symbol_unique (theory := theory)
            (operation := operation) candidate
        cases operationEquality
        exact .direct ihLeft ihRight
    | «comm» candidate first second =>
        have operationEquality :=
          ConstructorCTheory.comm_unique (theory := theory)
            (operation := operation) candidate
        cases operationEquality
        exact .swapped (.refl first) (.refl second)
    | «assoc» candidate _ _ _ =>
        exact (ConstructorCTheory.no_assoc (theory := theory)
          (operation := operation) (candidate := candidate)).elim
    | identityLeft candidate element _ =>
        exact (ConstructorCTheory.no_identity (theory := theory)
          (operation := operation) (candidate := candidate)
          (element := element)).elim
    | identityRight candidate element _ =>
        exact (ConstructorCTheory.no_identity (theory := theory)
          (operation := operation) (candidate := candidate)
          (element := element)).elim
  · intro equation
    induction equation with
    | ofEq equality => exact .ofEq equality
    | direct _ _ ihLeft ihRight =>
        exact .congr operation ihLeft ihRight
    | swapped _ _ ihLeft ihRight =>
        exact .trans (.congr operation ihLeft ihRight)
          (.comm operation _ _)

end EqMod

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
      let mut commutativeOperations : Array (TSyntax `term) := #[]
      let mut associativeOperations : Array (TSyntax `term) := #[]
      let mut identities : Array (TSyntax `term × TSyntax `term) := #[]
      for law in laws do
        match law with
        | `(structuralLaw| comm $operation:term) =>
            let declaration ← `(term| Structural.OperatorLaw.commutative)
            groups := addStructuralLaw groups operation declaration
            unless commutativeOperations.any fun existing =>
                existing.raw == operation.raw do
              commutativeOperations := commutativeOperations.push operation
        | `(structuralLaw| assoc $operation:term) =>
            let declaration ← `(term| Structural.OperatorLaw.associative)
            groups := addStructuralLaw groups operation declaration
            unless associativeOperations.any fun existing =>
                existing.raw == operation.raw do
              associativeOperations := associativeOperations.push operation
        | `(structuralLaw| id $operation:term $element:term) =>
            let declaration ← `(term| Structural.OperatorLaw.identity $element)
            groups := addStructuralLaw groups operation declaration
            unless identities.any fun existing =>
                existing.1.raw == operation.raw &&
                  existing.2.raw == element.raw do
              identities := identities.push (operation, element)
        | _ => throwUnsupportedSyntax

      let mut symbols : Array (TSyntax `term) := #[]
      for group in groups do
        let declaration ← `(term|
          Structural.Symbol.declare $(group.operation) [$(group.laws),*])
        symbols := symbols.push declaration
      let symbolList ← `(term| [$symbols,*])

      let mut commutativeDeclarations : Array (TSyntax `term) := #[]
      for operation in commutativeOperations do
        commutativeDeclarations := commutativeDeclarations.push
          (← `(term| Structural.CommutativeDeclaration.declare $operation))
      let commutativeList ← `(term| [$commutativeDeclarations,*])

      let mut associativeDeclarations : Array (TSyntax `term) := #[]
      for operation in associativeOperations do
        associativeDeclarations := associativeDeclarations.push
          (← `(term| Structural.AssociativeDeclaration.declare $operation))
      let associativeList ← `(term| [$associativeDeclarations,*])

      let mut identityDeclarations : Array (TSyntax `term) := #[]
      for (operation, element) in identities do
        identityDeclarations := identityDeclarations.push
          (← `(term|
            Structural.IdentityDeclaration.declare $operation $element))
      let identityList ← `(term| [$identityDeclarations,*])

      elabCommand (← `(command|
        def $name : Structural.Theory where
          symbols := $symbolList
          commutative := $commutativeList
          associative := $associativeList
          identities := $identityList))
      for group in groups do
        elabCommand (← `(command|
          instance : Structural.HasSymbol $name $(group.operation) where
            declaration := Structural.Symbol.declare
              $(group.operation) [$(group.laws),*]
            member := by simp [$(name):ident]
            operation_eq := HEq.rfl))
      for operation in commutativeOperations do
        elabCommand (← `(command|
          instance : Structural.HasComm $name $operation where
            declaration := Structural.CommutativeDeclaration.declare $operation
            member := by simp [$(name):ident]
            operation_eq := HEq.rfl))
      for operation in associativeOperations do
        elabCommand (← `(command|
          instance : Structural.HasAssoc $name $operation where
            declaration := Structural.AssociativeDeclaration.declare $operation
            member := by simp [$(name):ident]
            operation_eq := HEq.rfl))
      for (operation, element) in identities do
        elabCommand (← `(command|
          instance : Structural.HasIdentity $name $operation $element where
            declaration :=
              Structural.IdentityDeclaration.declare $operation $element
            member := by simp [$(name):ident]
            operation_eq := HEq.rfl
            element_eq := HEq.rfl))
      if groups.size == 1 && commutativeOperations.size == 1 &&
          associativeOperations.isEmpty && identities.isEmpty then
        let operation := commutativeOperations[0]!
        let isConstructor ← Lean.Elab.Command.liftTermElabM do
          let expression ← Lean.Elab.Term.elabTerm operation none
          let environment ← getEnv
          return match expression.getAppFn with
            | .const declaration _ =>
                match environment.find? declaration with
                | some (.ctorInfo _) => true
                | _ => false
            | _ => false
        if isConstructor then
          elabCommand (← `(command|
            instance : Structural.ConstructorCTheory $name $operation where
              operation_eq_iff := by simp
              symbol := inferInstance
              commEvidence := inferInstance
              symbol_unique := by
                intro β candidate hasSymbol
                rcases hasSymbol with ⟨declaration, member, operation_eq⟩
                simp [$(name):ident] at member
                subst declaration
                exact operation_eq.symm
              comm_unique := by
                intro β candidate hasComm
                rcases hasComm with ⟨declaration, member, operation_eq⟩
                simp [$(name):ident] at member
                subst declaration
                exact operation_eq.symm
              no_assoc := by
                intro β candidate hasAssoc
                have member := hasAssoc.member
                simp [$(name):ident] at member
              no_identity := by
                intro β candidate element hasIdentity
                have member := hasIdentity.member
                simp [$(name):ident] at member))
