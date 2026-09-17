import Expresso.Expresso

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

/-- An ordinary inductive constructor through which structural equality is
propagated.  Constructor symbols carry no equations of their own. -/
structure ConstructorDeclaration where
  {constructorType : Type u}
  constructor : constructorType

def ConstructorDeclaration.declare {constructorType : Type u}
    (constructor : constructorType) : ConstructorDeclaration where
  constructor := constructor

structure Theory where
  symbols : List (Symbol.{u}) := []
  constructors : List (ConstructorDeclaration.{u}) := []
  commutative : List (CommutativeDeclaration.{u}) := []
  associative : List (AssociativeDeclaration.{u}) := []
  identities : List (IdentityDeclaration.{u}) := []

/-- Proof-level evidence that a binary operation belongs to a theory. -/
class HasSymbol (theory : Theory.{u}) {α : Type u}
    (operation : α → α → α) where
  declaration : Symbol.{u}
  member : declaration ∈ theory.symbols
  operation_eq : HEq declaration.operation operation

/-- Proof-level evidence that an ordinary constructor belongs to the term
signature associated with a structural theory. -/
class HasConstructor (theory : Theory.{u}) {constructorType : Type u}
    (constructor : constructorType) where
  declaration : ConstructorDeclaration.{u}
  member : declaration ∈ theory.constructors
  constructor_eq : HEq declaration.constructor constructor

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
  no_constructor : ∀ {constructorType : Type u}
    (candidate : constructorType), [HasConstructor theory candidate] → False

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
  | constructor₁ {α β : Type u} (constructor : α → β)
      [HasConstructor theory constructor] {value value' : α} :
      EqMod theory value value' →
        EqMod theory (constructor value) (constructor value')
  | constructor₂ {α β γ : Type u} (constructor : α → β → γ)
      [HasConstructor theory constructor]
      {first first' : α} {second second' : β} :
      EqMod theory first first' → EqMod theory second second' →
        EqMod theory (constructor first second) (constructor first' second')
  | constructor₃ {α β γ δ : Type u} (constructor : α → β → γ → δ)
      [HasConstructor theory constructor]
      {first first' : α} {second second' : β} {third third' : γ} :
      EqMod theory first first' → EqMod theory second second' →
      EqMod theory third third' →
        EqMod theory (constructor first second third)
          (constructor first' second' third')
  | constructor₄ {α β γ δ ε : Type u}
      (constructor : α → β → γ → δ → ε)
      [HasConstructor theory constructor]
      {first first' : α} {second second' : β} {third third' : γ}
      {fourth fourth' : δ} :
      EqMod theory first first' → EqMod theory second second' →
      EqMod theory third third' → EqMod theory fourth fourth' →
        EqMod theory (constructor first second third fourth)
          (constructor first' second' third' fourth')
  | constructor₅ {α β γ δ ε ζ : Type u}
      (constructor : α → β → γ → δ → ε → ζ)
      [HasConstructor theory constructor]
      {first first' : α} {second second' : β} {third third' : γ}
      {fourth fourth' : δ} {fifth fifth' : ε} :
      EqMod theory first first' → EqMod theory second second' →
      EqMod theory third third' → EqMod theory fourth fourth' →
      EqMod theory fifth fifth' →
        EqMod theory (constructor first second third fourth fifth)
          (constructor first' second' third' fourth' fifth')
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

theorem symmAt (theory : Theory.{u}) {α : Type u}
    {left right : α} :
    EqMod theory left right → EqMod theory right left :=
  .symm

theorem congrAt (theory : Theory.{u}) {α : Type u}
    (operation : α → α → α) [HasSymbol theory operation]
    {left left' right right' : α} :
    EqMod theory left left' → EqMod theory right right' →
      EqMod theory (operation left right) (operation left' right') :=
  .congr operation

theorem constructor₁At (theory : Theory.{u}) {α β : Type u}
    (constructor : α → β) [HasConstructor theory constructor]
    {value value' : α} :
    EqMod theory value value' →
      EqMod theory (constructor value) (constructor value') :=
  .constructor₁ constructor

theorem constructor₂At (theory : Theory.{u}) {α β γ : Type u}
    (constructor : α → β → γ) [HasConstructor theory constructor]
    {first first' : α} {second second' : β} :
    EqMod theory first first' → EqMod theory second second' →
      EqMod theory (constructor first second) (constructor first' second') :=
  .constructor₂ constructor

theorem constructor₃At (theory : Theory.{u}) {α β γ δ : Type u}
    (constructor : α → β → γ → δ) [HasConstructor theory constructor]
    {first first' : α} {second second' : β} {third third' : γ} :
    EqMod theory first first' → EqMod theory second second' →
    EqMod theory third third' →
      EqMod theory (constructor first second third)
        (constructor first' second' third') :=
  .constructor₃ constructor

theorem constructor₄At (theory : Theory.{u}) {α β γ δ ε : Type u}
    (constructor : α → β → γ → δ → ε)
    [HasConstructor theory constructor]
    {first first' : α} {second second' : β} {third third' : γ}
    {fourth fourth' : δ} :
    EqMod theory first first' → EqMod theory second second' →
    EqMod theory third third' → EqMod theory fourth fourth' →
      EqMod theory (constructor first second third fourth)
        (constructor first' second' third' fourth') :=
  .constructor₄ constructor

theorem constructor₅At (theory : Theory.{u}) {α β γ δ ε ζ : Type u}
    (constructor : α → β → γ → δ → ε → ζ)
    [HasConstructor theory constructor]
    {first first' : α} {second second' : β} {third third' : γ}
    {fourth fourth' : δ} {fifth fifth' : ε} :
    EqMod theory first first' → EqMod theory second second' →
    EqMod theory third third' → EqMod theory fourth fourth' →
    EqMod theory fifth fifth' →
      EqMod theory (constructor first second third fourth fifth)
        (constructor first' second' third' fourth' fifth') :=
  .constructor₅ constructor

theorem commAt (theory : Theory.{u}) {α : Type u}
    (operation : α → α → α) [HasComm theory operation]
    (left right : α) :
    EqMod theory (operation left right) (operation right left) :=
  .comm operation left right

theorem identityRightAt (theory : Theory.{u}) {α : Type u}
    (operation : α → α → α) (element value : α)
    [HasIdentity theory operation element] :
    EqMod theory (operation value element) value :=
  .identityRight operation element value

private def foldOperation {α : Type u} (operation : α → α → α)
    (identity : α) : List α → α
  | [] => identity
  | value :: values => operation value (foldOperation operation identity values)

theorem foldOperation_append (theory : Theory.{u}) {α : Type u}
    (operation : α → α → α) (identity : α)
    [HasSymbol theory operation] [HasAssoc theory operation]
    [HasIdentity theory operation identity] (left right : List α) :
    EqMod theory
      (operation (foldOperation operation identity left)
        (foldOperation operation identity right))
      (foldOperation operation identity (left ++ right)) := by
  induction left with
  | nil => exact .identityLeft operation identity _
  | cons value values ih =>
      exact .trans (.assoc operation value _ _)
        (.congr operation (.ofEq rfl) ih)

theorem foldOperation_perm (theory : Theory.{u}) {α : Type u}
    (operation : α → α → α) (identity : α)
    [HasSymbol theory operation] [HasAssoc theory operation]
    [HasComm theory operation] [HasIdentity theory operation identity]
    {left right : List α} (permutation : left.Perm right) :
    EqMod theory (foldOperation operation identity left)
      (foldOperation operation identity right) := by
  induction permutation with
  | nil => exact .ofEq rfl
  | cons value _ ih => exact .congr operation (.ofEq rfl) ih
  | swap first second values =>
      exact .trans (.symm (.assoc operation second first _)) <|
        .trans (.congr operation (.comm operation second first) (.ofEq rfl))
          (.assoc operation first second _)
  | trans _ _ ihLeft ihRight => exact .trans ihLeft ihRight

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
    | symm _ ih => exact (ih operation).symm
    | trans _ _ ihLeft ihRight =>
        exact (ihLeft operation).trans (ihRight operation)
    | congr candidate _ _ ihLeft ihRight =>
        have leftProof := ihLeft operation
        have rightProof := ihRight operation
        have operationEquality :=
          ConstructorCTheory.symbol_unique (theory := theory)
            (operation := operation) candidate
        cases operationEquality
        exact .direct leftProof rightProof
    | constructor₁ candidate _ =>
        exact (ConstructorCTheory.no_constructor (theory := theory)
          (operation := operation) (candidate := candidate)).elim
    | constructor₂ candidate _ _ =>
        exact (ConstructorCTheory.no_constructor (theory := theory)
          (operation := operation) (candidate := candidate)).elim
    | constructor₃ candidate _ _ _ =>
        exact (ConstructorCTheory.no_constructor (theory := theory)
          (operation := operation) (candidate := candidate)).elim
    | constructor₄ candidate _ _ _ _ =>
        exact (ConstructorCTheory.no_constructor (theory := theory)
          (operation := operation) (candidate := candidate)).elim
    | constructor₅ candidate _ _ _ _ _ =>
        exact (ConstructorCTheory.no_constructor (theory := theory)
          (operation := operation) (candidate := candidate)).elim
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


open Lean Elab Command Meta

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

private def stateRootNames : Lean.Elab.Term.TermElabM (Array Name) := do
  let environment ← getEnv
  let mut roots := #[]
  for (declarationName, declaration) in environment.constants.toList do
    unless Lean.Meta.isInstanceCore environment declarationName do
      continue
    let rootName? ← Lean.Meta.forallTelescopeReducing declaration.type fun _ resultType => do
      let resultType ← whnf resultType
      unless resultType.isAppOfArity ``framework.State 1 do
        return none
      let rootType ← whnf resultType.getAppArgs[0]!
      return rootType.getAppFn.constName?
    if let some rootName := rootName? then
      unless roots.contains rootName do
        roots := roots.push rootName
  return roots

private partial def collectConstructorNames (pending : List Name)
    (visited constructors : Array Name) :
    Lean.Elab.Term.TermElabM (Array Name) := do
  match pending with
  | [] => return constructors
  | inductiveName :: rest =>
      if visited.contains inductiveName then
        collectConstructorNames rest visited constructors
      else
        let info ← getConstInfoInduct inductiveName
        unless info.numParams == 0 && info.numIndices == 0 do
          throwError "parameterized or indexed state sort is not supported: {inductiveName}"
        let mut dependencies := #[]
        let mut constructors := constructors
        for constructorName in info.ctors do
          let constructorInfo ← getConstInfoCtor constructorName
          unless constructorInfo.numParams == 0 do
            throwError "parameterized state constructor is not supported: {constructorName}"
          constructors := constructors.push constructorName
          let fieldNames ← Lean.Meta.forallTelescopeReducing
              constructorInfo.type fun arguments _ => do
            unless arguments.size == constructorInfo.numFields do
              throwError "unexpected constructor telescope for {constructorName}"
            let mut fieldNames := #[]
            for argument in arguments do
              let fieldType ← whnf (← inferType argument)
              let some fieldName := fieldType.getAppFn.constName?
                | throwError "expected an inductive constructor field, got: {fieldType}"
              match (← getEnv).find? fieldName with
              | some (.inductInfo _) =>
                  unless fieldNames.contains fieldName do
                    fieldNames := fieldNames.push fieldName
              | _ =>
                  throwError "expected an inductive constructor field, got: {fieldType}"
            return fieldNames
          for fieldName in fieldNames do
            unless dependencies.contains fieldName do
              dependencies := dependencies.push fieldName
        collectConstructorNames (rest ++ dependencies.toList)
          (visited.push inductiveName) constructors

private def stateConstructorNames :
    Lean.Elab.Term.TermElabM (Array Name) := do
  collectConstructorNames (← stateRootNames).toList #[] #[]

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

      let isConstructorC ←
        if groups.size == 1 && commutativeOperations.size == 1 &&
            associativeOperations.isEmpty && identities.isEmpty then
          let operation := commutativeOperations[0]!
          Lean.Elab.Command.liftTermElabM do
            let expression ← Lean.Elab.Term.elabTerm operation none
            let environment ← getEnv
            return match expression.getAppFn with
              | .const declaration _ =>
                  match environment.find? declaration with
                  | some (.ctorInfo _) => true
                  | _ => false
              | _ => false
        else
          pure false

      let constructorNames ←
        if isConstructorC then pure #[]
        else Lean.Elab.Command.liftTermElabM stateConstructorNames

      let mut symbols : Array (TSyntax `term) := #[]
      for group in groups do
        let declaration ← `(term|
          Structural.Symbol.declare $(group.operation) [$(group.laws),*])
        symbols := symbols.push declaration
      let symbolList ← `(term| [$symbols,*])

      let mut constructors : Array (TSyntax `term) := #[]
      for constructorName in constructorNames do
        constructors := constructors.push
          (← `(term| Structural.ConstructorDeclaration.declare
            $(mkIdent constructorName)))
      let constructorList ← `(term| [$constructors,*])

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
          constructors := $constructorList
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
      for constructorName in constructorNames do
        let constructor := mkIdent constructorName
        elabCommand (← `(command|
          instance : Structural.HasConstructor $name $constructor where
            declaration := Structural.ConstructorDeclaration.declare
              $constructor
            member := by simp [$(name):ident]
            constructor_eq := HEq.rfl))
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
      if isConstructorC then
        let operation := commutativeOperations[0]!
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
              simp [$(name):ident] at member
            no_constructor := by
              intro constructorType candidate hasConstructor
              have member := hasConstructor.member
              simp [$(name):ident] at member))
