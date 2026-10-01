import Expresso.Expresso

/-!
A prototype declarative interface for Maude-style structural equations.
Unlike `Theory.OperatorLaw`, these declarations generate witnesses consumed by
`EqMod`; they do not assert that raw Lean constructors are equal.
-/
namespace Structural

universe u v

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

/-!
`ConstructorCongruence` records an application spine whose head is a
registered constructor. Keeping the head evidence separate lets `EqMod` lift
structural equality through constructors of arbitrary heterogeneous arity.
-/
mutual
  /-- Equality generated by Lean equality, registered equations, and
  congruence through structural symbols and ordinary constructors. -/
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
    | constructor {α : Type u} {left right : α} :
        ConstructorCongruence theory left right → EqMod theory left right
    | comm {α : Type u} (operation : α → α → α)
        [HasComm theory operation] (left right : α) :
        EqMod theory (operation left right) (operation right left)
    | assoc {α : Type u} (operation : α → α → α)
        [HasAssoc theory operation] (first second third : α) :
        EqMod theory (operation (operation first second) third)
          (operation first (operation second third))
    | identityLeft {α : Type u} (operation : α → α → α)
        (element value : α) [HasIdentity theory operation element] :
        EqMod theory (operation element value) value
    | identityRight {α : Type u} (operation : α → α → α)
        (element value : α) [HasIdentity theory operation element] :
        EqMod theory (operation value element) value

  /-- Pointwise structural congruence along an arbitrary constructor spine. -/
  inductive ConstructorCongruence (theory : Theory.{u}) :
      {α : Type u} → α → α → Prop where
    | head {constructorType : Type u} (constructor : constructorType)
        [HasConstructor theory constructor] :
        ConstructorCongruence theory constructor constructor
    | app {α β : Type u} {left right : α → β} {argument argument' : α} :
        ConstructorCongruence theory left right →
        EqMod theory argument argument' →
        ConstructorCongruence theory (left argument) (right argument')
end

/-- Surface equality dispatch. Existing Theory values keep exactly their old
EqMod meaning; explicitly certified theory values use indexed semantics. -/
class ModRelation {T : Type v} (theory : T) (α : Type u) where
  relate : α → α → Prop

instance {theory : Theory.{u}} {α : Type u} : ModRelation theory α where
  relate := EqMod theory

abbrev eqModOf {T : Type v} (theory : T) {α : Type u}
    [ModRelation theory α] (left right : α) : Prop :=
  ModRelation.relate (theory := theory) left right

notation:50 left:50 " =[" theory "] " right:51 =>
  eqModOf theory left right

namespace ConstructorCongruence

theorem headAt (theory : Theory.{u}) {constructorType : Type u}
    (constructor : constructorType) [HasConstructor theory constructor] :
    ConstructorCongruence theory constructor constructor :=
  .head constructor

theorem appAt (theory : Theory.{u}) {α β : Type u}
    {left right : α → β} {argument argument' : α} :
    ConstructorCongruence theory left right →
    EqMod theory argument argument' →
    ConstructorCongruence theory (left argument) (right argument') :=
  .app

end ConstructorCongruence

namespace EqMod

theorem equivalence (theory : Theory.{u}) (α : Type u) :
    Equivalence (EqMod theory (α := α)) :=
  ⟨fun _ => .ofEq rfl, fun h => .symm h, fun h₁ h₂ => .trans h₁ h₂⟩

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

theorem constructorAt (theory : Theory.{u}) {α : Type u}
    {left right : α} :
    ConstructorCongruence theory left right → EqMod theory left right :=
  .constructor

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
    refine EqMod.rec
      (motive_1 := fun {β : Type u} left right _ =>
        ∀ (candidate : β → β → β),
          [ConstructorCTheory theory candidate] →
          CEquiv candidate left right)
      (motive_2 := fun {_ : Type u} _ _ _ => False)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ equation operation
    · intro β left right equality candidate
      intro candidateTheory
      exact .ofEq equality
    · intro β left right equation ih candidate
      intro candidateTheory
      exact (ih candidate).symm
    · intro β first second third leftEq rightEq ihLeft ihRight candidate
      intro candidateTheory
      exact (ihLeft candidate).trans (ihRight candidate)
    · intro β candidate hasSymbol left left' right right' leftEq rightEq
        ihLeft ihRight registered
      intro registeredTheory
      have operationEquality :=
        ConstructorCTheory.symbol_unique (theory := theory)
          (operation := registered) candidate
      cases operationEquality
      exact .direct (ihLeft candidate) (ihRight candidate)
    · intro β left right constructorCongruence impossible
      exact impossible.elim
    · intro β candidate hasComm first second registered
      intro registeredTheory
      have operationEquality :=
        ConstructorCTheory.comm_unique (theory := theory)
          (operation := registered) candidate
      cases operationEquality
      exact .swapped (.refl first) (.refl second)
    · intro β candidate hasAssoc first second third registered
      intro registeredTheory
      exact (ConstructorCTheory.no_assoc (theory := theory)
        (operation := registered) (candidate := candidate)).elim
    · intro β candidate element value hasIdentity registered
      intro registeredTheory
      exact (ConstructorCTheory.no_identity (theory := theory)
        (operation := registered) (candidate := candidate)
        (element := element)).elim
    · intro β candidate element value hasIdentity registered
      intro registeredTheory
      exact (ConstructorCTheory.no_identity (theory := theory)
        (operation := registered) (candidate := candidate)
        (element := element)).elim
    · intro constructorType candidate hasConstructor
      exact ConstructorCTheory.no_constructor (theory := theory)
        (operation := operation) (candidate := candidate)
    · intro β γ left right argument argument' functionProof argumentProof
        impossible argumentIH
      exact impossible
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


/-! ## Indexed structural semantics for certification

This is the signature-indexed successor to the type-erased constructor spine.
The old EqMod API remains available during migration. Indexed.NativeEq has a
proved map to it; no unproved equivalence between the representations is used.
-/

namespace Structural.Indexed

/-! ## Library prototype: finite-arity many-sorted syntax and derivations -/

structure Signature (Sorts : Type) where
  Symbol : List Sorts → Sorts → Type
  ACUOp : Sorts → Type
  add : ∀ {s}, ACUOp s → Symbol [s, s] s
  zero : ∀ {s}, ACUOp s → Symbol [] s

variable {Sorts : Type} (sig : Signature Sorts)

mutual
  inductive Tree : Sorts → Type where
    | app {ss s} (head : sig.Symbol ss s) (args : Trees ss) : Tree s
  inductive Trees : List Sorts → Type where
    | nil : Trees []
    | cons {s ss} (first : Tree s) (rest : Trees ss) : Trees (s :: ss)
end

def zero {s : Sorts} (op : sig.ACUOp s) : Tree sig s := .app (sig.zero op) .nil
def add {s : Sorts} (op : sig.ACUOp s) (a b : Tree sig s) : Tree sig s :=
  .app (sig.add op) (.cons a (.cons b .nil))

mutual
  /-- Constructor identity and argument sorts remain in EVERY derivation. -/
  inductive Eq : {s : Sorts} → Tree sig s → Tree sig s → Prop where
    | refl {s} (a : Tree sig s) : Eq a a
    | symm {s} {a b : Tree sig s} : Eq a b → Eq b a
    | trans {s} {a b c : Tree sig s} : Eq a b → Eq b c → Eq a c
    | congr {ss s} (head : sig.Symbol ss s) {a b : Trees sig ss} :
        Eqs a b → Eq (.app head a) (.app head b)
    | comm {s} (op : sig.ACUOp s) (a b : Tree sig s) :
        Eq (add sig op a b) (add sig op b a)
    | assoc {s} (op : sig.ACUOp s) (a b c : Tree sig s) :
        Eq (add sig op (add sig op a b) c) (add sig op a (add sig op b c))
    | unit {s} (op : sig.ACUOp s) (a : Tree sig s) : Eq (add sig op (zero sig op) a) a
  inductive Eqs : {ss : List Sorts} → Trees sig ss → Trees sig ss → Prop where
    | nil : Eqs .nil .nil
    | cons {s ss} {a b : Tree sig s} {as bs : Trees sig ss} :
        Eq a b → Eqs as bs → Eqs (.cons a as) (.cons b bs)
end

def Args (C : Sorts → Type) : List Sorts → Type
  | [] => PUnit
  | s :: ss => C s × Args C ss

structure Algebra where
  Carrier : Sorts → Type
  apply : ∀ {ss s}, sig.Symbol ss s → Args Carrier ss → Carrier s

variable {sig}

mutual
  def Tree.eval (A : Algebra sig) : {s : Sorts} → Tree sig s → A.Carrier s
    | _, .app f args => A.apply f (args.eval A)
  def Trees.eval (A : Algebra sig) : {ss : List Sorts} → Trees sig ss → Args A.Carrier ss
    | _, .nil => PUnit.unit
    | _, .cons a as => (a.eval A, as.eval A)
end

variable (sig)

def ArgsRel {C : Sorts → Type} (R : ∀ s, C s → C s → Prop) :
    (ss : List Sorts) → Args C ss → Args C ss → Prop
  | [], _, _ => True
  | s :: ss, (a, as), (b, bs) => R s a b ∧ ArgsRel R ss as bs

/-- Semantic metatheorem input, not user registration. Instantiated by library
interpretations below. Ordinary constructor compatibility is genuinely sorted. -/
structure Model (A : Algebra sig) where
  Rel : ∀ s, A.Carrier s → A.Carrier s → Prop
  refl : ∀ s a, Rel s a a
  symm : ∀ s {a b}, Rel s a b → Rel s b a
  trans : ∀ s {a b c}, Rel s a b → Rel s b c → Rel s a c
  congr : ∀ {ss s} (f : sig.Symbol ss s) {a b},
    ArgsRel Rel ss a b → Rel s (A.apply f a) (A.apply f b)
  comm : ∀ {s} (op : sig.ACUOp s) a b,
    Rel s (A.apply (sig.add op) (a, b, PUnit.unit))
      (A.apply (sig.add op) (b, a, PUnit.unit))
  assoc : ∀ {s} (op : sig.ACUOp s) a b c,
    Rel s (A.apply (sig.add op) (A.apply (sig.add op) (a, b, PUnit.unit), c, PUnit.unit))
      (A.apply (sig.add op) (a, A.apply (sig.add op) (b, c, PUnit.unit), PUnit.unit))
  unit : ∀ {s} (op : sig.ACUOp s) a,
    Rel s (A.apply (sig.add op) (A.apply (sig.zero op) PUnit.unit, a, PUnit.unit)) a

theorem Eq.sound {s : Sorts} {A : Algebra sig} (M : Model sig A)
    {a b : Tree sig s} (h : Eq sig a b) : M.Rel s (a.eval A) (b.eval A) := by
  refine Eq.rec
    (motive_1 := fun {s} a b _ => M.Rel s (a.eval A) (b.eval A))
    (motive_2 := fun {ss} a b _ => ArgsRel M.Rel ss (a.eval A) (b.eval A))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h
  · intro s a; exact M.refl s _
  · intro s a b h ih; exact M.symm s ih
  · intro s a b c h₁ h₂ ih₁ ih₂; exact M.trans s ih₁ ih₂
  · intro ss s f a b h ih; exact M.congr f ih
  · intro s op a b; exact M.comm op _ _
  · intro s op a b c; exact M.assoc op _ _ _
  · intro s op a; exact M.unit op _
  · trivial
  · intro s ss a b as bs h₁ h₂ ih₁ ih₂; exact ⟨ih₁, ih₂⟩

/-! ## Library prototype: native registration boundary

ONLY syntactic identities below. A generator emits quote by constructor recursion,
apply by constructor enumeration, and proves the equations by rfl / induction.
These fields are not semantic ACU proof obligations delegated to the user.
-/

def Args.quote {C : Sorts → Type} (quote : ∀ s, C s → Tree sig s) :
    (ss : List Sorts) → Args C ss → Trees sig ss
  | [], _ => .nil
  | s :: ss, (a, as) => .cons (quote s a) (Args.quote quote ss as)

structure Registration extends Algebra sig where
  quote : ∀ s, Carrier s → Tree sig s
  eval_quote : ∀ s a, (quote s a).eval toAlgebra = a
  quote_apply : ∀ {ss s} (f : sig.Symbol ss s) (args : Args Carrier ss),
    quote s (apply f args) = .app f (Args.quote sig quote ss args)

def NativeEq (reg : Registration sig) {s : Sorts} (a b : reg.Carrier s) : Prop :=
  Eq sig (reg.quote s a) (reg.quote s b)

/-- The same structural induction works for any constructor-compatible reifier,
without assuming that every semantic value is a valid syntax encoding. -/
theorem Tree.rebuild_eval (A : Algebra sig) (quote : ∀ s, A.Carrier s → Tree sig s)
    (compatible : ∀ {ss s} (f : sig.Symbol ss s) (args : Args A.Carrier ss),
      quote s (A.apply f args) = .app f (Args.quote sig quote ss args))
    {s : Sorts} (a : Tree sig s) : quote s (a.eval A) = a := by
  refine Tree.rec
    (motive_1 := fun {s} a => quote s (a.eval A) = a)
    (motive_2 := fun {ss} as => Args.quote sig quote ss (as.eval A) = as)
    ?_ ?_ ?_ a
  · intro ss s f args ih
    change quote s (A.apply f (args.eval A)) = _
    rw [compatible, ih]
  · rfl
  · intro s ss a as ih₁ ih₂
    change Trees.cons (quote s (a.eval A)) (Args.quote sig quote ss (as.eval A)) = _
    rw [ih₁, ih₂]

theorem Registration.quote_eval (reg : Registration sig) {s : Sorts} (a : Tree sig s) :
    reg.quote s (a.eval reg.toAlgebra) = a :=
  Tree.rebuild_eval sig reg.toAlgebra reg.quote reg.quote_apply a

/-! ## Library adapter to existing EqMod: arbitrary constructor arity -/

def Curried (C : Sorts → Type) : List Sorts → Sorts → Type
  | [], s => C s
  | a :: as, s => C a → Curried C as s

def applyCurried {C : Sorts → Type} : {ss : List Sorts} → {s : Sorts} →
    Curried C ss s → Args C ss → C s
  | [], _, f, _ => f
  | _ :: _, _, f, (a, as) => applyCurried (f a) as

theorem applyCurried_congr {B : Structural.Theory} {C : Sorts → Type}
    {ss : List Sorts} {s : Sorts} {f g : Curried C ss s}
    (h : Structural.ConstructorCongruence B f g) {a b : Args C ss}
    (args : ArgsRel (fun _ => Structural.EqMod B) ss a b) :
    Structural.EqMod B (applyCurried f a) (applyCurried g b) := by
  induction ss with
  | nil => exact .constructor h
  | cons first rest ih => exact ih (.app h args.1) args.2

/-- Only native symbols, registered-law witnesses and a definitional application
equation. No EqMod reflection field. This metadata is generated by enumeration. -/
structure Legacy (B : Structural.Theory) (A : Algebra sig) where
  head : ∀ {ss s}, sig.Symbol ss s → Curried A.Carrier ss s
  apply_head : ∀ {ss s} (f : sig.Symbol ss s) args,
    A.apply f args = applyCurried (head f) args
  registered : ∀ {ss s} (f : sig.Symbol ss s), Structural.HasConstructor B (head f)
  comm : ∀ {s} (op : sig.ACUOp s), Structural.HasComm B (head (sig.add op))
  assoc : ∀ {s} (op : sig.ACUOp s), Structural.HasAssoc B (head (sig.add op))
  unit : ∀ {s} (op : sig.ACUOp s),
    Structural.HasIdentity B (head (sig.add op)) (head (sig.zero op))

def Legacy.model {B : Structural.Theory} {A : Algebra sig} (metadata : Legacy sig B A) :
    Model sig A where
  Rel := fun _ => Structural.EqMod B
  refl := fun _ _ => .ofEq rfl
  symm := fun _ {_ _} h => .symm h
  trans := fun _ {_ _ _} h₁ h₂ => .trans h₁ h₂
  congr := by
    intro ss s f a b h
    rw [metadata.apply_head, metadata.apply_head]
    letI := metadata.registered f
    exact applyCurried_congr (.head (metadata.head f)) h
  comm := by
    intro s op a b
    simp only [metadata.apply_head, applyCurried]
    letI := metadata.comm op
    exact .comm _ _ _
  assoc := by
    intro s op a b c
    simp only [metadata.apply_head, applyCurried]
    letI := metadata.assoc op
    exact .assoc _ _ _ _
  unit := by
    intro s op a
    simp only [metadata.apply_head, applyCurried]
    letI := metadata.unit op
    exact .identityLeft _ _ _

theorem NativeEq.to_legacy {B : Structural.Theory} (reg : Registration sig)
    (metadata : Legacy sig B reg.toAlgebra) {s : Sorts} {a b : reg.Carrier s}
    (h : NativeEq sig reg a b) : Structural.EqMod B a b := by
  have lifted := Eq.sound sig (metadata.model sig) h
  simpa only [reg.eval_quote] using lifted

end Structural.Indexed

namespace Structural.Indexed.Wrapper

open Indexed

inductive SortTag where
  | bag | configuration
  deriving DecidableEq

inductive Symbol (Atom : Type) : List SortTag → SortTag → Type where
  | empty : Symbol Atom [] .bag
  | atom (a : Atom) : Symbol Atom [] .bag
  | union : Symbol Atom [.bag, .bag] .bag
  | wrap : Symbol Atom [.bag] .configuration

inductive Operator : SortTag → Type where
  | union : Operator .bag

def signature (Atom : Type) : Signature SortTag where
  Symbol := Symbol Atom
  ACUOp := Operator
  add := fun op => match op with | .union => .union
  zero := fun op => match op with | .union => .empty

variable {Atom : Type}

abbrev BagTree (Atom : Type) := Tree (signature Atom) .bag
abbrev ConfTree (Atom : Type) := Tree (signature Atom) .configuration
def empty : BagTree Atom := .app .empty .nil
def atom (a : Atom) : BagTree Atom := .app (.atom a) .nil
def union (a b : BagTree Atom) : BagTree Atom := .app .union (.cons a (.cons b .nil))
def wrap (a : BagTree Atom) : ConfTree Atom := .app .wrap (.cons a .nil)

end Structural.Indexed.Wrapper

namespace Structural

/-- A registered, signature-indexed theory. The legacy declaration is retained
for existing tools, but equality for this value is the indexed relation. -/
structure CertifiedTheory where
  Sorts : Type
  signature : Indexed.Signature Sorts
  native : Indexed.Registration signature
  original : Theory
  translation : Indexed.Legacy signature original native.toAlgebra

/-- Generated per native sort. The equality here is just rfl for generated
registrations; no inequality between unrelated Lean TYPES is requested. -/
class NativeSort (theory : CertifiedTheory) (α : Type) where
  tag : theory.Sorts
  carrier_eq : theory.native.Carrier tag = α

def CertifiedTheory.Rel (theory : CertifiedTheory) {α : Type}
    [sort : NativeSort theory α] (a b : α) : Prop :=
  Indexed.NativeEq theory.signature theory.native
    (cast sort.carrier_eq.symm a) (cast sort.carrier_eq.symm b)

instance {theory : CertifiedTheory} {α : Type} [NativeSort theory α] :
    ModRelation theory α where
  relate := theory.Rel

theorem CertifiedTheory.equivalence (theory : CertifiedTheory) (α : Type)
    [NativeSort theory α] : Equivalence (theory.Rel (α := α)) :=
  ⟨fun _ => .refl _, fun h => .symm h, fun h₁ h₂ => .trans h₁ h₂⟩

/-- Sound migration boundary. The reverse direction is deliberately not claimed. -/
theorem CertifiedTheory.to_original (theory : CertifiedTheory) {α : Type}
    [sort : NativeSort theory α] {a b : α} (h : theory.Rel a b) :
    EqMod theory.original a b := by
  rcases sort with ⟨s, hs⟩
  cases hs
  exact Indexed.NativeEq.to_legacy theory.signature theory.native theory.translation h

end Structural

open Lean Elab Command Meta

/-! Automatic registration supports many-sorted first-order datatypes with one
ACU operator. Generated proofs establish syntactic round trips and reuse existing
law witnesses. The unary-wrapper fragment retains its specialized metadata. -/

private partial def structuralList (e : Expr) : Term.TermElabM (Array Expr) := do
  let e ← whnf e
  if e.isAppOfArity ``List.nil 1 then return #[]
  if e.isAppOfArity ``List.cons 3 then
    return #[e.getAppArgs[1]!] ++ (← structuralList e.getAppArgs[2]!)
  throwError "expected a reducible structural declaration list"

private def structuralSingleton (theory : Expr) (field : Name) : Term.TermElabM Expr := do
  let xs ← structuralList (← mkAppM field #[theory])
  unless xs.size == 1 do
    throwError "certify_structural currently requires exactly one ACU operator"
  return xs[0]!

private def nativeFields (name : Name) : Term.TermElabM (Array Name) := do
  let info ← getConstInfoCtor name
  forallTelescopeReducing info.type fun xs _ => do
    xs.mapM fun x => do
      let t ← whnf (← inferType x)
      match t with
      | .const n [] => return n
      | _ => throwError "certify_structural requires first-order, unparameterized fields: {t}"

private def nativeSortInfo (name : Name) : Term.TermElabM InductiveVal := do
  let info ← getConstInfoInduct name
  unless info.numParams == 0 && info.numIndices == 0 && info.levelParams.isEmpty &&
      info.all.length == 1 do
    throwError "certify_structural requires an unparameterized, non-mutual datatype: {name}"
  return info

private structure NativeConstructor where
  name : Name
  fields : Array Name
  deriving Inhabited

private structure NativeSortDecl where
  name : Name
  constructors : Array NativeConstructor
  deriving Inhabited

private structure NativeRegistration where
  theory : Name
  root : Name
  sorts : Array NativeSortDecl
  bag : Name
  operation : Name
  unit : Name

-- Dependencies precede their users; direct recursion stays within one sort.
private partial def collectNativeSorts (name : Name) (path : Array Name := #[])
    (sorts : Array NativeSortDecl := #[]) : Term.TermElabM (Array NativeSortDecl) := do
  if sorts.any (·.name == name) then return sorts
  if path.contains name then
    throwError "certify_structural does not support mutually recursive sorts: {name}"
  let info ← nativeSortInfo name
  let constructors ← info.ctors.toArray.mapM fun ctor => do
    return { name := ctor, fields := ← nativeFields ctor : NativeConstructor }
  let mut sorts := sorts
  for ctor in constructors do
    for field in ctor.fields do
      if field != name then
        sorts ← collectNativeSorts field (path.push name) sorts
  return sorts.push { name, constructors }

private def inspectNativeRegistration (theory root : Ident) :
    Term.TermElabM NativeRegistration := do
  let b ← Term.elabTerm theory (some (mkConst ``Structural.Theory [Level.zero]))
  let some theoryName := b.constName?
    | throwError "certify_structural expects a named structural theory"
  let rootExpr ← Term.elabType root
  let some rootName := rootExpr.constName?
    | throwError "certify_structural expects a native state datatype"
  let _ ← synthInstance (← mkAppM ``framework.State #[rootExpr])
  let sorts ← collectNativeSorts rootName
  let idDecl ← structuralSingleton b ``Structural.Theory.identities
  let opExpr ← whnf (← mkAppM ``Structural.IdentityDeclaration.operation #[idDecl])
  let unitExpr ← whnf (← mkAppM ``Structural.IdentityDeclaration.element #[idDecl])
  let some operation := opExpr.constName?
    | throwError "ACU operation must be a native constructor"
  let some unit := unitExpr.constName?
    | throwError "ACU unit must be a native constructor"
  for (field, project) in [(``Structural.Theory.symbols, ``Structural.Symbol.operation),
      (``Structural.Theory.commutative, ``Structural.CommutativeDeclaration.operation),
      (``Structural.Theory.associative, ``Structural.AssociativeDeclaration.operation)] do
    let decl ← structuralSingleton b field
    unless ← isDefEq opExpr (← mkAppM project #[decl]) do
      throwError "certify_structural requires all laws to concern the same ACU constructor"
  let some bag := sorts.find? fun s => s.constructors.any (·.name == operation)
    | throwError "registered ACU operator is outside the native signature"
  unless (← nativeFields operation) == #[bag.name, bag.name] &&
      bag.constructors.any (·.name == unit) && (← nativeFields unit).isEmpty do
    throwError "expected an ACU binary constructor and a nullary unit in {bag.name}"
  return { theory := theoryName, root := rootName, sorts, bag := bag.name, operation, unit }

private def qualified (name : Name) : String := "_root_." ++ name.toString

private def emitRegistration (source : String) : CommandElabM Unit := do
  match Parser.runParserCategory (← getEnv) `command source with
  | .ok stx => elabCommand stx
  | .error err => throwError "generated registration syntax: {err}"

private def joinLines (lines : Array String) : String :=
  String.intercalate "\n" lines.toList

private def wrapperFragment? (spec : NativeRegistration) : Option (Name × Array Name) := Id.run do
  let some root := spec.sorts.find? (·.name == spec.root) | return none
  if root.constructors.size != 1 then return none
  let wrapper := root.constructors[0]!
  if wrapper.fields != #[spec.bag] then return none
  let some bag := spec.sorts.find? (·.name == spec.bag) | return none
  let atoms := bag.constructors.filter fun c => c.name != spec.operation && c.name != spec.unit
  if atoms.isEmpty || atoms.any (!·.fields.isEmpty) then return none
  return some (wrapper.name, atoms.map (·.name))

private def emitNativeRegistration (spec : NativeRegistration) : CommandElabM Unit := do
  let emit := emitRegistration
  let sortTag (name : Name) := s!"s{(spec.sorts.findIdx? (·.name == name)).get!}"
  let constructors := spec.sorts.flatMap fun s =>
    s.constructors.map fun c => (s.name, c)
  let symbol (name : Name) := s!"c{(constructors.findIdx? (·.2.name == name)).get!}"
  let fields (names : Array Name) :=
    "[" ++ String.intercalate ", " (names.toList.map fun n => "." ++ sortTag n) ++ "]"
  emit ("inductive Tag where\n" ++ joinLines (spec.sorts.mapIdx fun i _ => s!"  | s{i}") ++
    "\n  deriving DecidableEq")
  emit ("inductive Symbol : List Tag → Tag → Type where\n" ++
    joinLines (constructors.map fun (s, c) =>
      s!"  | {symbol c.name} : Symbol {fields c.fields} .{sortTag s}") ++
    "\n  deriving DecidableEq")
  emit s!"inductive Operator : Tag → Type where
  | acu : Operator .{sortTag spec.bag}
  deriving DecidableEq"
  emit s!"def Sig : Signature Tag where
  Symbol := Symbol
  ACUOp := Operator
  add := fun op => match op with | .acu => .{symbol spec.operation}
  zero := fun op => match op with | .acu => .{symbol spec.unit}"
  let argument (i : Nat) := "args" ++ String.join (List.replicate i ".2") ++ ".1"
  emit ("def nativeAlgebra : Algebra Sig where\n  Carrier := fun s => match s with\n" ++
    joinLines (spec.sorts.map fun s => s!"    | .{sortTag s.name} => {qualified s.name}") ++
    "\n  apply := fun f args => match f with\n" ++
    joinLines (constructors.map fun (_, c) =>
      s!"    | .{symbol c.name} => {qualified c.name}" ++
        String.join (c.fields.toList.mapIdx fun i _ => " " ++ argument i)))
  for i in [:spec.sorts.size] do
    let s := spec.sorts[i]!
    let cases := s.constructors.map fun c => Id.run do
      let mut args := ".nil"
      for j in (List.range c.fields.size).reverse do
        let index := (spec.sorts.findIdx? (·.name == c.fields[j]!)).get!
        args := s!"(.cons (quote{index} a{j}) {args})"
      let binders := String.join (c.fields.toList.mapIdx fun j _ => s!" a{j}")
      return s!"  | {qualified c.name}{binders} => .app .{symbol c.name} {args}"
    emit (s!"def quote{i} : {qualified s.name} → Tree Sig .s{i}\n" ++ joinLines cases)
    let dependencies := (s.constructors.flatMap (·.fields)).filter (· != s.name)
    let earlier := String.join ((dependencies.toList.eraseDups).map fun name =>
      s!", evalQuote{(spec.sorts.findIdx? (·.name == name)).get!}")
    emit s!"theorem evalQuote{i} (a : {qualified s.name}) : (quote{i} a).eval nativeAlgebra = a := by
  induction a <;> simp_all only [quote{i}, Tree.eval, Trees.eval{earlier}] <;> rfl"
  emit ("def quote : (s : Tag) → nativeAlgebra.Carrier s → Tree Sig s\n" ++
    joinLines (spec.sorts.mapIdx fun i _ => s!"  | .s{i}, a => quote{i} a"))
  let destructArgs (c : NativeConstructor) :=
    if c.fields.isEmpty then "cases args; rfl"
    else "rcases args with ⟨" ++
      String.intercalate ", " (c.fields.toList.mapIdx (fun i _ => s!"a{i}") ++ ["u"]) ++
      "⟩; cases u; rfl"
  emit ("def registration : Registration Sig where\n  toAlgebra := nativeAlgebra\n  quote := quote\n" ++
    "  eval_quote := by\n    intro s a\n    cases s with\n" ++
    joinLines (spec.sorts.mapIdx fun i _ => s!"    | s{i} => exact evalQuote{i} a") ++
    "\n  quote_apply := by\n    intro ss s f args\n    cases f with\n" ++
    joinLines (constructors.map fun (_, c) => s!"    | {symbol c.name} => {destructArgs c}"))
  emit ("def nativeHead {ss s} : Sig.Symbol ss s → Curried nativeAlgebra.Carrier ss s\n" ++
    joinLines (constructors.map fun (_, c) => s!"  | .{symbol c.name} => {qualified c.name}"))
  let t := qualified spec.theory
  emit (s!"def legacy : Legacy Sig {t} nativeAlgebra where
  head := nativeHead
  apply_head := by intro ss s f args; cases f <;> rfl
  registered := by
    intro ss s f
    cases f with\n" ++
    joinLines (constructors.map fun (_, c) => s!"    | {symbol c.name} =>
        exact (inferInstance : Structural.HasConstructor {t} {qualified c.name})") ++
    s!"\n  «comm» := by
    intro s op; cases op
    exact (inferInstance : Structural.HasComm {t} {qualified spec.operation})
  «assoc» := by
    intro s op; cases op
    exact (inferInstance : Structural.HasAssoc {t} {qualified spec.operation})
  unit := by
    intro s op; cases op
    exact (inferInstance : Structural.HasIdentity {t} {qualified spec.operation} {qualified spec.unit})")

private def emitWrapperRegistration (spec : NativeRegistration)
    (wrapper : Name) (atoms : Array Name) : CommandElabM Unit := do
  let emit := emitRegistration
  let join := joinLines
  let t := qualified spec.theory
  let r := qualified spec.root
  let bag := qualified spec.bag
  let wrapper := qualified wrapper
  let unit := qualified spec.unit
  let op := qualified spec.operation
  let atoms := atoms.map qualified
  emit ("inductive Atom where\n" ++ join (atoms.mapIdx fun i _ => s!"  | a{i}"))
  emit "abbrev Tag := Structural.Indexed.Wrapper.SortTag"
  emit "abbrev Sig := Structural.Indexed.Wrapper.signature Atom"
  emit (s!"def atomValue : Atom → {bag}\n" ++
    join (atoms.mapIdx fun i a => s!"  | .a{i} => {a}"))
  emit s!"def nativeAlgebra : Algebra Sig where
  Carrier := fun s => match s with | .bag => {bag} | .configuration => {r}
  apply := fun f args => match f, args with
    | .empty, _ => {unit}
    | .atom a, _ => atomValue a
    | .union, (a, b, _) => {op} a b
    | .wrap, (a, _) => {wrapper} a"
  emit (s!"def quoteBag : {bag} → Tree Sig .bag\n  | {unit} => .app .empty .nil\n" ++
    join (atoms.mapIdx fun i a => s!"  | {a} => .app (.atom .a{i}) .nil") ++
    s!"\n  | {op} a b => .app .union (.cons (quoteBag a) (.cons (quoteBag b) .nil))")
  emit s!"def quote : (s : Tag) → nativeAlgebra.Carrier s → Tree Sig s
  | .bag, a => quoteBag a
  | .configuration, {wrapper} a => .app .wrap (.cons (quoteBag a) .nil)"
  emit s!"def registration : Registration Sig where
  toAlgebra := nativeAlgebra
  quote := quote
  eval_quote := by
    intro s a
    cases s with
    | bag => induction a <;> simp_all [quote, quoteBag, Tree.eval, Trees.eval, nativeAlgebra, atomValue]
    | configuration =>
        cases a
        rename_i a
        have h : (quoteBag a).eval nativeAlgebra = a := by
          induction a <;> simp_all [quoteBag, Tree.eval, Trees.eval, nativeAlgebra, atomValue]
        change {wrapper} ((quoteBag a).eval nativeAlgebra) = {wrapper} a
        rw [h]
  quote_apply := by
    intro ss s f args
    cases f with
    | empty => cases args; rfl
    | atom a => cases args; cases a <;> rfl
    | union => rcases args with ⟨a, b, u⟩; cases u; rfl
    | wrap => rcases args with ⟨a, u⟩; cases u; rfl"
  emit ("def nativeHead {ss s} : Sig.Symbol ss s → Curried nativeAlgebra.Carrier ss s\n" ++ s!"
  | .empty => {unit}
  | .atom a => atomValue a
  | .union => {op}
  | .wrap => {wrapper}")
  emit (s!"def legacy : Legacy Sig {t} nativeAlgebra where
  head := nativeHead
  apply_head := by
    intro ss s f args
    cases f with
    | empty => rfl
    | atom a => cases a <;> rfl
    | union => rfl
    | wrap => rfl
  registered := by
    intro ss s f
    cases f with
    | atom a =>
        cases a with\n" ++ join (atoms.mapIdx fun i a =>
      s!"        | a{i} => exact (inferInstance : Structural.HasConstructor {t} {a})") ++ s!"
    | empty => exact (inferInstance : Structural.HasConstructor {t} {unit})
    | union => exact (inferInstance : Structural.HasConstructor {t} {op})
    | wrap => exact (inferInstance : Structural.HasConstructor {t} {wrapper})
  «comm» := by
    intro s op; cases op
    exact (inferInstance : Structural.HasComm {t} {op})
  «assoc» := by
    intro s op; cases op
    exact (inferInstance : Structural.HasAssoc {t} {op})
  unit := by
    intro s op; cases op
    exact (inferInstance : Structural.HasIdentity {t} {op} {unit})")
  emit ("def code : Atom → Nat\n" ++ join (atoms.mapIdx fun i _ => s!"  | .a{i} => {i}"))
  emit ("def read : Nat → Atom\n" ++ join (atoms.mapIdx fun i _ => s!"  | {i} => .a{i}") ++
    "\n  | _ => .a0")
  emit "theorem read_code (a : Atom) : read (code a) = a := by cases a <;> rfl"

syntax "certify_structural " ident " for " ident : command

elab_rules : command
  | `(certify_structural $theory:ident for $root:ident) => do
      let spec ← liftTermElabM <| inspectNativeRegistration theory root
      let generatedNamespace := theory.getId.toString
      unless spec.theory == (← getCurrNamespace) ++ theory.getId do
        throwError "place certify_structural beside the theory declaration and use its local name"
      let emit := emitRegistration
      let t := qualified spec.theory
      let wrapper? := wrapperFragment? spec
      emit s!"namespace {generatedNamespace}"
      emit "namespace Generated"
      emit "open Structural.Indexed"
      if let some (wrapper, atoms) := wrapper? then
        emitWrapperRegistration spec wrapper atoms
      else
        emitNativeRegistration spec
      emit "end Generated"
      emit s!"def certified : Structural.CertifiedTheory where
  Sorts := Generated.Tag
  signature := Generated.Sig
  native := Generated.registration
  original := {t}
  translation := Generated.legacy"
      let tags : Array (Name × String) := match wrapper? with
        | some _ => #[(spec.bag, "bag"), (spec.root, "configuration")]
        | none => spec.sorts.mapIdx fun i s => (s.name, s!"s{i}")
      for (name, tag) in tags do
        emit s!"instance : Structural.NativeSort certified {qualified name} := ⟨.{tag}, rfl⟩"
      emit s!"end {generatedNamespace}"

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
