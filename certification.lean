import conPanna.Structural
import examples.bakery
import conPanna.Maude

/-!
# Restart: automatic registration for a restricted native signature

The experiment was rolled back to commit 9be72d8 before adding this section.
The first new milestone is signature registration, not another equality relation.

Prototype UI:
  certification_signature BakeryTheory for Conf

It reads the existing Structural.Theory and checks State Conf. Later this can
be invoked from structural itself; no user-written list encodings or native
constructor proofs should be necessary for the supported fragment.

Supported: nonparameterized, nonindexed, first-order inductive sorts; free State
constructors; at most one structural operator per sort, with exactly ACU laws;
an ACU sort has only its binary operator, a nullary unit, and one nullary/unary
atom constructor. Different sorts may each have ACU operations, and atoms may
contain lower ACU sorts. Dependencies between DISTINCT sorts must be acyclic;
direct self-recursion such as Nat.succ and ProcSet.union is allowed.
Native Nat.add is a defined function, not a constructor, and is outside this path.

Generated evidence is kernel checked: finite sort identifiers, native constructor
types, constructor membership, RAW injectivity, registered ACU laws, and dependency
ordering. Raw injectivity is not injectivity modulo ACU. Registration performs no
Maude search and uses no problem-specific lemmas or admitted proofs.

Boundary: this data does NOT yet establish semantic constructor coverage,
disjointness, or EqMod inversion/completeness. Those belong to the generic
certification implementation, not extra user registration goals. In particular,
no constructor-name inspection is trusted as a proof of semantic faithfulness.
The original proof system and its five admissions remain below as the integration
target; the new data is not silently substituted for those missing proofs.
-/


namespace Certification.Registration

open Lean Meta Elab Command Term

private instance : Inhabited Maude.SortDecl := ⟨⟨Name.anonymous, #[]⟩⟩
private instance : Inhabited Maude.ConstructorDecl := ⟨⟨Name.anonymous, #[], Name.anonymous⟩⟩

/-- A constructor's curried native type, with explicit finite sort identifiers. -/
def Arrow {n : Nat} (carrier : Fin n → Type)
    (arguments : List (Fin n)) (result : Fin n) : Type :=
  match arguments with
  | [] => carrier result
  | first :: rest => carrier first → Arrow carrier rest result


def Arguments {n : Nat} (carrier : Fin n → Type) : List (Fin n) → Type
  | [] => PUnit
  | first :: rest => carrier first × Arguments carrier rest

def applyConstructor {n : Nat} {carrier : Fin n → Type} {result : Fin n}
    {arguments : List (Fin n)} :
    Arrow carrier arguments result → Arguments carrier arguments → carrier result :=
  match arguments with
  | [] => fun value _ => value
  | _ :: _ => fun f args => applyConstructor (f args.1) args.2

inductive ConstructorKind where
  | free | unit | atom | acu
  deriving Repr, BEq

structure NativeConstructor (B : Structural.Theory) (n : Nat)
    (carrier : Fin n → Type) where
  name : Name
  result : Fin n
  arguments : List (Fin n)
  kind : ConstructorKind
  implementation : Arrow carrier arguments result
  registered : Structural.HasConstructor B implementation
  injective : ∀ a b, applyConstructor implementation a = applyConstructor implementation b → a = b

structure ACUDeclaration (B : Structural.Theory) (n : Nat)
    (carrier : Fin n → Type) where
  sort : Fin n
  operation : carrier sort → carrier sort → carrier sort
  unit : carrier sort
  symbol : Structural.HasSymbol B operation
  associative : Structural.HasAssoc B operation
  commutative : Structural.HasComm B operation
  identity : Structural.HasIdentity B operation unit

/-- Checked native signature data, NOT an assertion of unification completeness. -/
structure Signature (B : Structural.Theory) (Root : Type) where
  sortCount : Nat
  names : Fin sortCount → Name
  carrier : Fin sortCount → Type
  root : Fin sortCount
  root_type : carrier root = Root
  constructors : Array (NativeConstructor B sortCount carrier)
  operators : Array (ACUDeclaration B sortCount carrier)
  dependency_order :
    constructors.toList.all (fun c => c.arguments.all (fun s => s.val ≤ c.result.val)) = true

private structure ACUInfo where
  sort : Name
  operation : Name
  unit : Name
  atom : Name

private def findCtor (sorts : Array Maude.SortDecl) (name : Name) :
    MetaM Maude.ConstructorDecl := do
  for sort in sorts do
    if let some c := sort.constructors.find? (·.leanName == name) then
      return c
  throwError "certification: {name} is not a constructor reachable from State"

private def checkACU (sorts : Array Maude.SortDecl) (root : Name)
    (operators : Array Maude.OperatorDecl) : MetaM (Array ACUInfo) := do
  let mut seen : Array Name := #[]
  for operator in operators do
    let c ← findCtor sorts operator.leanName
    if c.result == root then
      throwError "certification: State sort {root} must have free constructors"
    if seen.contains c.result then
      throwError "certification: multiple structural operators on sort {c.result} are unsupported"
    seen := seen.push c.result
  let mut result := #[]
  for operator in operators do
    let c ← findCtor sorts operator.leanName
    if c.result == root then
      throwError "certification: State sort {root} must have free constructors"
    unless c.fields == #[c.result, c.result] do
      throwError "certification: {c.leanName} must be a binary constructor on its own sort"
    let mut commutative := 0
    let mut associative := 0
    let mut units := #[]
    for law in operator.laws do
      match law with
      | .commutative => commutative := commutative + 1
      | .associative => associative := associative + 1
      | .identity unit => units := units.push unit
    unless commutative == 1 && associative == 1 && units.size == 1 do
      throwError "certification: {c.leanName} requires exactly comm, assoc, and one id declaration"
    let unit ← findCtor sorts units[0]!
    unless unit.result == c.result && unit.fields.isEmpty do
      throwError "certification: {c.leanName} needs a nullary unit of sort {c.result}"
    let some sort := sorts.find? (·.leanName == c.result)
      | throwError "certification: missing sort {c.result}"
    let atoms := sort.constructors.filter fun a =>
      a.leanName != c.leanName && a.leanName != unit.leanName
    unless atoms.size == 1 && atoms[0]!.fields.size ≤ 1 do
      throwError "certification: {c.result} needs exactly three constructors: unit, atom, ACU"
    let atom := atoms[0]!
    if atom.fields.contains c.result then
      throwError "certification: atom constructor {atom.leanName} cannot contain its own ACU sort"
    result := result.push {
      sort := c.result
      operation := c.leanName
      unit := unit.leanName
      atom := atom.leanName
    }
  return result


private partial def listEntries (expression : Expr) : MetaM (Array Expr) := do
  let value ← withTransparency .all <| whnf expression
  if value.isAppOfArity ``List.nil 1 then return #[]
  unless value.isAppOfArity ``List.cons 3 do
    throwError "certification: expected a concrete list of structural declarations"
  let args := value.getAppArgs
  return #[args[1]!] ++ (← listEntries args[2]!)

private def declarationName (projection : Name) (entry : Expr) : MetaM Name := do
  let value ← withTransparency .all <| whnf (← mkAppM projection #[entry])
  let some name := value.constName?
    | throwError "certification: structural declarations must name native constructors"
  return name

/-- Check the law tables actually consumed by EqMod, not just display metadata. -/
private def checkLawTables (theory : Expr) (acus : Array ACUInfo) : MetaM Unit := do
  let expected := acus.map (·.operation)
  for (table, projection) in
      [(``Structural.Theory.commutative, ``Structural.CommutativeDeclaration.operation),
       (``Structural.Theory.associative, ``Structural.AssociativeDeclaration.operation)] do
    let entries ← listEntries (← mkAppM table #[theory])
    let actual ← entries.mapM (declarationName projection)
    unless actual.size == expected.size && actual.all expected.contains do
      throwError "certification: the structural law tables disagree with the registered ACU symbols"
  let entries ← listEntries (← mkAppM ``Structural.Theory.identities #[theory])
  let mut actual := #[]
  for entry in entries do
    actual := actual.push
      (← declarationName ``Structural.IdentityDeclaration.operation entry,
       ← declarationName ``Structural.IdentityDeclaration.element entry)
  let expected := acus.map (fun a => (a.operation, a.unit))
  unless actual.size == expected.size && actual.all expected.contains do
    throwError "certification: the identity table disagrees with the registered ACU symbols"

/-- Sort dependencies are topologically ordered; direct self recursion is retained. -/
private def orderSorts (sorts : Array Maude.SortDecl) : MetaM (Array Maude.SortDecl) := do
  let mut pending := sorts
  let mut ordered := #[]
  for _ in [:sorts.size] do
    let mut rest := #[]
    for sort in pending do
      let ready := sort.constructors.all fun c => c.fields.all fun field =>
        field == sort.leanName || ordered.any (fun s : Maude.SortDecl => s.leanName == field)
      if ready then ordered := ordered.push sort else rest := rest.push sort
    if rest.isEmpty then return ordered
    if rest.size == pending.size then
      let names := rest.toList.map (·.leanName.toString)
      throwError "certification: cyclic dependencies between sorts: {String.intercalate ", " names}"
    pending := rest
  throwError "certification: could not order sort dependencies"

private def sortIndex (sorts : Array Maude.SortDecl) (name : Name) : CommandElabM Nat := do
  for i in [:sorts.size] do
    if sorts[i]!.leanName == name then return i
  throwError "certification: missing sort {name}"

private def finTerm (i : Nat) : CommandElabM (TSyntax `term) := do
  let n := Syntax.mkNumLit (toString i)
  `(term| ⟨$n, by decide⟩)

/-- This command does no Maude search: it only reuses native signature inspection. -/
elab "certification_signature " theory:ident " for " root:term : command => do
  let (sorts, acus, rootName, theoryName) ← liftTermElabM do
    let rootExpr ← elabType root
    let rootExpr ← whnf rootExpr
    let some rootName := rootExpr.constName?
      | throwError "certification: the State root must be a named inductive type"
    let _ ← synthInstance (← mkAppM ``framework.State #[rootExpr])
    let theoryExpr ← elabTerm theory (some (mkConst ``Structural.Theory [Level.zero]))
    let sorts ← Maude.collectSignature rootExpr
    let operators ← Maude.inspectTheory theoryExpr
    let acus ← checkACU sorts rootName operators
    checkLawTables theoryExpr acus
    let some theoryName := theoryExpr.constName?
      | throwError "certification: expected a named Structural.Theory"
    return (← orderSorts sorts, acus, rootName, theoryName)
  let count := Syntax.mkNumLit (toString sorts.size)
  let rootIndex ← sortIndex sorts rootName
  let rootTag ← finTerm rootIndex
  -- Numeric tags are distinct even though Lean types are not a separated sort syntax.
  let mut carrierBody ← `(term| PUnit)
  let mut nameBody ← `(term| Name.anonymous)
  for i in (List.range sorts.size).reverse do
    let num := Syntax.mkNumLit (toString i)
    let native := mkIdent sorts[i]!.leanName
    let nameValue : TSyntax `term := quote sorts[i]!.leanName
    carrierBody ← `(term| if i.val = $num then $native else $carrierBody)
    nameBody ← `(term| if i.val = $num then $nameValue else $nameBody)
  let carrier ← `(term| fun (i : Fin $count) => $carrierBody)
  let names ← `(term| fun (i : Fin $count) => $nameBody)
  let mut constructors : Array (TSyntax `term) := #[]
  for sort in sorts do
    let resultTag ← finTerm (← sortIndex sorts sort.leanName)
    for c in sort.constructors do
      let mut args : Array (TSyntax `term) := #[]
      for field in c.fields do args := args.push (← finTerm (← sortIndex sorts field))
      let native := mkIdent c.leanName
      let nameValue : TSyntax `term := quote c.leanName
      let kind ←
        if acus.any (·.operation == c.leanName) then `(term| ConstructorKind.acu)
        else if acus.any (·.unit == c.leanName) then `(term| ConstructorKind.unit)
        else if acus.any (·.atom == c.leanName) then `(term| ConstructorKind.atom)
        else `(term| ConstructorKind.free)
      constructors := constructors.push (← `(term| {
        name := $nameValue
        result := $resultTag
        arguments := [$args,*]
        kind := $kind
        implementation := $native
        registered := (show Structural.HasConstructor $theory $native from inferInstance)
        injective := by
          intro a b h
          simp_all [applyConstructor, Arguments, Prod.ext_iff]
          all_goals exact @Subsingleton.elim PUnit inferInstance _ _
      }))
  let mut operators : Array (TSyntax `term) := #[]
  for acu in acus do
    let tag ← finTerm (← sortIndex sorts acu.sort)
    let op := mkIdent acu.operation
    let unit := mkIdent acu.unit
    operators := operators.push (← `(term| {
      sort := $tag
      operation := $op
      unit := $unit
      symbol := (show Structural.HasSymbol $theory $op from inferInstance)
      associative := (show Structural.HasAssoc $theory $op from inferInstance)
      commutative := (show Structural.HasComm $theory $op from inferInstance)
      identity := (show Structural.HasIdentity $theory $op $unit from inferInstance)
    }))
  let name := mkIdent (Name.mkStr1 "_root_" ++ theoryName ++ `certificationSignature)
  elabCommand (← `(command|
    def $name : Signature $theory $root where
      sortCount := $count
      names := $names
      carrier := $carrier
      root := $rootTag
      root_type := by rfl
      constructors := #[$constructors,*]
      operators := #[$operators,*]
      dependency_order := by decide))

end Certification.Registration


/-!
# A model-independent proof system for unification certification

Part 1: semantic interfaces, inference rules, and adequacy, parameterized by
the user's types and Structural.Theory. No Bakery declarations occur here.
Part 2: once-per-model registrations for the actual imported Bakery definitions.
Part 3: inline certification proofs using Bakery's Conf.

The proof system uses Lean and Structural.EqMod; no Mathlib facts or tactics.
The example import brings Bakery's existing dependencies transitively.
Generic completeness proofs and two registration proofs remain admitted.

Inspiration: ACU-certification.pdf, Figure 1 and Lemma 5.5: transformations of
disjunctions of conjunctions preserve the entire solution set. Our adequacy
theorem composes such transformations. The paper's Theorem 5.9 assumes a
complete unsorted unifier; the ACU rules here address that additional layer.
-/

namespace Certification

open Structural
universe u

/-! ## Part 1. General interfaces and proof system -/

/--
A faithful bag interpretation of one user-defined ACU sort.
This is model-wide evidence, not the answer to a unification problem.

Structural registration supplies the four law witnesses. The interpretation
additionally justifies freeness: EqMod is EXACTLY permutation of encoded atoms,
and every finite bag is representable. Cancellation and complete splitting
cannot be inferred from ACU laws alone in an arbitrary algebra.

Atoms may themselves encode other structural theories (for example by using
quotient-valued atoms). No inductive term grammar is fixed by this interface.
-/
structure ACUView (B : Structural.Theory.{u}) {α : Type u}
    (op : α → α → α) (zero : α) where
  Atom : Type u
  atom : Atom → α
  encode : α → List Atom
  decode : List Atom → α
  encode_zero : encode zero = []
  encode_op : ∀ a b, encode (op a b) = encode a ++ encode b
  encode_atom : ∀ a, encode (atom a) = [a]
  encode_decode : ∀ xs, encode (decode xs) = xs
  reflects : ∀ a b, (a =[B] b) ↔ (encode a).Perm (encode b)
  symbol : HasSymbol B op
  associative : HasAssoc B op
  commutative : HasComm B op
  identity : HasIdentity B op zero

/-- Heterogeneous fields of a constructor, without an arity limit. -/
inductive Fields : Type (u + 1) where
  | unit
  | field (α : Type u)
  | product (left right : Fields)

def Fields.Values : Fields.{u} → Type u
  | .unit => PUnit
  | .field α => α
  | .product left right => left.Values × right.Values

/-- Componentwise EqMod, using the appropriate type for every field. -/
def Fields.Equal (B : Structural.Theory.{u}) :
    (fields : Fields.{u}) → fields.Values → fields.Values → Prop
  | .unit, _, _ => True
  | .field _, a, b => a =[B] b
  | .product left right, a, b =>
      left.Equal B a.1 b.1 ∧ right.Equal B a.2 b.2

/--
Faithful decomposition of a user-defined free constructor.
The signature registration must justify this for all arguments, once.
It is not assumed for a symbol carrying C, AC, or ACU equations.
-/
structure ConstructorView (B : Structural.Theory.{u})
    (fields : Fields.{u}) (α : Type u) where
  build : fields.Values → α
  reflects : ∀ a b, (build a =[B] build b) ↔ fields.Equal B a b

/-- General ACU refinement: four fresh pieces give one complete unifier. -/
theorem acu_split_iff {B : Structural.Theory.{u}} {α : Type u}
    {op : α → α → α} {zero : α}
    (view : ACUView B op zero) (a b c d : α) :
    op a b =[B] op c d ↔
      ∃ p q r s : α,
        a =[B] op p q ∧ b =[B] op r s ∧
        c =[B] op p r ∧ d =[B] op q s := by
  letI := view.symbol
  letI := view.associative
  letI := view.commutative
  constructor
  · -- General metatheorem TODO: partition equal bag sums into four pieces;
    -- use view.decode to realize them and view.reflects to return to EqMod.
    sorry
  · intro h
    obtain ⟨p, q, r, s, ha, hb, hc, hd⟩ := h
    have exchange :
        op (op p q) (op r s) =[B] op (op p r) (op q s) :=
      .trans (.assoc op p q (op r s)) <|
      .trans (.congr op (.ofEq rfl) (.symm (.assoc op q r s))) <|
      .trans (.congr op (.ofEq rfl)
        (.congr op (.comm op q r) (.ofEq rfl))) <|
      .trans (.congr op (.ofEq rfl) (.assoc op r q s))
        (.symm (.assoc op p r (op q s)))
    exact .trans (.congr op ha hb) <|
      .trans exchange (.symm (.congr op hc hd))

theorem acu_cancel_iff {B : Structural.Theory.{u}} {α : Type u}
    {op : α → α → α} {zero : α}
    (view : ACUView B op zero) (a b common : α) :
    op a common =[B] op b common ↔ a =[B] b := by
  letI := view.symbol
  constructor
  · -- General metatheorem TODO: cancel the common encoded bag.
    sorry
  · intro h
    exact .congr op h (.ofEq rfl)

theorem acu_atom_iff {B : Structural.Theory.{u}} {α : Type u}
    {op : α → α → α} {zero : α}
    (view : ACUView B op zero) (a b : α) (k : view.Atom) :
    op a b =[B] view.atom k ↔
      (a =[B] zero ∧ b =[B] view.atom k) ∨
      (a =[B] view.atom k ∧ b =[B] zero) := by
  letI := view.symbol
  letI := view.identity
  constructor
  · -- General metatheorem TODO: partition the singleton encoded bag.
    sorry
  · intro h
    cases h with
    | inl h =>
        exact .trans (.congr op h.1 h.2) (.identityLeft op zero (view.atom k))
    | inr h =>
        exact .trans (.congr op h.1 h.2) (.identityRight op zero (view.atom k))

/-!
### Inference rules

Write P ==>[B] Q for Derives B P Q, and a ~ b for a =[B] b.
In the algebra rules, +, 0, and atom come from an ACUView; they are not
constructors of a fixed term type. EΓ is Fields.Equal for a field layout Γ.

                      P ==> Q    Q ==> R
  -------- [Done]     -------------------- [Compose]
  P ==> P                  P ==> R

  P ==> P'    Q ==> Q'       P ==> P'    Q ==> Q'
  --------------------      --------------------
  P ∧ Q ==> P' ∧ Q' [And]    P ∨ Q ==> P' ∨ Q' [Or]

         for every u, P(u) ==> Q(u)
  -------------------------------------- [Exists]
       (∃ u, P(u)) ==> (∃ u, Q(u))

  a ~ a'    b ~ b'    (a' ~ b') ==> Q
  ---------------------------------- [Rewrite]
                (a ~ b) ==> Q

  ----------------------------------------------------- [ACU split]
  (a+b ~ c+d) ==> ∃ p q r s,
    a ~ p+q ∧ b ~ r+s ∧ c ~ p+r ∧ d ~ q+s

  ----------------------------- [Cancel]
  (a+c ~ b+c) ==> (a ~ b)

  ----------------------------------------------------- [Atom]
  (a+b ~ atom k) ==> (a ~ 0 ∧ b ~ atom k) ∨
                    (a ~ atom k ∧ b ~ 0)

  --------------------------------------------- [Decompose]
  build(args) ~ build(args') ==> EΓ(args,args')

  ----------------------------------------------------- [Distribute]
  (P∨Q) ∧ (R∨S) ==> (P∧R) ∨ (P∧S) ∨ (Q∧R) ∨ (Q∧S)

  ---------------- [Reflexive]     ---------------- [TrueLeft]
  (a ~ a) ==> True                True ∧ P ==> P

Read upwards to construct a derivation. Algebra/decomposition rules require
model-wide views; their semantic assumptions are not added as per-problem goals.

### From the proof system to the semantic certificate

For each assignment to the original variables, P is the equation and Q is
the proposed disjunction of substitution factorizations:
  (∃ fresh variables, x₁ ~ σ₁ ∧ ... ∧ xₙ ~ σₙ) ∨ ...

P and Q are ordinary Lean propositions using the existing EqMod semantics.
Derives.adequate interprets the derivation and produces P ↔ Q:
  P → Q is completeness; Q → P is soundness.
The top-level examples apply this theorem once, then use only general rules.
Proof search and completeness of this collection of proof rules are not claimed.
-/

inductive Derives (B : Structural.Theory.{u}) : Prop → Prop → Prop where
  | done {P : Prop} : Derives B P P
  | trans {P Q R : Prop} :
      Derives B P Q → Derives B Q R → Derives B P R
  | conj {P P' Q Q' : Prop} :
      Derives B P P' → Derives B Q Q' → Derives B (P ∧ Q) (P' ∧ Q')
  | disj {P P' Q Q' : Prop} :
      Derives B P P' → Derives B Q Q' → Derives B (P ∨ Q) (P' ∨ Q')
  | existsCongr {α : Type u} {P Q : α → Prop} :
      (∀ x, Derives B (P x) (Q x)) →
      Derives B (∃ x, P x) (∃ x, Q x)
  | distribute {P Q R S : Prop} :
      Derives B ((P ∨ Q) ∧ (R ∨ S))
        ((P ∧ R) ∨ (P ∧ S) ∨ (Q ∧ R) ∨ (Q ∧ S))
  | eqRefl {α : Type u} (a : α) : Derives B (a =[B] a) True
  | trueLeft {P : Prop} : Derives B (True ∧ P) P
  | rewrite {α : Type u} {a a' b b' : α} {Q : Prop} :
      a =[B] a' → b =[B] b' →
      Derives B (a' =[B] b') Q → Derives B (a =[B] b) Q
  | acu_split {α : Type u} {op : α → α → α} {zero : α}
      (view : ACUView B op zero) (a b c d : α) :
      Derives B (op a b =[B] op c d)
        (∃ p q r s : α,
          a =[B] op p q ∧ b =[B] op r s ∧
          c =[B] op p r ∧ d =[B] op q s)
  | acu_cancel {α : Type u} {op : α → α → α} {zero : α}
      (view : ACUView B op zero) (a b common : α) :
      Derives B (op a common =[B] op b common) (a =[B] b)
  | acu_atom {α : Type u} {op : α → α → α} {zero : α}
      (view : ACUView B op zero) (a b : α) (k : view.Atom) :
      Derives B (op a b =[B] view.atom k)
        ((a =[B] zero ∧ b =[B] view.atom k) ∨
          (a =[B] view.atom k ∧ b =[B] zero))
  | decompose {fields : Fields.{u}} {α : Type u}
      (view : ConstructorView B fields α) (a b : fields.Values) :
      Derives B (view.build a =[B] view.build b) (fields.Equal B a b)

/-- Model-independent interpretation of every derivation as an exact equivalence. -/
theorem Derives.adequate {B : Structural.Theory.{u}} {P Q : Prop}
    (proof : Derives B P Q) : P ↔ Q := by
  induction proof with
  | done => exact Iff.rfl
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | conj _ _ ih₁ ih₂ =>
      constructor
      · intro h
        exact ⟨ih₁.mp h.1, ih₂.mp h.2⟩
      · intro h
        exact ⟨ih₁.mpr h.1, ih₂.mpr h.2⟩
  | disj _ _ ih₁ ih₂ =>
      constructor
      · intro h
        cases h with
        | inl h => exact Or.inl (ih₁.mp h)
        | inr h => exact Or.inr (ih₂.mp h)
      · intro h
        cases h with
        | inl h => exact Or.inl (ih₁.mpr h)
        | inr h => exact Or.inr (ih₂.mpr h)
  | existsCongr _ ih =>
      constructor
      · intro h
        obtain ⟨x, hx⟩ := h
        exact ⟨x, (ih x).mp hx⟩
      · intro h
        obtain ⟨x, hx⟩ := h
        exact ⟨x, (ih x).mpr hx⟩
  | distribute =>
      constructor
      · intro h
        cases h.1 with
        | inl hp =>
            cases h.2 with
            | inl hr => exact Or.inl ⟨hp, hr⟩
            | inr hs => exact Or.inr (Or.inl ⟨hp, hs⟩)
        | inr hq =>
            cases h.2 with
            | inl hr => exact Or.inr (Or.inr (Or.inl ⟨hq, hr⟩))
            | inr hs => exact Or.inr (Or.inr (Or.inr ⟨hq, hs⟩))
      · intro h
        cases h with
        | inl h => exact ⟨Or.inl h.1, Or.inl h.2⟩
        | inr h =>
            cases h with
            | inl h => exact ⟨Or.inl h.1, Or.inr h.2⟩
            | inr h =>
                cases h with
                | inl h => exact ⟨Or.inr h.1, Or.inl h.2⟩
                | inr h => exact ⟨Or.inr h.1, Or.inr h.2⟩
  | eqRefl a => exact ⟨fun _ => True.intro, fun _ => EqMod.ofEq rfl⟩
  | trueLeft => exact ⟨fun h => h.2, fun h => ⟨True.intro, h⟩⟩
  | rewrite left right _ ih =>
      constructor
      · intro h
        exact ih.mp (.trans left.symm (.trans h right))
      · intro h
        exact .trans left (.trans (ih.mpr h) right.symm)
  | acu_split view a b c d => exact acu_split_iff view a b c d
  | acu_cancel view a b common => exact acu_cancel_iff view a b common
  | acu_atom view a b k => exact acu_atom_iff view a b k
  | decompose view a b => exact view.reflects a b

theorem Derives.complete {B : Structural.Theory.{u}} {P Q : Prop}
    (proof : Derives B P Q) : P → Q := proof.adequate.mp

theorem Derives.sound {B : Structural.Theory.{u}} {P Q : Prop}
    (proof : Derives B P Q) : Q → P := proof.adequate.mpr

/-! ## Part 2. Bakery registration, reusable for every certification

Only from this point does the file mention Bakery types. These declarations
describe the model, never a particular unification problem.
The new command generates checked native signature data without proof obligations.
The legacy ACUView/ConstructorView registrations below remain the semantic
integration target: their reflection holes are NOT filled by raw signature checks.
-/

-- Temporary separate command; intended to be automatic inside structural later.
certification_signature BakeryTheory for Conf

namespace BakeryRegistration

def elements : ProcSet → List Mode
  | .empty => []
  | .singleton mode => [mode]
  | .union left right => elements left ++ elements right

def rebuild : List Mode → ProcSet
  | [] => .empty
  | mode :: rest => .union (.singleton mode) (rebuild rest)

def procs : ACUView BakeryTheory ProcSet.union ProcSet.empty where
  Atom := Mode
  atom := ProcSet.singleton
  encode := elements
  decode := rebuild
  encode_zero := rfl
  encode_op := fun _ _ => rfl
  encode_atom := fun _ => rfl
  encode_decode := by
    intro modes
    induction modes with
    | nil => rfl
    | cons mode rest ih =>
        change [mode] ++ elements (rebuild rest) = mode :: rest
        rw [ih]
        rfl
  reflects := by
    -- MODEL-WIDE TODO: EqMod on ProcSet is exactly permutation of modes.
    -- This is required for every use of procs, not separately per certificate.
    sorry
  symbol := inferInstance
  associative := inferInstance
  commutative := inferInstance
  identity := inferInstance

def confFields : Fields :=
  .product (.field Nat) (.product (.field Nat) (.field ProcSet))

def conf : ConstructorView BakeryTheory confFields Conf where
  build := fun args => Conf.mk args.1 args.2.1 args.2.2
  reflects := by
    intro a b
    constructor
    · -- MODEL-WIDE TODO: invert EqMod through the free Conf.mk constructor.
      sorry
    · intro h
      exact EqMod.constructor
        (ConstructorCongruence.app
          (ConstructorCongruence.app
            (ConstructorCongruence.app (ConstructorCongruence.head Conf.mk) h.1)
            h.2.1)
          h.2.2)

end BakeryRegistration

/-! ## Part 3. One atomic Bakery problem, two unifiers

Uses the actual Conf, ProcSet, and BakeryTheory imported from examples/bakery.
The counters are shared rigid parameters. The unification variables are X, Y.

Problem:
  Conf(next, serving, (X union empty) union Y)
    =[BakeryTheory] Conf(next, serving, singleton idle)

Proposed substitutions:
  σ₁: X ↦ empty,          Y ↦ singleton idle
  σ₂: X ↦ singleton idle, Y ↦ empty

No fresh variables are needed. The disjunction below is precisely the
factorization formula for these two substitutions, modulo BakeryTheory.

The semantic certificate is one iff: completeness forwards, soundness backwards.
The single proof uses only general rules and the model-wide registration.
It inherits the explicitly admitted generic and registration metatheory.
-/

example (next serving : Nat) :
    ∀ X Y : ProcSet,
      Conf.mk next serving (ProcSet.union (ProcSet.union X ProcSet.empty) Y)
        =[BakeryTheory] Conf.mk next serving (ProcSet.singleton Mode.idle) ↔
      (X =[BakeryTheory] ProcSet.empty ∧
        Y =[BakeryTheory] ProcSet.singleton Mode.idle) ∨
      (X =[BakeryTheory] ProcSet.singleton Mode.idle ∧
        Y =[BakeryTheory] ProcSet.empty) := by
  intro X Y
  -- Interpret a derivation as the requested semantic soundness/completeness iff.
  apply Derives.adequate
  -- The free constructor rule generates three heterogeneous equations:
  -- next ~ next, serving ~ serving, and an ACU equation over ProcSet.
  refine Derives.trans (Derives.decompose BakeryRegistration.conf
    (next, serving, ProcSet.union (ProcSet.union X ProcSet.empty) Y)
    (next, serving, ProcSet.singleton Mode.idle)) ?_
  -- Discharge the rigid counter equations by general reflexivity rules.
  refine Derives.trans
    (Derives.conj (Derives.eqRefl next)
      (Derives.conj (Derives.eqRefl serving) Derives.done)) ?_
  refine Derives.trans Derives.trueLeft ?_
  refine Derives.trans Derives.trueLeft ?_
  -- Normalize the unit, leaving X union Y ~ singleton idle.
  apply Derives.rewrite
    (EqMod.congr ProcSet.union
      (EqMod.identityRight ProcSet.union ProcSet.empty X) (EqMod.ofEq rfl))
    (EqMod.ofEq rfl)
  -- General Atom rule yields exactly the two proposed alternatives.
  exact Derives.acu_atom BakeryRegistration.procs X Y Mode.idle

end Certification

/-! ## Registration regression tests

The following is not a second certification framework. It tests automatic
registration independently of the legacy semantic certificate above.
-/

namespace Certification.RegistrationTests

inductive Count where
  | zero | one
  | add : Count → Count → Count
inductive Mode where
  | idle
  | wait : Count → Mode
inductive Collection where
  | empty
  | singleton : Mode → Collection
  | union : Collection → Collection → Collection
structure Config where
  count : Count
  collection : Collection
instance : framework.State Config := ⟨⟩

open scoped Structural in
structural NestedTheory where
  assoc Count.add
  comm Count.add
  id Count.add Count.zero
  assoc Collection.union
  comm Collection.union
  id Collection.union Collection.empty

certification_signature NestedTheory for Config

example : NestedTheory.certificationSignature.sortCount = 4 := rfl
example : NestedTheory.certificationSignature.operators.size = 2 := rfl
example : NestedTheory.certificationSignature.names ⟨0, by decide⟩ = ``Count := rfl
example : NestedTheory.certificationSignature.names ⟨2, by decide⟩ = ``Collection := rfl

end Certification.RegistrationTests

namespace Certification.RegistrationTests.ExtraConstructor
inductive Bag where
  | empty
  | atom : Nat → Bag
  | union : Bag → Bag → Bag
  | locked : Bag → Bag
structure Config where
  bag : Bag
instance : framework.State Config := ⟨⟩
open scoped Structural in
structural ExtraTheory where
  assoc Bag.union
  comm Bag.union
  id Bag.union Bag.empty

/-- error: certification: Certification.RegistrationTests.ExtraConstructor.Bag needs exactly three constructors: unit, atom, ACU -/
#guard_msgs in
certification_signature ExtraTheory for Config
end Certification.RegistrationTests.ExtraConstructor

namespace Certification.RegistrationTests.Cyclic
mutual
  inductive Mode where
    | idle
    | group : Bag → Mode
  inductive Bag where
    | empty
    | atom : Mode → Bag
    | union : Bag → Bag → Bag
end
structure Config where
  bag : Bag
instance : framework.State Config := ⟨⟩
open scoped Structural in
structural CyclicTheory where
  assoc Bag.union
  comm Bag.union
  id Bag.union Bag.empty

/-- error: certification: cyclic dependencies between sorts: Certification.RegistrationTests.Cyclic.Config, Certification.RegistrationTests.Cyclic.Bag, Certification.RegistrationTests.Cyclic.Mode -/
#guard_msgs in
certification_signature CyclicTheory for Config
end Certification.RegistrationTests.Cyclic

namespace Certification.RegistrationTests

instance : framework.State Count := ⟨⟩

/-- error: certification: State sort Certification.RegistrationTests.Count must have free constructors -/
#guard_msgs in
certification_signature NestedTheory for Count

def InconsistentTheory : Structural.Theory :=
  { _root_.BakeryTheory with associative := [] }

/-- error: certification: the structural law tables disagree with the registered ACU symbols -/
#guard_msgs in
certification_signature InconsistentTheory for _root_.Conf

end Certification.RegistrationTests
