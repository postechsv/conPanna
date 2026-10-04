import examples.bakery

/-!
# Direct certification prototype

The proof system below uses Structural.Indexed.Eq / NativeEq, exactly the
relation selected by `=[T.certified]`. It does not import certification2, define
a second ACU term algebra, or ask for a BakeryEncoding/Bridge.

Reading order: generic metatheorems; automatic signature classification;
certificate data/checking; ordinary Bakery examples at the bottom.

First supported rule: split X+Y = an atomic constructor term. Its two unifiers
are retained together. Constructor payloads may contain variables of other
sorts. Profile generation, native reflection and replay are automatic: the user
proof is `by certify_direct profile`. The rule is selected locally in this first
prototype; Maude/native-unifier-guided certificate search is not implemented here.
General cancellation, refinement/Mutate and free-constructor inversion are next.
-/

namespace DirectCertification

open Structural.Indexed

variable {Sorts : Type} {sig : Signature Sorts}

/-! ## General semantic metatheorems

Classifying constructor heads is syntactic metadata. All semantic facts are
proved HERE, once for any signature with at most one ACU operation per sort.
The declaration generator below supplies this metadata with cases/rfl.
-/

inductive HeadView (sig : Signature Sorts) : {ss : List Sorts} → {s : Sorts} →
    sig.Symbol ss s → Type where
  | zero {s} (op : sig.ACUOp s) : HeadView sig (sig.zero op)
  | add {s} (op : sig.ACUOp s) : HeadView sig (sig.add op)
  | atom {ss s} (f : sig.Symbol ss s) : HeadView sig f

structure Profile (sig : Signature Sorts) where
  view : ∀ {ss s} (f : sig.Symbol ss s), HeadView sig f
  view_zero : ∀ {s} (op : sig.ACUOp s), view (sig.zero op) = .zero op
  view_add : ∀ {s} (op : sig.ACUOp s), view (sig.add op) = .add op
  unique : ∀ {s} (a b : sig.ACUOp s), a = b

variable (profile : Profile sig)

/-- A semantic invariant of the actual structural relation. Non-ACU heads have
mass one, regardless of payloads. No input/output certificate is translated to
this measure: it is only used in the proof of the generic splitting rule. -/
def measure : Algebra sig where
  Carrier := fun _ => Nat
  apply := fun f args => match profile.view f with
    | .zero _ => 0
    | .add _ => args.1 + args.2.1
    | .atom _ => 1

def mass {s} (a : Tree sig s) : Nat := a.eval (measure profile)

def measureModel : Model sig (measure profile) where
  Rel := fun _ => _root_.Eq
  refl := fun _ _ => rfl
  symm := fun _ {_ _} h => h.symm
  trans := fun _ {_ _ _} h k => h.trans k
  congr := by
    intro ss s f a b h
    cases hv : profile.view f with
    | zero => simp [measure, hv]
    | add => simpa [measure, hv] using congrArg₂ Nat.add h.1 h.2.1
    | atom => simp [measure, hv]
  «comm» := by
    intro s op a b
    simp [measure, profile.view_add, Nat.add_comm]
  «assoc» := by
    intro s op a b c
    simp [measure, profile.view_add, Nat.add_assoc]
  unit := by
    intro s op a
    simp [measure, profile.view_add, profile.view_zero]

theorem mass_congr {s} {a b : Tree sig s} (h : Structural.Indexed.Eq sig a b) :
    mass profile a = mass profile b :=
  Structural.Indexed.Eq.sound sig (measureModel profile) h

@[simp] theorem mass_zero {s} (op : sig.ACUOp s) :
    mass profile (zero sig op) = 0 := by
  simp [mass, zero, Tree.eval, measure, profile.view_zero]

@[simp] theorem mass_add {s} (op : sig.ACUOp s) (a b : Tree sig s) :
    mass profile (add sig op a b) = mass profile a + mass profile b := by
  simp [mass, add, Tree.eval, Trees.eval, measure, profile.view_add]

def AllTrees (P : ∀ s, Tree sig s → Prop) :
    {ss : List Sorts} → Trees sig ss → Prop
  | _, .nil => True
  | _, .cons a rest => P _ a ∧ AllTrees P rest

/-- Zero mass forces structural equality with the registered unit. This
freeness fact is derived from the datatype/signature, not a user hypothesis. -/
theorem zero_of_mass {s} (a : Tree sig s) (op : sig.ACUOp s)
    (h : mass profile a = 0) : Structural.Indexed.Eq sig a (zero sig op) := by
  let P := fun s (a : Tree sig s) => ∀ op : sig.ACUOp s,
    mass profile a = 0 → Structural.Indexed.Eq sig a (zero sig op)
  have all : P s a := by
    refine Tree.rec (motive_1 := fun {s} a => P s a)
      (motive_2 := fun {ss} args => AllTrees P args) ?_ ?_ ?_ a
    · intro ss s f args ih target hm
      cases hv : profile.view f with
      | zero other =>
          cases args
          have same := profile.unique other target
          cases same
          exact .refl _
      | add other =>
          cases args with
          | cons left rest =>
            cases rest with
            | cons right tail =>
              cases tail
              change mass profile (add sig other left right) = 0 at hm
              rw [mass_add] at hm
              have hl : mass profile left = 0 := by omega
              have hr : mass profile right = 0 := by omega
              have same := profile.unique other target
              cases same
              exact .trans
                (.congr (sig.add target) (.cons (ih.1 target hl) (.cons (ih.2.1 target hr) .nil)))
                (.unit target (zero sig target))
      | atom f =>
          simp [mass, Tree.eval, measure, hv] at hm
    · trivial
    · intro s ss first rest hfirst hrest
      exact ⟨hfirst, hrest⟩
  exact all op h

/-- Direct ACU splitting rule, stated ONLY in the library's structural relation.

       mass(a)=1
  ----------------------------- SplitAtom
  X+Y =B a  ⇔  (X=B 0 ∧ Y=B a) ∨ (X=B a ∧ Y=B 0)

One atomic constructor has mass one independently of its payload assignment.
The rule preserves every solution and both branches, so it certifies both
soundness and completeness. -/
theorem split_atom {s} (op : sig.ACUOp s) (x y a : Tree sig s)
    (ha : mass profile a = 1) :
    Structural.Indexed.Eq sig (add sig op x y) a ↔
      (Structural.Indexed.Eq sig x (zero sig op) ∧ Structural.Indexed.Eq sig y a) ∨
      (Structural.Indexed.Eq sig x a ∧ Structural.Indexed.Eq sig y (zero sig op)) := by
  constructor
  · intro h
    have count := mass_congr profile h
    rw [mass_add, ha] at count
    have cases : mass profile x = 0 ∨ mass profile y = 0 := by omega
    rcases cases with hx | hy
    · have zx := zero_of_mass profile x op hx
      have reduced : Structural.Indexed.Eq sig (add sig op x y) y :=
        .trans (.congr (sig.add op) (.cons zx (.cons (.refl _) .nil))) (.unit op y)
      exact .inl ⟨zx, .trans (.symm reduced) h⟩
    · have zy := zero_of_mass profile y op hy
      have reduced : Structural.Indexed.Eq sig (add sig op x y) x :=
        .trans (.comm op x y)
          (.trans (.congr (sig.add op) (.cons zy (.cons (.refl _) .nil))) (.unit op x))
      exact .inr ⟨.trans (.symm reduced) h, zy⟩
  · rintro (⟨hx, hy⟩ | ⟨hx, hy⟩)
    · exact .trans (.congr (sig.add op) (.cons hx (.cons hy .nil))) (.unit op a)
    · exact .trans (.congr (sig.add op) (.cons hx (.cons hy .nil)))
        (.trans (.comm op a _) (.unit op a))

end DirectCertification

/-! ## Automatic syntactic metadata (prototype command, eventually library code)

The registered signature already knows every constructor and which symbols are
the ACU operation/unit. This command simply enumerates them. There is no
semantic field to prove and no problem-specific theorem name in the generator.
-/

open Lean Meta Elab Command in
elab "derive_direct_profile " name:ident " for " theory:ident : command => do
  let (theoryName, symbolNames, zeroHeads, addHeads) ← liftTermElabM do
    let t ← Term.elabTerm theory (some (mkConst ``Structural.CertifiedTheory))
    let some theoryName := t.constName?
      | throwError "expected a named certified theory"
    let sig ← mkAppM ``Structural.CertifiedTheory.signature #[t]
    let symbol ← whnf (← mkAppM ``Structural.Indexed.Signature.Symbol #[sig])
    let some symbolName := symbol.getAppFn.constName?
      | throwError "expected a generated constructor datatype"
    let symbolInfo ← getConstInfoInduct symbolName
    let operations ← whnf (← mkAppM ``Structural.Indexed.Signature.ACUOp #[sig])
    let some opName := operations.getAppFn.constName?
      | throwError "expected a generated ACU operator datatype"
    let opInfo ← getConstInfoInduct opName
    let mut zeros := #[]
    let mut adds := #[]
    let mut resultSorts := #[]
    for op in opInfo.ctors do
      let info ← getConstInfoCtor op
      unless info.numFields == 0 && info.numParams == 0 do
        throwError "ACU operator identifiers must be nullary"
      let opExpr := mkConst op
      let resultType ← whnf (← inferType opExpr)
      let sort := resultType.getAppArgs.back!
      if resultSorts.contains sort then
        throwError "direct prototype requires at most one ACU operator per sort"
      resultSorts := resultSorts.push sort
      let zero ← whnf (← mkAppM ``Structural.Indexed.Signature.zero #[sig, opExpr])
      let add ← whnf (← mkAppM ``Structural.Indexed.Signature.add #[sig, opExpr])
      let some zeroName := zero.constName? | throwError "unit must be a constructor"
      let some addName := add.constName? | throwError "operation must be a constructor"
      zeros := zeros.push (zeroName, op)
      adds := adds.push (addName, op)
    return (theoryName, symbolInfo.ctors, zeros, adds)
  let q (n : Name) := "_root_." ++ n.toString
  let signature := "(Structural.CertifiedTheory.signature " ++ q theoryName ++ ")"
  let branches := symbolNames.map fun symbol =>
    let rhs := match zeroHeads.find? (·.1 == symbol) with
      | some (_, op) => "DirectCertification.HeadView.zero (sig := " ++ signature ++ ") " ++ q op
      | none => match addHeads.find? (·.1 == symbol) with
        | some (_, op) => "DirectCertification.HeadView.add (sig := " ++ signature ++ ") " ++ q op
        | none => "DirectCertification.HeadView.atom (sig := " ++ signature ++ ") _"
    "    | " ++ q symbol ++ " => " ++ rhs
  let source := "def " ++ name.getId.toString ++
    " : DirectCertification.Profile " ++ signature ++ " where\n" ++
    "  view := fun f => match f with\n" ++ String.intercalate "\n" branches ++
    "\n  view_zero := by intro s op; cases op <;> rfl" ++
    "\n  view_add := by intro s op; cases op <;> rfl" ++
    "\n  unique := by intro s a b; cases a <;> cases b <;> rfl"
  match Parser.runParserCategory (← getEnv) `command source with
  | .ok stx => elabCommand stx
  | .error e => throwError "generated profile syntax: {e}"

/-! ## Direct first-order proof system (eventually library code)

Terms use the SAME registered constructor symbols as Structural.Indexed.Tree.
Assignments are sorted native values. Formula semantics is NativeEq, with no
portable interpretation or transport to a different equality relation.

Certificate data is untrusted: a successful replay constructs an equivalence
proof. It can later be produced by a Maude strategy guided by native `unify`.
-/

namespace DirectCertification

open Structural.Indexed

variable {Sorts : Type} {sig : Signature Sorts}

mutual
  inductive Term (sig : Signature Sorts) : Sorts → Type where
    | var {s} (id : Nat) : Term sig s
    | app {ss s} (head : sig.Symbol ss s) (args : Terms sig ss) : Term sig s
  inductive Terms (sig : Signature Sorts) : List Sorts → Type where
    | nil : Terms sig []
    | cons {s ss} (first : Term sig s) (rest : Terms sig ss) : Terms sig (s :: ss)
end

abbrev Assignment (reg : Registration sig) := ∀ s, Nat → reg.Carrier s

mutual
  def Term.eval (reg : Registration sig) (ρ : Assignment reg) :
      {s : Sorts} → Term sig s → reg.Carrier s
    | s, .var i => ρ s i
    | _, .app f args => reg.apply f (args.eval reg ρ)
  def Terms.eval (reg : Registration sig) (ρ : Assignment reg) :
      {ss : List Sorts} → Terms sig ss → Args reg.Carrier ss
    | _, .nil => PUnit.unit
    | _, .cons a rest => (a.eval reg ρ, rest.eval reg ρ)
end

inductive Formula (sig : Signature Sorts) where
  | equation {s} (left right : Term sig s)
  | conjunction (left right : Formula sig)
  | disjunction (left right : Formula sig)

def Formula.sat (reg : Registration sig) (ρ : Assignment reg) : Formula sig → Prop
  | .equation a b => NativeEq sig reg (a.eval reg ρ) (b.eval reg ρ)
  | .conjunction p q => p.sat reg ρ ∧ q.sat reg ρ
  | .disjunction p q => p.sat reg ρ ∨ q.sat reg ρ

def unitTerm {s} (op : sig.ACUOp s) : Term sig s := .app (sig.zero op) .nil
def plusTerm {s} (op : sig.ACUOp s) (a b : Term sig s) : Term sig s :=
  .app (sig.add op) (.cons a (.cons b .nil))

/-- The two substitutions are output DATA, not an assumption of completeness. -/
def allocations {s} (op : sig.ACUOp s) (x y atom : Term sig s) : Formula sig :=
  .disjunction
    (.conjunction (.equation x (unitTerm op)) (.equation y atom))
    (.conjunction (.equation x atom) (.equation y (unitTerm op)))

/-- Finite certificate instructions; no embedded Lean proof or model names. -/
inductive Certificate where
  | splitAtom
  | sequence (first second : Certificate)
  | left (child : Certificate)
  | right (child : Certificate)
  deriving Repr, DecidableEq

abbrev Checked (reg : Registration sig) (input : Formula sig) :=
  { output : Formula sig // ∀ ρ : Assignment reg, input.sat reg ρ ↔ output.sat reg ρ }

/-- General splitting metatheorem specialized to generated native constructors.
The only quote/eval identities used here are provided by automatic registration. -/
theorem split_native (profile : Profile sig) (reg : Registration sig) {s}
    (op : sig.ACUOp s) (x y a : reg.Carrier s)
    (ha : mass profile (reg.quote s a) = 1) :
    NativeEq sig reg (reg.apply (sig.add op) (x, y, PUnit.unit)) a ↔
      (NativeEq sig reg x (reg.apply (sig.zero op) PUnit.unit) ∧ NativeEq sig reg y a) ∨
      (NativeEq sig reg x a ∧ NativeEq sig reg y (reg.apply (sig.zero op) PUnit.unit)) := by
  unfold NativeEq
  rw [reg.quote_apply, reg.quote_apply]
  exact split_atom profile op _ _ _ ha

def splitStep (profile : Profile sig) (reg : Registration sig)
    (input : Formula sig) : Option (Checked reg input) := by
  cases input with
  | equation lhs rhs =>
    cases lhs with
    | var => exact none
    | app f args =>
      cases hv : profile.view f with
      | zero => exact none
      | atom => exact none
      | add op =>
        cases args with
        | cons x rest =>
          cases rest with
          | cons y tail =>
            cases tail
            cases rhs with
            | var => exact none
            | app g payload =>
              cases hg : profile.view g with
              | zero => exact none
              | add => exact none
              | atom g =>
                exact some ⟨allocations op x y (.app g payload), by
                  intro ρ
                  apply split_native profile reg op
                  simp only [Term.eval]
                  rw [reg.quote_apply]
                  simp [mass, Tree.eval, measure, hg]⟩
  | conjunction => exact none
  | disjunction => exact none

/-- Replay proves exactness as it computes the result. Failed applications are
None. Neither a missing branch nor a native solver answer is accepted on trust. -/
def replay (profile : Profile sig) (reg : Registration sig) :
    Certificate → (input : Formula sig) → Option (Checked reg input)
  | .splitAtom, input => splitStep profile reg input
  | .sequence a b, input => do
      let first ← replay profile reg a input
      let second ← replay profile reg b first.val
      return ⟨second.val, fun ρ => (first.property ρ).trans (second.property ρ)⟩
  | .left c, .disjunction p q => do
      let next ← replay profile reg c p
      return ⟨.disjunction next.val q, fun ρ => or_congr (next.property ρ) Iff.rfl⟩
  | .right c, .disjunction p q => do
      let next ← replay profile reg c q
      return ⟨.disjunction p next.val, fun ρ => or_congr Iff.rfl (next.property ρ)⟩
  | .left _, _ | .right _, _ => none

end DirectCertification

/-! ## Automatic reflection and replay (eventually library code)

This tactic reads a native equation and the registered signature. It builds the
sorted certificate input and assignment automatically, and accepts the proof
only if the computed output matches the requested native proposition. There is
no Bakery constructor name in this implementation. -/

namespace DirectCertification.Reflection

open Lean Meta Elab Tactic Parser.Term

structure Constructor where
  symbol : Expr
  head : Name
  fields : Array Expr
  resultSort : Expr

private partial def listItems (e : Expr) : MetaM (Array Expr) := do
  let e ← whnf e
  if e.isAppOfArity ``List.nil 1 then return #[]
  if e.isAppOfArity ``List.cons 3 then
    return #[e.getAppArgs[1]!] ++ (← listItems e.getAppArgs[2]!)
  throwError "expected a closed sort list"

private def constructors (sig reg : Expr) : MetaM (Array Constructor) := do
  let symbolType ← whnf (← mkAppM ``Structural.Indexed.Signature.Symbol #[sig])
  let info ← getConstInfoInduct symbolType.getAppFn.constName!
  let algebra ← mkAppM ``Structural.Indexed.Registration.toAlgebra #[reg]
  info.ctors.toArray.mapM fun name => do
    let symbol := mkConst name
    let ty ← whnf (← inferType symbol)
    let xs := ty.getAppArgs
    let fields ← listItems xs[xs.size - 2]!
    let resultSort := xs.back!
    let apply ← mkAppM ``Structural.Indexed.Algebra.apply #[algebra, symbol]
    let applyType ← whnf (← inferType apply)
    let head ← withLocalDeclD `args applyType.bindingDomain! fun args => do
      let value ← withTransparency .all <| whnf (mkApp apply args)
      let some name := value.getAppFn.constName?
        | throwError "registered symbol does not evaluate to a native constructor"
      return name
    return { symbol, head, fields, resultSort }

private partial def defaultValue (ctors : Array Constructor) (sort : Expr)
    (visited : Array Expr := #[]) : MetaM Expr := do
  if visited.contains sort then throwError "recursive default"
  for ctor in ctors do
    if ctor.resultSort != sort then continue
    try
      let args ← ctor.fields.mapM fun field => defaultValue ctors field (visited.push sort)
      return mkAppN (mkConst ctor.head) args
    catch _ => continue
  throwError "no closed native value for this unused assignment sort"

private partial def reify (sorts sig : Expr) (ctors : Array Constructor)
    (sort value : Expr) : StateRefT (Array (Expr × Expr)) MetaM Expr := do
  let value ← withTransparency .all <| whnf value
  let head := value.getAppFn.constName?
  if let some ctor := ctors.find? fun c => some c.head == head && c.resultSort == sort then
    let values := value.getAppArgs
    unless values.size == ctor.fields.size do throwError "unexpected native constructor arity"
    let mut args := mkAppN (mkConst ``Terms.nil) #[sorts, sig]
    let mut tail := mkApp (mkConst ``List.nil [Level.zero]) sorts
    for i in (List.range values.size).reverse do
      let item ← reify sorts sig ctors ctor.fields[i]! values[i]!
      args := mkAppN (mkConst ``Terms.cons) #[sorts, sig, ctor.fields[i]!, tail, item, args]
      tail := mkAppN (mkConst ``List.cons [Level.zero]) #[sorts, ctor.fields[i]!, tail]
    return mkAppN (mkConst ``Term.app) #[sorts, sig, tail, sort, ctor.symbol, args]
  let bindings ← get
  let index := (bindings.findIdx? fun (s, v) => s == sort && v == value).getD bindings.size
  if index == bindings.size then modify (·.push (sort, value))
  return mkAppN (mkConst ``Term.var) #[sorts, sig, sort, mkNatLit index]

private def makeAssignment (reg sorts : Expr) (ctors : Array Constructor)
    (bindings : Array (Expr × Expr)) : TermElabM Expr := do
  let sorts ← whnf sorts
  let info ← getConstInfoInduct sorts.constName!
  let index := mkIdent (← mkFreshUserName `index)
  let sortName := mkIdent (← mkFreshUserName `sort)
  let mut alternatives : Array (TSyntax ``Parser.Term.matchAlt) := #[]
  for constructor in info.ctors do
    let sort := mkConst constructor
    let mut value ← Term.exprToSyntax (← defaultValue ctors sort)
    for i in (List.range bindings.size).reverse do
      let (s, v) := bindings[i]!
      if s != sort then continue
      let rhs ← Term.exprToSyntax v
      value ← `(if $index:ident = $(quote i) then $rhs else $value)
    let pattern := mkIdent constructor
    alternatives := alternatives.push (← `(matchAltExpr| | $pattern:ident => $value))
  let sortType ← Term.exprToSyntax sorts
  let assignSyntax ← `(fun ($sortName:ident : $sortType) ($index:ident : Nat) =>
    match $sortName:ident with $alternatives:matchAlt*)
  Term.elabTerm assignSyntax (some (← mkAppM ``Assignment #[reg]))

elab "certify_direct " profileSyntax:term : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let target ← goal.getType
    unless target.isAppOfArity ``Iff 2 do throwError "expected a unification exactness iff"
    let equation := target.getAppArgs[0]!
    unless equation.isAppOfArity ``Structural.eqModOf 6 do
      throwError "expected a native equation using =[theory.certified]"
    let xs := equation.getAppArgs
    let theory := xs[1]!
    let nativeType := xs[2]!
    let reg ← mkAppM ``Structural.CertifiedTheory.native #[theory]
    let sig ← mkAppM ``Structural.CertifiedTheory.signature #[theory]
    let sorts ← mkAppM ``Structural.CertifiedTheory.Sorts #[theory]
    let profile ← Tactic.elabTerm profileSyntax (some (← mkAppM ``Profile #[sig]))
    let ctors ← constructors sig reg
    let sortInfo ← getConstInfoInduct (← whnf sorts).constName!
    let algebra ← mkAppM ``Structural.Indexed.Registration.toAlgebra #[reg]
    let mut selectedSort := none
    for name in sortInfo.ctors do
      let sort := mkConst name
      let carrier ← mkAppM ``Structural.Indexed.Algebra.Carrier #[algebra, sort]
      if ← isDefEq carrier nativeType then selectedSort := some sort
    let some sort := selectedSort | throwError "native sort is outside the registered signature"
    let ((left, right), bindings) ← (do
      let left ← reify sorts sig ctors sort xs[4]!
      let right ← reify sorts sig ctors sort xs[5]!
      return (left, right)).run #[]
    let input := mkAppN (mkConst ``Formula.equation) #[sorts, sig, sort, left, right]
    let result ← mkAppM ``replay #[profile, reg, mkConst ``Certificate.splitAtom, input]
    let accepted ← mkEq (← mkAppM ``Option.isSome #[result]) (mkConst ``Bool.true)
    let evidence ← Tactic.elabTerm (← `(by decide)) (some accepted)
    let checked ← mkAppM ``Option.get #[result, evidence]
    let assignment ← makeAssignment reg sorts ctors bindings
    let proof := mkApp (mkProj ``Subtype 1 checked) assignment
    unless ← isDefEq (← inferType proof) target do
      throwError "computed certificate output differs from the goal"
    goal.assign proof
    replaceMainGoal []

end DirectCertification.Reflection

/-! ## Bakery user examples

The actual model and its structural annotation come from examples/bakery.
One trivial metadata command; no handwritten interpretation or registration proof.
-/

namespace DirectCertification.Bakery

open Structural.Indexed BakeryTheory.Generated

derive_direct_profile profile for BakeryTheory.certified

/- Internal packet illustration, not something the user has to write.
The tactic below produces this kind of input from the ordinary native goal. -/
-- Variables are sorted: bag variables 0/1 and ticket variable 0 do not collide.
-- Input: P + Q = singleton(wait n). The Nat payload n is SYMBOLIC.
def input : Formula Sig := .equation
  (plusTerm Operator.acu (.var 0) (.var 1))
  (.app Symbol.c6 (.cons (.app Symbol.c3 (.cons (.var 0) .nil)) .nil))

def certificate : Certificate := .splitAtom

def checked : Checked registration input :=
  (replay profile registration certificate input).get (by decide)

/-- Entire certification proof: evaluate a first-order certificate and apply the
generic semantic correctness theorem. No example-specific supporting lemma. -/
theorem two_unifiers (n : Nat) (P Q : ProcSet) :
    ProcSet.union P Q =[BakeryTheory.certified] ProcSet.singleton (.wait n) ↔
      (P =[BakeryTheory.certified] ProcSet.empty ∧
        Q =[BakeryTheory.certified] ProcSet.singleton (.wait n)) ∨
      (P =[BakeryTheory.certified] ProcSet.singleton (.wait n) ∧
        Q =[BakeryTheory.certified] ProcSet.empty) := by
  certify_direct profile

#print axioms two_unifiers

-- Same generic automation, different constructor and compound symbolic payload.
-- No new signature interpretation, proof rule, or registration obligation.
example (ticket : Nat) (left right : ProcSet) :
    ProcSet.union left right =[BakeryTheory.certified] ProcSet.singleton (.crit ticket.succ) ↔
      (left =[BakeryTheory.certified] ProcSet.empty ∧
        right =[BakeryTheory.certified] ProcSet.singleton (.crit ticket.succ)) ∨
      (left =[BakeryTheory.certified] ProcSet.singleton (.crit ticket.succ) ∧
        right =[BakeryTheory.certified] ProcSet.empty) := by
  certify_direct profile

-- Ground atoms use the very same path (including automatic unused-sort values).
example (P Q : ProcSet) :
    ProcSet.union P Q =[BakeryTheory.certified] ProcSet.singleton .idle ↔
      (P =[BakeryTheory.certified] ProcSet.empty ∧
        Q =[BakeryTheory.certified] ProcSet.singleton .idle) ∨
      (P =[BakeryTheory.certified] ProcSet.singleton .idle ∧
        Q =[BakeryTheory.certified] ProcSet.empty) := by
  certify_direct profile

-- The native expected proposition is checked: losing a family is not accepted.
/-- error: computed certificate output differs from the goal -/
#guard_msgs in
example (n : Nat) (P Q : ProcSet) :
    ProcSet.union P Q =[BakeryTheory.certified] ProcSet.singleton (.wait n) ↔
      P =[BakeryTheory.certified] ProcSet.empty ∧
        Q =[BakeryTheory.certified] ProcSet.singleton (.wait n) := by
  certify_direct profile

-- Unit splitting is outside this first rule and must fail, not return no solutions.
example : (replay profile registration .splitAtom
    (.equation (plusTerm Operator.acu (.var 0) (.var 1))
      (unitTerm Operator.acu))).isNone = true := by decide

#print axioms profile
#print axioms DirectCertification.split_atom
#print axioms DirectCertification.replay

end DirectCertification.Bakery
