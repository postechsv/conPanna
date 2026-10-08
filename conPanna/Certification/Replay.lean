import conPanna.Certification.Enumeration
import conPanna.Certification.Frontend

/-! Registered profile generation, typed certificate rules, and term acceptance. -/


/-! ## Automatic syntactic metadata (prototype command, eventually library code)

The registered signature already knows every constructor and which symbols are
the ACU operation/unit. This command enumerates them and computes the finite
sort-dependency graph. A sort is rigid only if no constructor path reaches an
ACU sort (cycles such as Nat -> Nat are allowed). All resulting metadata fields
are checked by constructor cases/reduction. There is no semantic field for the
user to prove and no problem-specific theorem name in the generator.
Decidable sort/head equality is forwarded from the already-generated finite
tag types, so opaque registration projections require no extra user instances.

This frontend now enforces the DOCUMENTED initial contract, rather than merely
one operation per sort: exactly one ACU operation globally; its result sort has
only unit, operation, and one unary free constructor; that constructor's payload
cannot reach the bag sort. Free configurations ABOVE bags remain admissible.
These checks do not prove the pending finite-sharing search-success theorem.
-/

open Lean Meta Elab Command in
elab "derive_direct_profile " name:ident " for " theory:ident : command => do
  let (theoryName, sortName, symbolName, symbolNames, zeroHeads, addHeads, rigidSorts) ← liftTermElabM do
    let t ← Term.elabTerm theory (some (mkConst ``Structural.CertifiedTheory))
    let some theoryName := t.constName?
      | throwError "expected a named certified theory"
    let sorts ← whnf (← mkAppM ``Structural.CertifiedTheory.Sorts #[t])
    let some sortName := sorts.constName?
      | throwError "expected a generated finite sort datatype"
    let sig ← mkAppM ``Structural.CertifiedTheory.signature #[t]
    let symbol ← whnf (← mkAppM ``Structural.Indexed.Signature.Symbol #[sig])
    let some symbolName := symbol.getAppFn.constName?
      | throwError "expected a generated constructor datatype"
    let symbolInfo ← getConstInfoInduct symbolName
    let operations ← whnf (← mkAppM ``Structural.Indexed.Signature.ACUOp #[sig])
    let some opName := operations.getAppFn.constName?
      | throwError "expected a generated ACU operator datatype"
    let opInfo ← getConstInfoInduct opName
    unless opInfo.ctors.length == 1 do
      throwError "certification contract requires exactly one ACU bag fragment"
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
    -- Dependency analysis is purely syntactic. Starting with ACU result sorts,
    -- propagate non-rigidity backwards through ALL constructor arguments.
    -- In particular a free Conf constructor containing a bag is not rigid.
    let mut tags : Array Name := #[]
    let mut dependencies : Array (Expr × Array Expr) := #[]
    let mut bagPayloads : Array Expr := #[]
    for symbol in symbolInfo.ctors do
      let info ← getConstInfoCtor symbol
      unless info.numFields == 0 && info.numParams == 0 do
        throwError "constructor identifiers must be nullary"
      let ty ← whnf info.type
      let args := ty.getAppArgs
      unless args.size == 2 do throwError "expected argument-sort and result-sort indices"
      let output ← whnf args[1]!
      let mut inputs := #[]
      let mut inputList := args[0]!
      while true do
        let cell ← whnf inputList
        if cell.getAppFn.constName? == some ``List.nil then break
        unless cell.getAppFn.constName? == some ``List.cons do
          throwError "expected a finite list of constructor argument sorts"
        let fields := cell.getAppArgs
        inputs := inputs.push (← whnf fields[1]!)
        inputList := fields[2]!
      dependencies := dependencies.push (output, inputs)
      if resultSorts.contains output &&
          !(zeros.any (·.1 == symbol)) && !(adds.any (·.1 == symbol)) then
        unless inputs.size == 1 do
          throwError "bag fragment requires a unary singleton constructor"
        bagPayloads := bagPayloads.push inputs[0]!
      for tag in #[output] ++ inputs do
        let some tagName := tag.constName? | throwError "sort tags must be nullary constructors"
        unless tags.contains tagName do tags := tags.push tagName
    let mut blocked := resultSorts
    for _ in [:tags.size] do
      for (output, inputs) in dependencies do
        if inputs.any blocked.contains && !blocked.contains output then
          blocked := blocked.push output
    unless bagPayloads.size == 1 do
      throwError "bag fragment must contain only unit, operation, and one singleton"
    if blocked.contains bagPayloads[0]! then
      throwError "singleton payload must not contain the ACU bag sort"
    return (theoryName, sortName, symbolName, symbolInfo.ctors, zeros, adds,
      tags.map fun tag => (tag, !blocked.contains (mkConst tag)))
  let q (n : Name) := "_root_." ++ n.toString
  let signature := "(Structural.CertifiedTheory.signature " ++ q theoryName ++ ")"
  let branches := symbolNames.map fun symbol =>
    let rhs := match zeroHeads.find? (·.1 == symbol) with
      | some (_, op) => "DirectCertification.HeadView.zero (sig := " ++ signature ++ ") " ++ q op
      | none => match addHeads.find? (·.1 == symbol) with
        | some (_, op) => "DirectCertification.HeadView.add (sig := " ++ signature ++ ") " ++ q op
        | none => "DirectCertification.HeadView.atom (sig := " ++ signature ++ ") _"
    "    | " ++ q symbol ++ " => " ++ rhs
  let rigidBranches := rigidSorts.map fun (tag, rigid) =>
    "    | " ++ q tag ++ " => " ++ (if rigid then "true" else "false")
  let codeBranches := symbolNames.toArray.mapIdx fun i symbol =>
    "    | " ++ q symbol ++ " => " ++ toString i
  let source := "def " ++ name.getId.toString ++
    " : DirectCertification.Profile " ++ signature ++ " where\n" ++
    "  view := fun f => match f with\n" ++ String.intercalate "\n" branches ++
    "\n  view_zero := by intro s op; cases op <;> rfl" ++
    "\n  view_add := by intro s op; cases op <;> rfl" ++
    "\n  unique := by intro s a b; cases a <;> cases b <;> rfl" ++
    "\n  code := fun f => match f with\n" ++ String.intercalate "\n" codeBranches.toList ++
    "\n  rigid := fun s => match s with\n" ++ String.intercalate "\n" rigidBranches.toList ++
    "\n  rigid_args := by intro ss s f h; cases f <;> simp_all [DirectCertification.AllRigid]" ++
    "\n  rigid_no_acu := by intro s op; cases op <;> rfl"
  match Parser.runParserCategory (← getEnv) `command source with
  | .ok stx => elabCommand stx
  | .error e => throwError "generated profile syntax: {e}"
  -- Serialize the registered signature once. Names do not choose algorithms:
  -- only finite sort/head codes and registered free/zero/add roles are exported.
  let sortTags := (← getConstInfoInduct sortName).ctors.toArray
  let mut schema : Array Lean.Json := #[]
  for i in [:symbolNames.length] do
    let symbol := symbolNames[i]!
    let (inputs, output) ← liftTermElabM do
      let ty ← whnf (← getConstInfoCtor symbol).type
      let args := ty.getAppArgs
      let output ← whnf args[1]!
      let mut inputs := #[]
      let mut rest := args[0]!
      while true do
        let cell ← whnf rest
        if cell.getAppFn.constName? == some ``List.nil then break
        let fields := cell.getAppArgs
        inputs := inputs.push (← whnf fields[1]!)
        rest := fields[2]!
      return (inputs, output)
    let tagCode := fun (e : Expr) => (sortTags.findIdx? (fun n => e.constName? == some n)).getD sortTags.size
    let role := if zeroHeads.any (·.1 == symbol) then "zero"
      else if addHeads.any (·.1 == symbol) then "add" else "free"
    schema := schema.push (Lean.Json.mkObj [("id", toJson i),
      ("inputs", toJson (inputs.map tagCode)), ("output", toJson (tagCode output)),
      ("role", toJson role)])
  let text := (Lean.Json.arr schema).compress
  let schemaSource := "def " ++ name.getId.toString ++ "_signature : Lean.Json := " ++
    "(Lean.Json.parse " ++ (Lean.Json.str text).compress ++ ").toOption.get!"
  match Parser.runParserCategory (← getEnv) `command schemaSource with
  | .ok stx => elabCommand stx
  | .error e => throwError "generated signature syntax: {e}"
  -- Forward existing decidable metadata through opaque registration projections.
  -- This is generated here, not a new user registration obligation.
  for source in [
      "def " ++ name.getId.toString ++ "_sortCode : " ++ q sortName ++ " → Nat := fun s => match s with\n" ++
        String.intercalate "\n" ((← getConstInfoInduct sortName).ctors.toArray.mapIdx
          (fun i tag => "  | " ++ q tag ++ " => " ++ toString i)).toList,
      "local instance " ++ name.getId.toString ++ "_decidableSorts : DecidableEq (" ++
        q theoryName ++ ".Sorts) := inferInstanceAs (DecidableEq " ++ q sortName ++ ")",
      "local instance " ++ name.getId.toString ++ "_decidableSymbols : ∀ ss s, DecidableEq (" ++
        signature ++ ".Symbol ss s) := fun ss s => inferInstanceAs (DecidableEq (" ++
        q symbolName ++ " ss s))"] do
    match Parser.runParserCategory (← getEnv) `command source with
    | .ok stx => elabCommand stx
    | .error e => throwError "generated decidable metadata syntax: {e}"

/-! ## General native proof rules

These are theorem schemas, not rules specialized to Bakery.
For every assignment they preserve exactly the same solutions:

  X + Y =B atom
  ---------------------------------------------- SplitAtom
  (X =B 0 AND Y =B atom) OR (X =B atom AND Y =B 0)

  X + Y =B A + R
  ------------------------------------------------------------ MutateACU
  EXISTS P Q S T,
    X =B P+Q AND Y =B S+T AND A =B P+S AND R =B Q+T

The existential variables are fresh pieces, not extra input equations.
The forward direction is completeness; the reverse direction is soundness.
Orient, Congruence, Unit and Transitivity simplify the resulting substitutions.
They are general structural-equality proof rules, not unification search.

The atom side condition is checked syntactically: a registered constructor
other than the ACU operation/unit has mass one, regardless of its arguments.
-/

namespace DirectCertification

open Structural.Indexed

variable {Sorts : Type} {sig : Signature Sorts}

theorem native_refl (reg : Registration sig) {s} (x : reg.Carrier s) :
    NativeEq sig reg x x :=
  .refl _

theorem native_symm (reg : Registration sig) {s} {x y : reg.Carrier s}
    (h : NativeEq sig reg x y) : NativeEq sig reg y x :=
  .symm h

theorem native_trans (reg : Registration sig) {s} {x y z : reg.Carrier s}
    (h : NativeEq sig reg x y) (k : NativeEq sig reg y z) : NativeEq sig reg x z :=
  .trans h k

theorem native_add_congr (reg : Registration sig) {s} (op : sig.ACUOp s)
    {x x' y y' : reg.Carrier s}
    (hx : NativeEq sig reg x x') (hy : NativeEq sig reg y y') :
    NativeEq sig reg (reg.apply (sig.add op) (x, y, PUnit.unit))
      (reg.apply (sig.add op) (x', y', PUnit.unit)) := by
  unfold NativeEq
  rw [reg.quote_apply, reg.quote_apply]
  exact .congr (sig.add op) (.cons hx (.cons hy .nil))

theorem native_unit (reg : Registration sig) {s} (op : sig.ACUOp s)
    (x : reg.Carrier s) :
    NativeEq sig reg
      (reg.apply (sig.add op) (reg.apply (sig.zero op) PUnit.unit, x, PUnit.unit)) x := by
  simp only [NativeEq, reg.quote_apply, Args.quote]
  exact .unit op _

theorem native_comm (reg : Registration sig) {s} (op : sig.ACUOp s)
    (x y : reg.Carrier s) :
    NativeEq sig reg (reg.apply (sig.add op) (x, y, PUnit.unit))
      (reg.apply (sig.add op) (y, x, PUnit.unit)) := by
  unfold NativeEq
  rw [reg.quote_apply, reg.quote_apply]
  exact .comm op _ _

/-- Native reassociation: a general equality rule, also used when repeated
variables remain correlated after Mutate/Split. -/
theorem native_assoc (reg : Registration sig) {s} (op : sig.ACUOp s)
    (x y z : reg.Carrier s) :
    NativeEq sig reg
      (reg.apply (sig.add op) (reg.apply (sig.add op) (x, y, PUnit.unit), z, PUnit.unit))
      (reg.apply (sig.add op) (x, reg.apply (sig.add op) (y, z, PUnit.unit), PUnit.unit)) := by
  simp only [NativeEq, reg.quote_apply, Args.quote]
  exact .assoc op _ _ _

/-- Native repeated addition: no new modeling constructor or wrapper. -/
def nativeRepeat (reg : Registration sig) {s} (op : sig.ACUOp s) :
    Nat → reg.Carrier s → reg.Carrier s
  | 0, _ => reg.apply (sig.zero op) PUnit.unit
  | k + 1, a => reg.apply (sig.add op) (a, nativeRepeat reg op k a, PUnit.unit)

theorem quote_nativeRepeat (reg : Registration sig) {s} (op : sig.ACUOp s)
    (k : Nat) (a : reg.Carrier s) :
    reg.quote s (nativeRepeat reg op k a) = bagCopies op k (reg.quote s a) := by
  induction k with
  | zero => simp only [nativeRepeat, bagCopies, zero, reg.quote_apply, Args.quote]
  | succ k ih => simp only [nativeRepeat, bagCopies, add, reg.quote_apply, Args.quote, ih]

/-! ### Native specialization of the exhaustive FiniteSharing rule

These operations evaluate only the user's registered zero/union constructors.
They introduce no datatype wrapper, alternative equality, or registration proof.
Quotation/rebuilding are already proved by Registration, so specialization is
mechanical. The indexed/native relation remains the public certificate semantics.
-/

def nativeBagSum (reg : Registration sig) {s n} (op : sig.ACUOp s)
    (coeff : FiniteSharing.Vector n) (values : Fin n → reg.Carrier s) : reg.Carrier s :=
  (FiniteSharing.bagSum op coeff (fun i => reg.quote s (values i))).eval reg.toAlgebra

def nativeSharingImages (reg : Registration sig) {s n} (op : sig.ACUOp s)
    (left right : FiniteSharing.Vector n) (generators : List (FiniteSharing.Vector n))
    (parameters : Fin generators.length → reg.Carrier s)
    (passthrough : Fin n → reg.Carrier s) : Fin n → reg.Carrier s := fun i =>
  (FiniteSharing.sharingImages op left right generators (fun j => reg.quote s (parameters j))
    (fun j => reg.quote s (passthrough j)) i).eval reg.toAlgebra

/-- Exact native finite sharing, inferred from existing constructor registration.
ALL original bag-variable images are compared modulo the registered theory,
including inactive inputs which keep their independent passthrough parameters.
The finite parameter family is computed, not supplied or trusted complete.
This theorem is semantic rule validity, not automated search/replay success. -/
theorem finiteSharing_native (profile : Profile sig) (reg : Registration sig) {s n rows cols}
    (op : sig.ACUOp s) (left right : FiniteSharing.Vector n)
    (rowLabels : Fin rows → Fin n) (colLabels : Fin cols → Fin n)
    (rowCounts : ∀ i, FiniteSharing.labelCount rowLabels i = left i)
    (colCounts : ∀ i, FiniteSharing.labelCount colLabels i = right i)
    (disjoint : FiniteSharing.Disjoint left right) (values : Fin n → reg.Carrier s) :
    NativeEq sig reg (nativeBagSum reg op left values) (nativeBagSum reg op right values) ↔
      ∃ parameters : Fin (FiniteSharing.supportGenerators rowLabels colLabels).length → reg.Carrier s,
        ∃ passthrough : Fin n → reg.Carrier s,
          ∀ i, NativeEq sig reg (values i)
            (nativeSharingImages reg op left right (FiniteSharing.supportGenerators rowLabels colLabels)
              parameters passthrough i) := by
  have exactRule := FiniteSharing.bags_generated profile op left right rowLabels colLabels
    rowCounts colCounts disjoint (fun i => reg.quote s (values i))
  constructor
  · intro equation
    obtain ⟨parameters, passthrough, images⟩ := exactRule.mp
      (by simpa only [NativeEq, nativeBagSum, reg.quote_eval] using equation)
    refine ⟨fun j => (parameters j).eval reg.toAlgebra,
      fun j => (passthrough j).eval reg.toAlgebra, fun i => ?_⟩
    simpa only [NativeEq, nativeSharingImages, reg.quote_eval] using images i
  · rintro ⟨parameters, passthrough, images⟩
    apply (show NativeEq sig reg (nativeBagSum reg op left values) (nativeBagSum reg op right values) ↔
        Structural.Indexed.Eq sig
          (FiniteSharing.bagSum op left (fun i => reg.quote s (values i)))
          (FiniteSharing.bagSum op right (fun i => reg.quote s (values i))) from
      by simp only [NativeEq, nativeBagSum, reg.quote_eval]).mpr
    apply exactRule.mpr
    refine ⟨fun j => reg.quote s (parameters j), fun j => reg.quote s (passthrough j), fun i => ?_⟩
    simpa only [NativeEq, nativeSharingImages, reg.quote_eval] using images i

/-- General native rule used by answer-guided coverage, for ANY positive k. -/
theorem multiplicity_native (profile : Profile sig) (reg : Registration sig) {s}
    (op : sig.ACUOp s) (k : Nat) (positive : 0 < k) (a b : reg.Carrier s) :
    NativeEq sig reg (nativeRepeat reg op k a) (nativeRepeat reg op k b) ↔
      NativeEq sig reg a b := by
  simp only [NativeEq, quote_nativeRepeat]
  exact multiplicity_cancel profile op k positive _ _

/-- Structural argument equality and the ordinary native argument tuple have
the same components. No constructor-arity bound or hand-written carrier map. -/
theorem quote_args_iff (reg : Registration sig) {ss}
    (a b : Args reg.Carrier ss) :
    Eqs sig (Args.quote sig reg.quote ss a) (Args.quote sig reg.quote ss b) ↔
      ArgsRel (fun s => NativeEq sig reg (s := s)) ss a b := by
  induction ss with
  | nil =>
      cases a; cases b
      exact ⟨fun _ => True.intro, fun _ => .nil⟩
  | cons s ss ih =>
      rcases a with ⟨x, rest⟩
      rcases b with ⟨y, tail⟩
      constructor
      · intro h
        cases h with
        | cons hx ht => exact ⟨hx, (ih rest tail).mp ht⟩
      · rintro ⟨hx, ht⟩
        exact .cons hx ((ih rest tail).mpr ht)

/-- Arbitrary-arity native Decompose. The only side condition is syntactic
free-head classification, checked by reduction of generated metadata. -/
theorem decompose_native (profile : Profile sig) (reg : Registration sig) {ss s}
    (f : sig.Symbol ss s) (free : profile.view f = .atom f)
    (a b : Args reg.Carrier ss) :
    NativeEq sig reg (reg.apply f a) (reg.apply f b) ↔
      ArgsRel (fun s => NativeEq sig reg (s := s)) ss a b := by
  unfold NativeEq
  rw [reg.quote_apply, reg.quote_apply]
  exact (decompose profile f free _ _).trans (quote_args_iff reg a b)

theorem clash_native (profile : Profile sig) (reg : Registration sig) {ss tt s}
    (f : sig.Symbol ss s) (g : sig.Symbol tt s)
    (hf : profile.view f = .atom f) (hg : profile.view g = .atom g)
    (different : (⟨ss, f⟩ : Σ us, sig.Symbol us s) ≠ ⟨tt, g⟩)
    (a : Args reg.Carrier ss) (b : Args reg.Carrier tt) :
    ¬ NativeEq sig reg (reg.apply f a) (reg.apply g b) := by
  unfold NativeEq
  rw [reg.quote_apply, reg.quote_apply]
  exact clash profile f g hf hg different _ _

/-- Ordinary equality elimination is safe on a rigid native sort, and ONLY
there. In particular this rule must not be applied to a bag or a bag wrapper. -/
theorem rigid_native (profile : Profile sig) (reg : Registration sig) {s}
    (rigid : profile.rigid s = true) (a b : reg.Carrier s) :
    NativeEq sig reg a b ↔ a = b := by
  constructor
  · intro h
    have same := eq_of_rigid profile rigid h
    simpa only [reg.eval_quote] using congrArg (fun t => t.eval reg.toAlgebra) same
  · intro h
    cases h
    exact .refl _

/-- Emit a shared parameter for two equal rigid-sort variables. -/
theorem share_literal {α : Type} (x y : α) : x = y ↔ ∃ u : α, x = u ∧ y = u :=
  ⟨fun h => ⟨x, rfl, h.symm⟩, fun ⟨_u, hx, hy⟩ => hx.trans hy.symm⟩

/-- Emit a shared parameter for two equal variables on ANY registered sort.
Bag images remain equal modulo B, not literally equal as raw constructor trees. -/
theorem share_native (reg : Registration sig) {s} (x y : reg.Carrier s) :
    NativeEq sig reg x y ↔ ∃ u : reg.Carrier s,
      NativeEq sig reg x u ∧ NativeEq sig reg y u :=
  ⟨fun h => ⟨x, .refl _, .symm h⟩,
    fun ⟨_u, hx, hy⟩ => .trans hx (.symm hy)⟩

/-- Native SplitAtom. Syntactic registration supplies every quote/apply identity. -/
theorem split_native (profile : Profile sig) (reg : Registration sig) {s}
    (op : sig.ACUOp s) (x y a : reg.Carrier s)
    (ha : mass profile (reg.quote s a) = 1) :
    NativeEq sig reg (reg.apply (sig.add op) (x, y, PUnit.unit)) a ↔
      (NativeEq sig reg x (reg.apply (sig.zero op) PUnit.unit) ∧ NativeEq sig reg y a) ∨
      (NativeEq sig reg x a ∧ NativeEq sig reg y (reg.apply (sig.zero op) PUnit.unit)) := by
  unfold NativeEq
  rw [reg.quote_apply, reg.quote_apply]
  exact split_atom profile op _ _ _ ha

namespace NativeRules

/-- The surface ATOM rule. Its premises mention registered constructors and
native values only; quotation, mass, and sorted variable positions stay internal.

    x + y =B f(args)
    ------------------------------- ATOM (f is a singleton constructor)
    (x =B 0 ∧ y =B f(args)) ∨ (x =B f(args) ∧ y =B 0)

This is a derived presentation of the existing semantic split rule, not search
or a new trusted axiom. The `.atom` replay node handles the general finite sum. -/
theorem singletonCases (profile : Profile sig) (reg : Registration sig) {s ss}
    (op : sig.ACUOp s) (f : sig.Symbol ss s) (free : profile.view f = .atom f)
    (args : Args reg.Carrier ss) (x y : reg.Carrier s) :
    NativeEq sig reg (reg.apply (sig.add op) (x, y, PUnit.unit)) (reg.apply f args) ↔
      (NativeEq sig reg x (reg.apply (sig.zero op) PUnit.unit) ∧
        NativeEq sig reg y (reg.apply f args)) ∨
      (NativeEq sig reg x (reg.apply f args) ∧
        NativeEq sig reg y (reg.apply (sig.zero op) PUnit.unit)) := by
  apply split_native profile reg op x y (reg.apply f args)
  simp [reg.quote_apply, mass, Tree.eval, measure, free]

/-- Surface UNIT-R: the dump expands this to COMM followed by UNIT-L. -/
theorem rightUnit (reg : Registration sig) {s} (op : sig.ACUOp s)
    (x : reg.Carrier s) :
    NativeEq sig reg
      (reg.apply (sig.add op) (x, reg.apply (sig.zero op) PUnit.unit, PUnit.unit)) x :=
  native_trans reg (native_comm reg op _ _) (native_unit reg op x)

/-- A unary CONGR rule. No source-level quotation or argument-vector bookkeeping
is required when the user lifts an equality through a unary constructor. -/
theorem unaryCongruence (reg : Registration sig) {s t}
    (f : sig.Symbol [s] t) {x y : reg.Carrier s} (same : NativeEq sig reg x y) :
    NativeEq sig reg (reg.apply f (x, PUnit.unit)) (reg.apply f (y, PUnit.unit)) := by
  unfold NativeEq
  rw [reg.quote_apply, reg.quote_apply]
  exact .congr f (.cons same .nil)

end NativeRules

/-- Native MutateACU. Fresh pieces are native values, not a wrapper datatype. -/
theorem mutate_native (profile : Profile sig) (reg : Registration sig) {s}
    (op : sig.ACUOp s) (x y a rest : reg.Carrier s) :
    NativeEq sig reg (reg.apply (sig.add op) (x, y, PUnit.unit))
      (reg.apply (sig.add op) (a, rest, PUnit.unit)) ↔
      ∃ p q r t : reg.Carrier s,
        NativeEq sig reg x (reg.apply (sig.add op) (p, q, PUnit.unit)) ∧
        NativeEq sig reg y (reg.apply (sig.add op) (r, t, PUnit.unit)) ∧
        NativeEq sig reg a (reg.apply (sig.add op) (p, r, PUnit.unit)) ∧
        NativeEq sig reg rest (reg.apply (sig.add op) (q, t, PUnit.unit)) := by
  have rule := mutate profile op (reg.quote s x) (reg.quote s y)
    (reg.quote s a) (reg.quote s rest)
  constructor
  · intro input
    unfold NativeEq at input
    rw [reg.quote_apply, reg.quote_apply] at input
    obtain ⟨p, q, r, t, hx, hy, ha, hr⟩ := rule.mp input
    refine ⟨p.eval reg.toAlgebra, q.eval reg.toAlgebra,
      r.eval reg.toAlgebra, t.eval reg.toAlgebra, ?_, ?_, ?_, ?_⟩
    · simpa only [NativeEq, reg.quote_apply, Args.quote, reg.quote_eval] using hx
    · simpa only [NativeEq, reg.quote_apply, Args.quote, reg.quote_eval] using hy
    · simpa only [NativeEq, reg.quote_apply, Args.quote, reg.quote_eval] using ha
    · simpa only [NativeEq, reg.quote_apply, Args.quote, reg.quote_eval] using hr
  · rintro ⟨p, q, r, t, hx, hy, ha, hr⟩
    unfold NativeEq
    rw [reg.quote_apply, reg.quote_apply]
    apply rule.mpr
    refine ⟨reg.quote s p, reg.quote s q, reg.quote s r, reg.quote s t, ?_, ?_, ?_, ?_⟩
    · simpa only [NativeEq, reg.quote_apply, Args.quote] using hx
    · simpa only [NativeEq, reg.quote_apply, Args.quote] using hy
    · simpa only [NativeEq, reg.quote_apply, Args.quote] using ha
    · simpa only [NativeEq, reg.quote_apply, Args.quote] using hr

/-! ### General native cancellation and exchange

These are semantic rules for arbitrary registered constructors. Exchange is a
useful derived two-case rule, not the complete finite-sharing search procedure.
Payload equality remains structural equality; rigid reflection is optional.
-/

theorem cancel_native (profile : Profile sig) (reg : Registration sig) {s}
    (op : sig.ACUOp s) (a x y : reg.Carrier s) :
    NativeEq sig reg (reg.apply (sig.add op) (a, x, PUnit.unit))
      (reg.apply (sig.add op) (a, y, PUnit.unit)) ↔ NativeEq sig reg x y := by
  unfold NativeEq
  rw [reg.quote_apply, reg.quote_apply]
  exact cancel profile op _ _ _

/-- Lift Exchange without exposing the internal quotient or tree syntax. -/
theorem exchange_native (profile : Profile sig) (reg : Registration sig) {s}
    (op : sig.ACUOp s) (a b x y : reg.Carrier s)
    (ha : mass profile (reg.quote s a) = 1)
    (hb : mass profile (reg.quote s b) = 1) :
    NativeEq sig reg (reg.apply (sig.add op) (a, x, PUnit.unit))
      (reg.apply (sig.add op) (b, y, PUnit.unit)) ↔
      (NativeEq sig reg a b ∧ NativeEq sig reg x y) ∨
      ∃ n : reg.Carrier s,
        NativeEq sig reg x (reg.apply (sig.add op) (b, n, PUnit.unit)) ∧
        NativeEq sig reg y (reg.apply (sig.add op) (a, n, PUnit.unit)) := by
  have rule := exchange profile op (reg.quote s a) (reg.quote s b)
    (reg.quote s x) (reg.quote s y) ha hb
  constructor
  · intro input
    unfold NativeEq at input
    rw [reg.quote_apply, reg.quote_apply] at input
    rcases rule.mp input with matched | ⟨n, hx, hy⟩
    · exact .inl matched
    · refine .inr ⟨n.eval reg.toAlgebra, ?_, ?_⟩
      · simpa only [NativeEq, reg.quote_apply, Args.quote, reg.quote_eval] using hx
      · simpa only [NativeEq, reg.quote_apply, Args.quote, reg.quote_eval] using hy
  · intro output
    unfold NativeEq
    rw [reg.quote_apply, reg.quote_apply]
    rcases output with matched | ⟨n, hx, hy⟩
    · exact rule.mpr (.inl matched)
    · apply rule.mpr (.inr ⟨reg.quote s n, ?_, ?_⟩)
      · simpa only [NativeEq, reg.quote_apply, Args.quote] using hx
      · simpa only [NativeEq, reg.quote_apply, Args.quote] using hy

/-! ## General substitution and coverage data

An answer is now an explicit, many-sorted substitution, not a family tag.
`parameters` lists its FRESH variables; `images` gives one term for EVERY input.
Repeated occurrences refer to the same typed variable. An absent/empty sort
does not require a dummy inhabitant: valuations are finite native argument tuples.

The generic coverage leaf is the usual instantiation rule:

  reference images τ =B proposed images σβ
  ======================================== Factor
         Instances(τ) ⊆ Instances(σ)

β maps σ's fresh parameters into τ's parameter context. It is explicit finite
syntax, not a Lean function or a semantic axiom. Equality derivations are also
finite constructor data. A coverage certificate chooses an answer INDEX for
each reference branch; it works for any number/shape of proposed substitutions.

  original equation ⇒ some reference branch
  every reference branch factors through a proposed answer
  every proposed answer solves the original equation
  ======================================================= Exact
  original equation ⇔ some proposed answer

The first premise is still supplied by the proved splitting/decomposition rules.
Factor does NOT magically certify that all original solutions were enumerated.
No new equality is exposed: every metatheorem concludes in registered NativeEq.
-/
namespace Substitution

inductive Variable : List Sorts → Sorts → Type where
  | here {s ss} : Variable (s :: ss) s
  | there {s t ss} : Variable ss s → Variable (t :: ss) s
  deriving DecidableEq

def Variable.eval {C : Sorts → Type} {Γ s} : Variable Γ s → Args C Γ → C s
  | .here, values => values.1
  | .there v, values => v.eval values.2

mutual
  inductive Term (sig : Signature Sorts) (Γ : List Sorts) : Sorts → Type where
    | var {s} : Variable Γ s → Term sig Γ s
    | app {ss s} : sig.Symbol ss s → Terms sig Γ ss → Term sig Γ s
  inductive Terms (sig : Signature Sorts) (Γ : List Sorts) : List Sorts → Type where
    | nil : Terms sig Γ []
    | cons {s ss} : Term sig Γ s → Terms sig Γ ss → Terms sig Γ (s :: ss)
end

mutual
  def Term.eval (reg : Registration sig) {Γ s} (values : Args reg.Carrier Γ) :
      Term sig Γ s → reg.Carrier s
    | .var v => v.eval values
    | .app f args => reg.apply f (args.eval reg values)
  def Terms.eval (reg : Registration sig) {Γ ss} (values : Args reg.Carrier Γ) :
      Terms sig Γ ss → Args reg.Carrier ss
    | .nil => PUnit.unit
    | .cons a rest => (a.eval reg values, rest.eval reg values)
end

def Terms.get {Γ ss s} : Terms sig Γ ss → Variable ss s → Term sig Γ s
  | .cons a _, .here => a
  | .cons _ rest, .there v => rest.get v

def Terms.variables (Γ : List Sorts) : (Δ : List Sorts) →
    (∀ {s}, Variable Δ s → Variable Γ s) → Terms sig Γ Δ
  | [], _ => .nil
  | _ :: ss, rename => .cons (.var (rename .here))
      (Terms.variables Γ ss (fun v => rename (.there v)))

def Terms.identity (Γ : List Sorts) : Terms sig Γ Γ := Terms.variables Γ Γ (fun v => v)

theorem Terms.variables_get {Γ Δ t} (rename : ∀ {s}, Variable Δ s → Variable Γ s)
    (v : Variable Δ t) : (Terms.variables Γ Δ rename : Terms sig Γ Δ).get v = .var (rename v) := by
  induction v with
  | here => rfl
  | there v ih => exact ih (fun v => rename (.there v))

theorem variables_eval (reg : Registration sig) {Γ Δ}
    (rename : ∀ {s}, Variable Δ s → Variable Γ s)
    (old : Args reg.Carrier Δ) (fresh : Args reg.Carrier Γ)
    (same : ∀ {s} (v : Variable Δ s), (rename v).eval fresh = v.eval old) :
    (Terms.variables Γ Δ rename : Terms sig Γ Δ).eval reg fresh = old := by
  induction Δ with
  | nil => cases old; rfl
  | cons s ss ih =>
    exact Prod.ext (same .here) (ih (fun v => rename (.there v)) old.2
      (fun v => same (.there v)))

mutual
  def Term.subst {Γ Δ s} (images : Terms sig Δ Γ) : Term sig Γ s → Term sig Δ s
    | .var v => images.get v
    | .app f args => .app f (args.subst images)
  def Terms.subst {Γ Δ ss} (terms : Terms sig Γ ss) (images : Terms sig Δ Γ) : Terms sig Δ ss :=
    match terms with
    | .nil => .nil
    | .cons a rest => .cons (a.subst images) (rest.subst images)
end

theorem Variable.eval_get (reg : Registration sig) {Γ Δ s} (v : Variable Γ s)
    (images : Terms sig Δ Γ) (values : Args reg.Carrier Δ) :
    v.eval (images.eval reg values) = (images.get v).eval reg values := by
  induction v with
  | here => cases images; rfl
  | there v ih => cases images with | cons a rest => exact ih rest

theorem Term.eval_subst (reg : Registration sig) {Γ Δ s} (term : Term sig Γ s)
    (images : Terms sig Δ Γ) (values : Args reg.Carrier Δ) :
    (term.subst images).eval reg values = term.eval reg (images.eval reg values) := by
  refine Term.rec
    (motive_1 := fun {s} a => (a.subst images).eval reg values = a.eval reg (images.eval reg values))
    (motive_2 := fun {ss} as => (as.subst images).eval reg values = as.eval reg (images.eval reg values))
    ?_ ?_ ?_ ?_ term
  · intro s v; exact (Variable.eval_get reg v images values).symm
  · intro ss s f args ih; exact congrArg (reg.apply f) ih
  · rfl
  · intro s ss a rest ha hr; simp only [Terms.subst, Terms.eval, ha, hr]

theorem Terms.eval_subst (reg : Registration sig) {Γ Δ ss} (terms : Terms sig Γ ss)
    (images : Terms sig Δ Γ) (values : Args reg.Carrier Δ) :
    (terms.subst images).eval reg values = terms.eval reg (images.eval reg values) := by
  refine Terms.rec
    (motive_1 := fun {_} _ => True)
    (motive_2 := fun {ss} as => (as.subst images).eval reg values = as.eval reg (images.eval reg values))
    ?_ ?_ ?_ ?_ terms
  · intros; trivial
  · intros; trivial
  · rfl
  · intro s ss a rest _ hr
    simp only [Terms.subst, Terms.eval, Term.eval_subst, hr]

def add {Γ s} (op : sig.ACUOp s) (a b : Term sig Γ s) : Term sig Γ s :=
  .app (sig.add op) (.cons a (.cons b .nil))
def zero {Γ s} (op : sig.ACUOp s) : Term sig Γ s := .app (sig.zero op) .nil

def copies {Γ s} (op : sig.ACUOp s) : Nat → Term sig Γ s → Term sig Γ s
  | 0, _ => zero op
  | k + 1, a => add op a (copies op k a)

theorem copies_subst {Γ Δ s} (op : sig.ACUOp s) (k : Nat) (a : Term sig Γ s)
    (images : Terms sig Δ Γ) :
    (copies op k a).subst images = copies op k (a.subst images) := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [copies, add, Term.subst, Terms.subst, ih]

theorem copies_eval (reg : Registration sig) {Γ s} (op : sig.ACUOp s)
    (k : Nat) (a : Term sig Γ s) (values : Args reg.Carrier Γ) :
    (copies op k a).eval reg values = nativeRepeat reg op k (a.eval reg values) := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [copies, add, Term.eval, Terms.eval, nativeRepeat, ih]

/-! ### Generated typed finite-sharing substitution

Slots is a finite selection table over the ORIGINAL sorted context. take selects
a variable of the designated bag sort; skip preserves any sort. Each variable
is visited once, so repetitions are coefficients, not duplicated selections.
The generated scope prepends one shared bag parameter per canonical support.
Unselected variables and inactive selected variables retain their old indices.
No sort-equality oracle or semantic proof field is needed in a dumped selection.
-/
namespace Sharing

inductive Slots (s : Sorts) : List Sorts → Nat → Type where
  | nil : Slots s [] 0
  | skip {t Γ n} : Slots s Γ n → Slots s (t :: Γ) n
  | take {Γ n} : Slots s Γ n → Slots s (s :: Γ) (n + 1)

def Slots.variable {s} : {Γ : List Sorts} → {n : Nat} → Slots s Γ n → Fin n → Variable Γ s
  | _, _, .nil, i => Fin.elim0 i
  | _, _, .skip rest, i => .there (rest.variable i)
  | _, _, .take rest, i => Fin.cases .here (fun j => .there (rest.variable j)) i

def Slots.replace {s Δ} : {Γ : List Sorts} → {n : Nat} → Slots s Γ n →
    (Fin n → Term sig Δ s) → Terms sig Δ Γ → Terms sig Δ Γ
  | _, _, .nil, _, .nil => .nil
  | _, _, .skip rest, replacement, .cons a tail => .cons a (rest.replace replacement tail)
  | _, _, .take rest, replacement, .cons _ tail =>
      .cons (replacement 0) (rest.replace (fun i => replacement i.succ) tail)

theorem Slots.get_replace {s Γ n Δ} (slots : Slots s Γ n)
    (replacement : Fin n → Term sig Δ s) (others : Terms sig Δ Γ) (i : Fin n) :
    (slots.replace replacement others).get (slots.variable i) = replacement i := by
  induction slots with
  | nil => exact Fin.elim0 i
  | skip rest ih => cases others with | cons a tail => exact ih replacement tail i
  | take rest ih =>
    cases others with
    | cons a tail => exact Fin.cases rfl (fun j => ih _ tail j) i

def weaken (s : Sorts) : (k : Nat) → {Γ : List Sorts} → {t : Sorts} →
    Variable Γ t → Variable (List.replicate k s ++ Γ) t
  | 0, _, _, v => v
  | k + 1, _, _, v => .there (weaken s k v)

def parameter {Γ} (s : Sorts) : (k : Nat) → Fin k → Variable (List.replicate k s ++ Γ) s
  | 0, i => Fin.elim0 i
  | k + 1, i => Fin.cases .here (fun j => .there (parameter s k j)) i

def extend {C : Sorts → Type} {Γ s} : {k : Nat} →
    (Fin k → C s) → Args C Γ → Args C (List.replicate k s ++ Γ)
  | 0, _, values => values
  | _ + 1, parameters, values => (parameters 0, extend (fun i => parameters i.succ) values)

theorem weaken_eval {C : Sorts → Type} {Γ s t k} (v : Variable Γ t)
    (parameters : Fin k → C s) (values : Args C Γ) :
    (weaken s k v).eval (extend parameters values) = v.eval values := by
  induction k with
  | zero => rfl
  | succ k ih => exact ih (fun i => parameters i.succ)

theorem parameter_eval {C : Sorts → Type} {Γ s k} (i : Fin k)
    (parameters : Fin k → C s) (values : Args C Γ) :
    (parameter (Γ := Γ) s k i).eval (extend parameters values) = parameters i := by
  induction k with
  | zero => exact Fin.elim0 i
  | succ k ih => exact Fin.cases rfl (fun j => ih j (fun i => parameters i.succ)) i

def lift {Γ s} (k : Nat) : Terms sig (List.replicate k s ++ Γ) Γ :=
  Terms.variables _ Γ (weaken s k)

theorem lift_eval (reg : Registration sig) {Γ s k} (parameters : Fin k → reg.Carrier s)
    (values : Args reg.Carrier Γ) :
    (lift (sig := sig) (Γ := Γ) (s := s) k).eval reg (extend parameters values) = values :=
  variables_eval reg _ values _ (fun v => weaken_eval v parameters values)

def sum {Γ s} (op : sig.ACUOp s) : {n : Nat} → FiniteSharing.Vector n →
    (Fin n → Term sig Γ s) → Term sig Γ s
  | 0, _, _ => zero op
  | _ + 1, coeff, values => add op (copies op (coeff 0) (values 0))
      (sum op (fun i => coeff i.succ) (fun i => values i.succ))

theorem sum_quote (reg : Registration sig) {Γ s n} (op : sig.ACUOp s)
    (coeff : FiniteSharing.Vector n) (terms : Fin n → Term sig Γ s) (values : Args reg.Carrier Γ) :
    reg.quote s ((sum op coeff terms).eval reg values) =
      FiniteSharing.bagSum op coeff (fun i => reg.quote s ((terms i).eval reg values)) := by
  induction n with
  | zero =>
    simp only [sum, zero, Term.eval, Terms.eval, reg.quote_apply, Args.quote, FiniteSharing.bagSum]
    rfl
  | succ n ih =>
    simp only [sum, add, Term.eval, Terms.eval, copies_eval, reg.quote_apply, Args.quote,
      quote_nativeRepeat, FiniteSharing.bagSum, ih]
    rfl

theorem sum_eval (reg : Registration sig) {Γ s n} (op : sig.ACUOp s)
    (coeff : FiniteSharing.Vector n) (terms : Fin n → Term sig Γ s) (values : Args reg.Carrier Γ) :
    (sum op coeff terms).eval reg values = nativeBagSum reg op coeff (fun i => (terms i).eval reg values) :=
  (reg.eval_quote _ _).symm.trans (congrArg (fun tree => tree.eval reg.toAlgebra)
    (sum_quote reg op coeff terms values))

def replacement {Γ s n} (op : sig.ACUOp s) (slots : Slots s Γ n)
    (left right : FiniteSharing.Vector n) (generators : List (FiniteSharing.Vector n)) :
    Fin n → Term sig (List.replicate generators.length s ++ Γ) s := fun i =>
  if left i = 0 ∧ right i = 0 then .var (weaken s generators.length (slots.variable i))
  else sum op (fun j => generators.get j i) (fun j => .var (parameter s generators.length j))

def substitution {Γ s n} (op : sig.ACUOp s) (slots : Slots s Γ n)
    (left right : FiniteSharing.Vector n) (generators : List (FiniteSharing.Vector n)) :
    Terms sig (List.replicate generators.length s ++ Γ) Γ :=
  slots.replace (replacement op slots left right generators) (lift generators.length)

theorem Slots.replace_congr (reg : Registration sig) {Γ s n Δ} (slots : Slots s Γ n)
    (replacement : Fin n → Term sig Δ s) (others : Terms sig Δ Γ)
    (values : Args reg.Carrier Γ) (fresh : Args reg.Carrier Δ)
    (preserved : ArgsRel (fun t => NativeEq sig reg (s := t)) Γ values (others.eval reg fresh))
    (selected : ∀ i, NativeEq sig reg ((slots.variable i).eval values) ((replacement i).eval reg fresh)) :
    ArgsRel (fun t => NativeEq sig reg (s := t)) Γ values
      ((slots.replace replacement others).eval reg fresh) := by
  induction slots with
  | nil => trivial
  | skip rest ih =>
    cases others with
    | cons a tail => exact ⟨preserved.1, ih replacement tail values.2 preserved.2
        (fun i => selected i)⟩
  | take rest ih =>
    cases others with
    | cons a tail => exact ⟨selected 0, ih (fun i => replacement i.succ) tail values.2 preserved.2
        (fun i => selected i.succ)⟩

theorem replacement_eval (reg : Registration sig) {Γ s n} (op : sig.ACUOp s) (slots : Slots s Γ n)
    (left right : FiniteSharing.Vector n) (generators : List (FiniteSharing.Vector n))
    (fresh : Args reg.Carrier (List.replicate generators.length s ++ Γ)) (i : Fin n) :
    ((replacement op slots left right generators) i).eval reg fresh =
      nativeSharingImages reg op left right generators
        (fun j => (parameter s generators.length j).eval fresh)
        (fun j => (weaken s generators.length (slots.variable j)).eval fresh) i := by
  unfold replacement nativeSharingImages FiniteSharing.sharingImages
  split
  · exact (reg.eval_quote _ _).symm
  · exact sum_eval reg op _ _ fresh

end Sharing

/- Internal finite equality traces. These are DATA, not arbitrary Lean proofs.
Their constructors mirror ordinary ACU/congruence rules in a Maude dump. -/
mutual
  inductive Equality (sig : Signature Sorts) (Γ : List Sorts) :
      {s : Sorts} → Term sig Γ s → Term sig Γ s → Type where
    | refl {s} (a : Term sig Γ s) : Equality sig Γ a a
    | symm {s} {a b : Term sig Γ s} : Equality sig Γ a b → Equality sig Γ b a
    | trans {s} {a b c : Term sig Γ s} :
        Equality sig Γ a b → Equality sig Γ b c → Equality sig Γ a c
    | congr {ss s} (f : sig.Symbol ss s) {a b : Terms sig Γ ss} :
        Equalities sig Γ a b → Equality sig Γ (.app f a) (.app f b)
    | comm {s} (op : sig.ACUOp s) (a b : Term sig Γ s) :
        Equality sig Γ (add op a b) (add op b a)
    | assoc {s} (op : sig.ACUOp s) (a b c : Term sig Γ s) :
        Equality sig Γ (add op (add op a b) c) (add op a (add op b c))
    | unit {s} (op : sig.ACUOp s) (a : Term sig Γ s) :
        Equality sig Γ (add op (zero op) a) a
  inductive Equalities (sig : Signature Sorts) (Γ : List Sorts) :
      {ss : List Sorts} → Terms sig Γ ss → Terms sig Γ ss → Type where
    | nil : Equalities sig Γ .nil .nil
    | cons {s ss} {a b : Term sig Γ s} {as bs : Terms sig Γ ss} :
        Equality sig Γ a b → Equalities sig Γ as bs →
        Equalities sig Γ (.cons a as) (.cons b bs)
end

theorem apply_congr (reg : Registration sig) {ss s} (f : sig.Symbol ss s)
    {a b : Args reg.Carrier ss}
    (h : ArgsRel (fun s => NativeEq sig reg (s := s)) ss a b) :
    NativeEq sig reg (reg.apply f a) (reg.apply f b) := by
  unfold NativeEq
  rw [reg.quote_apply, reg.quote_apply]
  exact .congr f ((quote_args_iff reg a b).mpr h)

theorem Equality.sound (reg : Registration sig) {Γ s} {a b : Term sig Γ s}
    (proof : Equality sig Γ a b) (values : Args reg.Carrier Γ) :
    NativeEq sig reg (a.eval reg values) (b.eval reg values) := by
  refine Equality.rec
    (motive_1 := fun {s} a b _ => NativeEq sig reg (a.eval reg values) (b.eval reg values))
    (motive_2 := fun {ss} as bs _ =>
      ArgsRel (fun s => NativeEq sig reg (s := s)) ss (as.eval reg values) (bs.eval reg values))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ proof
  · intro s a; exact .refl _
  · intro s a b h ih; exact .symm ih
  · intro s a b c h k ih ik; exact .trans ih ik
  · intro ss s f as bs h ih; exact apply_congr reg f ih
  · intro s op a b; exact native_comm reg op _ _
  · intro s op a b c
    simp only [NativeEq, Term.eval, Terms.eval, add, reg.quote_apply, Args.quote]
    exact .assoc op _ _ _
  · intro s op a; exact native_unit reg op _
  · trivial
  · intro s ss a b as bs h k ih ik; exact ⟨ih, ik⟩

theorem Equalities.sound (reg : Registration sig) {Γ ss} {a b : Terms sig Γ ss}
    (proof : Equalities sig Γ a b) (values : Args reg.Carrier Γ) :
    ArgsRel (fun s => NativeEq sig reg (s := s)) ss (a.eval reg values) (b.eval reg values) :=
  match proof with
  | .nil => True.intro
  | .cons h rest => ⟨h.sound reg values, rest.sound reg values⟩

/-- Derived equality rule: A+(B+R) =B B+(A+R). This is just a finite
Assoc/Comm/Congruence derivation; it knows no constructor names or variable IDs. -/
def Equality.swap_right {Γ s} (op : sig.ACUOp s) (a b rest : Term sig Γ s) :
    Equality sig Γ (add op a (add op b rest)) (add op b (add op a rest)) :=
  .trans (.symm (.assoc op a b rest))
    (.trans (.congr (sig.add op) (.cons (.comm op a b) (.cons (.refl rest) .nil)))
      (.assoc op b a rest))

/-- Tail-first presentation of the same adjacent-head exchange. -/
def Equality.exchange_tail {Γ s} (op : sig.ACUOp s) (a b rest : Term sig Γ s) :
    Equality sig Γ (add op a (add op rest b)) (add op b (add op rest a)) :=
  .trans (.congr (sig.add op) (.cons (.refl a) (.cons (.comm op rest b) .nil)))
    (.trans
      (.swap_right op a b rest)
      (.congr (sig.add op) (.cons (.refl b) (.cons (.comm op a rest) .nil))))

/-- The four-piece ACU equality used by Mutate, derived from the SAME small
equality proof system. No Diophantine reasoning or free-atom dictionary. -/
def Equality.matrix {Γ s} (op : sig.ACUOp s) (a b c d : Term sig Γ s) :
    Equality sig Γ (add op (add op a b) (add op c d)) (add op (add op a c) (add op b d)) :=
  .trans (.assoc op a b (add op c d))
    (.trans (.congr (sig.add op) (.cons (.refl a) (.cons (.swap_right op b c d) .nil)))
      (.symm (.assoc op a c (add op b d))))

def Equalities.refl {Γ ss} (terms : Terms sig Γ ss) : Equalities sig Γ terms terms :=
  match terms with
  | .nil => .nil
  | .cons a rest => .cons (.refl a) (.refl rest)

/-- Derived finite congruence trace: repeat a checked equality k times. This
constructs ordinary proof DATA; it performs no multiplicity search or counting. -/
def Equality.copies {Γ s} (op : sig.ACUOp s) (k : Nat) {a b : Term sig Γ s}
    (proof : Equality sig Γ a b) : Equality sig Γ (copies op k a) (copies op k b) :=
  match k with
  | 0 => .refl (zero op)
  | k + 1 => .congr (sig.add op) (.cons proof (.cons (.copies op k proof) .nil))

/-- Generated equality DATA for any number of copies of the unit. -/
def Equality.copies_zero {Γ s} (op : sig.ACUOp s) : (k : Nat) →
    Equality sig Γ (Substitution.copies op k (zero op)) (zero op)
  | 0 => .refl _
  | k + 1 => .trans (.unit op _) (.copies_zero op k)

def Equality.sum_zero {Γ s} (op : sig.ACUOp s) : {n : Nat} → (coeff : FiniteSharing.Vector n) →
    Equality sig Γ (Sharing.sum op coeff (fun _ => zero op)) (zero op)
  | 0, _ => .refl _
  | _ + 1, coeff => .trans (.congr (sig.add op)
      (.cons (.copies_zero op (coeff 0))
        (.cons (.sum_zero op (fun i => coeff i.succ)) .nil))) (.unit op _)

/-- Finite soundness trace for a chosen coefficient-one supplier. This only
builds Congruence/Unit/Comm traces; it does not perform proof search. -/
def Equality.sum_choice {Γ s} (op : sig.ACUOp s) (target : Term sig Γ s) :
    {n : Nat} → (coeff : FiniteSharing.Vector n) → (j : Fin n) → coeff j = 1 →
    Equality sig Γ (Sharing.sum op coeff (fun i => if i = j then target else zero op)) target
  | 0, _, j, _ => Fin.elim0 j
  | _ + 1, coeff, j, degree =>
      Fin.cases (motive := fun j => coeff j = 1 →
        Equality sig Γ (Sharing.sum op coeff (fun i => if i = j then target else zero op)) target)
        (fun degree => by
          simp only [Sharing.sum, if_true, Fin.succ_ne_zero, if_false, degree, Substitution.copies]
          exact .trans (.congr (sig.add op)
            (.cons (.trans (.comm op target _) (.unit op target))
              (.cons (.sum_zero op (fun i => coeff i.succ)) .nil)))
            (.trans (.comm op target _) (.unit op target)))
        (fun j degree => by
          simp only [Sharing.sum, Ne.symm (Fin.succ_ne_zero j), if_false, Fin.succ_inj]
          exact .trans (.congr (sig.add op)
            (.cons (.copies_zero op (coeff 0))
              (.cons (.sum_choice op target (fun i => coeff i.succ) j degree) .nil)))
            (.unit op target)) j degree

/-- General substitution/congruence rule. The rewrite is a theorem about
syntax, not an extra equality assumption or problem-specific proof lemma. -/
def Equality.copies_substitution {Γ Δ s} (op : sig.ACUOp s) (k : Nat)
    (a b : Term sig Γ s) (images : Terms sig Δ Γ)
    (proof : Equality sig Δ (a.subst images) (b.subst images)) :
    Equality sig Δ ((Substitution.copies op k a).subst images)
      ((Substitution.copies op k b).subst images) := by
  rw [copies_subst, copies_subst]
  exact .copies op k proof

theorem args_trans (reg : Registration sig) {ss} {a b c : Args reg.Carrier ss}
    (h : ArgsRel (fun s => NativeEq sig reg (s := s)) ss a b)
    (k : ArgsRel (fun s => NativeEq sig reg (s := s)) ss b c) :
    ArgsRel (fun s => NativeEq sig reg (s := s)) ss a c := by
  induction ss with
  | nil => trivial
  | cons s ss ih => exact ⟨.trans h.1 k.1, ih h.2 k.2⟩

theorem args_refl (reg : Registration sig) {Γ} (values : Args reg.Carrier Γ) :
    ArgsRel (fun s => NativeEq sig reg (s := s)) Γ values values := by
  induction Γ with
  | nil => trivial
  | cons s ss ih => exact ⟨.refl _, ih values.2⟩

structure Answer (sig : Signature Sorts) (inputs : List Sorts) where
  parameters : List Sorts
  images : Terms sig parameters inputs

def Answer.Holds (reg : Registration sig) {inputs} (answer : Answer sig inputs)
    (values : Args reg.Carrier inputs) : Prop :=
  ∃ fresh : Args reg.Carrier answer.parameters,
    ArgsRel (fun s => NativeEq sig reg (s := s)) inputs values (answer.images.eval reg fresh)

def Solutions (reg : Registration sig) {inputs} (proposed : List (Answer sig inputs))
    (values : Args reg.Carrier inputs) : Prop :=
  ∃ answer, answer ∈ proposed ∧ answer.Holds reg values

/-- A target answer may have different parameters, order, or number of bindings.
The entire input-image vector is checked; no field/correlation is discarded. -/
structure Factor {inputs} (source target : Answer sig inputs) where
  parameters : Terms sig source.parameters target.parameters
  images : Equalities sig source.parameters source.images (target.images.subst parameters)

theorem Factor.sound (reg : Registration sig) {inputs} {source target : Answer sig inputs}
    (factor : Factor source target) {values} (input : source.Holds reg values) :
    target.Holds reg values := by
  rcases input with ⟨fresh, images⟩
  refine ⟨factor.parameters.eval reg fresh, ?_⟩
  have matched := factor.images.sound reg fresh
  rw [Terms.eval_subst] at matched
  exact args_trans reg images matched

/-- A finite list of answer-indexed coverage leaves. No semantic proof fields,
family labels, unifier search, or problem-specific constructors. Fin's bound is
a syntactic index check, discharged by the kernel when a dump is reconstructed. -/
inductive Coverage {inputs : List Sorts} (proposed : List (Answer sig inputs)) : List (Answer sig inputs) → Type where
  | nil : Coverage proposed []
  | cons {source rest} (index : Fin proposed.length)
      (factor : Factor source (proposed.get index)) (tail : Coverage proposed rest) :
      Coverage proposed (source :: rest)

theorem Coverage.sound (reg : Registration sig) {inputs}
    {proposed reference : List (Answer sig inputs)} (proof : Coverage proposed reference)
    {values} : Solutions reg reference values → Solutions reg proposed values := by
  induction proof with
  | nil => rintro ⟨_, impossible, _⟩; cases impossible
  | @cons source rest index factor tail ih =>
      rintro ⟨answer, member, input⟩
      rcases List.mem_cons.mp member with same | member
      · cases same
        exact ⟨_, List.get_mem _ _, factor.sound reg input⟩
      · exact ih ⟨answer, member, input⟩

structure Problem (sig : Signature Sorts) (inputs : List Sorts) where
  sort : Sorts
  left : Term sig inputs sort
  right : Term sig inputs sort

def Problem.Holds (reg : Registration sig) {inputs} (problem : Problem sig inputs)
    (values : Args reg.Carrier inputs) : Prop :=
  NativeEq sig reg (problem.left.eval reg values) (problem.right.eval reg values)

theorem Variable.eval_congr (reg : Registration sig) {Γ s} (v : Variable Γ s)
    {a b : Args reg.Carrier Γ}
    (h : ArgsRel (fun s => NativeEq sig reg (s := s)) Γ a b) :
    NativeEq sig reg (v.eval a) (v.eval b) := by
  induction v with
  | here => exact h.1
  | there v ih => exact ih h.2

theorem Term.eval_congr (reg : Registration sig) {Γ s} (term : Term sig Γ s)
    {a b : Args reg.Carrier Γ}
    (h : ArgsRel (fun s => NativeEq sig reg (s := s)) Γ a b) :
    NativeEq sig reg (term.eval reg a) (term.eval reg b) := by
  refine Term.rec
    (motive_1 := fun {s} term => NativeEq sig reg (term.eval reg a) (term.eval reg b))
    (motive_2 := fun {ss} terms =>
      ArgsRel (fun s => NativeEq sig reg (s := s)) ss (terms.eval reg a) (terms.eval reg b))
    ?_ ?_ ?_ ?_ term
  · intro s v; exact v.eval_congr reg h
  · intro ss s f args ih; exact apply_congr reg f ih
  · trivial
  · intro s ss first rest ih ir; exact ⟨ih, ir⟩

theorem Terms.eval_congr (reg : Registration sig) {Γ ss} (terms : Terms sig Γ ss)
    {a b : Args reg.Carrier Γ}
    (h : ArgsRel (fun s => NativeEq sig reg (s := s)) Γ a b) :
    ArgsRel (fun s => NativeEq sig reg (s := s)) ss (terms.eval reg a) (terms.eval reg b) := by
  induction ss with
  | nil => cases terms; trivial
  | cons s ss ih =>
    cases terms with
    | cons a rest => exact ⟨a.eval_congr reg h, ih rest⟩

/-! ### BIND: typed removal of ONE live variable (CERTIFICATION.md §4.1)

     E ⊢ x =B t↑       Eσ ; ασ ⇒ proposed
     =================================== BIND
                  E ; α ⇒ proposed

Removal records a POSITION, not a variable name or an assumed sort inequality.
The replacement t lives in the reduced context Δ, so x cannot occur in it.
σ : Δ → Γ replaces x by t and retains every other input with the same sort.
The live context is strictly shorter. Evaluation/factorization stays modulo B,
including when x is a bag; no ordinary syntactic occurs failure is applied to ACU.
The rule is valid generally. Automatic equation selection remains separate.
-/
namespace Binding

inductive Removal (s : Sorts) : List Sorts → List Sorts → Type where
  | here {Γ} : Removal s (s :: Γ) Γ
  | there {t Γ Δ} : Removal s Γ Δ → Removal s (t :: Γ) (t :: Δ)

def Removal.variable {s} : {Γ Δ : List Sorts} → Removal s Γ Δ → Variable Γ s
  | _, _, .here => .here
  | _, _, .there rest => .there rest.variable

def Removal.weaken {s} : {Γ Δ : List Sorts} → Removal s Γ Δ →
    {t : Sorts} → Variable Δ t → Variable Γ t
  | _, _, .here, _, v => .there v
  | _, _, .there _, _, .here => .here
  | _, _, .there rest, _, .there v => .there (rest.weaken v)

def Removal.restrict {C : Sorts → Type} {s} : {Γ Δ : List Sorts} →
    Removal s Γ Δ → Args C Γ → Args C Δ
  | _, _, .here, values => values.2
  | _, _, .there rest, values => (values.1, rest.restrict values.2)

theorem Removal.weaken_eval {C : Sorts → Type} {s Γ Δ t} (remove : Removal s Γ Δ)
    (v : Variable Δ t) (values : Args C Γ) :
    (remove.weaken v).eval values = v.eval (remove.restrict values) := by
  induction remove with
  | here => rfl
  | there rest ih =>
    cases v with
    | here => rfl
    | there v => exact ih v values.2

def tabulate (Δ : List Sorts) : (Γ : List Sorts) →
    (∀ {s}, Variable Γ s → Term sig Δ s) → Terms sig Δ Γ
  | [], _ => .nil
  | _ :: Γ, images => .cons (images .here) (tabulate Δ Γ (fun v => images (.there v)))

theorem tabulate_get {Γ Δ s} (images : ∀ {t}, Variable Γ t → Term sig Δ t) (v : Variable Γ s) :
    (tabulate Δ Γ images).get v = images v := by
  induction v with
  | here => rfl
  | there v ih => exact ih (fun v => images (.there v))

theorem tabulate_congr (reg : Registration sig) {Γ Δ}
    (images : ∀ {s}, Variable Γ s → Term sig Δ s)
    (old : Args reg.Carrier Γ) (fresh : Args reg.Carrier Δ)
    (same : ∀ {s} (v : Variable Γ s), NativeEq sig reg (v.eval old) ((images v).eval reg fresh)) :
    ArgsRel (fun s => NativeEq sig reg (s := s)) Γ old ((tabulate Δ Γ images).eval reg fresh) := by
  induction Γ with
  | nil => trivial
  | cons s Γ ih => exact ⟨same .here, ih (fun v => images (.there v)) old.2
      (fun v => same (.there v))⟩

def Removal.replace {s Ω} : {Γ Δ : List Sorts} → Removal s Γ Δ → Term sig Ω s →
    (∀ {t}, Variable Δ t → Term sig Ω t) → ∀ {t}, Variable Γ t → Term sig Ω t
  | _, _, .here, term, _, _, .here => term
  | _, _, .here, _, others, _, .there v => others v
  | _, _, .there _, _, others, _, .here => others .here
  | _, _, .there rest, term, others, _, .there v =>
      rest.replace term (fun v => others (.there v)) v

theorem Removal.replace_variable {s Γ Δ Ω} (remove : Removal s Γ Δ) (term : Term sig Ω s)
    (others : ∀ {t}, Variable Δ t → Term sig Ω t) :
    remove.replace term others remove.variable = term := by
  induction remove with
  | here => rfl
  | there rest ih => exact ih (fun v => others (.there v))

theorem Removal.replace_weaken {s Γ Δ Ω t} (remove : Removal s Γ Δ) (term : Term sig Ω s)
    (others : ∀ {t}, Variable Δ t → Term sig Ω t) (v : Variable Δ t) :
    remove.replace term others (remove.weaken v) = others v := by
  induction remove with
  | here => rfl
  | there rest ih =>
    cases v with
    | here => rfl
    | there v => exact ih (fun v => others (.there v)) v

def Removal.embedding {s Γ Δ} (remove : Removal s Γ Δ) : Terms sig Γ Δ :=
  Terms.variables Γ Δ remove.weaken

/-- Deletion is inferred from the typed variable POSITION, at any sort. -/
def deletion {Γ : List Sorts} {s : Sorts} : Variable Γ s → Σ Δ, Removal s Γ Δ
  | .here => ⟨_, .here⟩
  | .there v => let ⟨Δ, remove⟩ := deletion v; ⟨_ :: Δ, .there remove⟩

theorem deletion_variable {Γ : List Sorts} {s : Sorts} (v : Variable Γ s) :
    (deletion v).2.variable = v := by
  induction v with
  | here => rfl
  | there v ih => exact congrArg Variable.there ih

def Removal.lowerVariable {s} : {Γ Δ : List Sorts} → Removal s Γ Δ →
    {t : Sorts} → Variable Γ t → Option (Variable Δ t)
  | _, _, .here, _, .here => none
  | _, _, .here, _, .there v => some v
  | _, _, .there _, _, .here => some .here
  | _, _, .there rest, _, .there v => (rest.lowerVariable v).map Variable.there

theorem Removal.lowerVariable_sound {s t : Sorts} {Γ Δ : List Sorts} (remove : Removal s Γ Δ)
    (v : Variable Γ t) (w : Variable Δ t) (found : remove.lowerVariable v = some w) :
    remove.weaken w = v := by
  induction remove with
  | here =>
    cases v with
    | here => cases found
    | there v => cases found; rfl
  | there rest ih =>
    cases v with
    | here => cases found; rfl
    | there v =>
      cases h : rest.lowerVariable v with
      | none => simp only [Removal.lowerVariable, h, Option.map_none] at found; cases found
      | some lower =>
        simp only [Removal.lowerVariable, h, Option.map_some, Option.some.injEq] at found
        cases found
        exact congrArg Variable.there (ih v lower h)

mutual
  def lower {s Γ Δ} (remove : Removal s Γ Δ) : {t : Sorts} → Term sig Γ t → Option (Term sig Δ t)
    | _, .var v => (remove.lowerVariable v).map Term.var
    | _, .app f args => (lowerArgs remove args).map (Term.app f)
  def lowerArgs {s Γ Δ} (remove : Removal s Γ Δ) :
      {ss : List Sorts} → Terms sig Γ ss → Option (Terms sig Δ ss)
    | _, .nil => some .nil
    | _, .cons first rest => do
        let first ← lower remove first
        let rest ← lowerArgs remove rest
        pure (.cons first rest)
end

theorem lower_sound {s Γ Δ t} (remove : Removal s Γ Δ)
    (term : Term sig Γ t) (reduced : Term sig Δ t) (found : lower remove term = some reduced) :
    reduced.subst remove.embedding = term := by
  refine Term.rec
    (motive_1 := fun {t} term => ∀ reduced : Term sig Δ t,
      lower remove term = some reduced → reduced.subst remove.embedding = term)
    (motive_2 := fun {ss} args => ∀ reduced : Terms sig Δ ss,
      lowerArgs remove args = some reduced → reduced.subst remove.embedding = args)
    ?_ ?_ ?_ ?_ term reduced found
  · intro t v reduced found
    cases h : remove.lowerVariable v with
    | none => simp only [lower, h, Option.map_none] at found; cases found
    | some w =>
      simp only [lower, h, Option.map_some, Option.some.injEq] at found
      cases found
      change (remove.embedding).get w = .var v
      rw [Removal.embedding, Terms.variables_get, remove.lowerVariable_sound v w h]
  · intro ss t f args ih reduced found
    cases h : lowerArgs remove args with
    | none => simp only [lower, h, Option.map_none] at found; cases found
    | some reducedArgs =>
      simp only [lower, h, Option.map_some, Option.some.injEq] at found
      cases found
      exact congrArg (Term.app f) (ih _ h)
  · intro reduced found
    cases found; rfl
  · intro t ss first rest hf hr reduced found
    cases hfirst : lower remove first with
    | none => simp only [lowerArgs, hfirst] at found; cases found
    | some first' =>
      cases hrest : lowerArgs remove rest with
      | none => simp only [lowerArgs, hfirst, hrest] at found; cases found
      | some rest' =>
        simp only [lowerArgs, hfirst, hrest, Option.pure_def] at found
        cases found
        simp only [Terms.subst, hf _ hfirst, hr _ hrest]

/-- Executable scoped extraction. Success returns checked reconstruction data;
failure says only that the chosen variable occurs, NOT that ACU is unsatisfiable. -/
structure Prepared {Γ s} (selected : Variable Γ s) (rhs : Term sig Γ s) where
  context : List Sorts
  remove : Removal s Γ context
  position : remove.variable = selected
  replacement : Term sig context s
  reconstruction : replacement.subst remove.embedding = rhs

def prepare {Γ s} (selected : Variable Γ s) (rhs : Term sig Γ s) : Option (Prepared selected rhs) :=
  let remove := (deletion selected).2
  match found : lower remove rhs with
  | none => none
  | some replacement => some ⟨_, remove, deletion_variable selected, replacement,
      lower_sound remove rhs replacement found⟩

def Removal.substitution {s Γ Δ} (remove : Removal s Γ Δ) (term : Term sig Δ s) : Terms sig Δ Γ :=
  tabulate Δ Γ (remove.replace term (fun v => .var v))

theorem Removal.length {s : Sorts} {Γ Δ : List Sorts} (remove : Removal s Γ Δ) :
    Γ.length = Δ.length + 1 := by
  induction remove with
  | here => rfl
  | there rest ih => simp only [List.length_cons, ih, Nat.add_assoc]

def problem {s Γ Δ} (remove : Removal s Γ Δ) (term : Term sig Δ s) : Problem sig Γ :=
  ⟨s, .var remove.variable, term.subst remove.embedding⟩

def answer {s Γ Δ} (remove : Removal s Γ Δ) (term : Term sig Δ s) : Answer sig Γ :=
  ⟨Δ, remove.substitution term⟩

theorem Removal.embedding_eval (reg : Registration sig) {s Γ Δ} (remove : Removal s Γ Δ)
    (values : Args reg.Carrier Γ) : remove.embedding.eval reg values = remove.restrict values :=
  variables_eval reg _ _ _ (fun v => remove.weaken_eval v values)

theorem Removal.embedding_substitution_eval (reg : Registration sig) {s Γ Δ}
    (remove : Removal s Γ Δ) (term : Term sig Δ s) (fresh : Args reg.Carrier Δ) :
    remove.embedding.eval reg (remove.substitution term |>.eval reg fresh) = fresh := by
  apply variables_eval reg
  intro t v
  rw [Variable.eval_get, Removal.substitution, tabulate_get, Removal.replace_weaken]
  rfl

theorem Removal.replace_congr (reg : Registration sig) {s Γ Δ Ω}
    (remove : Removal s Γ Δ) (term : Term sig Ω s)
    (others : ∀ {t}, Variable Δ t → Term sig Ω t)
    (old : Args reg.Carrier Γ) (fresh : Args reg.Carrier Ω)
    (chosen : NativeEq sig reg (remove.variable.eval old) (term.eval reg fresh))
    (same : ∀ {t} (v : Variable Δ t), NativeEq sig reg ((remove.weaken v).eval old)
      ((others v).eval reg fresh)) : ∀ {t} (v : Variable Γ t),
      NativeEq sig reg (v.eval old) ((remove.replace term others v).eval reg fresh) := by
  induction remove with
  | here =>
    intro t v
    cases v with
    | here => exact chosen
    | there v => exact same v
  | there rest ih =>
    intro t v
    cases v with
    | here => exact same .here
    | there v => exact ih (fun v => others (.there v)) old.2 chosen (fun v => same (.there v)) v

/-- Completeness: restricting the old valuation provides ONE correlated witness
for every original variable, not a separate witness per equation or field. -/
theorem complete (reg : Registration sig) {s Γ Δ} (remove : Removal s Γ Δ)
    (term : Term sig Δ s) (values : Args reg.Carrier Γ)
    (input : NativeEq sig reg (remove.variable.eval values)
      ((term.subst remove.embedding).eval reg values)) :
    ArgsRel (fun s => NativeEq sig reg (s := s)) Γ values
      ((remove.substitution term).eval reg (remove.restrict values)) := by
  apply tabulate_congr reg
  apply remove.replace_congr reg
  · simpa only [Term.eval_subst, Removal.embedding_eval] using input
  · intro t v
    rw [remove.weaken_eval]
    exact .refl _

/-- Soundness: every reduced-context valuation satisfies the binding equation. -/
theorem sound (reg : Registration sig) {s Γ Δ} (remove : Removal s Γ Δ)
    (term : Term sig Δ s) (fresh : Args reg.Carrier Δ) :
    NativeEq sig reg (remove.variable.eval ((remove.substitution term).eval reg fresh))
      ((term.subst remove.embedding).eval reg ((remove.substitution term).eval reg fresh)) := by
  rw [Variable.eval_get, Removal.substitution, tabulate_get, Removal.replace_variable,
    Term.eval_subst, ← Removal.substitution, Removal.embedding_substitution_eval]
  exact .refl _

end Binding

/-! ### Checked FREE-OCCURS (§4.1)

FreePath is a finite path through FREE constructors only. A proper occurrence
starts with at least one such constructor, e.g. n in succ(n). Native structural
equality preserves FreeDepth, while every step of the path strictly increases
that depth. Thus x =B f(...x...) is impossible along such a path.

There is deliberately no union-path constructor: P =B P+Q is not a contradiction.
The observer also handles free wrappers above ACU sorts; it does not assume all
non-bag values are rigid or replace their structural equality by literal equality.
-/
namespace FreeOccurs

def argsDepth (profile : Profile sig) (reg : Registration sig) {ss}
    (values : Args reg.Carrier ss) : Nat :=
  FreeDepth.maxArgs ((Args.quote sig reg.quote ss values).eval (FreeDepth.algebra profile))

theorem field_le (profile : Profile sig) (reg : Registration sig) {ss s}
    (field : Variable ss s) (values : Args reg.Carrier ss) :
    FreeDepth.depth profile (reg.quote s (field.eval values)) ≤ argsDepth profile reg values := by
  induction field with
  | here => exact Nat.le_max_left _ _
  | there field ih => exact Nat.le_trans (ih values.2) (Nat.le_max_right _ _)

theorem field_lt (profile : Profile sig) (reg : Registration sig) {ss s t}
    (f : sig.Symbol ss s) (free : profile.view f = .atom f)
    (field : Variable ss t) (values : Args reg.Carrier ss) :
    FreeDepth.depth profile (reg.quote t (field.eval values)) <
      FreeDepth.depth profile (reg.quote s (reg.apply f values)) := by
  rw [reg.quote_apply]
  have head : FreeDepth.depth profile (.app f (Args.quote sig reg.quote ss values)) =
      argsDepth profile reg values + 1 := by
    simp only [FreeDepth.depth, Tree.eval, FreeDepth.algebra, free, argsDepth]
  rw [head]
  exact Nat.lt_succ_of_le (field_le profile reg field values)

inductive Path (profile : Profile sig) {Γ s} (v : Variable Γ s) :
    {t : Sorts} → Term sig Γ t → Type where
  | root : Path profile v (.var v)
  | field {ss t u} (f : sig.Symbol ss t) (free : profile.view f = .atom f)
      (args : Terms sig Γ ss) (index : Variable ss u) (child : Path profile v (args.get index)) :
      Path profile v (.app f args)

theorem Path.le (profile : Profile sig) (reg : Registration sig) {Γ s t}
    (v : Variable Γ s) (term : Term sig Γ t) (path : Path profile v term)
    (values : Args reg.Carrier Γ) :
    FreeDepth.depth profile (reg.quote s (v.eval values)) ≤
      FreeDepth.depth profile (reg.quote t (term.eval reg values)) := by
  induction path with
  | root => exact Nat.le_refl _
  | field f free args index child ih =>
    apply Nat.le_of_lt (Nat.lt_of_le_of_lt ih _)
    simpa only [Variable.eval_get, Term.eval] using field_lt profile reg f free index (args.eval reg values)

inductive Proper (profile : Profile sig) {Γ s} (v : Variable Γ s) : Term sig Γ s → Type where
  | field {ss t} (f : sig.Symbol ss s) (free : profile.view f = .atom f)
      (args : Terms sig Γ ss) (index : Variable ss t) (child : Path profile v (args.get index)) :
      Proper profile v (.app f args)

theorem Proper.sound (profile : Profile sig) (reg : Registration sig) {Γ s}
    (v : Variable Γ s) (term : Term sig Γ s) (path : Proper profile v term)
    (values : Args reg.Carrier Γ) : ¬ NativeEq sig reg (v.eval values) (term.eval reg values) := by
  intro same
  cases path with
  | field f free args index child =>
    have lower := child.le profile reg v (args.get index) values
    have upper := field_lt profile reg f free index (args.eval reg values)
    rw [Variable.eval_get] at upper
    have different := Nat.ne_of_lt (Nat.lt_of_le_of_lt lower upper)
    exact different (FreeDepth.congr profile same)

/- Executable witness search. Decidable sort/position equality is syntactic
metadata, already supplied by generated finite sort tags, not semantic evidence.
Traversal is structural, with no depth bound or constructor-arity restriction. -/
mutual
  def findPath [DecidableEq Sorts] (profile : Profile sig) {Γ s}
      (v : Variable Γ s) : {t : Sorts} → (term : Term sig Γ t) → Option (Path profile v term)
    | t, .var w => if sameSort : s = t then by
        subst t
        exact if same : v = w then by subst w; exact some .root else none
      else none
    | _, .app f args => by
      cases free : profile.view f with
      | zero => exact none
      | add => exact none
      | atom f => exact (findArgs profile v args).map fun ⟨_, index, child⟩ => .field f free args index child
  def findArgs [DecidableEq Sorts] (profile : Profile sig) {Γ s}
      (v : Variable Γ s) : {ss : List Sorts} → (args : Terms sig Γ ss) →
        Option (Σ t, Σ index : Variable ss t, Path profile v (args.get index))
    | _, .nil => none
    | _, .cons first rest => match findPath profile v first with
      | some path => some ⟨_, .here, path⟩
      | none => (findArgs profile v rest).map fun ⟨t, index, path⟩ => ⟨t, .there index, path⟩
end

def findProper [DecidableEq Sorts] (profile : Profile sig) {Γ s}
    (v : Variable Γ s) : (term : Term sig Γ s) → Option (Proper profile v term)
  | .var _ => none
  | .app f args => by
    cases free : profile.view f with
    | zero => exact none
    | add => exact none
    | atom f => exact (findArgs profile v args).map fun ⟨_, index, child⟩ => .field f free args index child

end FreeOccurs

/-! ### Automatic free-equation classification

This is a TOTAL, unbounded, signature-generic selector for checked primitive
steps. It does not loop a scheduler or guess that a postponed equation is solved.
It tries safe BIND even on bag variables, but only proves FREE-OCCURS using an
actual proper free path. ACU heads are postponed for the complete bag phase.
Model annotations supply decidable sort/symbol tags automatically.
-/
namespace FreePhase

inductive Action (profile : Profile sig) {Γ} : {s : Sorts} → Term sig Γ s → Term sig Γ s → Type where
  | delete {s} (term : Term sig Γ s) : Action profile term term
  | bind {s} (v : Variable Γ s) (rhs : Term sig Γ s) (entry : Binding.Prepared v rhs) :
      Action profile (.var v) rhs
  | occurs {s} (v : Variable Γ s) (rhs : Term sig Γ s) (path : FreeOccurs.Proper profile v rhs) :
      Action profile (.var v) rhs
  | orient {s a b} (action : Action profile (s := s) b a) : Action profile a b
  | decompose {ss s} (f : sig.Symbol ss s) (free : profile.view f = .atom f)
      (a b : Terms sig Γ ss) : Action profile (.app f a) (.app f b)
  | clash {ss tt s} (f : sig.Symbol ss s) (g : sig.Symbol tt s)
      (hf : profile.view f = .atom f) (hg : profile.view g = .atom g)
      (different : (⟨ss, f⟩ : Σ us, sig.Symbol us s) ≠ ⟨tt, g⟩)
      (a : Terms sig Γ ss) (b : Terms sig Γ tt) : Action profile (.app f a) (.app g b)
  | postpone {s a b} : Action profile (s := s) a b

def classifyVariable [DecidableEq Sorts] (profile : Profile sig) {Γ s} (v : Variable Γ s)
    (rhs : Term sig Γ s) : Action profile (.var v) rhs :=
  match rhs with
  | .var w => if same : v = w then by subst w; exact .delete _
      else match Binding.prepare v (.var w) with
        | some entry => .bind v _ entry
        | none => .postpone
  | .app f args => match Binding.prepare v (.app f args) with
      | some entry => .bind v _ entry
      | none => match FreeOccurs.findProper profile v (.app f args) with
        | some path => .occurs v _ path
        | none => .postpone

def classify [DecidableEq Sorts] [∀ ss s, DecidableEq (sig.Symbol ss s)]
    (profile : Profile sig) {Γ s} (left right : Term sig Γ s) : Action profile left right :=
  match left, right with
  | .var v, rhs => classifyVariable profile v rhs
  | lhs, .var v => .orient (classifyVariable profile v lhs)
  | @Term.app _ _ _ ss _ f a, @Term.app _ _ _ tt _ g b => by
      cases hf : profile.view f with
      | zero => exact .postpone
      | add => exact .postpone
      | atom f =>
        cases hg : profile.view g with
        | zero => exact .postpone
        | add => exact .postpone
        | atom g =>
          exact if sameSorts : ss = tt then by
            cases sameSorts
            exact if sameHead : f = g then by subst g; exact .decompose f hf a b
            else .clash f g hf hg (fun same => sameHead (eq_of_heq (Sigma.mk.inj same).2)) a b
          else .clash f g hf hg (fun same => sameSorts (Sigma.mk.inj same).1) a b

end FreePhase

namespace Sharing

def problem {Γ s n} (op : sig.ACUOp s) (slots : Slots s Γ n)
    (left right : FiniteSharing.Vector n) : Problem sig Γ :=
  ⟨s, sum op left (fun i => .var (slots.variable i)),
    sum op right (fun i => .var (slots.variable i))⟩

def answer {Γ s n} (op : sig.ACUOp s) (slots : Slots s Γ n)
    (left right : FiniteSharing.Vector n) (generators : List (FiniteSharing.Vector n)) : Answer sig Γ :=
  ⟨List.replicate generators.length s ++ Γ, substitution op slots left right generators⟩

theorem image_eval (reg : Registration sig) {Γ s n} (op : sig.ACUOp s) (slots : Slots s Γ n)
    (left right : FiniteSharing.Vector n) (generators : List (FiniteSharing.Vector n))
    (fresh : Args reg.Carrier (List.replicate generators.length s ++ Γ)) (i : Fin n) :
    (slots.variable i).eval ((substitution op slots left right generators).eval reg fresh) =
      nativeSharingImages reg op left right generators
        (fun j => (parameter s generators.length j).eval fresh)
        (fun j => (weaken s generators.length (slots.variable j)).eval fresh) i := by
  rw [Variable.eval_get]
  simp only [substitution, Slots.get_replace, replacement_eval]

/-- Completeness of the generated OPEN substitution on a MANY-SORTED context.
Original payload/configuration variables are retained; ONLY selected bag variables
are replaced. This produces one common fresh valuation for the entire image vector.
The existential proof uses the native metatheorem, not an external solver result. -/
theorem complete (profile : Profile sig) (reg : Registration sig) {Γ s n rows cols}
    (op : sig.ACUOp s) (slots : Slots s Γ n) (left right : FiniteSharing.Vector n)
    (rowLabels : Fin rows → Fin n) (colLabels : Fin cols → Fin n)
    (rowCounts : ∀ i, FiniteSharing.labelCount rowLabels i = left i)
    (colCounts : ∀ i, FiniteSharing.labelCount colLabels i = right i)
    (disjoint : FiniteSharing.Disjoint left right) (values : Args reg.Carrier Γ)
    (input : (problem op slots left right).Holds reg values) :
    (answer op slots left right (FiniteSharing.supportGenerators rowLabels colLabels)).Holds reg values := by
  have equation : NativeEq sig reg
      (nativeBagSum reg op left (fun i => (slots.variable i).eval values))
      (nativeBagSum reg op right (fun i => (slots.variable i).eval values)) := by
    simpa only [problem, Problem.Holds, sum_eval, Term.eval] using input
  obtain ⟨parameters, passthrough, images⟩ := (finiteSharing_native profile reg op left right
    rowLabels colLabels rowCounts colCounts disjoint _).mp equation
  refine ⟨extend parameters values, ?_⟩
  apply slots.replace_congr reg
  · rw [lift_eval]
    exact args_refl reg values
  · intro i
    rw [replacement_eval]
    simp only [parameter_eval, weaken_eval]
    by_cases inactive : left i = 0 ∧ right i = 0
    · simp only [nativeSharingImages, FiniteSharing.sharingImages, if_pos inactive, reg.eval_quote]
      exact .refl _
    · simpa only [nativeSharingImages, FiniteSharing.sharingImages, if_neg inactive] using images i

/-- Soundness of EVERY assignment to the generated parameter scope. No residual
structural condition or payload constraint is hidden in this unifier family. -/
theorem sound (profile : Profile sig) (reg : Registration sig) {Γ s n rows cols}
    (op : sig.ACUOp s) (slots : Slots s Γ n) (left right : FiniteSharing.Vector n)
    (rowLabels : Fin rows → Fin n) (colLabels : Fin cols → Fin n)
    (rowCounts : ∀ i, FiniteSharing.labelCount rowLabels i = left i)
    (colCounts : ∀ i, FiniteSharing.labelCount colLabels i = right i)
    (disjoint : FiniteSharing.Disjoint left right)
    (fresh : Args reg.Carrier (List.replicate (FiniteSharing.supportGenerators rowLabels colLabels).length s ++ Γ)) :
    (problem op slots left right).Holds reg
      ((substitution op slots left right (FiniteSharing.supportGenerators rowLabels colLabels)).eval reg fresh) := by
  simp only [problem, Problem.Holds, sum_eval, Term.eval, image_eval]
  apply (finiteSharing_native profile reg op left right rowLabels colLabels rowCounts colCounts disjoint _).mpr
  exact ⟨_, _, fun _ => .refl _⟩

end Sharing

/-- One finite equality trace for EACH proposed substitution. A proposal cannot
be accepted merely because other members cover the problem: junk is rejected. -/
inductive Soundness {inputs : List Sorts} : Problem sig inputs → List (Answer sig inputs) → Type where
  | nil {problem} : Soundness problem []
  | cons {problem answer rest}
      (proof : Equality sig answer.parameters
        (problem.left.subst answer.images) (problem.right.subst answer.images))
      (tail : Soundness problem rest) : Soundness problem (answer :: rest)
  | sharing {s n rows cols rest} (profile : Profile sig) (op : sig.ACUOp s)
      (slots : Sharing.Slots s inputs n) (left right : FiniteSharing.Vector n)
      (rowLabels : Fin rows → Fin n) (colLabels : Fin cols → Fin n)
      (rowCounts : ∀ i, FiniteSharing.labelCount rowLabels i = left i)
      (colCounts : ∀ i, FiniteSharing.labelCount colLabels i = right i)
      (disjoint : FiniteSharing.Disjoint left right)
      (tail : Soundness (Sharing.problem op slots left right) rest) :
      Soundness (Sharing.problem op slots left right)
        (Sharing.answer op slots left right (FiniteSharing.supportGenerators rowLabels colLabels) :: rest)
  | binding {s Δ rest} (remove : Binding.Removal s inputs Δ) (term : Term sig Δ s)
      (tail : Soundness (Binding.problem remove term) rest) :
      Soundness (Binding.problem remove term) (Binding.answer remove term :: rest)

theorem Soundness.sound (reg : Registration sig) {inputs} {problem : Problem sig inputs}
    {proposed : List (Answer sig inputs)} (proof : Soundness problem proposed) :
    ∀ values, Solutions reg proposed values → problem.Holds reg values := by
  induction proof with
  | nil => rintro _ ⟨_, impossible, _⟩; cases impossible
  | @cons problem answer rest equality tail ih =>
      rintro values ⟨candidate, member, fresh, images⟩
      rcases List.mem_cons.mp member with same | member
      · cases same
        have equation := equality.sound reg fresh
        rw [Term.eval_subst, Term.eval_subst] at equation
        exact .trans (problem.left.eval_congr reg images)
          (.trans equation (.symm (problem.right.eval_congr reg images)))
      · exact ih values ⟨candidate, member, fresh, images⟩
  | sharing profile op slots left right rows cols rowCounts colCounts disjoint tail ih =>
      rintro values ⟨candidate, member, fresh, images⟩
      rcases List.mem_cons.mp member with same | member
      · cases same
        have equation := Sharing.sound profile reg op slots left right rows cols rowCounts colCounts disjoint fresh
        exact .trans ((Sharing.problem op slots left right).left.eval_congr reg images)
          (.trans equation (.symm ((Sharing.problem op slots left right).right.eval_congr reg images)))
      · exact ih values ⟨candidate, member, fresh, images⟩
  | binding remove term tail ih =>
      rintro values ⟨candidate, member, fresh, images⟩
      rcases List.mem_cons.mp member with same | member
      · cases same
        exact .trans ((Binding.problem remove term).left.eval_congr reg images)
          (.trans (Binding.sound reg remove term fresh)
            (.symm ((Binding.problem remove term).right.eval_congr reg images)))
      · exact ih values ⟨candidate, member, fresh, images⟩

/-- General semantic aggregation. The supplied reference completeness must
come from semantic rule metatheorems, not a successful native unify command. -/
theorem exact_of_coverage (reg : Registration sig) {inputs} (problem : Problem sig inputs)
    (reference proposed : List (Answer sig inputs))
    (complete : ∀ values, problem.Holds reg values → Solutions reg reference values)
    (sound : Soundness problem proposed)
    (cover : Coverage proposed reference) :
    ∀ values, problem.Holds reg values ↔ Solutions reg proposed values :=
  fun values => ⟨fun h => cover.sound reg (complete values h), sound.sound reg values⟩

/-! ### General completeness trees over equation worklists

Judgement: E ; images ⇒ proposed
  Every valuation satisfying ALL equations E has its input images covered by
  one proposed answer. E retains variable INDICES, including repeated ones.

  E ⊢ a+b = c+d       E↑, a↑=p+q, b↑=r+t, c↑=p+r, d↑=q+t ; images↑ ⇒ proposed
  ========================================================================== Mutate
                             E ; images ⇒ proposed

  E ⊢ x+y = atom       E,x=0,y=atom ; images ⇒ proposed
                        E,x=atom,y=0 ; images ⇒ proposed
  ===================================================== SplitAtom
                    E ; images ⇒ proposed

  choose proposed[i] and β       E ⊢ images =B proposed[i] β
  ======================================================= EARLY-COVER
                      E ; images ⇒ proposed

These are finite DATA constructors, not proof search tactics. Mutate introduces
four fresh indices and lifts every old index uniformly. It NEVER renames two
occurrences independently. Split requires BOTH children. EARLY-COVER checks the
WHOLE original-input vector using ONE β. Its conditional derivation must hold
for EVERY solution of E; a single satisfying instance cannot close a branch.

`Derives` includes ordinary equality, free decomposition, common-bag cancellation,
and positive-multiplicity cancellation. `Complete.cover` is the answer-guided
closure rule: it need not first materialize a reference CSU or solve E completely.
Mutate/Split are optional proved derived rules, NOT the documented finite-grid
fallback or a claim of complete search control. FINITE-SHARING now uses its
proved semantic rule: a typed Slots table generates ONE correlated substitution,
and the child receives ALL residual equations and original images substituted
with it. The canonical support list is computed internally, never supplied as
an unchecked "complete" table. Soundness.sharing certifies this same generated
family. These replay constructors still do not constitute certificate search.

ATOM-CHOOSE is Complete.atom: EVERY coefficient-one index needs a child, with
all selected-component constraints added to the SAME original equation context.
ZERO is Complete.zero: one child with all positive-coefficient terms empty.
Coefficient-zero fields receive only reflexive equations. Complete.nonempty
closes a free atom =B empty contradiction. Explicit singleton terms in an atom
branch are decomposed modulo B by Derives.decompose, exposing their payloads.
BIND and PURIFY below supply scope-safe substitution/naming. An automatic
equation-processing/search schedule is still pending.
-/
namespace Worklist

def Holds (reg : Registration sig) {Γ} (eqs : List (Problem sig Γ))
    (values : Args reg.Carrier Γ) : Prop := ∀ p ∈ eqs, p.Holds reg values

mutual
  inductive Derives (profile : Profile sig) {Γ} (eqs : List (Problem sig Γ)) :
      {s : Sorts} → Term sig Γ s → Term sig Γ s → Type where
    | axiom {s a b} : Equality sig Γ (s := s) a b → Derives profile eqs a b
    | hyp (index : Fin eqs.length) : Derives profile eqs (eqs.get index).left (eqs.get index).right
    | symm {s a b} : Derives profile eqs (s := s) a b → Derives profile eqs b a
    | trans {s a b c} : Derives profile eqs (s := s) a b → Derives profile eqs b c → Derives profile eqs a c
    | congr {ss s} (f : sig.Symbol ss s) {a b : Terms sig Γ ss} :
        DerivesArgs profile eqs a b → Derives profile eqs (.app f a) (.app f b)
    | cancel {s} (op : sig.ACUOp s) (common a b : Term sig Γ s) :
        Derives profile eqs (add op common a) (add op common b) →
        Derives profile eqs a b
    | multiplicity {s} (op : sig.ACUOp s) (k : Nat) (positive : 0 < k)
        (a b : Term sig Γ s) :
        Derives profile eqs (copies op k a) (copies op k b) →
        Derives profile eqs a b
    | decompose {ss s t} (f : sig.Symbol ss s) (free : profile.view f = .atom f)
        (a b : Terms sig Γ ss) (field : Variable ss t) :
        Derives profile eqs (.app f a) (.app f b) →
        Derives profile eqs (a.get field) (b.get field)
  inductive DerivesArgs (profile : Profile sig) {Γ} (eqs : List (Problem sig Γ)) :
      {ss : List Sorts} → Terms sig Γ ss → Terms sig Γ ss → Type where
    | nil : DerivesArgs profile eqs .nil .nil
    | cons {s ss a b as bs} : Derives profile eqs (s := s) a b →
        DerivesArgs profile eqs (ss := ss) as bs → DerivesArgs profile eqs (.cons a as) (.cons b bs)
end

theorem Derives.sound (reg : Registration sig) {profile : Profile sig} {Γ eqs s a b}
    (proof : Derives profile (Γ := Γ) eqs (s := s) a b) (values : Args reg.Carrier Γ)
    (input : Holds reg eqs values) : NativeEq sig reg (a.eval reg values) (b.eval reg values) := by
  refine Derives.rec
    (motive_1 := fun {s} a b _ => NativeEq sig reg (a.eval reg values) (b.eval reg values))
    (motive_2 := fun {ss} as bs _ =>
      ArgsRel (fun s => NativeEq sig reg (s := s)) ss (as.eval reg values) (bs.eval reg values))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ proof
  · intro s a b h; exact h.sound reg values
  · intro index; exact input _ (List.get_mem _ _)
  · intro s a b h ih; exact .symm ih
  · intro s a b c h k ih ik; exact .trans ih ik
  · intro ss s f as bs h ih; exact apply_congr reg f ih
  · intro s op common a b h ih
    exact (cancel_native profile reg op _ _ _).mp ih
  · intro s op k positive a b h ih
    apply (multiplicity_native profile reg op k positive _ _).mp
    simpa only [copies_eval] using ih
  · intro ss s t f free a b field h ih
    have args := (decompose_native profile reg f free _ _).mp ih
    have selected := Variable.eval_congr reg field args
    simpa only [Variable.eval_get] using selected
  · trivial
  · intro s ss a b as bs h k ih ik; exact ⟨ih, ik⟩

theorem DerivesArgs.sound (reg : Registration sig) {profile : Profile sig} {Γ eqs ss a b}
    (proof : DerivesArgs profile (Γ := Γ) eqs (ss := ss) a b) (values : Args reg.Carrier Γ)
    (input : Holds reg eqs values) :
    ArgsRel (fun s => NativeEq sig reg (s := s)) ss (a.eval reg values) (b.eval reg values) :=
  match proof with
  | .nil => True.intro
  | .cons h rest => ⟨h.sound reg values input, rest.sound reg values input⟩

def equation {Γ s} (a b : Term sig Γ s) : Problem sig Γ := ⟨s, a, b⟩

def lift4 {Γ s} : Terms sig (s :: s :: s :: s :: Γ) Γ :=
  Terms.variables _ Γ (fun v => .there (.there (.there (.there v))))

theorem lift4_eval (reg : Registration sig) {Γ s} (p q r t : reg.Carrier s)
    (values : Args reg.Carrier Γ) :
    (lift4 (sig := sig) (Γ := Γ) (s := s)).eval (Γ := s :: s :: s :: s :: Γ)
      reg (p, q, r, t, values) = values :=
  variables_eval reg _ values _ (fun _ => rfl)

theorem identity_eval (reg : Registration sig) {Γ} (values : Args reg.Carrier Γ) :
    (Terms.identity Γ : Terms sig Γ Γ).eval reg values = values :=
  variables_eval reg _ values values (fun _ => rfl)

def liftEquations {Γ s} (eqs : List (Problem sig Γ)) : List (Problem sig (s :: s :: s :: s :: Γ)) :=
  eqs.map fun e => equation (e.left.subst lift4) (e.right.subst lift4)

def mutated {Γ s} (op : sig.ACUOp s) (a b c d : Term sig Γ s)
    (eqs : List (Problem sig Γ)) : List (Problem sig (s :: s :: s :: s :: Γ)) :=
  [equation (a.subst lift4) (add op (.var .here) (.var (.there .here))),
   equation (b.subst lift4) (add op (.var (.there (.there .here))) (.var (.there (.there (.there .here))))),
   equation (c.subst lift4) (add op (.var .here) (.var (.there (.there .here)))),
   equation (d.subst lift4) (add op (.var (.there .here)) (.var (.there (.there (.there .here)))))] ++
    liftEquations eqs

def substituteEquations {Γ Δ} (images : Terms sig Δ Γ) (eqs : List (Problem sig Γ)) :
    List (Problem sig Δ) := eqs.map fun e => equation (e.left.subst images) (e.right.subst images)

/-- The SAME image tuple transports ALL residual equations. This is generic
substitution congruence, used by both binding and finite sharing. -/
theorem substituteEquations_holds (reg : Registration sig) {Γ Δ}
    (images : Terms sig Δ Γ) (eqs : List (Problem sig Γ))
    (old : Args reg.Carrier Γ) (fresh : Args reg.Carrier Δ)
    (same : ArgsRel (fun s => NativeEq sig reg (s := s)) Γ old (images.eval reg fresh))
    (input : Holds reg eqs old) : Holds reg (substituteEquations images eqs) fresh := by
  intro e member
  obtain ⟨original, inOriginal, rfl⟩ := List.mem_map.mp member
  simp only [Problem.Holds, equation, Term.eval_subst]
  exact .trans (.symm (original.left.eval_congr reg same))
    (.trans (input original inOriginal) (original.right.eval_congr reg same))

/-! ### PURIFY: a fresh name with its retained defining equation (§4.2)

   old equation = template[A := t]       D = A =B t↑
   D, template, E↑ ; α↑ ⇒ proposed
   ================================================= PURIFY
           template[A := t], E ; α ⇒ proposed

The template is a typed expression over ONE new index A plus the old context.
Its substitution by t computes the exact original equation, so abstraction is
checked syntactically, not trusted or justified by a model-specific lemma.
Every old solution extends by A:=eval(t). Conversely D guarantees that replacing
A by t preserves template evaluation modulo B. Payload/variable sharing is kept.
The algorithm uses this general rule to name singleton occurrences, once each;
the replay rule itself cannot guarantee a scheduler avoids repeated abstraction.
-/
namespace Purification

def embedding {Γ : List Sorts} {s : Sorts} : Terms sig (s :: Γ) Γ :=
  Binding.Removal.embedding (.here : Binding.Removal s (s :: Γ) Γ)

def assignment {Γ s} (term : Term sig Γ s) : Terms sig Γ (s :: Γ) :=
  Binding.Removal.substitution .here term

def source {Γ s} (term : Term sig Γ s) (template : Problem sig (s :: Γ)) : Problem sig Γ :=
  equation (template.left.subst (assignment term)) (template.right.subst (assignment term))

def definition {Γ s} (term : Term sig Γ s) : Problem sig (s :: Γ) :=
  equation (.var .here) (term.subst embedding)

def state {Γ s} (term : Term sig Γ s) (template : Problem sig (s :: Γ))
    (rest : List (Problem sig Γ)) : List (Problem sig (s :: Γ)) :=
  definition term :: template :: substituteEquations embedding rest

theorem embedding_eval (reg : Registration sig) {Γ s} (fresh : Args reg.Carrier (s :: Γ)) :
    (embedding (sig := sig) (Γ := Γ) (s := s)).eval reg fresh = fresh.2 :=
  Binding.Removal.embedding_eval reg .here fresh

theorem assignment_eval (reg : Registration sig) {Γ s} (term : Term sig Γ s)
    (values : Args reg.Carrier Γ) :
    (assignment term).eval reg values = (term.eval reg values, values) := by
  apply Prod.ext
  · rfl
  · simpa only [assignment, Binding.Removal.embedding_eval, Binding.Removal.restrict] using
      Binding.Removal.embedding_substitution_eval reg .here term values

theorem complete (reg : Registration sig) {Γ s} (term : Term sig Γ s)
    (template : Problem sig (s :: Γ)) (rest : List (Problem sig Γ))
    (values : Args reg.Carrier Γ) (selected : (source term template).Holds reg values)
    (input : Holds reg rest values) :
    Holds reg (state term template rest) (term.eval reg values, values) := by
  intro e member
  rcases List.mem_cons.mp member with rfl | member
  · simp only [Problem.Holds, definition, equation, Term.eval, Variable.eval,
      Term.eval_subst, embedding_eval]
    exact .refl _
  rcases List.mem_cons.mp member with rfl | member
  · simpa only [source, equation, Problem.Holds, Term.eval_subst, assignment_eval] using selected
  · obtain ⟨original, inOriginal, rfl⟩ := List.mem_map.mp member
    simpa only [Problem.Holds, equation, Term.eval_subst, embedding_eval] using input original inOriginal

theorem sound (reg : Registration sig) {Γ s} (term : Term sig Γ s)
    (template : Problem sig (s :: Γ)) (fresh : Args reg.Carrier (s :: Γ))
    (named : (definition term).Holds reg fresh) (selected : template.Holds reg fresh) :
    (source term template).Holds reg fresh.2 := by
  have same : ArgsRel (fun s => NativeEq sig reg (s := s)) (s :: Γ) fresh
      ((assignment term).eval reg fresh.2) := by
    rw [assignment_eval]
    exact ⟨by simpa only [definition, equation, Problem.Holds, Term.eval, Variable.eval,
      Term.eval_subst, embedding_eval] using named, args_refl reg fresh.2⟩
  simp only [source, equation, Problem.Holds, Term.eval_subst]
  exact .trans (.symm (template.left.eval_congr reg same))
    (.trans selected (template.right.eval_congr reg same))

/-- Exactness of fresh naming, including WHOLE original valuations. It adds
neither an assumption about payload equality nor a semantic registration gap. -/
theorem exact (reg : Registration sig) {Γ s} (term : Term sig Γ s)
    (template : Problem sig (s :: Γ)) (rest : List (Problem sig Γ))
    (values : Args reg.Carrier Γ) :
    Holds reg (source term template :: rest) values ↔
      ∃ fresh : Args reg.Carrier (s :: Γ),
        ArgsRel (fun s => NativeEq sig reg (s := s)) Γ values fresh.2 ∧
          Holds reg (state term template rest) fresh := by
  constructor
  · intro input
    exact ⟨(term.eval reg values, values), args_refl reg values,
      complete reg term template rest values (input _ (List.mem_cons_self))
        (fun e member => input e (List.mem_cons_of_mem _ member))⟩
  · rintro ⟨fresh, same, input⟩ e member
    have projected : Holds reg (source term template :: rest) fresh.2 := by
      intro p member
      rcases List.mem_cons.mp member with rfl | member
      · exact sound reg term template fresh (input _ List.mem_cons_self)
          (input _ (List.mem_cons_of_mem _ List.mem_cons_self))
      · have h := input _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_map.mpr ⟨p, member, rfl⟩)))
        simpa only [Problem.Holds, equation, Term.eval_subst, embedding_eval] using h
    exact .trans (e.left.eval_congr reg same)
      (.trans (projected e member) (.symm (e.right.eval_congr reg same)))

end Purification

/- Finite branch constraints. A coefficient-zero entry contributes only t=t,
so it remains a genuine passthrough rather than being silently forced empty.
Terms may include explicit singletons, whose equations then yield payload
equations by Derives.decompose. No constructor name or arity is hardcoded. -/
def zeroRequirements {Γ s n} (op : sig.ACUOp s) (coeff : FiniteSharing.Vector n)
    (terms : Fin n → Term sig Γ s) : List (Problem sig Γ) :=
  List.ofFn fun i => equation (terms i) (if coeff i = 0 then terms i else zero op)

def atomRequirements {Γ s n} (op : sig.ACUOp s) (coeff : FiniteSharing.Vector n)
    (terms : Fin n → Term sig Γ s) (target : Term sig Γ s) (chosen : Fin n) :
    List (Problem sig Γ) :=
  List.ofFn fun i => equation (terms i)
    (if coeff i = 0 then terms i else if i = chosen then target else zero op)

theorem zeroRequirements_holds (reg : Registration sig) {Γ s n} (op : sig.ACUOp s)
    (coeff : FiniteSharing.Vector n) (terms : Fin n → Term sig Γ s)
    (values : Args reg.Carrier Γ)
    (empty : ∀ i, coeff i ≠ 0 → NativeEq sig reg ((terms i).eval reg values)
      ((zero op).eval reg values)) : Holds reg (zeroRequirements op coeff terms) values := by
  intro e member
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp member
  by_cases h : coeff i = 0
  · simp only [Problem.Holds, equation, if_pos h]; exact .refl _
  · simpa only [Problem.Holds, equation, if_neg h] using empty i h

theorem atomRequirements_holds (reg : Registration sig) {Γ s n} (op : sig.ACUOp s)
    (coeff : FiniteSharing.Vector n) (terms : Fin n → Term sig Γ s)
    (target : Term sig Γ s) (chosen : Fin n) (values : Args reg.Carrier Γ)
    (same : NativeEq sig reg ((terms chosen).eval reg values) (target.eval reg values))
    (empty : ∀ i, i ≠ chosen → coeff i ≠ 0 → NativeEq sig reg ((terms i).eval reg values)
      ((zero op).eval reg values)) : Holds reg (atomRequirements op coeff terms target chosen) values := by
  intro e member
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp member
  by_cases h : coeff i = 0
  · simp only [Problem.Holds, equation, if_pos h]; exact .refl _
  · by_cases selected : i = chosen
    · subst i; simpa only [Problem.Holds, equation, if_neg h, if_true] using same
    · simpa only [Problem.Holds, equation, if_neg h, if_neg selected] using empty i selected h

inductive Complete (profile : Profile sig) {inputs} (proposed : List (Answer sig inputs)) :
    {Γ : List Sorts} → Terms sig Γ inputs → List (Problem sig Γ) → Type where
  | cover {Γ images eqs} (index : Fin proposed.length)
      (bindings : Terms sig Γ (proposed.get index).parameters)
      (derived : DerivesArgs profile eqs images ((proposed.get index).images.subst bindings)) :
      Complete profile proposed images eqs
  | bind {Γ Δ images eqs s} (remove : Binding.Removal s Γ Δ) (term : Term sig Δ s)
      (selected : Derives profile eqs (Binding.problem remove term).left
        (Binding.problem remove term).right)
      (child : Complete profile proposed (images.subst (remove.substitution term))
        (substituteEquations (remove.substitution term) eqs)) :
      Complete profile proposed images eqs
  | occurs {Γ images eqs s} (v : Variable Γ s) (rhs : Term sig Γ s)
      (path : FreeOccurs.Proper profile v rhs)
      (selected : Derives profile eqs (.var v) rhs) : Complete profile proposed images eqs
  | purify {Γ images s} (term : Term sig Γ s) (template : Problem sig (s :: Γ))
      (before after : List (Problem sig Γ))
      (child : Complete profile proposed (images.subst Purification.embedding)
        (Purification.state term template (before ++ after))) :
      Complete profile proposed images (before ++ Purification.source term template :: after)
  | atom {Γ images eqs s n ss} (op : sig.ACUOp s) (coeff : FiniteSharing.Vector n)
      (terms : Fin n → Term sig Γ s) (f : sig.Symbol ss s)
      (free : profile.view f = .atom f) (args : Terms sig Γ ss)
      (selected : Derives profile eqs (Sharing.sum op coeff terms) (.app f args))
      (children : ∀ j, coeff j = 1 → Complete profile proposed images
        (atomRequirements op coeff terms (.app f args) j ++ eqs)) :
      Complete profile proposed images eqs
  | zero {Γ images eqs s n} (op : sig.ACUOp s) (coeff : FiniteSharing.Vector n)
      (terms : Fin n → Term sig Γ s)
      (selected : Derives profile eqs (Sharing.sum op coeff terms) (zero op))
      (child : Complete profile proposed images (zeroRequirements op coeff terms ++ eqs)) :
      Complete profile proposed images eqs
  | nonempty {Γ images eqs s ss} (op : sig.ACUOp s) (f : sig.Symbol ss s)
      (free : profile.view f = .atom f) (args : Terms sig Γ ss)
      (selected : Derives profile eqs (.app f args) (zero op)) :
      Complete profile proposed images eqs
  | sharing {Γ images eqs s n rows cols} (op : sig.ACUOp s) (slots : Sharing.Slots s Γ n)
      (left right : FiniteSharing.Vector n)
      (rowLabels : Fin rows → Fin n) (colLabels : Fin cols → Fin n)
      (rowCounts : ∀ i, FiniteSharing.labelCount rowLabels i = left i)
      (colCounts : ∀ i, FiniteSharing.labelCount colLabels i = right i)
      (disjoint : FiniteSharing.Disjoint left right)
      (selected : Derives profile eqs (Sharing.problem op slots left right).left
        (Sharing.problem op slots left right).right)
      (child : Complete profile proposed
        (images.subst (Sharing.substitution op slots left right (FiniteSharing.supportGenerators rowLabels colLabels)))
        (substituteEquations (Sharing.substitution op slots left right
          (FiniteSharing.supportGenerators rowLabels colLabels)) eqs)) :
      Complete profile proposed images eqs
  | mutate {Γ images eqs s} (op : sig.ACUOp s) (a b c d : Term sig Γ s)
      (selected : Derives profile eqs (add op a b) (add op c d))
      (child : Complete profile proposed (images.subst lift4) (mutated op a b c d eqs)) :
      Complete profile proposed images eqs
  | split {Γ images eqs ss s} (op : sig.ACUOp s) (x y : Term sig Γ s)
      (f : sig.Symbol ss s) (free : profile.view f = .atom f) (args : Terms sig Γ ss)
      (selected : Derives profile eqs (add op x y) (.app f args))
      (left : Complete profile proposed images
        (equation x (zero op) :: equation y (.app f args) :: eqs))
      (right : Complete profile proposed images
        (equation x (.app f args) :: equation y (zero op) :: eqs)) :
      Complete profile proposed images eqs
  | clash {Γ images eqs ss tt s} (f : sig.Symbol ss s) (g : sig.Symbol tt s)
      (hf : profile.view f = .atom f) (hg : profile.view g = .atom g)
      (different : (⟨ss, f⟩ : Σ us, sig.Symbol us s) ≠ ⟨tt, g⟩)
      (a : Terms sig Γ ss) (b : Terms sig Γ tt)
      (selected : Derives profile eqs (.app f a) (.app g b)) :
      Complete profile proposed images eqs

/-- A typed replay boundary. The original input vector is fixed, while Γ is the
current variable scope. A rule changes this whole state, not independently
reconstructed images/equations. This is presentation data, not a new calculus. -/
structure ReplayState (sig : Signature Sorts) (inputs Γ : List Sorts) where
  images : Terms sig Γ inputs
  equations : List (Problem sig Γ)

namespace ReplayState

abbrev Certified {inputs Γ} (profile : Profile sig) (proposed : List (Answer sig inputs))
    (state : ReplayState sig inputs Γ) : Type :=
  Complete profile proposed state.images state.equations

/-- Compute the successor of a substitution rule at the SAME original inputs. -/
def substitute {inputs Γ Δ} (state : ReplayState sig inputs Γ) (bindings : Terms sig Δ Γ) :
    ReplayState sig inputs Δ :=
  ⟨state.images.subst bindings, substituteEquations bindings state.equations⟩

/-- Add rule-generated obligations without changing the original image vector. -/
def prepend {inputs Γ} (state : ReplayState sig inputs Γ) (extra : List (Problem sig Γ)) :
    ReplayState sig inputs Γ :=
  ⟨state.images, extra ++ state.equations⟩

/-- PURIFY extends the scope by exactly one variable and retains its defining
equation. The source snapshot's equation list is fixed by Complete.purify. -/
def purify {inputs Γ s} (state : ReplayState sig inputs Γ) (term : Term sig Γ s)
    (template : Problem sig (s :: Γ)) (rest : List (Problem sig Γ)) :
    ReplayState sig inputs (s :: Γ) :=
  ⟨state.images.subst Purification.embedding, Purification.state term template rest⟩

/-- A transition's computed successor is checked equal to the external snapshot
ONCE. Its already checked child is then transported. No semantic premise or
producer-correctness assumption is introduced: checked is ordinary Lean equality.
The states have the same sorted Γ; a wrong scope cannot even type this interface. -/
def accept {inputs Γ} {profile : Profile sig} {proposed : List (Answer sig inputs)}
    (expected actual : ReplayState sig inputs Γ) (checked : expected = actual)
    (child : Certified profile proposed actual) : Certified profile proposed expected :=
  Eq.mpr (congrArg (Certified profile proposed) checked) child

end ReplayState

/-- External producers may supply an explicit finite support table. Its equality
to the EXHAUSTIVE enumeration is still checked, not trusted. Keeping the child
scope/substitution in terms of this table avoids unfolding enumeration at every
dependent variable/equality in a large emitted proof. This is the SAME sharing
rule, with a proved change of presentation; no search or semantic axiom is added. -/
def Complete.sharingTable {profile : Profile sig} {inputs proposed Γ images eqs s n rows cols}
    (op : sig.ACUOp s) (slots : Sharing.Slots s Γ n)
    (left right : FiniteSharing.Vector n)
    (rowLabels : Fin rows → Fin n) (colLabels : Fin cols → Fin n)
    (rowCounts : ∀ i, FiniteSharing.labelCount rowLabels i = left i)
    (colCounts : ∀ i, FiniteSharing.labelCount colLabels i = right i)
    (disjoint : FiniteSharing.Disjoint left right)
    (selected : Derives profile eqs (Sharing.problem op slots left right).left
      (Sharing.problem op slots left right).right)
    (table : List (FiniteSharing.Vector n))
    (checked : FiniteSharing.supportGenerators rowLabels colLabels = table)
    (child : Complete profile proposed (inputs := inputs)
      (images.subst (Sharing.substitution op slots left right table))
      (substituteEquations (Sharing.substitution op slots left right table) eqs)) :
    Complete profile proposed (Γ := Γ) images eqs := by
  let motive := fun gs => Complete profile proposed
    (images.subst (Sharing.substitution op slots left right gs))
    (substituteEquations (Sharing.substitution op slots left right gs) eqs)
  exact .sharing op slots left right rowLabels colLabels rowCounts colCounts disjoint selected
    (Eq.mpr (congrArg motive checked) child)

theorem Complete.sound (reg : Registration sig) {profile : Profile sig} {inputs proposed Γ images eqs}
    (proof : Complete profile (inputs := inputs) proposed (Γ := Γ) images eqs) :
    ∀ values, Holds reg eqs values → Solutions reg proposed (images.eval reg values) := by
  induction proof with
  | cover index bindings derived =>
    intro values input
    refine ⟨_, List.get_mem _ _, bindings.eval reg values, ?_⟩
    simpa only [Terms.eval_subst] using derived.sound reg values input
  | @bind Γ Δ images eqs s remove term selected child ih =>
    intro values input
    have same := Binding.complete reg remove term values (selected.sound reg values input)
    obtain ⟨answer, member, parameters, covered⟩ := ih (remove.restrict values)
      (substituteEquations_holds reg (remove.substitution term) _ values _ same input)
    refine ⟨answer, member, parameters, ?_⟩
    rw [Terms.eval_subst] at covered
    exact args_trans reg (images.eval_congr reg same) covered
  | occurs v rhs path selected =>
    intro values input
    exact False.elim (path.sound profile reg v rhs values (selected.sound reg values input))
  | @purify Γ images s term template before after child ih =>
    intro values input
    have selected := input _ (List.mem_append.mpr (.inr List.mem_cons_self))
    have residual : Holds reg (before ++ after) values := by
      intro e member
      rcases List.mem_append.mp member with member | member
      · exact input e (List.mem_append.mpr (.inl member))
      · exact input e (List.mem_append.mpr (.inr (List.mem_cons_of_mem _ member)))
    have covered := ih (term.eval reg values, values)
      (Purification.complete reg term template _ values selected residual)
    simpa only [Terms.eval_subst, Purification.embedding_eval] using covered
  | @atom Γ images eqs s n ss op coeff terms f free args selected children ih =>
    intro values input
    have count : mass profile (reg.quote s ((Term.app f args).eval reg values)) = 1 := by
      simp [Term.eval, reg.quote_apply, mass, Tree.eval, measure, free]
    have selected := selected.sound reg values input
    rw [NativeEq, Sharing.sum_quote] at selected
    obtain ⟨j, degree, same, empty⟩ := (AtomProcessing.sum_atom profile op coeff
      (fun i => reg.quote s ((terms i).eval reg values)) _ count).mp selected
    have constraints := atomRequirements_holds reg op coeff terms (.app f args) j values
      same (fun i different positive => by
        simpa only [NativeEq, Substitution.zero, Structural.Indexed.zero,
          Term.eval, Terms.eval, reg.quote_apply, Args.quote]
          using empty i different positive)
    apply ih j degree values
    intro e member
    rcases List.mem_append.mp member with member | member
    · exact constraints e member
    · exact input e member
  | @zero Γ images eqs s n op coeff terms selected child ih =>
    intro values input
    have selected := selected.sound reg values input
    simp only [NativeEq, Sharing.sum_quote, Substitution.zero, Term.eval, Terms.eval,
      reg.quote_apply, Args.quote] at selected
    have empty := (AtomProcessing.sum_zero profile op coeff
      (fun i => reg.quote s ((terms i).eval reg values))).mp selected
    have constraints := zeroRequirements_holds reg op coeff terms values (fun i positive => by
      simpa only [NativeEq, Substitution.zero, Structural.Indexed.zero,
        Term.eval, Terms.eval, reg.quote_apply, Args.quote] using empty i positive)
    apply ih values
    intro e member
    rcases List.mem_append.mp member with member | member
    · exact constraints e member
    · exact input e member
  | nonempty op f free args selected =>
    intro values input
    have count := mass_congr profile (selected.sound reg values input)
    simp [Substitution.zero, Term.eval, Terms.eval, reg.quote_apply, mass, Tree.eval,
      measure, free, profile.view_zero] at count
  | @sharing Γ images eqs s n nr nc op slots left right rows cols rowCounts colCounts disjoint selected child ih =>
    intro values input
    obtain ⟨fresh, imagesSame⟩ := Sharing.complete profile reg op slots left right rows cols
      rowCounts colCounts disjoint values (selected.sound reg values input)
    have residual := substituteEquations_holds reg (Sharing.substitution op slots left right
      (FiniteSharing.supportGenerators rows cols)) eqs values fresh imagesSame input
    obtain ⟨answer, member, parameters, covered⟩ := ih fresh residual
    refine ⟨answer, member, parameters, ?_⟩
    rw [Terms.eval_subst] at covered
    exact args_trans reg (images.eval_congr reg imagesSame) covered
  | @mutate Γ images eqs s op a b c d selected child ih =>
    intro values input
    have selected := selected.sound reg values input
    rcases (mutate_native profile reg op (a.eval reg values) (b.eval reg values)
      (c.eval reg values) (d.eval reg values)).mp selected with ⟨p, q, r, t, ha, hb, hc, hd⟩
    have lifted : Holds reg (liftEquations (s := s) eqs) (p, q, r, t, values) := by
      intro e member
      simp only [liftEquations] at member
      rcases List.mem_map.mp member with ⟨original, horiginal, heq⟩
      rw [← heq]
      simpa only [Problem.Holds, equation, Term.eval_subst, lift4_eval] using input original horiginal
    have result := ih (p, q, r, t, values) (by
      intro e member
      simp only [mutated, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with (rfl | rfl | rfl | rfl) | member
      · simpa only [Problem.Holds, equation, Term.eval_subst, lift4_eval, add,
          Term.eval, Terms.eval, Variable.eval] using ha
      · simpa only [Problem.Holds, equation, Term.eval_subst, lift4_eval, add,
          Term.eval, Terms.eval, Variable.eval] using hb
      · simpa only [Problem.Holds, equation, Term.eval_subst, lift4_eval, add,
          Term.eval, Terms.eval, Variable.eval] using hc
      · simpa only [Problem.Holds, equation, Term.eval_subst, lift4_eval, add,
          Term.eval, Terms.eval, Variable.eval] using hd
      · exact lifted e member)
    simpa only [Terms.eval_subst, lift4_eval] using result
  | @split Γ images eqs ss s op x y f free args selected left right il ir =>
    intro values input
    have atom : mass profile (reg.quote s ((Term.app f args).eval reg values)) = 1 := by
      simp [Term.eval, reg.quote_apply, mass, Tree.eval, measure, free]
    rcases (split_native profile reg op (x.eval reg values) (y.eval reg values)
      ((Term.app f args).eval reg values) atom).mp (selected.sound reg values input) with
      ⟨hx, hy⟩ | ⟨hx, hy⟩
    · apply il values
      intro e member
      rcases List.mem_cons.mp member with rfl | member
      · exact hx
      rcases List.mem_cons.mp member with rfl | member
      · exact hy
      exact input e member
    · apply ir values
      intro e member
      rcases List.mem_cons.mp member with rfl | member
      · exact hx
      rcases List.mem_cons.mp member with rfl | member
      · exact hy
      exact input e member
  | clash f g hf hg different a b selected =>
    intro values input
    exact False.elim ((clash_native profile reg f g hf hg different _ _)
      (selected.sound reg values input))

/-- Compile a discovered contradiction to the EXISTING finite replay tree.
None means "not closed by this step", never "the equation has no solution".
Orientation is traversed structurally and the same selected equation is retained.
This is ordinary proof-data construction, not a tactic or a bounded solver. -/
def closeAction [DecidableEq Sorts] {profile : Profile sig} {inputs Γ}
    {proposed : List (Answer sig inputs)} {images : Terms sig Γ inputs}
    {eqs : List (Problem sig Γ)} {s a b} (action : FreePhase.Action profile (s := s) a b)
    (selected : Derives profile eqs a b) : Option (Complete profile proposed images eqs) :=
  match action with
  | .occurs v rhs path => some (.occurs v rhs path selected)
  | .clash f g hf hg different a b => some (.clash f g hf hg different a b selected)
  | .orient action => closeAction action (.symm selected)
  | _ => none

def closeFree [DecidableEq Sorts] [∀ ss s, DecidableEq (sig.Symbol ss s)]
    (profile : Profile sig) {inputs Γ} (proposed : List (Answer sig inputs))
    (images : Terms sig Γ inputs) (eqs : List (Problem sig Γ)) (index : Fin eqs.length) :
    Option (Complete profile proposed images eqs) :=
  closeAction (FreePhase.classify profile (eqs.get index).left (eqs.get index).right) (.hyp index)

/-- Soundness of ALL proposed answers for ALL original equations. Keeping the
same proposed vectors in every component preserves cross-equation correlations.
This is certificate data, not an assumption about the external engine. -/
inductive SystemSoundness {inputs} (proposed : List (Answer sig inputs)) :
    List (Problem sig inputs) → Type where
  | nil : SystemSoundness proposed []
  | cons {problem rest} (head : Soundness problem proposed)
      (tail : SystemSoundness proposed rest) : SystemSoundness proposed (problem :: rest)

theorem SystemSoundness.sound (reg : Registration sig) {inputs proposed eqs}
    (proof : SystemSoundness (sig := sig) (inputs := inputs) proposed eqs)
    (values : Args reg.Carrier inputs) (solution : Solutions reg proposed values) :
    Holds reg eqs values := by
  induction proof with
  | nil => intro e member; cases member
  | @cons e rest head tail ih =>
    intro p member
    rcases List.mem_cons.mp member with same | member
    · cases same; exact head.sound reg values solution
    · exact ih p member

/-- Native exactness for a finite EQUATION SYSTEM (CERTIFICATION.md §8.4).
This proves accepted-certificate validity, not successful search for certificates.
There is no premise trusting native Maude, and no search-success axiom. -/
theorem exact_system (reg : Registration sig) {profile : Profile sig} {inputs}
    (eqs : List (Problem sig inputs)) (proposed : List (Answer sig inputs))
    (complete : Complete profile proposed (Terms.identity inputs) eqs)
    (sound : SystemSoundness proposed eqs) :
    ∀ values, Holds reg eqs values ↔ Solutions reg proposed values :=
  fun values => ⟨fun input =>
    (identity_eval reg values) ▸ complete.sound reg values input,
    sound.sound reg values⟩

/-- One checked completeness tree plus the existing checked soundness data
establishes EXACTNESS. No independent reference-completeness premise remains. -/
theorem exact (reg : Registration sig) {profile : Profile sig} {inputs}
    (problem : Problem sig inputs) (proposed : List (Answer sig inputs))
    (complete : Complete profile proposed (Terms.identity inputs) [problem])
    (sound : Soundness problem proposed) :
    ∀ values, problem.Holds reg values ↔ Solutions reg proposed values :=
  fun values => ⟨fun input =>
    (identity_eval reg values) ▸ complete.sound reg values
      (fun _p member => (List.mem_singleton.mp member) ▸ input),
    sound.sound reg values⟩

end Worklist

/-! ## Lean-ready certificate boundary (prototype only)

A producer emits an explicit proof TERM using the existing semantic/replay rules.
Lean parses that term against a FIXED expected proposition and kernel-checks it.
There is no kernel evaluation of a proof-producing interpreter.

The wrapper exports typed data and compiles restricted external rule records to
ordinary Lean applications. The current session checks them; the producer does
not invoke another Lean verifier. The full Lean term language is not a security
sandbox: the supported boundary uses approved rule templates, not arbitrary
external tactics or commands.
-/
namespace LeanReady

open Lean Meta Elab Term

/-- Export only typed syntactic DATA already held by Lean. The finite sort/head
codes come from the registered signature, not a second native-answer parser. -/
def variableIndex {Γ : List Sorts} {s : Sorts} : Variable Γ s → Nat
  | .here => 0
  | .there v => variableIndex v + 1

mutual
  def termJson (profile : Profile sig) {Γ s} : Term sig Γ s → Json
    | .var v => Json.mkObj [("var", toJson (variableIndex v))]
    | .app f args => Json.mkObj [("app", toJson (profile.code f)), ("args", termsJson profile args)]
  def termsJson (profile : Profile sig) {Γ ss} : Terms sig Γ ss → Json
    | .nil => toJson ([] : List Json)
    | .cons a rest => match termsJson profile rest with
      | .arr xs => .arr (#[termJson profile a] ++ xs)
      | _ => .null -- unreachable: the recursive result is always an array
end

def requestJson (profile : Profile sig) (sortCode : Sorts → Nat) {inputs}
    (eqs : List (Problem sig inputs)) (proposed : List (Answer sig inputs))
    (problemName answerName : String) (signature : Json := .null) : Json :=
  Json.mkObj [("aggregate", toJson "system"), ("problem", toJson problemName),
    ("answers", toJson answerName), ("signature", signature), ("scope", toJson (inputs.map sortCode)),
    ("eqs", toJson (eqs.map fun p => Json.mkObj [
      ("sort", toJson (sortCode p.sort)), ("left", termJson profile p.left),
      ("right", termJson profile p.right)])),
    ("proposed", toJson (proposed.map fun p => Json.mkObj [
      ("parameters", toJson (p.parameters.map sortCode)),
      ("images", termsJson profile p.images)]))]

/-- Ask for evidence of a FIXED answer family. This subprocess neither invokes
native unify nor starts Lean. The current elaborator checks the returned term.
The producer enforces its own CPU/wall limits on Maude. No certificate cache or
precompilation is performed while elaborating a user's proof. -/
def produce (request : Json) (compiler : System.FilePath := "certifier.py") : IO String := do
  let out ← IO.Process.output { cmd := "python3", args := #[compiler.toString, "--certify"] }
    (some request.compress)
  unless out.exitCode == 0 do
    throw (IO.userError s!"certificate producer failed: {out.stderr}")
  pure out.stdout

end LeanReady

end Substitution

end DirectCertification
