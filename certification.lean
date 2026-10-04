import examples.bakery_acu

/-!
# Direct, rule-based unification certificates

This file contains three clearly separated parts:
1. GENERAL METATHEOREMS: correctness of the rules for any registered signature.
2. SYNTACTIC METADATA: constructor classification, generated without user proofs.
3. CERTIFICATES: ordinary, tactic-free proof terms over Bakery's own datatypes.

The equality is the existing Structural.Indexed.NativeEq, written
`=[BakeryTheory.certified]`. We introduce no second equality or user-model
encoding. Lists/quotients appear only inside proofs of the general metatheorems.

A future Maude dump can name each general rule and its arguments. Reconstruction
then builds the corresponding Lean application; it does not run a Lean tactic.
The commented traces below are schematic, NOT dumps fetched from Maude.
There is no Maude invocation, parser, custom proof tactic, or proof search here.

References:
* Comon–Lescanne, Equational Problems and Disunification (1989), §§3–4:
  https://doi.org/10.1016/S0747-7171(89)80017-3
  Separation of rules from control, and preservation of the WHOLE solution set.
* Fernández, AC Complement Problems (1996), §3:
  transformation rules and their semantic correctness. This prototype does NOT
  implement that paper's complement procedure or import its AC decision results.

This is a small ACU rule fragment, NOT a complete ACU unification algorithm.
The existing production narrowing and legacy EqMod certificates are unchanged.
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
    | add => simp [measure, hv, h.1, h.2.1]
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

/-! ## A remainder-sensitive ACU rule

Auxiliary lists below contain equivalence classes of the SAME indexed trees.
They are used only in the generic metatheorem, never as a user encoding or a
second notion of structural equality. Constructor congruence is retained by
Quotient.sound, including equations inside singleton payloads.
-/

def treeSetoid {s} : Setoid (Tree sig s) where
  r := Structural.Indexed.Eq sig
  iseqv := ⟨.refl, .symm, .trans⟩

abbrev QTree (sig : Signature Sorts) (s : Sorts) :=
  Quotient (treeSetoid (sig := sig) (s := s))

def qtree {s} (a : Tree sig s) : QTree sig s := Quotient.mk _ a

def qadd {s} (op : sig.ACUOp s) (a b : QTree sig s) : QTree sig s :=
  Quotient.liftOn₂ a b (fun x y => qtree (add sig op x y))
    (fun _ _ _ _ hx hy => Quotient.sound
      (.congr (sig.add op) (.cons hx (.cons hy .nil))))

theorem qadd_comm {s} (op : sig.ACUOp s) (a b : QTree sig s) :
    qadd op a b = qadd op b a := by
  induction a using Quotient.inductionOn
  induction b using Quotient.inductionOn
  exact Quotient.sound (.comm op _ _)

theorem qadd_assoc {s} (op : sig.ACUOp s) (a b c : QTree sig s) :
    qadd op (qadd op a b) c = qadd op a (qadd op b c) := by
  induction a using Quotient.inductionOn
  induction b using Quotient.inductionOn
  induction c using Quotient.inductionOn
  exact Quotient.sound (.assoc op _ _ _)

theorem qadd_unit {s} (op : sig.ACUOp s) (a : QTree sig s) :
    qadd op (qtree (zero sig op)) a = a := by
  induction a using Quotient.inductionOn
  exact Quotient.sound (.unit op _)

theorem qadd_unit_right {s} (op : sig.ACUOp s) (a : QTree sig s) :
    qadd op a (qtree (zero sig op)) = a :=
  (qadd_comm op _ _).trans (qadd_unit op a)

def qfold {s} (op : sig.ACUOp s) (xs : List (QTree sig s)) : QTree sig s :=
  xs.foldr (qadd op) (qtree (zero sig op))

theorem qfold_append {s} (op : sig.ACUOp s) (xs ys : List (QTree sig s)) :
    qfold op (xs ++ ys) = qadd op (qfold op xs) (qfold op ys) := by
  induction xs with
  | nil => exact (qadd_unit op _).symm
  | cons a rest ih =>
      change qadd op a (qfold op (rest ++ ys)) = _
      rw [ih]
      exact (qadd_assoc op a (qfold op rest) (qfold op ys)).symm

theorem qfold_perm {s} (op : sig.ACUOp s) {xs ys : List (QTree sig s)}
    (h : xs.Perm ys) : qfold op xs = qfold op ys := by
  induction h with
  | nil => rfl
  | cons a h ih => exact congrArg (qadd op a) ih
  | swap a b rest =>
      change qadd op b (qadd op a _) = qadd op a (qadd op b _)
      rw [← qadd_assoc, qadd_comm op b a, qadd_assoc]
  | trans h k ih ik => exact ih.trans ik

private def flatHead {ss s} {f : sig.Symbol ss s} (view : HeadView sig f) (args : Trees sig ss)
    (parts : Args (fun s => List (QTree sig s)) ss) : List (QTree sig s) :=
  match view with
  | .zero _ => []
  | .add _ => parts.1 ++ parts.2.1
  | .atom f => [qtree (.app f args)]

mutual
  def flatten {s} : Tree sig s → List (QTree sig s)
    | .app f args => flatHead (profile.view f) args (flattenArgs args)
  def flattenArgs : {ss : List Sorts} → Trees sig ss →
      Args (fun s => List (QTree sig s)) ss
    | _, .nil => PUnit.unit
    | _, .cons a rest => (flatten a, flattenArgs rest)
end

@[simp] theorem flatten_zero {s} (op : sig.ACUOp s) :
    flatten profile (zero sig op) = [] := by
  simp [flatten, zero, flatHead, profile.view_zero]

@[simp] theorem flatten_add {s} (op : sig.ACUOp s) (a b : Tree sig s) :
    flatten profile (add sig op a b) = flatten profile a ++ flatten profile b := by
  simp [flatten, add, flattenArgs, flatHead, profile.view_add]

theorem flatten_congr {s} {a b : Tree sig s} (h : Structural.Indexed.Eq sig a b) :
    (flatten profile a).Perm (flatten profile b) := by
  refine Structural.Indexed.Eq.rec
    (motive_1 := fun {s} a b _ => (flatten profile a).Perm (flatten profile b))
    (motive_2 := fun {ss} a b _ => ArgsRel (fun _ => List.Perm) ss
      (flattenArgs profile a) (flattenArgs profile b))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h
  · intro s a; exact .refl _
  · intro s a b h ih; exact ih.symm
  · intro s a b c h k ih ik; exact ih.trans ik
  · intro ss s f a b h ih
    cases hv : profile.view f with
    | zero => simp [flatten, flatHead, hv]
    | add =>
        simpa only [flatten, hv, flatHead] using ih.1.append ih.2.1
    | atom f =>
        have eq : qtree (.app f a) = qtree (.app f b) := Quotient.sound (.congr f h)
        simp [flatten, flatHead, hv, eq]
  · intro s op a b
    simp only [flatten_add]
    exact List.perm_append_comm
  · intro s op a b c
    simp only [flatten_add, List.append_assoc]
    exact .refl _
  · intro s op a
    simp only [flatten_add, flatten_zero, List.nil_append]
    exact .refl _
  · trivial
  · intro s ss a b rest tail h k ih ik; exact ⟨ih, ik⟩

theorem qfold_flatten {s} (op : sig.ACUOp s) (a : Tree sig s) :
    qfold op (flatten profile a) = qtree a := by
  let P := fun s (a : Tree sig s) => ∀ op : sig.ACUOp s,
    qfold op (flatten profile a) = qtree a
  have all : P s a := by
    refine Tree.rec (motive_1 := fun {s} a => P s a)
      (motive_2 := fun {ss} args => AllTrees P args) ?_ ?_ ?_ a
    · intro ss s f args ih target
      cases hv : profile.view f with
      | zero other =>
          cases args
          cases profile.unique other target
          change qfold target (flatten profile (zero sig target)) = _
          rw [flatten_zero]
          rfl
      | add other =>
          cases args with
          | cons left rest =>
            cases rest with
            | cons right tail =>
              cases tail
              cases profile.unique other target
              change qfold target (flatten profile (add sig target left right)) = _
              rw [flatten_add, qfold_append, ih.1 target, ih.2.1 target]
              rfl
      | atom f =>
          simp only [flatten, flatHead, hv]
          simpa [qfold] using qadd_unit_right target (qtree (.app f args))
    · trivial
    · intro s ss first rest hfirst hrest; exact ⟨hfirst, hrest⟩
  exact all op

/-- Finite bag refinement, used only to prove the semantic Mutate rule. -/
theorem perm_refine {α : Type} (a b c d : List α)
    (h : (a ++ b).Perm (c ++ d)) :
    ∃ p q r t, a.Perm (p ++ q) ∧ b.Perm (r ++ t) ∧
      c.Perm (p ++ r) ∧ d.Perm (q ++ t) := by
  induction a generalizing c d with
  | nil => exact ⟨[], [], c, d, .refl _, h, .refl _, .refl _⟩
  | cons x a ih =>
      have hm : x ∈ c ++ d := h.mem_iff.mp (by simp)
      rcases List.mem_append.mp hm with hc | hd
      · rcases List.mem_iff_append.mp hc with ⟨l, r, rfl⟩
        have hp : (l ++ x :: r ++ d).Perm (x :: ((l ++ r) ++ d)) := by
          simpa only [List.cons_append] using
            (List.perm_middle (a := x) (l₁ := l) (l₂ := r)).append_right d
        obtain ⟨p, q, r', t, ha, hb, hc, hd⟩ := ih (l ++ r) d (h.trans hp).cons_inv
        exact ⟨x :: p, q, r', t, ha.cons x, hb,
          List.perm_middle.trans (hc.cons x), hd⟩
      · rcases List.mem_iff_append.mp hd with ⟨l, r, rfl⟩
        have hp : (c ++ (l ++ x :: r)).Perm (x :: (c ++ (l ++ r))) := by
          exact ((List.perm_middle (a := x) (l₁ := l) (l₂ := r)).append_left c).trans
            List.perm_middle
        obtain ⟨p, q, r', t, ha, hb, hc, hd⟩ := ih c (l ++ r) (h.trans hp).cons_inv
        exact ⟨p, x :: q, r', t, (ha.cons x).trans List.perm_middle.symm,
          hb, hc, List.perm_middle.trans (hd.cons x)⟩

theorem qadd_exchange {s} (op : sig.ACUOp s) (p q r t : QTree sig s) :
    qadd op (qadd op p q) (qadd op r t) =
      qadd op (qadd op p r) (qadd op q t) := by
  rw [qadd_assoc op p q, ← qadd_assoc op q r, qadd_comm op q r,
    qadd_assoc op r q, ← qadd_assoc op p r]

/-- A direct, many-sorted semantic proof rule. Lists/quotients are completely
internal to this metatheorem; its interface uses only registered structural Eq.

  X+Y =B A+R
  ---------------------------------------------------- MutateACU
  ∃ P Q S T, X=B P+Q ∧ Y=B S+T ∧ A=B P+S ∧ R=B Q+T

The reverse implication proves soundness; the forward proves completeness.
No Diophantine solver, model-specific encoding, or extra user evidence is used.
-/
theorem mutate (profile : Profile sig) {s} (op : sig.ACUOp s) (x y a b : Tree sig s) :
    Structural.Indexed.Eq sig (add sig op x y) (add sig op a b) ↔
      ∃ p q r t : Tree sig s,
        Structural.Indexed.Eq sig x (add sig op p q) ∧
        Structural.Indexed.Eq sig y (add sig op r t) ∧
        Structural.Indexed.Eq sig a (add sig op p r) ∧
        Structural.Indexed.Eq sig b (add sig op q t) := by
  constructor
  · intro h
    have hp := flatten_congr profile h
    simp only [flatten_add] at hp
    obtain ⟨ps, qs, rs, ts, hx, hy, ha, hb⟩ := perm_refine _ _ _ _ hp
    obtain ⟨p, ep⟩ := Quotient.exists_rep (qfold op ps)
    obtain ⟨q, eq⟩ := Quotient.exists_rep (qfold op qs)
    obtain ⟨r, er⟩ := Quotient.exists_rep (qfold op rs)
    obtain ⟨t, et⟩ := Quotient.exists_rep (qfold op ts)
    have lift : ∀ (value : Tree sig s) u v (us vs : List (QTree sig s)),
        (flatten profile value).Perm (us ++ vs) →
        qtree u = qfold op us → qtree v = qfold op vs →
        Structural.Indexed.Eq sig value (add sig op u v) := by
      intro value u v us vs perm eu ev
      apply Quotient.exact (s := treeSetoid (sig := sig))
      change qtree value = qadd op (qtree u) (qtree v)
      rw [eu, ev, ← qfold_append, ← qfold_flatten profile op value]
      exact qfold_perm op perm
    exact ⟨p, q, r, t, lift x p q ps qs hx ep eq,
      lift y r t rs ts hy er et, lift a p r ps rs ha ep er,
      lift b q t qs ts hb eq et⟩
  · rintro ⟨p, q, r, t, hx, hy, ha, hb⟩
    apply Quotient.exact (s := treeSetoid (sig := sig))
    change qadd op (qtree x) (qtree y) = qadd op (qtree a) (qtree b)
    have ex := Quotient.sound (s := treeSetoid) hx
    have ey := Quotient.sound (s := treeSetoid) hy
    have ea := Quotient.sound (s := treeSetoid) ha
    have eb := Quotient.sound (s := treeSetoid) hb
    change qtree x = qadd op (qtree p) (qtree q) at ex
    change qtree y = qadd op (qtree r) (qtree t) at ey
    change qtree a = qadd op (qtree p) (qtree r) at ea
    change qtree b = qadd op (qtree q) (qtree t) at eb
    rw [ex, ey, ea, eb]
    exact qadd_exchange op _ _ _ _

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

end DirectCertification

/-! ## Certification examples — no tactics, no problem-specific helper lemmas

Only this section mentions Bakery. Each certificate is a term consisting of
applications of the general rules above, plus ordinary logical constructors.
The profile command generates syntactic metadata; it proves no input certificate.
No pattern constraints are considered: these are unconstrained unification.

Read an iff as two certificates:
  .mp: every solution factors through one of the displayed substitutions.
  .mpr: every displayed substitution solves the original equation.
Equality of substitution images is MODULO THE THEORY, not literal Lean equality.
-/

namespace DirectCertification.Bakery

open BakeryACU Structural.Indexed BakeryACU.BakeryTheory.Generated

derive_direct_profile profile for BakeryTheory.certified

/- Trace:
     SplitAtom(P, Q, singleton(wait(n)))
     ├─ Emit { P ↦ empty,              Q ↦ singleton(wait(n)) }
     └─ Emit { P ↦ singleton(wait(n)), Q ↦ empty }

   The payload n is shared and arbitrary; it is not a ground atom dictionary ID.
   The rule returns BOTH alternatives. Applying .mp gives completeness directly.
-/
theorem atomic_certificate (n : Nat) (P Q : ProcSet) :
    ProcSet.union P Q =[BakeryTheory.certified] ProcSet.singleton (.wait n) ↔
      (P =[BakeryTheory.certified] ProcSet.empty ∧
        Q =[BakeryTheory.certified] ProcSet.singleton (.wait n)) ∨
      (P =[BakeryTheory.certified] ProcSet.singleton (.wait n) ∧
        Q =[BakeryTheory.certified] ProcSet.empty) :=
  split_native profile registration Operator.acu P Q (ProcSet.singleton (.wait n))
    rfl

/- Trace:
     MutateACU(P, Q, A, R; fresh U V W Z)
     Emit { P ↦ U+V, Q ↦ W+Z, A ↦ U+W, R ↦ V+Z }

   One unification equation, one family with four fresh parameters.
   This is a complete family even when assignments contain arbitrary bags.
-/
theorem refinement_certificate (P Q A R : ProcSet) :
    ProcSet.union P Q =[BakeryTheory.certified] ProcSet.union A R ↔
      ∃ U V W Z : ProcSet,
        P =[BakeryTheory.certified] ProcSet.union U V ∧
        Q =[BakeryTheory.certified] ProcSet.union W Z ∧
        A =[BakeryTheory.certified] ProcSet.union U W ∧
        R =[BakeryTheory.certified] ProcSet.union V Z :=
  mutate_native profile registration Operator.acu P Q A R

/- Trace:
     MutateACU(P, Q, singleton(wait(n)), R; fresh p q r t)
     Orient(singleton(wait(n)) =B p+r)
     SplitAtom(p, r, singleton(wait(n)))
     ├─ p=B 0, r=B atom: Congruence; Unit; Transitivity
     │  Emit { P ↦ q,      Q ↦ atom+t, R ↦ q+t }
     └─ p=B atom, r=B 0: Congruence; Unit; Transitivity
        Emit { P ↦ atom+q, Q ↦ t,      R ↦ q+t }

   The proof below mirrors this trace explicitly. Exists.elim opens the fresh
   pieces; Or.elim checks BOTH SplitAtom branches. Packing the remaining q,t
   with Exists.intro emits the substitutions. No search or hidden macro rule.

   Completeness does NOT require deciding whether individual instances are
   feasible. Here there are no constraints; every structural solution is covered.
-/
theorem remainder_certificate (n : Nat) (P Q R : ProcSet) :
    ProcSet.union P Q =[BakeryTheory.certified]
      ProcSet.union (ProcSet.singleton (.wait n)) R ↔
      (∃ U V : ProcSet,
        P =[BakeryTheory.certified] ProcSet.union (ProcSet.singleton (.wait n)) U ∧
        Q =[BakeryTheory.certified] V ∧
        R =[BakeryTheory.certified] ProcSet.union U V) ∨
      (∃ U V : ProcSet,
        P =[BakeryTheory.certified] U ∧
        Q =[BakeryTheory.certified] ProcSet.union (ProcSet.singleton (.wait n)) V ∧
        R =[BakeryTheory.certified] ProcSet.union U V) :=
  let atom := ProcSet.singleton (.wait n)
  let mutation := mutate_native profile registration Operator.acu P Q atom R
  let split := fun p r => split_native profile registration Operator.acu p r atom rfl
  Iff.intro
    -- COMPLETENESS: Mutate → Orient → Split → both branches → Emit.
    (fun input =>
      Exists.elim (mutation.mp input) (fun p hp =>
      Exists.elim hp (fun q hq =>
      Exists.elim hq (fun r hr =>
      Exists.elim hr (fun t pieces =>
        Or.elim ((split p r).mp (native_symm registration pieces.2.2.1))
          -- p=B 0, r=B atom. Eliminate the zero piece from P.
          (fun zeroAtom =>
            Or.inr ⟨q, t,
              native_trans registration pieces.1
                (native_trans registration
                  (native_add_congr registration Operator.acu
                    zeroAtom.1 (native_refl registration q))
                  (native_unit registration Operator.acu q)),
              native_trans registration pieces.2.1
                (native_add_congr registration Operator.acu
                  zeroAtom.2 (native_refl registration t)),
              pieces.2.2.2⟩)
          -- p=B atom, r=B 0. Eliminate the zero piece from Q.
          (fun atomZero =>
            Or.inl ⟨q, t,
              native_trans registration pieces.1
                (native_add_congr registration Operator.acu
                  atomZero.1 (native_refl registration q)),
              native_trans registration pieces.2.1
                (native_trans registration
                  (native_add_congr registration Operator.acu
                    atomZero.2 (native_refl registration t))
                  (native_unit registration Operator.acu t)),
              pieces.2.2.2⟩))))))
    -- SOUNDNESS: instantiate Mutate with the displayed substitution pieces.
    (fun output =>
      Or.elim output
        (fun first =>
          Exists.elim first (fun u hu =>
          Exists.elim hu (fun v images =>
            mutation.mpr ⟨atom, u, ProcSet.empty, v,
              images.1,
              native_trans registration images.2.1
                (native_symm registration (native_unit registration Operator.acu v)),
              native_trans registration
                (native_symm registration (native_unit registration Operator.acu atom))
                (native_comm registration Operator.acu ProcSet.empty atom),
              images.2.2⟩)))
        (fun second =>
          Exists.elim second (fun u hu =>
          Exists.elim hu (fun v images =>
            mutation.mpr ⟨ProcSet.empty, u, atom, v,
              native_trans registration images.1
                (native_symm registration (native_unit registration Operator.acu u)),
              images.2.1,
              native_symm registration (native_unit registration Operator.acu atom),
              images.2.2⟩))))

-- Axiom audits should report only propext / Quot.sound, never sorryAx.
#print axioms atomic_certificate
#print axioms refinement_certificate
#print axioms remainder_certificate

end DirectCertification.Bakery
