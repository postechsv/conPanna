import examples.bakery_acu

/-!
# ACU certification: semantic rules and checked coverage

Specification and provenance: CERTIFICATION.md, especially §§4–9 and §14.
This is ONE prototype, with four parts:
1. GENERAL SEMANTIC RULES over the existing registered structural equality.
2. EXHAUSTIVE FINITE SHARING: semantic exactness and typed substitution generation.
3. TYPED CERTIFICATE DATA and acceptance (soundness plus complete coverage).
4. BAKERY CERTIFICATES: explicit proof terms and computed occurs/clash closure,
   without custom proof tactics.

Kept from the previous prototype: quotient-based internal proofs, arbitrary-arity
free-head rules, native lifting, typed image vectors, and checked worklist trees.
Removed: shape-specific family recognizers, one-tail guard wrappers, duplicated
replay engines, bounded Maude search, and elaboration-time external calls.
The separate Maude experiments are NOT evidence for a general search guarantee.

The equality is Structural.Indexed.NativeEq, written `=[BakeryTheory.certified]`.
Quotients and multiplicity vectors are INTERNAL proof tools, not user encodings.
Only the last section uses Bakery; the rules work over a generic signature.
The profile command generates/checks syntactic metadata, not semantic user proofs.
Scoped binding preparation and free-step classification now compute checked data;
proper free-occurrence/clash closure is automatic. A repeated worklist driver,
bag-phase scheduling, and complete whole-vector factor search remain unfinished.

Proved acceptance is not proved search success:
* equality traces establish SOUNDNESS of each proposed substitution;
* a coverage tree establishes COMPLETENESS for every native valuation;
* checked early coverage can close a whole branch before sharing expansion;
* exhaustive finite-sharing search success is the INFORMAL argument in the
  document. No Lean search-success theorem or complete ACU solver is claimed.

Initial frontend contract: one homogeneous three-constructor ACU bag fragment;
payloads cannot reach that bag sort; remaining constructors are free. Arbitrary
repeated variables are permitted. General semantic rules may hold more widely.
Multiple interacting structural components require a future combination argument.

Rule provenance:
* DELETE/ORIENT/DECOMPOSE/CLASH/BIND: standard first-order unification.
* Finite occurrence sharing: Boudet–Contejean (1994), adapted to ACU emptiness.
* Cancellation, atom splitting, and positive-multiplicity cancellation:
  consequences of constructor-generated free bags, NOT arbitrary ACU monoids.
* Whole-vector factorization: standard complete-unifier-set instantiation.
* External search / checked acceptance: skeptical certification (e.g. SMTCoq).
No complement/disunification calculus or order-sorted membership rules are used.
Full references, differences, and limits on novelty are in CERTIFICATION.md §14.
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

/-- Syntactic closure of a sort under rigid (non-ACU) constructor arguments. -/
def AllRigid (rigid : Sorts → Bool) : List Sorts → Prop
  | [] => True
  | s :: ss => rigid s = true ∧ AllRigid rigid ss

structure Profile (sig : Signature Sorts) where
  view : ∀ {ss s} (f : sig.Symbol ss s), HeadView sig f
  view_zero : ∀ {s} (op : sig.ACUOp s), view (sig.zero op) = .zero op
  view_add : ∀ {s} (op : sig.ACUOp s), view (sig.add op) = .add op
  unique : ∀ {s} (a b : sig.ACUOp s), a = b
  /-- Purely syntactic head labels. Unequal codes prove unequal constructors;
  no injectivity assumption or user semantic proof is required. -/
  code : ∀ {ss s}, sig.Symbol ss s → Nat
  rigid : Sorts → Bool
  rigid_args : ∀ {ss s} (_f : sig.Symbol ss s), rigid s = true → AllRigid rigid ss
  rigid_no_acu : ∀ {s} (_op : sig.ACUOp s), rigid s = false

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

/- A second INTERNAL observer for FREE-OCCURS. ACU nodes take maximum depth,
while every free constructor adds one. max is commutative/associative with zero,
so this observer respects B, including free wrappers containing bag arguments.
It proves that an actual proper free-constructor occurrence cannot be a fixed
point. It is NOT syntactic occurs rejection for bag unions. -/
namespace FreeDepth

def maxArgs : {ss : List Sorts} → Args (fun _ : Sorts => Nat) ss → Nat
  | [], _ => 0
  | _ :: _, args => max args.1 (maxArgs args.2)

theorem maxArgs_congr {ss} (a b : Args (fun _ : Sorts => Nat) ss)
    (same : ArgsRel (fun _ => _root_.Eq) ss a b) : maxArgs a = maxArgs b := by
  induction ss with
  | nil => rfl
  | cons s ss ih => simp only [maxArgs, same.1, ih a.2 b.2 same.2]

def algebra (profile : Profile sig) : Algebra sig where
  Carrier := fun _ => Nat
  apply := fun f args => match profile.view f with
    | .zero _ => 0
    | .add _ => max args.1 args.2.1
    | .atom _ => (maxArgs args) + 1

def model (profile : Profile sig) : Model sig (algebra profile) where
  Rel := fun _ => _root_.Eq
  refl := fun _ _ => rfl
  symm := fun _ {_ _} h => h.symm
  trans := fun _ {_ _ _} h k => h.trans k
  congr := by
    intro ss s f a b h
    cases hv : profile.view f with
    | zero => rfl
    | add => simp only [algebra, hv, h.1, h.2.1]
    | atom => simp only [algebra, hv, maxArgs_congr a b h]
  «comm» := by intro s op a b; simp [algebra, profile.view_add, Nat.max_comm]
  «assoc» := by intro s op a b c; simp [algebra, profile.view_add, Nat.max_assoc]
  unit := by intro s op a; simp [algebra, profile.view_add, profile.view_zero]

def depth (profile : Profile sig) {s} (term : Tree sig s) : Nat := term.eval (algebra profile)

theorem congr (profile : Profile sig) {s} {a b : Tree sig s}
    (same : Structural.Indexed.Eq sig a b) : depth profile a = depth profile b :=
  Structural.Indexed.Eq.sound sig (model profile) same

end FreeDepth

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

/-! ### Cancellation and atom exchange

All quotients here identify exactly the EXISTING indexed structural relation:
`qtree a = qtree b` iff `Structural.Indexed.Eq sig a b`. They are internal proof
tools, not a different equality exposed to model authors.
-/

theorem qtree_eq_iff {s} (a b : Tree sig s) :
    qtree a = qtree b ↔ Structural.Indexed.Eq sig a b :=
  ⟨fun h => Quotient.exact h, fun h => Quotient.sound (s := treeSetoid) h⟩

theorem eq_of_flatten_perm {s} (op : sig.ACUOp s) {x y : Tree sig s}
    (h : (flatten profile x).Perm (flatten profile y)) :
    Structural.Indexed.Eq sig x y :=
  Quotient.exact ((qfold_flatten profile op x).symm.trans
    ((qfold_perm op h).trans (qfold_flatten profile op y)))

private theorem perm_cancel_prefix {α : Type} (front : List α) {xs ys : List α}
    (h : (front ++ xs).Perm (front ++ ys)) : xs.Perm ys := by
  induction front with
  | nil => exact h
  | cons a rest ih => exact ih h.cons_inv

/-- Cancel an arbitrary COMMON bag, including bags with repeated atoms. -/
theorem cancel (profile : Profile sig) {s} (op : sig.ACUOp s) (a x y : Tree sig s) :
    Structural.Indexed.Eq sig (add sig op a x) (add sig op a y) ↔
      Structural.Indexed.Eq sig x y :=
  ⟨fun h => eq_of_flatten_perm profile op (perm_cancel_prefix _
      (by simpa only [flatten_add] using flatten_congr profile h)),
    fun h => .congr (sig.add op) (.cons (.refl a) (.cons h .nil))⟩

/-! ### Positive multiplicity cancellation (CERTIFICATION.md §9)

     k > 0        kX =B kY
     --------------------- MULTIPLICITY-CANCEL
              X =B Y

This is a general semantic rule. It counts quotient atom classes in flattened
constructor bags, so payloads are compared modulo the SAME registered theory.
It does not assert cancellation in every algebra satisfying only ACU laws.
Zero is deliberately excluded: 0X =B 0Y imposes no condition on X,Y.
-/

def bagCopies {s} (op : sig.ACUOp s) : Nat → Tree sig s → Tree sig s
  | 0, _ => zero sig op
  | k + 1, a => add sig op a (bagCopies op k a)

theorem repeat_congr {s} (op : sig.ACUOp s) (k : Nat) {a b : Tree sig s}
    (h : Structural.Indexed.Eq sig a b) :
    Structural.Indexed.Eq sig (bagCopies op k a) (bagCopies op k b) := by
  induction k with
  | zero => exact .refl _
  | succ k ih => exact .congr (sig.add op) (.cons h (.cons ih .nil))

private theorem count_flatten_repeat {s} (op : sig.ACUOp s) (k : Nat)
    (a : Tree sig s) (generator : QTree sig s) [BEq (QTree sig s)] :
    List.count generator (flatten profile (bagCopies op k a)) =
      k * List.count generator (flatten profile a) := by
  induction k with
  | zero => simp [bagCopies]
  | succ k ih => simp only [bagCopies, flatten_add, List.count_append, ih, Nat.succ_mul,
      Nat.add_comm]

theorem multiplicity_cancel (profile : Profile sig) {s} (op : sig.ACUOp s) (k : Nat) (positive : 0 < k)
    (a b : Tree sig s) :
    Structural.Indexed.Eq sig (bagCopies op k a) (bagCopies op k b) ↔
      Structural.Indexed.Eq sig a b := by
  classical
  constructor
  · intro h
    apply eq_of_flatten_perm profile op
    apply List.perm_iff_count.mpr
    intro generator
    have same := (flatten_congr profile h).count_eq generator
    rw [count_flatten_repeat, count_flatten_repeat] at same
    exact Nat.eq_of_mul_eq_mul_left positive same
  · exact repeat_congr op k

theorem flatten_length {s} (a : Tree sig s) :
    (flatten profile a).length = mass profile a := by
  let P := fun s (a : Tree sig s) => (flatten profile a).length = mass profile a
  refine Tree.rec (motive_1 := fun {s} a => P s a)
    (motive_2 := fun {ss} args => AllTrees P args) ?_ ?_ ?_ a
  · intro ss s f args ih
    cases hv : profile.view f with
    | zero op => simp [P, flatten, flatHead, mass, Tree.eval, measure, hv]
    | add op =>
        cases args with
        | cons left rest =>
          cases rest with
          | cons right tail =>
            cases tail
            simp only [P] at ih
            simp only [P, flatten, flattenArgs, flatHead, mass, Tree.eval,
              Trees.eval, measure, hv, List.length_append]
            rw [ih.1, ih.2.1]
            rfl
    | atom f => simp [P, flatten, flatHead, mass, Tree.eval, measure, hv]
  · trivial
  · intro s ss first rest hf hr; exact ⟨hf, hr⟩

theorem flatten_atom {s} (op : sig.ACUOp s) (a : Tree sig s)
    (ha : mass profile a = 1) : flatten profile a = [qtree a] := by
  have length : (flatten profile a).length = 1 := (flatten_length profile a).trans ha
  cases hs : flatten profile a with
  | nil => simp [hs] at length
  | cons first rest =>
      have empty : rest = [] := by
        have hr : rest.length + 1 = 1 := by simpa only [hs, List.length_cons] using length
        have hz : rest.length = 0 := by omega
        exact List.eq_nil_of_length_eq_zero hz
      have folded := qfold_flatten profile op a
      rw [hs, empty] at folded
      change qadd op first (qtree (zero sig op)) = qtree a at folded
      have same : first = qtree a := (qadd_unit_right op first).symm.trans folded
      simp only [empty, same]

/-- The one-head exchange rule, with two possibly overlapping families.

  a+X =B b+Y
  ---------------------------------------------------------------- Exchange
  (a=B b AND X=B Y) OR EXISTS N, X=B b+N AND Y=B a+N

Atoms can have arbitrary payloads, even payloads with structural theories.
The second family does NOT require a !=B b. The proof never loses correlations
between the two occurrences of N. No independent unification search is used.
-/
theorem exchange {s} (op : sig.ACUOp s) (a b x y : Tree sig s)
    (ha : mass profile a = 1) (hb : mass profile b = 1) :
    Structural.Indexed.Eq sig (add sig op a x) (add sig op b y) ↔
      (Structural.Indexed.Eq sig a b ∧ Structural.Indexed.Eq sig x y) ∨
      ∃ n, Structural.Indexed.Eq sig x (add sig op b n) ∧
        Structural.Indexed.Eq sig y (add sig op a n) := by
  constructor
  · intro h
    classical
    by_cases hab : Structural.Indexed.Eq sig a b
    · exact .inl ⟨hab, (cancel profile op b x y).mp
        (.trans (.congr (sig.add op) (.cons (.symm hab) (.cons (.refl x) .nil))) h)⟩
    · have hp := flatten_congr profile h
      simp only [flatten_add, flatten_atom profile op a ha,
        flatten_atom profile op b hb, List.singleton_append] at hp
      have member : qtree a ∈ flatten profile y := by
        have hm := hp.mem_iff.mp List.mem_cons_self
        rcases List.mem_cons.mp hm with equal | member
        · exact False.elim (hab (Quotient.exact equal))
        · exact member
      obtain ⟨before, after, hy⟩ := List.mem_iff_append.mp member
      obtain ⟨n, hn⟩ := Quotient.exists_rep (qfold op (before ++ after))
      have tailPerm : (flatten profile x).Perm (qtree b :: (before ++ after)) := by
        rw [hy] at hp
        exact (hp.trans ((List.perm_middle.cons (qtree b)).trans
          (List.Perm.swap _ _ _))).cons_inv
      have hxq : qtree x = qadd op (qtree b) (qtree n) := by
        rw [← qfold_flatten profile op x, qfold_perm op tailPerm]
        change qadd op (qtree b) (qfold op (before ++ after)) = _
        rw [← hn]
        rfl
      have hyq : qtree y = qadd op (qtree a) (qtree n) := by
        rw [← qfold_flatten profile op y, hy, qfold_perm op List.perm_middle]
        change qadd op (qtree a) (qfold op (before ++ after)) = _
        rw [← hn]
        rfl
      exact .inr ⟨n, Quotient.exact hxq, Quotient.exact hyq⟩
  · rintro (⟨hab, hxy⟩ | ⟨n, hx, hy⟩)
    · exact .congr (sig.add op) (.cons hab (.cons hxy .nil))
    · apply Quotient.exact (s := treeSetoid (sig := sig))
      change qadd op (qtree a) (qtree x) = qadd op (qtree b) (qtree y)
      have ex := Quotient.sound (s := treeSetoid) hx
      have ey := Quotient.sound (s := treeSetoid) hy
      change qtree x = qadd op (qtree b) (qtree n) at ex
      change qtree y = qadd op (qtree a) (qtree n) at ey
      rw [ex, ey, ← qadd_assoc, qadd_comm op (qtree a) (qtree b), qadd_assoc]

/-- A sound ACU occurs rule: a bag cannot equal itself PLUS a nonempty atom.
Do NOT reject X=B X+Y: that equation has the solutions Y=B 0. -/
theorem occurs_atom {s} (op : sig.ACUOp s) (a x : Tree sig s)
    (ha : mass profile a = 1) :
    ¬ Structural.Indexed.Eq sig x (add sig op a x) := by
  intro h
  have count := mass_congr profile h
  rw [mass_add, ha] at count
  omega

/-! ### Free constructor decomposition and clash

The earlier bag observation stored whole atom classes. To invert a free
constructor we need one finer observation: its SORTED head and the equivalence
classes of its arguments. Argument classes use the existing structural Eqs.
Nothing below depends on a particular constructor, datatype, or arity.
-/

namespace ConstructorObservation

private theorem eqs_refl {ss} (args : Trees sig ss) : Eqs sig args args := by
  induction ss with
  | nil => cases args; exact .nil
  | cons s ss ih => cases args with
    | cons a rest => exact .cons (.refl _) (ih rest)

private theorem eqs_symm {ss} {a b : Trees sig ss} (h : Eqs sig a b) : Eqs sig b a := by
  induction ss with
  | nil => cases h; exact .nil
  | cons s ss ih => cases h with
    | cons h k => exact .cons (.symm h) (ih k)

private theorem eqs_trans {ss} {a b c : Trees sig ss}
    (h : Eqs sig a b) (k : Eqs sig b c) : Eqs sig a c := by
  induction ss with
  | nil => cases h; cases k; exact .nil
  | cons s ss ih =>
      cases h with
      | cons h tail => cases k with
        | cons k rest => exact .cons (.trans h k) (ih tail rest)

def argsSetoid (sig : Signature Sorts) (ss : List Sorts) : Setoid (Trees sig ss) where
  r := Eqs sig
  iseqv := ⟨eqs_refl, eqs_symm, eqs_trans⟩

abbrev Atom (sig : Signature Sorts) (s : Sorts) :=
  Σ ss : List Sorts, sig.Symbol ss s × Quotient (argsSetoid sig ss)

def atom {ss s} (f : sig.Symbol ss s) (args : Trees sig ss) : Atom sig s :=
  ⟨ss, f, Quotient.mk _ args⟩

private def head {ss s} {f : sig.Symbol ss s} (view : HeadView sig f)
    (args : Trees sig ss) (parts : Args (fun s => List (Atom sig s)) ss) : List (Atom sig s) :=
  match view with
  | .zero _ => []
  | .add _ => parts.1 ++ parts.2.1
  | .atom f => [atom f args]

mutual
  def observe (profile : Profile sig) {s} : Tree sig s → List (Atom sig s)
    | .app f args => head (profile.view f) args (observeArgs profile args)
  def observeArgs (profile : Profile sig) : {ss : List Sorts} → Trees sig ss →
      Args (fun s => List (Atom sig s)) ss
    | _, .nil => PUnit.unit
    | _, .cons a rest => (observe profile a, observeArgs profile rest)
end

theorem invariant (profile : Profile sig) {s} {a b : Tree sig s}
    (h : Structural.Indexed.Eq sig a b) : (observe profile a).Perm (observe profile b) := by
  refine Structural.Indexed.Eq.rec
    (motive_1 := fun {s} a b _ => (observe profile a).Perm (observe profile b))
    (motive_2 := fun {ss} a b _ => ArgsRel (fun _ => List.Perm) ss
      (observeArgs profile a) (observeArgs profile b))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h
  · intro s a; exact .refl _
  · intro s a b h ih; exact ih.symm
  · intro s a b c h k ih ik; exact ih.trans ik
  · intro ss s f a b h ih
    cases hv : profile.view f with
    | zero => simp [observe, head, hv]
    | add => simpa only [observe, head, hv] using ih.1.append ih.2.1
    | atom f =>
        have same : (atom f a : Atom sig s) = atom f b :=
          congrArg (fun q => ⟨ss, f, q⟩ : Quotient (argsSetoid sig ss) → Atom sig s)
            (Quotient.sound (s := argsSetoid sig ss) h)
        simp [observe, head, hv, same]
  · intro s op a b
    simp only [add, observe, head, profile.view_add, observeArgs]
    exact List.perm_append_comm
  · intro s op a b c
    simp only [add, observe, head, profile.view_add, observeArgs, List.append_assoc]
    exact .refl _
  · intro s op a
    simp only [add, zero, observe, head, profile.view_add, profile.view_zero,
      observeArgs, List.nil_append]
    exact .refl _
  · trivial
  · intro s ss a b rest tail h k ih ik; exact ⟨ih, ik⟩

end ConstructorObservation

/-- Constructor decomposition is valid ONLY for free heads, not ACU add/zero.

  f(a1,...,an) =B f(b1,...,bn)     f is a free constructor
  ========================================================= Decompose
  a1=B b1 AND ... AND an=B bn

Argument equality stays modulo B: payloads may themselves contain ACU terms.
-/
theorem decompose (profile : Profile sig) {ss s} (f : sig.Symbol ss s)
    (free : profile.view f = .atom f) (a b : Trees sig ss) :
    Structural.Indexed.Eq sig (.app f a) (.app f b) ↔ Eqs sig a b := by
  constructor
  · intro h
    have hp := ConstructorObservation.invariant profile h
    simp only [ConstructorObservation.observe, ConstructorObservation.head, free] at hp
    have same := (List.cons.inj (List.perm_singleton.mp hp)).1
    have parts := eq_of_heq (Sigma.mk.inj same).2
    exact Quotient.exact (congrArg Prod.snd parts)
  · exact fun h => .congr f h

/-- Head clash retains the argument-sort index: different free constructor
heads cannot be made equal by equations in their payloads. -/
theorem clash (profile : Profile sig) {ss tt s}
    (f : sig.Symbol ss s) (g : sig.Symbol tt s)
    (hf : profile.view f = .atom f) (hg : profile.view g = .atom g)
    (different : (⟨ss, f⟩ : Σ us, sig.Symbol us s) ≠ ⟨tt, g⟩)
    (a : Trees sig ss) (b : Trees sig tt) :
    ¬ Structural.Indexed.Eq sig (.app f a) (.app g b) := by
  intro h
  have hp := ConstructorObservation.invariant profile h
  simp only [ConstructorObservation.observe, ConstructorObservation.head, hf, hg] at hp
  have same := (List.cons.inj (List.perm_singleton.mp hp)).1
  exact different (congrArg (fun x => (⟨x.1, x.2.1⟩ : Σ us, sig.Symbol us s)) same)

/-- On a sort whose constructor dependencies cannot reach any ACU sort,
structural equality is ordinary equality. The registration generator computes
this finite graph property; the proof below works for recursive rigid sorts.
Merely having no ACU operation at the TOP sort would not be sufficient: a free
wrapper around an ACU bag is not rigid. -/
theorem eq_of_rigid (profile : Profile sig) {s} {a b : Tree sig s}
    (hs : profile.rigid s = true) (h : Structural.Indexed.Eq sig a b) : a = b := by
  have invariant : profile.rigid s = true → a = b := by
    refine Structural.Indexed.Eq.rec
      (motive_1 := fun {s} a b _ => profile.rigid s = true → a = b)
      (motive_2 := fun {ss} a b _ => AllRigid profile.rigid ss → a = b)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h
    · intro s a hs; rfl
    · intro s a b h ih hs; exact (ih hs).symm
    · intro s a b c h k ih ik hs; exact (ih hs).trans (ik hs)
    · intro ss s f a b h ih hs
      exact congrArg (Tree.app f) (ih (profile.rigid_args f hs))
    · intro s op a b hs; simp [profile.rigid_no_acu op] at hs
    · intro s op a b c hs; simp [profile.rigid_no_acu op] at hs
    · intro s op a hs; simp [profile.rigid_no_acu op] at hs
    · intro hs; rfl
    · intro s ss a b rest tail h k ih ik hs
      have first := ih hs.1
      have remaining := ik hs.2
      cases first; cases remaining; rfl
  exact invariant hs

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

namespace FiniteSharing
/-!
## General multiplicity lemmas for the future FiniteSharing rule

This is a once-for-all PROOF auxiliary, not a Diophantine search backend,
a user registration interface, or a claim that ACU certification is complete.
For one atom class, a bag assignment induces a vector of multiplicities.
The balance coefficients retain repeated occurrences of the original variables.

The two established steps are:
  Balanced(v) ==> v = m1 + ... + mk, with every mi minimal and nonzero.
  Every minimal vector belongs to G, and every vector in G is balanced
  ==================================================================
                   Balanced(v) <==> Generated(G,v)

Below, boolean_supports_exact proves the numerical exactness: every balanced
active vector is a sum of nonempty Boolean support degrees, and every such sum
is balanced. Minimal occurrence-level rounding is fully proved, not assumed.
supportGenerators_exact additionally proves exactness of the EXECUTABLE exhaustive
support list. bags_generated and finiteSharing_native lift this to tree/native
bag images. Sharing generates typed open substitutions and checked replay nodes.
General certificate search remains pending.

The decomposition uses classical existence and strong induction. It is not
executable certificate search, and no domain constraints or Bakery symbols
occur in the statements.
-/

abbrev Vector (n : Nat) := Fin n → Nat
def zeroVector {n} : Vector n := fun _ => 0
def plus {n} (v w : Vector n) : Vector n := fun i => v i + w i
def minus {n} (v w : Vector n) : Vector n := fun i => v i - w i
def Below {n} (v w : Vector n) : Prop := ∀ i, v i ≤ w i
def size : {n : Nat} → Vector n → Nat
  | 0, _ => 0
  | _ + 1, v => v 0 + size (fun i => v i.succ)
theorem size_zero (n : Nat) : size (zeroVector (n := n)) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [size, zeroVector] using ih
theorem size_plus {n} (v w : Vector n) :
    size (plus v w) = size v + size w := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [size, plus]
    have ht := ih (fun i => v i.succ) (fun i => w i.succ)
    change size (fun i => v i.succ + w i.succ) = _ at ht
    rw [ht]
    omega
theorem size_mono {n} {v w : Vector n} (h : Below v w) : size v ≤ size w := by
  induction n with
  | zero => exact Nat.le_refl _
  | succ n ih =>
    exact Nat.add_le_add (h 0) (ih (fun i => h i.succ))
theorem eq_of_below_size_eq {n} {v w : Vector n}
    (h : Below v w) (hs : size v = size w) : v = w := by
  induction n with
  | zero => funext i; exact Fin.elim0 i
  | succ n ih =>
    have ht : size (fun i => v i.succ) ≤ size (fun i => w i.succ) :=
      size_mono (fun i => h i.succ)
    have h0 := h 0
    simp only [size] at hs
    have first : v 0 = w 0 := by omega
    have tail : size (fun i => v i.succ) = size (fun i => w i.succ) := by omega
    have same := ih (fun i => h i.succ) tail
    funext i
    exact Fin.cases first (fun j => congrFun same j) i
theorem size_pos {n} {v : Vector n} (h : v ≠ zeroVector) : 0 < size v := by
  apply Nat.pos_of_ne_zero
  intro hs
  have same : zeroVector = v :=
    eq_of_below_size_eq (fun _ => Nat.zero_le _) ((size_zero n).trans hs.symm)
  exact h same.symm
theorem split_below {n} {w v : Vector n} (h : Below w v) :
    v = plus w (minus v w) :=
  funext fun i => (Nat.add_sub_of_le (h i)).symm
def dot {n} (coeff v : Vector n) : Nat := size (fun i => coeff i * v i)
def Balanced {n} (left right v : Vector n) : Prop := dot left v = dot right v
theorem dot_plus {n} (coeff v w : Vector n) :
    dot coeff (plus v w) = dot coeff v + dot coeff w := by
  unfold dot plus
  simp only [Nat.mul_add]
  exact size_plus _ _
theorem balanced_minus {n} {left right v w : Vector n}
    (hv : Balanced left right v) (hw : Balanced left right w) (hle : Below w v) :
    Balanced left right (minus v w) := by
  unfold Balanced at *
  rw [split_below hle, dot_plus, dot_plus, hw] at hv
  exact Nat.add_left_cancel hv
/-- Minimality is componentwise: there is no smaller nonzero balanced vector.
Zero is deliberately excluded; the empty decomposition accounts for it. -/
def Minimal {n} (left right v : Vector n) : Prop :=
  v ≠ zeroVector ∧ Balanced left right v ∧
    ∀ w, Below w v → Balanced left right w → w ≠ zeroVector → w = v
def total {n} : List (Vector n) → Vector n
  | [] => zeroVector
  | v :: rest => plus v (total rest)
theorem total_append {n} (xs ys : List (Vector n)) :
    total (xs ++ ys) = plus (total xs) (total ys) := by
  induction xs with
  | nil => funext i; simp [total, plus, zeroVector]
  | cons x xs ih =>
    simp only [List.cons_append, total, ih]
    funext i
    exact (Nat.add_assoc _ _ _).symm
/-- Every balance solution is a finite sum of minimal balance solutions.
Split off a proper balanced subvector when one exists. Both summands have
strictly smaller total multiplicity, so the induction retains every solution.
No positivity or linearity restriction on the coefficient vectors is needed. -/
theorem decompose_minimal {n} (left right v : Vector n) (hv : Balanced left right v) :
    ∃ parts : List (Vector n),
      (∀ w ∈ parts, Minimal left right w) ∧ total parts = v := by
  classical
  refine Nat.strongRecOn (motive := fun k => ∀ v : Vector n,
    size v = k → Balanced left right v →
      ∃ parts : List (Vector n),
        (∀ w ∈ parts, Minimal left right w) ∧ total parts = v)
    (size v) ?_ v rfl hv
  intro k ih current hk hc
  by_cases hz : current = zeroVector
  · exact ⟨[], fun _ h => False.elim (List.not_mem_nil h), hz.symm⟩
  by_cases smaller : ∃ w, Below w current ∧ Balanced left right w ∧
      w ≠ zeroVector ∧ w ≠ current
  · obtain ⟨w, hle, hw, hnz, hne⟩ := smaller
    have wlt : size w < k := by
      have hleSize := size_mono hle
      have hneSize : size w ≠ size current :=
        fun h => hne (eq_of_below_size_eq hle h)
      have hlt := Nat.lt_of_le_of_ne hleSize hneSize
      omega
    have sumSplit : size current = size w + size (minus current w) := by
      exact (congrArg size (split_below hle)).trans (size_plus _ _)
    have dlt : size (minus current w) < k := by
      have positive := size_pos hnz
      omega
    obtain ⟨ws, hws, ews⟩ := ih (size w) wlt w rfl hw
    obtain ⟨ds, hds, eds⟩ := ih (size (minus current w)) dlt
      (minus current w) rfl (balanced_minus hc hw hle)
    refine ⟨ws ++ ds, ?_, ?_⟩
    · intro u member
      rcases List.mem_append.mp member with member | member
      · exact hws u member
      · exact hds u member
    · rw [total_append, ews, eds]
      exact (split_below hle).symm
  · refine ⟨[current], ?_, ?_⟩
    · intro w member
      have same : w = current := by simpa using member
      subst w
      refine ⟨hz, hc, ?_⟩
      intro w hle hw hnz
      exact Classical.byContradiction (fun hne => smaller ⟨w, hle, hw, hnz, hne⟩)
    · funext i
      simp [total, plus, zeroVector]


def Generated {n} (generators : List (Vector n)) (v : Vector n) : Prop :=
  ∃ parts : List (Vector n), (∀ w ∈ parts, w ∈ generators) ∧ total parts = v
theorem balanced_zero {n} (left right : Vector n) :
    Balanced left right zeroVector := by
  unfold Balanced dot zeroVector
  simp only [Nat.mul_zero]
theorem balanced_plus {n} {left right v w : Vector n}
    (hv : Balanced left right v) (hw : Balanced left right w) :
    Balanced left right (plus v w) := by
  unfold Balanced at *
  rw [dot_plus, dot_plus, hv, hw]
theorem total_balanced {n} (left right : Vector n) (parts : List (Vector n))
    (h : ∀ w ∈ parts, Balanced left right w) :
    Balanced left right (total parts) := by
  induction parts with
  | nil => exact balanced_zero left right
  | cons w rest ih =>
    exact balanced_plus (h w (List.mem_cons_self))
      (ih (fun u hu => h u (List.mem_cons_of_mem w hu)))
theorem generated_of_minimal_coverage {n} (left right : Vector n)
    (generators : List (Vector n))
    (covers : ∀ w, Minimal left right w → w ∈ generators)
    {v : Vector n} (hv : Balanced left right v) : Generated generators v := by
  obtain ⟨parts, minimal, sum⟩ := decompose_minimal left right v hv
  exact ⟨parts, fun w member => covers w (minimal w member), sum⟩
/-- General reduction of exact generation to coverage of minimal vectors.
The hypotheses are proof obligations for the GENERAL grid metatheorem, not
a per-model registration or a certificate supplied by the user/Maude. -/
theorem generated_iff_balanced {n} (left right : Vector n)
    (generators : List (Vector n))
    (sound : ∀ w ∈ generators, Balanced left right w)
    (covers : ∀ w, Minimal left right w → w ∈ generators)
    (v : Vector n) : Generated generators v ↔ Balanced left right v := by
  constructor
  · rintro ⟨parts, member, rfl⟩
    exact total_balanced left right parts (fun w hw => sound w (member w hw))
  · exact generated_of_minimal_coverage left right generators covers

/-!
### Minimal vectors and finite sharing capacities

The next lemmas retain the arbitrary coefficients and variable repetitions.
A transport matrix distributes the weighted multiplicities from left variables
to right variables. It has the required row/column totals, without any bound
on the size of the input problem.

If a minimal vector had BOTH v_i > b_j and v_j > a_i, the elementary solution
    X_i := b_j, Y_j := a_i, all other variables := 0
would be a proper nonzero balanced subvector. Minimality forbids this.
Consequently each transport block is bounded by a_i*b_j, exactly the number
of cells between the occurrences of those two variables.

IMPORTANT: bounded block totals alone do not prove that individual occurrence
rows have equal degrees. The later Boolean-grid section proves that stronger
representation separately; none of the capacity lemmas silently assume it.

The repair argument for that final theorem is:
* Expand the variable labels to occurrence rows/columns with degrees v_i/v_j.
  The transport existence lemma gives a natural-entry matrix with these margins.
* Suppose a cell (u,z) contains a >= 2. Minimality gives either rowDegree(u)
  <= number of columns with z's label, or the transposed inequality.
* In the first case, some column z' with the same label has entry 0 in row u.
  Its column total equals that of z, so some other row u' has
  d := M[u',z'] > c := M[u',z].
* Replace the rectangle (a,0;c,d) by (a-1,1;c+1,d-1). Margins are unchanged;
  switch_cost_lt proves its squared-entry cost strictly decreases.
* Use strong induction on the whole matrix's squared-entry cost. Eventually
  every cell is 0 or 1, and its selected cells preserve every occurrence margin.
  boolean_transport_exists proves this argument in Lean below.

Matrix rounding, exhaustive support enumeration, and native bag instantiation
are now proved below. Typed replay is connected; general search remains pending. No new
search control or user registration is introduced by these metatheorems.
-/

def spike {n} (index : Fin n) (value : Nat) : Vector n :=
  fun i => if i = index then value else 0

theorem size_spike {n} (index : Fin n) (value : Nat) : size (spike index value) = value := by
  induction n with
  | zero => exact Fin.elim0 index
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) index
    · have tail : (fun i : Fin n => spike (0 : Fin (n+1)) value i.succ) = zeroVector := by
        funext i
        simp [spike, zeroVector, Fin.succ_ne_zero]
      change spike (0 : Fin (n+1)) value 0 + size _ = value
      rw [tail, size_zero]
      simp [spike]
    · have tail : (fun i : Fin n => spike j.succ value i.succ) = spike j value := by
        funext i
        simp [spike, Fin.succ_inj]
      change spike j.succ value 0 + size _ = value
      rw [tail, ih j]
      simp [spike, Ne.symm (Fin.succ_ne_zero j)]

theorem dot_spike {n} (coeff : Vector n) (index : Fin n) (value : Nat) :
    dot coeff (spike index value) = coeff index * value := by
  have image : (fun i => coeff i * spike index value i) = spike index (coeff index * value) := by
    funext i
    by_cases hi : i = index
    · subst i; simp [spike]
    · simp [spike, hi]
  unfold dot
  rw [image]
  exact size_spike _ _

def pairVector {n} (left right : Vector n) (i j : Fin n) : Vector n :=
  plus (spike i (right j)) (spike j (left i))

theorem pair_balanced {n} (left right : Vector n) (i j : Fin n)
    (hi : right i = 0) (hj : left j = 0) :
    Balanced left right (pairVector left right i j) := by
  unfold Balanced pairVector
  rw [dot_plus, dot_plus, dot_spike, dot_spike, dot_spike, dot_spike, hi, hj]
  simp only [Nat.zero_mul, Nat.add_zero, Nat.zero_add]
  exact Nat.mul_comm _ _

/-- Opposite-side minimal multiplicities cannot both exceed the elementary
two-variable solution. The hypotheses locate two distinct variable indices
after cancellation; no occurrence is treated as an independent variable. -/
theorem minimal_pair_bound {n} {left right v : Vector n} (minimal : Minimal left right v)
    (i j : Fin n) (hr : 0 < right j)
    (hi : right i = 0) (hj : left j = 0) :
    v i ≤ right j ∨ v j ≤ left i := by
  classical
  have different : i ≠ j := by
    intro same
    subst j
    omega
  by_cases first : v i ≤ right j
  · exact Or.inl first
  by_cases second : v j ≤ left i
  · exact Or.inr second
  have below : Below (pairVector left right i j) v := by
    intro k
    by_cases ki : k = i
    · subst k
      simp [pairVector, plus, spike, different]
      omega
    by_cases kj : k = j
    · subst k
      simp [pairVector, plus, spike, Ne.symm different]
      omega
    · simp [pairVector, plus, spike, ki, kj]
  have nonzero : pairVector left right i j ≠ zeroVector := by
    intro equal
    have atI := congrFun equal i
    simp [pairVector, plus, spike, zeroVector, different] at atI
    omega
  have same := minimal.2.2 (pairVector left right i j) below (pair_balanced left right i j hi hj) nonzero
  have atI := congrFun same i
  simp [pairVector, plus, spike, different] at atI
  omega

/-- One rectangle exchange strictly decreases squared-entry cost. The zero
entry is explicit in the formula; the other diagonal entry d exceeds c.
This is a general arithmetic metatheorem, not problem-specific automation. -/
theorem switch_cost_lt (a c d : Nat) (ha : 2 ≤ a) (hd : c < d) :
    (a-1)*(a-1) + 1 + (c+1)*(c+1) + (d-1)*(d-1) <
      a*a + c*c + d*d := by
  obtain ⟨x, rfl⟩ := Nat.exists_eq_add_of_le ha
  obtain ⟨y, rfl⟩ := Nat.exists_eq_add_of_le (Nat.succ_le_of_lt hd)
  simp only [Nat.succ_eq_add_one]
  have hx : 2 + x - 1 = 1 + x := by omega
  have hy : c + 1 + y - 1 = c + y := by omega
  simp only [hx, hy, Nat.mul_add, Nat.mul_comm]
  omega



theorem size_split {n} {small large : Vector n} (h : Below small large) :
    size large = size small + size (minus large small) :=
  (congrArg size (split_below h)).trans (size_plus _ _)

theorem coordinate_le_size {n} (v : Vector n) (index : Fin n) : v index ≤ size v := by
  have below : Below (spike index (v index)) v := by
    intro i
    by_cases same : i = index
    · subst i; simp [spike]
    · simp [spike, same]
  have bound := size_mono below
  rw [size_spike] at bound
  exact bound

/-- Allocate any requested amount no larger than the available finite total. -/
theorem allocate {n} (available : Vector n) (amount : Nat) (h : amount ≤ size available) :
    ∃ chosen : Vector n, Below chosen available ∧ size chosen = amount := by
  induction n generalizing amount with
  | zero =>
    exact ⟨zeroVector, fun i => Fin.elim0 i, by simpa [size] using (Nat.eq_zero_of_le_zero h).symm⟩
  | succ n ih =>
    by_cases fits : amount ≤ available 0
    · refine ⟨spike 0 amount, ?_, size_spike _ _⟩
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa [spike] using fits
      · simp [spike, Fin.succ_ne_zero]
    · have remaining : amount - available 0 ≤ size (fun i => available i.succ) := by
        simp only [size] at h
        omega
      obtain ⟨tail, below, enough⟩ := ih (fun i => available i.succ)
        (amount - available 0) remaining
      refine ⟨Fin.cases (available 0) tail, ?_, ?_⟩
      · intro i
        exact Fin.cases (Nat.le_refl _) (fun j => below j) i
      · change available 0 + size tail = amount
        rw [enough]
        omega

abbrev Matrix (rows cols : Nat) := Fin rows → Fin cols → Nat

/-- Every pair of finite natural margin vectors with equal totals admits a
transport matrix. The proof fills one row and recurses, retaining all margins. -/
theorem transport_exists {rows cols} (rowTotals : Vector rows) (colTotals : Vector cols)
    (same : size rowTotals = size colTotals) :
    ∃ matrix : Matrix rows cols,
      (∀ i, size (matrix i) = rowTotals i) ∧
      (∀ j, size (fun i => matrix i j) = colTotals j) := by
  induction rows generalizing colTotals with
  | zero =>
    have allZero : colTotals = zeroVector :=
      (eq_of_below_size_eq (fun _ => Nat.zero_le _)
        ((size_zero cols).trans same)).symm
    refine ⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i, ?_⟩
    intro j
    rw [allZero]
    rfl
  | succ rows ih =>
    have enough : rowTotals 0 ≤ size colTotals := by
      simp only [size] at same
      omega
    obtain ⟨first, below, firstTotal⟩ := allocate colTotals (rowTotals 0) enough
    have remaining : size (fun i => rowTotals i.succ) = size (minus colTotals first) := by
      have split := size_split below
      simp only [size] at same
      omega
    obtain ⟨rest, restRows, restCols⟩ := ih (fun i => rowTotals i.succ)
      (minus colTotals first) remaining
    refine ⟨Fin.cases first rest, ?_, ?_⟩
    · intro i
      exact Fin.cases firstTotal (fun j => restRows j) i
    · intro j
      change first j + size (fun i => rest i j) = colTotals j
      rw [restCols]
      exact Nat.add_sub_of_le (below j)

/-- Syntactic cancellation puts each active variable on at most one side.
Variables canceled completely are handled separately as passthrough parameters. -/
def Disjoint {n} (left right : Vector n) : Prop :=
  ∀ i, left i = 0 ∨ right i = 0

/-- General finite-capacity transport for ANY minimal balance vector.
This proves the variable-pair bounds, NOT yet Boolean occurrence-grid coverage. -/
theorem minimal_bounded_transport {n} {left right v : Vector n}
    (disjoint : Disjoint left right) (minimal : Minimal left right v) :
    ∃ matrix : Matrix n n,
      (∀ i, size (matrix i) = left i * v i) ∧
      (∀ j, size (fun i => matrix i j) = right j * v j) ∧
      (∀ i j, matrix i j ≤ left i * right j) := by
  obtain ⟨matrix, rows, cols⟩ := transport_exists
    (fun i => left i * v i) (fun j => right j * v j) minimal.2.1
  refine ⟨matrix, rows, cols, ?_⟩
  intro i j
  have rowBound : matrix i j ≤ left i * v i :=
    by rw [← rows i]; exact coordinate_le_size (matrix i) j
  have colBound : matrix i j ≤ right j * v j :=
    by rw [← cols j]; exact coordinate_le_size (fun k => matrix k j) i
  by_cases li : left i = 0
  · simpa [li] using rowBound
  by_cases rj : right j = 0
  · simpa [rj] using colBound
  have hr : 0 < right j := Nat.pos_of_ne_zero rj
  have ri : right i = 0 := (disjoint i).resolve_left li
  have lj : left j = 0 := (disjoint j).resolve_right rj
  rcases minimal_pair_bound minimal i j hr ri lj with first | second
  · exact Nat.le_trans rowBound (Nat.mul_le_mul_left (left i) first)
  · exact Nat.le_trans colBound (by simpa [Nat.mul_comm] using Nat.mul_le_mul_left (right j) second)

/-! ### Boolean occurrence-grid rounding (CERTIFICATION.md, Lemma 5.4)

The lemmas below work on arbitrary finite matrices. A row/column total records
the multiplicity of its variable, not an independently chosen occurrence.
Rectangle exchanges preserve ALL margins and strictly decrease squared cost.
No coefficient bound, linearity assumption, Bakery symbol, or solver is used.
-/

private def erase {n} (v : Vector n) (index : Fin n) : Vector n :=
  fun i => if i = index then 0 else v i

private theorem size_erase {n} (v : Vector n) (index : Fin n) :
    size v = v index + size (erase v index) := by
  have split : v = plus (spike index (v index)) (erase v index) := by
    funext i
    by_cases same : i = index
    · subst i; simp [plus, spike, erase]
    · simp [plus, spike, erase, same]
  have sum := congrArg size split
  simpa only [size_plus, size_spike] using sum

/-- Compare finite sums when exactly two coordinates may change. The additive
form avoids assuming that subtraction commutes with finite sums. -/
private theorem size_compare_pair {n} (v w : Vector n) (i j : Fin n)
    (different : i ≠ j) (outside : ∀ k, k ≠ i → k ≠ j → v k = w k) :
    size w + v i + v j = size v + w i + w j := by
  have same : erase (erase v i) j = erase (erase w i) j := by
    funext k
    by_cases first : k = i
    · subst k; simp [erase]
    by_cases second : k = j
    · subst k; simp [erase]
    · simp [erase, first, second, outside k first second]
  have hv := size_erase v i
  have hw := size_erase w i
  have hv' := size_erase (erase v i) j
  have hw' := size_erase (erase w i) j
  simp only [erase, if_neg (Ne.symm different)] at hv' hw'
  rw [same] at hv'
  omega

private theorem size_strict {n} {v w : Vector n} (below : Below v w)
    (index : Fin n) (strict : v index < w index) : size v < size w := by
  have bound := size_mono below
  have different : size v ≠ size w := by
    intro same
    have values := congrFun (eq_of_below_size_eq below same) index
    omega
  omega

def transpose {rows cols} (matrix : Matrix rows cols) : Matrix cols rows :=
  fun j i => matrix i j

def Margins {rows cols} (matrix : Matrix rows cols)
    (rowTotals : Vector rows) (colTotals : Vector cols) : Prop :=
  (∀ i, size (matrix i) = rowTotals i) ∧
  (∀ j, size (fun i => matrix i j) = colTotals j)

def cost {rows cols} (matrix : Matrix rows cols) : Nat :=
  size (fun i => size (fun j => matrix i j * matrix i j))

private theorem size_swap {rows cols} (matrix : Matrix rows cols) :
    size (fun i => size (matrix i)) = size (fun j => size (fun i => matrix i j)) := by
  induction rows with
  | zero =>
    change 0 = size (zeroVector (n := cols))
    exact (size_zero cols).symm
  | succ rows ih =>
    change size (matrix 0) + size (fun i => size (matrix i.succ)) =
      size (fun j => matrix 0 j + size (fun i => matrix i.succ j))
    rw [ih]
    exact (size_plus (matrix 0) (fun j => size (fun i => matrix i.succ j))).symm

theorem cost_transpose {rows cols} (matrix : Matrix rows cols) :
    cost (transpose matrix) = cost matrix :=
  (size_swap (fun i j => matrix i j * matrix i j)).symm

private theorem zero_in_column_class {rows cols} (matrix : Matrix rows cols)
    (colTotals : Vector cols) (r : Fin rows) (c : Fin cols)
    (bound : size (matrix r) ≤ size (fun j => if colTotals j = colTotals c then 1 else 0))
    (large : 2 ≤ matrix r c) :
    ∃ c', colTotals c' = colTotals c ∧ matrix r c' = 0 := by
  classical
  apply Classical.byContradiction
  intro none
  have below : Below (fun j => if colTotals j = colTotals c then 1 else 0) (matrix r) := by
    intro j
    by_cases same : colTotals j = colTotals c
    · have positive : matrix r j ≠ 0 := fun zero => none ⟨j, same, zero⟩
      simp only [if_pos same]
      omega
    · simp [same]
  have strict := size_strict below c (by simp; omega)
  omega

private theorem crossing_row {rows cols} (matrix : Matrix rows cols)
    (r : Fin rows) (c c' : Fin cols)
    (same : size (fun i => matrix i c) = size (fun i => matrix i c'))
    (strict : matrix r c' < matrix r c) :
    ∃ r', matrix r' c < matrix r' c' := by
  classical
  apply Classical.byContradiction
  intro none
  have below : Below (fun i => matrix i c') (fun i => matrix i c) := by
    intro i
    change matrix i c' ≤ matrix i c
    have notLess : ¬ matrix i c < matrix i c' := fun lt => none ⟨i, lt⟩
    omega
  have smaller := size_strict below r strict
  omega

/-- One rectangle exchange: (A,0;C,D) becomes (A-1,1;C+1,D-1). -/
def rectangle {rows cols} (matrix : Matrix rows cols)
    (r r' : Fin rows) (c c' : Fin cols) : Matrix rows cols :=
  fun i j => if i = r then
    if j = c then matrix i j - 1 else if j = c' then matrix i j + 1 else matrix i j
  else if i = r' then
    if j = c then matrix i j + 1 else if j = c' then matrix i j - 1 else matrix i j
  else matrix i j

private theorem rectangle_improves {rows cols} (matrix : Matrix rows cols)
    (r r' : Fin rows) (c c' : Fin cols)
    (large : 2 ≤ matrix r c) (empty : matrix r c' = 0)
    (cross : matrix r' c < matrix r' c') :
    (∀ i, size (rectangle matrix r r' c c' i) = size (matrix i)) ∧
    (∀ j, size (fun i => rectangle matrix r r' c c' i j) = size (fun i => matrix i j)) ∧
    cost (rectangle matrix r r' c c') < cost matrix := by
  have dr : r ≠ r' := by intro same; subst r'; omega
  have dc : c ≠ c' := by intro same; subst c'; omega
  have at₁ : rectangle matrix r r' c c' r c = matrix r c - 1 := by simp [rectangle]
  have at₂ : rectangle matrix r r' c c' r c' = 1 := by simp [rectangle, Ne.symm dc, empty]
  have at₃ : rectangle matrix r r' c c' r' c = matrix r' c + 1 := by
    simp [rectangle, Ne.symm dr]
  have at₄ : rectangle matrix r r' c c' r' c' = matrix r' c' - 1 := by
    simp [rectangle, Ne.symm dr, Ne.symm dc]
  have row₁ := size_compare_pair (matrix r) (rectangle matrix r r' c c' r) c c' dc
    (fun j first second => by simp [rectangle, first, second])
  have row₂ := size_compare_pair (matrix r') (rectangle matrix r r' c c' r') c c' dc
    (fun j first second => by simp [rectangle, first, second])
  have col₁ := size_compare_pair (fun i => matrix i c)
    (fun i => rectangle matrix r r' c c' i c) r r' dr
    (fun i first second => by simp [rectangle, first, second])
  have col₂ := size_compare_pair (fun i => matrix i c')
    (fun i => rectangle matrix r r' c c' i c') r r' dr
    (fun i first second => by simp [rectangle, first, second])
  dsimp only at row₁ row₂ col₁ col₂
  rw [at₁, at₂, empty] at row₁
  rw [at₃, at₄] at row₂
  rw [at₁, at₃] at col₁
  rw [at₂, at₄, empty] at col₂
  refine ⟨?_, ?_, ?_⟩
  · intro i
    by_cases first : i = r
    · subst i; omega
    by_cases second : i = r'
    · subst i; omega
    · have unchanged : rectangle matrix r r' c c' i = matrix i := by
        funext j
        simp [rectangle, first, second]
      exact congrArg size unchanged
  · intro j
    by_cases first : j = c
    · subst j; omega
    by_cases second : j = c'
    · subst j; omega
    · have unchanged : (fun i => rectangle matrix r r' c c' i j) = (fun i => matrix i j) := by
        funext i
        simp [rectangle, first, second]
      exact congrArg size unchanged
  · have squares₁ := size_compare_pair (fun j => matrix r j * matrix r j)
      (fun j => rectangle matrix r r' c c' r j * rectangle matrix r r' c c' r j) c c' dc
      (fun j first second => by simp [rectangle, first, second])
    have squares₂ := size_compare_pair (fun j => matrix r' j * matrix r' j)
      (fun j => rectangle matrix r r' c c' r' j * rectangle matrix r r' c c' r' j) c c' dc
      (fun j first second => by simp [rectangle, first, second])
    have whole := size_compare_pair
      (fun i => size (fun j => matrix i j * matrix i j))
      (fun i => size (fun j => rectangle matrix r r' c c' i j * rectangle matrix r r' c c' i j))
      r r' dr (fun i first second => by simp [rectangle, first, second])
    dsimp only at squares₁ squares₂ whole
    rw [at₁, at₂, empty] at squares₁
    rw [at₃, at₄] at squares₂
    simp only [Nat.zero_mul, Nat.one_mul, Nat.add_zero] at squares₁
    have decreased := switch_cost_lt (matrix r c) (matrix r' c) (matrix r' c') large cross
    unfold cost
    omega

/-- Number of occurrences having the same required multiplicity as this one.
Grouping by totals may combine several variable labels; that only enlarges the
class. Thus the document's label-count bounds imply these weaker bounds. -/
def classCount {n} (totals : Vector n) (index : Fin n) : Nat :=
  size (fun j => if totals j = totals index then 1 else 0)

def PairBound {rows cols} (rowTotals : Vector rows) (colTotals : Vector cols) : Prop :=
  ∀ r c, rowTotals r ≤ classCount colTotals c ∨ colTotals c ≤ classCount rowTotals r

private theorem row_improvement {rows cols} (matrix : Matrix rows cols)
    (rowTotals : Vector rows) (colTotals : Vector cols)
    (margins : Margins matrix rowTotals colTotals) (r : Fin rows) (c : Fin cols)
    (large : 2 ≤ matrix r c) (bound : rowTotals r ≤ classCount colTotals c) :
    ∃ updated : Matrix rows cols,
      Margins updated rowTotals colTotals ∧ cost updated < cost matrix := by
  obtain ⟨c', same, empty⟩ := zero_in_column_class matrix colTotals r c
    (by rw [margins.1 r]; exact bound) large
  have equalColumns : size (fun i => matrix i c) = size (fun i => matrix i c') := by
    rw [margins.2 c, margins.2 c', same]
  obtain ⟨r', cross⟩ := crossing_row matrix r c c' equalColumns (by omega)
  obtain ⟨rowsSame, colsSame, decreased⟩ := rectangle_improves matrix r r' c c' large empty cross
  exact ⟨rectangle matrix r r' c c',
    ⟨fun i => (rowsSame i).trans (margins.1 i), fun j => (colsSame j).trans (margins.2 j)⟩,
    decreased⟩

/-- A least-cost witness exists for any nonempty family of finite matrices.
This is an internal classical metaproof, NOT an executable optimizer/certificate
search, and introduces no axiom requiring a solver or a model author's proof. -/
private theorem least_cost {rows cols} (P : Matrix rows cols → Prop)
    (witness : ∃ matrix, P matrix) :
    ∃ matrix, P matrix ∧ ∀ other, P other → cost matrix ≤ cost other := by
  classical
  obtain ⟨seed, valid⟩ := witness
  refine Nat.strongRecOn (motive := fun k => ∀ seed : Matrix rows cols,
    cost seed = k → P seed →
      ∃ matrix, P matrix ∧ ∀ other, P other → cost matrix ≤ cost other)
    (cost seed) ?_ seed rfl valid
  intro k ih seed same valid
  by_cases smaller : ∃ other, P other ∧ cost other < k
  · obtain ⟨other, validOther, lower⟩ := smaller
    exact ih (cost other) lower other rfl validOther
  · refine ⟨seed, valid, ?_⟩
    intro other validOther
    have notLower : ¬ cost other < k := fun lower => smaller ⟨other, validOther, lower⟩
    omega

/-- GENERAL BOOLEAN-GRID THEOREM (the rounding step of Lemma 5.4).

Equal finite margin totals plus the opposite-pair bound imply a zero/one matrix
with EXACTLY those margins. Dimensions, degrees, and repetitions are arbitrary.
Choose a least squared-cost transport. Any entry >=2 admits a decreasing
rectangle, directly or after transposition, contradicting minimality.

This proves existence of the Boolean support. Relating label-count bounds to
minimal balance vectors and lifting their generated sums to native bags remain
separate steps; this theorem alone is NOT an ACU certification algorithm.
-/
theorem boolean_transport_exists {rows cols} (rowTotals : Vector rows) (colTotals : Vector cols)
    (same : size rowTotals = size colTotals) (bound : PairBound rowTotals colTotals) :
    ∃ matrix : Matrix rows cols,
      Margins matrix rowTotals colTotals ∧ ∀ i j, matrix i j ≤ 1 := by
  obtain ⟨matrix, margins, minimal⟩ := least_cost
    (fun matrix => Margins matrix rowTotals colTotals) (transport_exists rowTotals colTotals same)
  refine ⟨matrix, margins, ?_⟩
  intro r c
  apply Classical.byContradiction
  intro tooLarge
  have large : 2 ≤ matrix r c := by omega
  rcases bound r c with rowBound | colBound
  · obtain ⟨updated, valid, lower⟩ := row_improvement matrix rowTotals colTotals margins r c large rowBound
    have impossible := minimal updated valid
    omega
  · have swapped : Margins (transpose matrix) colTotals rowTotals := ⟨margins.2, margins.1⟩
    obtain ⟨updated, valid, lower⟩ := row_improvement
      (transpose matrix) colTotals rowTotals swapped c r large colBound
    have restored : Margins (transpose updated) rowTotals colTotals := ⟨valid.2, valid.1⟩
    have impossible := minimal (transpose updated) restored
    rw [cost_transpose] at impossible lower
    omega

/-- Count occurrence positions carrying a given variable label. -/
def labelCount {n positions} (labels : Fin positions → Fin n) (label : Fin n) : Nat :=
  size (fun i => if labels i = label then 1 else 0)

private theorem size_scale {n} (k : Nat) (v : Vector n) :
    size (fun i => k * v i) = k * size v := by
  induction n with
  | zero => simp [size]
  | succ n ih => simp only [size, ih, Nat.mul_add]

/-- Expanding each variable into its occurrences preserves its weighted total.
This connects actual coefficient vectors to the occurrence-grid margins. -/
theorem size_labels {n positions} (labels : Fin positions → Fin n) (v : Vector n) :
    size (fun i => v (labels i)) = dot (labelCount labels) v := by
  have row : ∀ i, size (fun j => if labels i = j then v j else 0) = v (labels i) := by
    intro i
    have same : (fun j => if labels i = j then v j else 0) = spike (labels i) (v (labels i)) := by
      funext j
      by_cases equal : j = labels i
      · subst j; simp [spike]
      · simp [spike, equal, Ne.symm equal]
    rw [same, size_spike]
  have col : ∀ j, size (fun i => if labels i = j then v j else 0) = labelCount labels j * v j := by
    intro j
    have same : (fun i => if labels i = j then v j else 0) =
        (fun i => v j * (if labels i = j then 1 else 0)) := by
      funext i
      by_cases equal : labels i = j <;> simp [equal]
    rw [same, size_scale, Nat.mul_comm]
    rfl
  have swapped := size_swap (fun i j => if labels i = j then v j else 0)
  simp only [row, col] at swapped
  exact swapped

private theorem label_count_positive {n positions} (labels : Fin positions → Fin n) (index : Fin positions) :
    0 < labelCount labels (labels index) := by
  have bound := coordinate_le_size (fun i => if labels i = labels index then 1 else 0) index
  simpa [labelCount] using bound

private theorem label_count_le_class_count {n positions}
    (labels : Fin positions → Fin n) (v : Vector n) (index : Fin positions) :
    labelCount labels (labels index) ≤ classCount (fun i => v (labels i)) index := by
  apply size_mono
  intro i
  change (if labels i = labels index then 1 else 0) ≤
    (if v (labels i) = v (labels index) then 1 else 0)
  by_cases same : labels i = labels index <;> simp [same]

/-- A minimal balance vector is represented by a Boolean occurrence matrix.

The label counts are the original coefficients (e.g. two positions labelled X
for 2X), while every such position has degree v(X). These GENERAL hypotheses
describe the automatically constructed grid, not per-model/user registration.
No occurrence is mistaken for an independent unification variable.
-/
theorem minimal_boolean_support {n rows cols} (left right v : Vector n)
    (rowLabels : Fin rows → Fin n) (colLabels : Fin cols → Fin n)
    (rowCounts : ∀ i, labelCount rowLabels i = left i)
    (colCounts : ∀ i, labelCount colLabels i = right i)
    (disjoint : Disjoint left right) (minimal : Minimal left right v) :
    ∃ matrix : Matrix rows cols,
      Margins matrix (fun r => v (rowLabels r)) (fun c => v (colLabels c)) ∧
      ∀ r c, matrix r c ≤ 1 := by
  have same : size (fun r => v (rowLabels r)) = size (fun c => v (colLabels c)) := by
    rw [size_labels, size_labels]
    have rowsSame : labelCount rowLabels = left := funext rowCounts
    have colsSame : labelCount colLabels = right := funext colCounts
    rw [rowsSame, colsSame]
    exact minimal.2.1
  apply boolean_transport_exists _ _ same
  intro r c
  have lp : 0 < left (rowLabels r) := by
    rw [← rowCounts]
    exact label_count_positive rowLabels r
  have rp : 0 < right (colLabels c) := by
    rw [← colCounts]
    exact label_count_positive colLabels c
  have rz : right (rowLabels r) = 0 := (disjoint _).resolve_left (Nat.ne_of_gt lp)
  have lz : left (colLabels c) = 0 := (disjoint _).resolve_right (Nat.ne_of_gt rp)
  rcases minimal_pair_bound minimal (rowLabels r) (colLabels c) rp rz lz with first | second
  · left
    have count := label_count_le_class_count colLabels v c
    rw [colCounts] at count
    exact Nat.le_trans first count
  · right
    have count := label_count_le_class_count rowLabels v r
    rw [rowCounts] at count
    exact Nat.le_trans second count

private theorem label_count_exists {n positions} (labels : Fin positions → Fin n)
    (label : Fin n) (positive : 0 < labelCount labels label) : ∃ i, labels i = label := by
  classical
  apply Classical.byContradiction
  intro none
  have zero : (fun i => if labels i = label then 1 else 0) = zeroVector := by
    funext i
    have different : labels i ≠ label := fun same => none ⟨i, same⟩
    simp [different, zeroVector]
  unfold labelCount at positive
  rw [zero, size_zero] at positive
  omega

/-- COMPLETE OCCURRENCE REPRESENTATION of an active minimal balance vector.

Every minimal vector has a NONEMPTY Boolean support with its exact degrees.
The final hypothesis merely excludes inactive coordinates from this active
vector; canceled/inactive unification variables are separate passthrough images,
not silently forced to empty by the eventual unification rule.

This is Lemma 5.4, for arbitrary finite coefficient vectors after cancellation.
Combined with decompose_minimal, it represents EVERY balanced active vector as
a finite sum of support-degree vectors. The later supportGenerators and Sharing
sections enumerate that family and rebuild checked symbolic/native substitutions.
-/
theorem minimal_nonempty_boolean_support {n rows cols} (left right v : Vector n)
    (rowLabels : Fin rows → Fin n) (colLabels : Fin cols → Fin n)
    (rowCounts : ∀ i, labelCount rowLabels i = left i)
    (colCounts : ∀ i, labelCount colLabels i = right i)
    (disjoint : Disjoint left right) (minimal : Minimal left right v)
    (active : ∀ i, left i = 0 → right i = 0 → v i = 0) :
    ∃ matrix : Matrix rows cols,
      Margins matrix (fun r => v (rowLabels r)) (fun c => v (colLabels c)) ∧
      (∀ r c, matrix r c ≤ 1) ∧ ∃ r c, matrix r c = 1 := by
  obtain ⟨matrix, margins, boolean⟩ := minimal_boolean_support
    left right v rowLabels colLabels rowCounts colCounts disjoint minimal
  refine ⟨matrix, margins, boolean, ?_⟩
  apply Classical.byContradiction
  intro none
  have allZero : ∀ r c, matrix r c = 0 := by
    intro r c
    have small := boolean r c
    have notOne : matrix r c ≠ 1 := fun one => none ⟨r, c, one⟩
    omega
  have rowZero : ∀ r, v (rowLabels r) = 0 := by
    intro r
    have zero : matrix r = zeroVector := funext (allZero r)
    have same := margins.1 r
    rw [zero, size_zero] at same
    exact same.symm
  have colZero : ∀ c, v (colLabels c) = 0 := by
    intro c
    have zero : (fun r => matrix r c) = zeroVector := funext (fun r => allZero r c)
    have same := margins.2 c
    rw [zero, size_zero] at same
    exact same.symm
  apply minimal.1
  funext i
  change v i = 0
  by_cases leftZero : left i = 0
  · by_cases rightZero : right i = 0
    · exact active i leftZero rightZero
    · obtain ⟨c, same⟩ := label_count_exists colLabels i
        (by rw [colCounts]; exact Nat.pos_of_ne_zero rightZero)
      simpa only [same] using colZero c
  · obtain ⟨r, same⟩ := label_count_exists rowLabels i
      (by rw [rowCounts]; exact Nat.pos_of_ne_zero leftZero)
    simpa only [same] using rowZero r

private theorem member_below_total {n} {parts : List (Vector n)} {v : Vector n}
    (member : v ∈ parts) : Below v (total parts) := by
  induction parts with
  | nil => cases member
  | cons first rest ih =>
    rcases List.mem_cons.mp member with same | member
    · subst v
      intro i
      exact Nat.le_add_right _ _
    · intro i
      exact Nat.le_trans (ih member i) (Nat.le_add_left _ _)

/-- Soundness of support-degree vectors: each cell contributes once to each
side. Uniform label margins therefore satisfy the original balance equation.
Boolean/nonempty conditions are not needed for this direction. -/
theorem balanced_of_margins {n rows cols} (left right v : Vector n)
    (rowLabels : Fin rows → Fin n) (colLabels : Fin cols → Fin n)
    (rowCounts : ∀ i, labelCount rowLabels i = left i)
    (colCounts : ∀ i, labelCount colLabels i = right i)
    (matrix : Matrix rows cols)
    (margins : Margins matrix (fun r => v (rowLabels r)) (fun c => v (colLabels c))) :
    Balanced left right v := by
  have same := size_swap matrix
  simp only [margins.1, margins.2] at same
  rw [size_labels, size_labels] at same
  have rowsSame : labelCount rowLabels = left := funext rowCounts
  have colsSame : labelCount colLabels = right := funext colCounts
  rw [rowsSame, colsSame] at same
  exact same

/-- NUMERIC FINITE-SHARING COMPLETENESS, uniformly for arbitrary repetitions.

Every balanced ACTIVE vector is a finite sum of degree vectors of nonempty
Boolean supports, including the zero vector via the empty sum. The same input
labels/coefficients are used by every summand. Inactive coordinates are handled
outside this active balance by independent passthrough parameters.

This establishes the multiplicity argument needed by Proposition 5.5. It is a
general metatheorem, not a certificate-search implementation or an assumption
that a particular enumerated support list is exhaustive.
-/
theorem decompose_boolean_supports {n rows cols} (left right v : Vector n)
    (rowLabels : Fin rows → Fin n) (colLabels : Fin cols → Fin n)
    (rowCounts : ∀ i, labelCount rowLabels i = left i)
    (colCounts : ∀ i, labelCount colLabels i = right i)
    (disjoint : Disjoint left right) (balanced : Balanced left right v)
    (active : ∀ i, left i = 0 → right i = 0 → v i = 0) :
    ∃ parts : List (Vector n), total parts = v ∧
      ∀ w ∈ parts, ∃ matrix : Matrix rows cols,
        Margins matrix (fun r => w (rowLabels r)) (fun c => w (colLabels c)) ∧
        (∀ r c, matrix r c ≤ 1) ∧ ∃ r c, matrix r c = 1 := by
  obtain ⟨parts, minimal, same⟩ := decompose_minimal left right v balanced
  refine ⟨parts, same, ?_⟩
  intro w member
  have below := member_below_total member
  rw [same] at below
  have activePart : ∀ i, left i = 0 → right i = 0 → w i = 0 := by
    intro i hl hr
    have bound := below i
    rw [active i hl hr] at bound
    exact Nat.eq_zero_of_le_zero bound
  exact minimal_nonempty_boolean_support left right w rowLabels colLabels
    rowCounts colCounts disjoint (minimal w member) activePart

/-- Both directions of the multiplicity-level finite-sharing rule.
The representation is a solution SET; minimality is not required of the
submitted supports, and redundant/overlapping generators do not invalidate it.
This theorem supplies the once-for-all numeric foundation for the later computed
support family, native image reconstruction, and typed sharing replay constructors.
-/
theorem boolean_supports_exact {n rows cols} (left right v : Vector n)
    (rowLabels : Fin rows → Fin n) (colLabels : Fin cols → Fin n)
    (rowCounts : ∀ i, labelCount rowLabels i = left i)
    (colCounts : ∀ i, labelCount colLabels i = right i)
    (disjoint : Disjoint left right)
    (active : ∀ i, left i = 0 → right i = 0 → v i = 0) :
    Balanced left right v ↔
      ∃ parts : List (Vector n), total parts = v ∧
        ∀ w ∈ parts, ∃ matrix : Matrix rows cols,
          Margins matrix (fun r => w (rowLabels r)) (fun c => w (colLabels c)) ∧
          (∀ r c, matrix r c ≤ 1) ∧ ∃ r c, matrix r c = 1 := by
  constructor
  · intro balanced
    exact decompose_boolean_supports left right v rowLabels colLabels
      rowCounts colCounts disjoint balanced active
  · rintro ⟨parts, same, represented⟩
    rw [← same]
    apply total_balanced
    intro w member
    obtain ⟨matrix, margins, _boolean, _nonempty⟩ := represented w member
    exact balanced_of_margins left right w rowLabels colLabels rowCounts colCounts matrix margins

/-! ### Executable exhaustive support family

The grid dimensions come from the input occurrences, not a search bound.
Enumerate every zero/one grid; retain precisely the nonempty grids whose row
and column degrees agree at repeated labels. Equal degree vectors from different
grids may remain duplicated. No supplied support table is trusted complete.
-/

def booleanVectors : (n : Nat) → List (Vector n)
  | 0 => [zeroVector]
  | n + 1 => (booleanVectors n).flatMap fun tail =>
      [Fin.cases 0 tail, Fin.cases 1 tail]

theorem mem_booleanVectors {n} (v : Vector n) :
    v ∈ booleanVectors n ↔ ∀ i, v i ≤ 1 := by
  induction n with
  | zero =>
    have same : v = zeroVector := funext fun i => Fin.elim0 i
    subst v
    simp [booleanVectors]
  | succ n ih =>
    constructor
    · intro member
      obtain ⟨tail, member, same⟩ := List.mem_flatMap.mp member
      have small := (ih tail).mp member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at same
      rcases same with same | same
      · subst v
        exact Fin.cases (Nat.zero_le _) small
      · subst v
        exact Fin.cases (Nat.le_refl _) small
    · intro small
      let tail : Vector n := fun i => v i.succ
      have member := (ih tail).mpr (fun i => small i.succ)
      apply List.mem_flatMap.mpr
      refine ⟨tail, member, ?_⟩
      have head := small 0
      have shape : v = Fin.cases (v 0) tail :=
        funext (Fin.cases rfl (fun _ => rfl))
      rw [shape]
      have cases : v 0 = 0 ∨ v 0 = 1 := by omega
      rcases cases with zero | one
      · rw [zero]
        exact List.mem_cons_self
      · rw [one]
        exact List.mem_cons_of_mem _ List.mem_cons_self

def booleanMatrices : (rows cols : Nat) → List (Matrix rows cols)
  | 0, _ => [fun i => Fin.elim0 i]
  | rows + 1, cols => (booleanVectors cols).flatMap fun first =>
      (booleanMatrices rows cols).map fun rest => Fin.cases first rest

theorem mem_booleanMatrices {rows cols} (matrix : Matrix rows cols) :
    matrix ∈ booleanMatrices rows cols ↔ ∀ r c, matrix r c ≤ 1 := by
  induction rows with
  | zero =>
    have same : matrix = fun i => Fin.elim0 i := funext fun i => Fin.elim0 i
    subst matrix
    simp [booleanMatrices]
  | succ rows ih =>
    constructor
    · intro member
      obtain ⟨first, firstMember, member⟩ := List.mem_flatMap.mp member
      obtain ⟨rest, restMember, same⟩ := List.mem_map.mp member
      subst matrix
      exact Fin.cases ((mem_booleanVectors first).mp firstMember)
        ((ih rest).mp restMember)
    · intro small
      let rest : Matrix rows cols := fun r => matrix r.succ
      refine List.mem_flatMap.mpr ⟨matrix 0,
        (mem_booleanVectors _).mpr (small 0), List.mem_map.mpr ⟨rest,
          (ih rest).mpr (fun r => small r.succ), ?_⟩⟩
      exact funext (Fin.cases rfl (fun _ => rfl))

private def peak : {n : Nat} → Vector n → Nat
  | 0, _ => 0
  | _ + 1, v => max (v 0) (peak (fun i => v i.succ))

private theorem peak_le {n} (v : Vector n) (bound : Nat) (small : ∀ i, v i ≤ bound) :
    peak v ≤ bound := by
  induction n with
  | zero => exact Nat.zero_le _
  | succ n ih =>
    exact Nat.max_le.mpr ⟨small 0, ih _ (fun i => small i.succ)⟩

private theorem coordinate_le_peak {n} (v : Vector n) (i : Fin n) : v i ≤ peak v := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    exact Fin.cases (Nat.le_max_left _ _)
      (fun j => Nat.le_trans (ih (fun i => v i.succ) j) (Nat.le_max_right _ _)) i

/-- Recover a variable's degree from its occurrences. Max is only a convenient
computable projection: the subsequent margin check requires ALL its occurrences
to have that same degree. Absent variables have degree zero here, and are later
represented by separate passthrough parameters in the native substitution. -/
def supportDegrees {n rows cols}
    (rowLabels : Fin rows → Fin n) (colLabels : Fin cols → Fin n)
    (matrix : Matrix rows cols) : Vector n := fun i =>
  max (peak (fun r => if rowLabels r = i then size (matrix r) else 0))
    (peak (fun c => if colLabels c = i then size (fun r => matrix r c) else 0))

theorem supportDegrees_eq {n rows cols} (v : Vector n)
    (rowLabels : Fin rows → Fin n) (colLabels : Fin cols → Fin n)
    (matrix : Matrix rows cols)
    (margins : Margins matrix (fun r => v (rowLabels r)) (fun c => v (colLabels c)))
    (active : ∀ i, labelCount rowLabels i = 0 → labelCount colLabels i = 0 → v i = 0) :
    supportDegrees rowLabels colLabels matrix = v := by
  funext i
  have upper : supportDegrees rowLabels colLabels matrix i ≤ v i := by
    apply Nat.max_le.mpr
    constructor
    · apply peak_le
      intro r
      split
      · rename_i same
        simpa only [same] using Nat.le_of_eq (margins.1 r)
      · exact Nat.zero_le _
    · apply peak_le
      intro c
      split
      · rename_i same
        simpa only [same] using Nat.le_of_eq (margins.2 c)
      · exact Nat.zero_le _
  apply Nat.le_antisymm upper
  by_cases rowZero : labelCount rowLabels i = 0
  · by_cases colZero : labelCount colLabels i = 0
    · rw [active i rowZero colZero]
      exact Nat.zero_le _
    · obtain ⟨c, same⟩ := label_count_exists colLabels i (Nat.pos_of_ne_zero colZero)
      have bound := coordinate_le_peak
        (fun c => if colLabels c = i then size (fun r => matrix r c) else 0) c
      simp only [margins.2 c, same] at bound
      exact Nat.le_trans bound (Nat.le_max_right _ _)
  · obtain ⟨r, same⟩ := label_count_exists rowLabels i (Nat.pos_of_ne_zero rowZero)
    have bound := coordinate_le_peak
      (fun r => if rowLabels r = i then size (matrix r) else 0) r
    simp only [margins.1 r, same] at bound
    exact Nat.le_trans bound (Nat.le_max_left _ _)

def ValidSupport {n rows cols}
    (rowLabels : Fin rows → Fin n) (colLabels : Fin cols → Fin n)
    (matrix : Matrix rows cols) : Prop :=
  Margins matrix
    (fun r => supportDegrees rowLabels colLabels matrix (rowLabels r))
    (fun c => supportDegrees rowLabels colLabels matrix (colLabels c)) ∧
  ∃ r c, matrix r c = 1

instance {n rows cols} (rowLabels : Fin rows → Fin n) (colLabels : Fin cols → Fin n)
    (matrix : Matrix rows cols) : Decidable (ValidSupport rowLabels colLabels matrix) :=
  inferInstanceAs (Decidable ((_ ∧ _) ∧ ∃ r c, matrix r c = 1))

/-- All finite balanced supports, computed from occurrence labels only. -/
def supportGenerators {n rows cols}
    (rowLabels : Fin rows → Fin n) (colLabels : Fin cols → Fin n) : List (Vector n) :=
  ((booleanMatrices rows cols).filter
    (fun matrix => decide (ValidSupport rowLabels colLabels matrix))).map
      (supportDegrees rowLabels colLabels)

theorem supportGenerators_sound {n rows cols} (left right : Vector n)
    (rowLabels : Fin rows → Fin n) (colLabels : Fin cols → Fin n)
    (rowCounts : ∀ i, labelCount rowLabels i = left i)
    (colCounts : ∀ i, labelCount colLabels i = right i)
    (v : Vector n) (member : v ∈ supportGenerators rowLabels colLabels) :
    Balanced left right v := by
  obtain ⟨matrix, member, same⟩ := List.mem_map.mp member
  have valid := of_decide_eq_true (List.mem_filter.mp member).2
  rw [← same]
  exact balanced_of_margins left right _ rowLabels colLabels rowCounts colCounts matrix valid.1

theorem supportGenerators_cover {n rows cols} (v : Vector n)
    (rowLabels : Fin rows → Fin n) (colLabels : Fin cols → Fin n)
    (active : ∀ i, labelCount rowLabels i = 0 → labelCount colLabels i = 0 → v i = 0)
    (matrix : Matrix rows cols)
    (margins : Margins matrix (fun r => v (rowLabels r)) (fun c => v (colLabels c)))
    (boolean : ∀ r c, matrix r c ≤ 1) (nonempty : ∃ r c, matrix r c = 1) :
    v ∈ supportGenerators rowLabels colLabels := by
  have same := supportDegrees_eq v rowLabels colLabels matrix margins active
  apply List.mem_map.mpr
  refine ⟨matrix, List.mem_filter.mpr ⟨(mem_booleanMatrices matrix).mpr boolean, ?_⟩, same⟩
  apply decide_eq_true
  exact ⟨by simpa only [same] using margins, nonempty⟩

/-- EXACTNESS OF THE COMPUTED LIST. No completeness hypothesis about a proposed
list remains: Boolean enumeration and its filter are proved exhaustive. This is
numeric exactness, not yet a native bag rule or a general certification solver.
All coefficients and dimensions are arbitrary; repetitions are not bounded. -/
theorem supportGenerators_exact {n rows cols} (left right v : Vector n)
    (rowLabels : Fin rows → Fin n) (colLabels : Fin cols → Fin n)
    (rowCounts : ∀ i, labelCount rowLabels i = left i)
    (colCounts : ∀ i, labelCount colLabels i = right i)
    (disjoint : Disjoint left right)
    (active : ∀ i, left i = 0 → right i = 0 → v i = 0) :
    Generated (supportGenerators rowLabels colLabels) v ↔ Balanced left right v := by
  constructor
  · rintro ⟨parts, members, same⟩
    rw [← same]
    exact total_balanced left right parts (fun w member =>
      supportGenerators_sound left right rowLabels colLabels rowCounts colCounts w (members w member))
  · intro balanced
    obtain ⟨parts, same, supports⟩ := decompose_boolean_supports left right v
      rowLabels colLabels rowCounts colCounts disjoint balanced active
    refine ⟨parts, ?_, same⟩
    intro w member
    obtain ⟨matrix, margins, boolean, nonempty⟩ := supports w member
    apply supportGenerators_cover w rowLabels colLabels _ matrix margins boolean nonempty
    intro i hl hr
    have bound := member_below_total member i
    rw [same, active i (by rw [← rowCounts]; exact hl)
      (by rw [← colCounts]; exact hr)] at bound
    exact Nat.eq_zero_of_le_zero bound

/-- Convert a generated sum to one multiplicity per PARAMETER POSITION.
Positions, not vector equality, are essential: duplicate support vectors must
not duplicate an element's assigned multiplicity. -/
theorem generated_weights {n} (generators : List (Vector n)) (v : Vector n)
    (generated : Generated generators v) :
    ∃ weights : Vector generators.length,
      ∀ i, dot (fun j => generators.get j i) weights = v i := by
  obtain ⟨parts, members, same⟩ := generated
  have build : ∀ parts : List (Vector n), (∀ w ∈ parts, w ∈ generators) →
      ∃ weights : Vector generators.length,
        ∀ i, dot (fun j => generators.get j i) weights = total parts i := by
    intro parts
    induction parts with
    | nil =>
      intro _
      refine ⟨zeroVector, fun i => ?_⟩
      simp only [dot, zeroVector, Nat.mul_zero, total]
      exact size_zero _
    | cons first rest ih =>
      intro members
      obtain ⟨index, atIndex⟩ := List.mem_iff_get.mp (members first List.mem_cons_self)
      obtain ⟨weights, sum⟩ := ih (fun w member => members w (List.mem_cons_of_mem _ member))
      refine ⟨plus (spike index 1) weights, fun i => ?_⟩
      rw [dot_plus, dot_spike, Nat.mul_one, atIndex, sum]
      rfl
  obtain ⟨weights, sum⟩ := build parts members
  exact ⟨weights, fun i => (sum i).trans (congrFun same i)⟩

/-- Exchange finite sums: applying coefficients to reconstructed parameter
images is the same as applying each generator's balance to the parameters. -/
theorem dot_images {n m} (coeff : Vector n) (generators : Fin m → Vector n)
    (weights : Vector m) :
    dot coeff (fun i => dot (fun j => generators j i) weights) =
      dot (fun j => dot coeff (generators j)) weights := by
  unfold dot
  calc
    _ = size (fun i => size (fun j => coeff i * generators j i * weights j)) := by
      apply congrArg size
      funext i
      simpa only [Nat.mul_assoc] using
        (size_scale (coeff i) (fun j => generators j i * weights j)).symm
    _ = size (fun j => size (fun i => coeff i * generators j i * weights j)) :=
      size_swap _
    _ = _ := by
      apply congrArg size
      funext j
      simpa only [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
        size_scale (weights j) (fun i => coeff i * generators j i)

theorem balanced_images {n m} (left right : Vector n)
    (generators : Fin m → Vector n) (sound : ∀ j, Balanced left right (generators j))
    (weights : Vector m) :
    Balanced left right (fun i => dot (fun j => generators j i) weights) := by
  unfold Balanced
  rw [dot_images, dot_images]
  exact congrArg (fun coeff => dot coeff weights) (funext sound)

/-! ### Collect multiplicity witnesses into actual finite bags

Lists here are INTERNAL bags of atom classes, not a new model representation.
For every class a, generated_weights supplies one number per support POSITION.
Put that many copies of a into the corresponding parameter bag. The dictionary
is finite because the input bags are finite; arbitrary payload values are kept.
Permutation, not literal list equality, is the reconstruction guarantee.
-/

def listCopies {α : Type} : Nat → List α → List α
  | 0, _ => []
  | k + 1, xs => xs ++ listCopies k xs

def listSum {α : Type} : {n : Nat} → Vector n → (Fin n → List α) → List α
  | 0, _, _ => []
  | _ + 1, coeff, bags => listCopies (coeff 0) (bags 0) ++
      listSum (fun i => coeff i.succ) (fun i => bags i.succ)

theorem count_listCopies {α : Type} [DecidableEq α] (a : α) (k : Nat) (xs : List α) :
    List.count a (listCopies k xs) = k * List.count a xs := by
  induction k with
  | zero => simp [listCopies]
  | succ k ih => simp only [listCopies, List.count_append, ih, Nat.succ_mul, Nat.add_comm]

theorem count_listSum {α : Type} [DecidableEq α] {n} (a : α)
    (coeff : Vector n) (bags : Fin n → List α) :
    List.count a (listSum coeff bags) = dot coeff (fun i => List.count a (bags i)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [listSum, List.count_append, count_listCopies, dot, size]
    exact congrArg (fun tail => coeff 0 * List.count a (bags 0) + tail)
      (ih (fun i => coeff i.succ) (fun i => bags i.succ))

private def dictionary {α : Type} [DecidableEq α] : List α → List α
  | [] => []
  | a :: rest => let tail := dictionary rest
      if a ∈ tail then tail else a :: tail

private theorem dictionary_mem {α : Type} [DecidableEq α] (a : α) (xs : List α) :
    a ∈ dictionary xs ↔ a ∈ xs := by
  induction xs generalizing a with
  | nil => rfl
  | cons first rest ih =>
    simp only [dictionary]
    split
    · rename_i present
      have present := (ih first).mp present
      simpa only [List.mem_cons, ih] using
        (show a ∈ rest ↔ a = first ∨ a ∈ rest from
          ⟨Or.inr, fun h => h.elim (fun same => same ▸ present) id⟩)
    · simp only [List.mem_cons, ih]

private theorem dictionary_nodup {α : Type} [DecidableEq α] (xs : List α) :
    (dictionary xs).Nodup := by
  induction xs with
  | nil => exact List.nodup_nil
  | cons first rest ih =>
    simp only [dictionary]
    split
    · exact ih
    · exact List.nodup_cons.mpr ⟨‹_›, ih⟩

private theorem count_dictionary {α : Type} [DecidableEq α] (xs : List α)
    (nodup : xs.Nodup) (weights : α → Nat) (a : α) :
    List.count a (xs.flatMap (fun b => List.replicate (weights b) b)) =
      if a ∈ xs then weights a else 0 := by
  induction xs with
  | nil => simp
  | cons first rest ih =>
    have distinct := List.nodup_cons.mp nodup
    simp only [List.flatMap_cons, List.count_append, ih distinct.2]
    by_cases same : a = first
    · subst a
      simp [distinct.1]
    · simp [List.count_replicate, same, Ne.symm same]

/-- Lift numeric generation to finite bags of ANY element type. Duplicated
generator vectors are assigned by index, preserving one shared parameter scope.
This classical witness construction belongs to the general metatheorem, not
runtime search and not a per-model registration obligation. -/
theorem lists_generated {α : Type} [DecidableEq α] {n} (generators : List (Vector n))
    (bags : Fin n → List α)
    (generated : ∀ a, Generated generators (fun i => List.count a (bags i))) :
    ∃ parameters : Fin generators.length → List α,
      ∀ i, (bags i).Perm (listSum (fun j => generators.get j i) parameters) := by
  classical
  let atoms := dictionary ((List.finRange n).flatMap bags)
  have contains : ∀ a i, a ∈ bags i → a ∈ atoms := by
    intro a i member
    apply (dictionary_mem a _).mpr
    exact List.mem_flatMap.mpr ⟨i, List.mem_ofFn.mpr ⟨i, rfl⟩, member⟩
  have witnesses := fun a => generated_weights generators _ (generated a)
  let weights := fun a => Classical.choose (witnesses a)
  have sums : ∀ a i, dot (fun j => generators.get j i) (weights a) = List.count a (bags i) :=
    fun a => Classical.choose_spec (witnesses a)
  let parameters := fun j => atoms.flatMap (fun a => List.replicate (weights a j) a)
  refine ⟨parameters, fun i => List.perm_iff_count.mpr (fun a => ?_)⟩
  rw [count_listSum]
  have counts : ∀ j, List.count a (parameters j) = if a ∈ atoms then weights a j else 0 :=
    fun j => count_dictionary atoms (dictionary_nodup _) (fun a => weights a j) a
  by_cases member : a ∈ atoms
  · simp only [counts, if_pos member]
    exact (sums a i).symm
  · have zero : List.count a (bags i) = 0 :=
      List.count_eq_zero.mpr (fun present => member (contains a i present))
    simp only [counts, if_neg member, dot, Nat.mul_zero, zero]
    exact (size_zero _).symm

/-! ### Finite sharing in the EXISTING indexed structural semantics

Each support gets ONE bag parameter, shared by every original variable image.
Flattening/counts are internal proof auxiliaries; the conclusion relates ordinary
registered constructor trees by Structural.Indexed.Eq, without new axioms.
-/

def bagSum {s} (op : sig.ACUOp s) :
    {n : Nat} → Vector n → (Fin n → Tree sig s) → Tree sig s
  | 0, _, _ => zero sig op
  | _ + 1, coeff, values => add sig op (bagCopies op (coeff 0) (values 0))
      (bagSum op (fun i => coeff i.succ) (fun i => values i.succ))

theorem count_bagSum (profile : Profile sig) {s n} (op : sig.ACUOp s)
    (coeff : Vector n) (values : Fin n → Tree sig s) (a : QTree sig s)
    [DecidableEq (QTree sig s)] :
    List.count a (flatten profile (bagSum op coeff values)) =
      dot coeff (fun i => List.count a (flatten profile (values i))) := by
  induction n with
  | zero => simp [bagSum, flatten_zero, dot, size]
  | succ n ih =>
    simp only [bagSum, flatten_add, List.count_append, count_flatten_repeat, dot, size]
    exact congrArg (fun tail => coeff 0 * List.count a (flatten profile (values 0)) + tail)
      (ih (fun i => coeff i.succ) (fun i => values i.succ))

theorem bagSum_balance (profile : Profile sig) {s n} (op : sig.ACUOp s)
    (left right : Vector n) (values : Fin n → Tree sig s) [DecidableEq (QTree sig s)] :
    Structural.Indexed.Eq sig (bagSum op left values) (bagSum op right values) ↔
      ∀ a : QTree sig s, Balanced left right
        (fun i => List.count a (flatten profile (values i))) := by
  classical
  constructor
  · intro same a
    have counts := (flatten_congr profile same).count_eq a
    simpa only [count_bagSum] using counts
  · intro balanced
    apply eq_of_flatten_perm profile op
    apply List.perm_iff_count.mpr
    intro a
    simpa only [count_bagSum] using balanced a

private theorem qtree_bagCopies {s} (op : sig.ACUOp s) (k : Nat)
    (value : Tree sig s) (atoms : List (QTree sig s)) (folded : qtree value = qfold op atoms) :
    qtree (bagCopies op k value) = qfold op (listCopies k atoms) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change qadd op (qtree value) (qtree (bagCopies op k value)) = _
    rw [folded, ih]
    exact (qfold_append op atoms (listCopies k atoms)).symm

private theorem qtree_bagSum {s n} (op : sig.ACUOp s) (coeff : Vector n)
    (values : Fin n → Tree sig s) (atoms : Fin n → List (QTree sig s))
    (folded : ∀ i, qtree (values i) = qfold op (atoms i)) :
    qtree (bagSum op coeff values) = qfold op (listSum coeff atoms) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change qadd op (qtree (bagCopies op (coeff 0) (values 0)))
      (qtree (bagSum op (fun i => coeff i.succ) (fun i => values i.succ))) = _
    rw [qtree_bagCopies op _ _ _ (folded 0),
      ih (fun i => coeff i.succ) (fun i => values i.succ) (fun i => atoms i.succ)
        (fun i => folded i.succ)]
    exact (qfold_append op _ _).symm

/-- Exact finite sharing for active bags. The unit condition concerns only
inactive coordinates of this intermediate balance, NOT original canceled inputs.
The public tree rule below restores those inputs as independent passthroughs. -/
theorem bags_generated_active (profile : Profile sig) {s n rows cols}
    (op : sig.ACUOp s) (left right : Vector n)
    (rowLabels : Fin rows → Fin n) (colLabels : Fin cols → Fin n)
    (rowCounts : ∀ i, labelCount rowLabels i = left i)
    (colCounts : ∀ i, labelCount colLabels i = right i)
    (disjoint : Disjoint left right) (values : Fin n → Tree sig s)
    (active : ∀ i, left i = 0 → right i = 0 →
      Structural.Indexed.Eq sig (values i) (zero sig op)) :
    Structural.Indexed.Eq sig (bagSum op left values) (bagSum op right values) ↔
      ∃ parameters : Fin (supportGenerators rowLabels colLabels).length → Tree sig s,
        ∀ i, Structural.Indexed.Eq sig (values i)
          (bagSum op (fun j => (supportGenerators rowLabels colLabels).get j i) parameters) := by
  classical
  let generators := supportGenerators rowLabels colLabels
  constructor
  · intro equation
    have balanced := (bagSum_balance profile op left right values).mp equation
    have generated : ∀ a : QTree sig s, Generated generators
        (fun i => List.count a (flatten profile (values i))) := by
      intro a
      apply (supportGenerators_exact left right _ rowLabels colLabels rowCounts colCounts disjoint ?_).mpr
        (balanced a)
      intro i hl hr
      have count := (flatten_congr profile (active i hl hr)).count_eq a
      simpa only [flatten_zero, List.count_nil] using count
    obtain ⟨pieces, represented⟩ := lists_generated generators (fun i => flatten profile (values i)) generated
    have reps := fun j => Quotient.exists_rep (qfold op (pieces j))
    let parameters := fun j => Classical.choose (reps j)
    have folded : ∀ j, qtree (parameters j) = qfold op (pieces j) :=
      fun j => Classical.choose_spec (reps j)
    refine ⟨parameters, fun i => (qtree_eq_iff _ _).mp ?_⟩
    exact (qfold_flatten profile op (values i)).symm.trans
      ((qfold_perm op (represented i)).trans
        (qtree_bagSum op _ parameters pieces folded).symm)
  · rintro ⟨parameters, images⟩
    apply (bagSum_balance profile op left right values).mpr
    intro a
    have counts : ∀ i, List.count a (flatten profile (values i)) =
        dot (fun j => generators.get j i)
          (fun j => List.count a (flatten profile (parameters j))) := by
      intro i
      have same := (flatten_congr profile (images i)).count_eq a
      simpa only [count_bagSum] using same
    have generated := balanced_images left right (fun j => generators.get j)
      (fun j => supportGenerators_sound left right rowLabels colLabels rowCounts colCounts _
        (List.get_mem _ j)) (fun j => List.count a (flatten profile (parameters j)))
    simpa only [counts] using generated

theorem bagSum_congr {s n} (op : sig.ACUOp s) (coeff : Vector n)
    (values other : Fin n → Tree sig s)
    (same : ∀ i, coeff i ≠ 0 → Structural.Indexed.Eq sig (values i) (other i)) :
    Structural.Indexed.Eq sig (bagSum op coeff values) (bagSum op coeff other) := by
  induction n with
  | zero => exact .refl _
  | succ n ih =>
    apply Structural.Indexed.Eq.congr (sig.add op)
    apply Eqs.cons
    · by_cases zero : coeff 0 = 0
      · simp only [zero, bagCopies]
        exact .refl _
      · exact repeat_congr op _ (same 0 zero)
    · exact .cons (ih (fun i => coeff i.succ) (fun i => values i.succ)
        (fun i => other i.succ) (fun i => same i.succ)) .nil

def sharingImages {s n} (op : sig.ACUOp s) (left right : Vector n)
    (generators : List (Vector n)) (parameters : Fin generators.length → Tree sig s)
    (passthrough : Fin n → Tree sig s) : Fin n → Tree sig s := fun i =>
  if left i = 0 ∧ right i = 0 then passthrough i
  else bagSum op (fun j => generators.get j i) parameters

/-- FINITE-SHARING EXACTNESS in registered tree equality, with EVERY input image.

  sum_i left_i * X_i =B sum_i right_i * X_i
  ==================================================== FiniteSharing
  EXISTS shared Z_s and independent inactive P_i,
    FOR ALL i, X_i =B (P_i if inactive; sum_s degree_i(s) * Z_s otherwise)

Zero-sided grids and the empty equation are included. No user semantic bridge,
linearity assumption, fixed arity/coefficients, or trusted generator table occurs.
This is a general proof rule, not yet certificate-search/replay implementation.
-/
theorem bags_generated (profile : Profile sig) {s n rows cols}
    (op : sig.ACUOp s) (left right : Vector n)
    (rowLabels : Fin rows → Fin n) (colLabels : Fin cols → Fin n)
    (rowCounts : ∀ i, labelCount rowLabels i = left i)
    (colCounts : ∀ i, labelCount colLabels i = right i)
    (disjoint : Disjoint left right) (values : Fin n → Tree sig s) :
    Structural.Indexed.Eq sig (bagSum op left values) (bagSum op right values) ↔
      ∃ parameters : Fin (supportGenerators rowLabels colLabels).length → Tree sig s,
        ∃ passthrough : Fin n → Tree sig s,
          ∀ i, Structural.Indexed.Eq sig (values i)
            (sharingImages op left right (supportGenerators rowLabels colLabels) parameters passthrough i) := by
  classical
  let activeValues := fun i => if left i = 0 ∧ right i = 0 then zero sig op else values i
  have leftSame := bagSum_congr op left values activeValues (fun i nonzero => by
    simp only [activeValues, nonzero, false_and, if_false]
    exact .refl _)
  have rightSame := bagSum_congr op right values activeValues (fun i nonzero => by
    simp only [activeValues, nonzero, and_false, if_false]
    exact .refl _)
  constructor
  · intro equation
    have equation := leftSame.symm.trans (equation.trans rightSame)
    have active : ∀ i, left i = 0 → right i = 0 →
        Structural.Indexed.Eq sig (activeValues i) (zero sig op) := by
      intro i hl hr
      simp only [activeValues, hl, hr, and_self, if_true]
      exact .refl _
    obtain ⟨parameters, images⟩ := (bags_generated_active profile op left right rowLabels
      colLabels rowCounts colCounts disjoint activeValues active).mp equation
    refine ⟨parameters, values, fun i => ?_⟩
    by_cases inactive : left i = 0 ∧ right i = 0
    · simp only [sharingImages, if_pos inactive]
      exact .refl _
    · simpa only [sharingImages, activeValues, if_neg inactive] using images i
  · rintro ⟨parameters, passthrough, images⟩
    let generatedValues := fun i => bagSum op
      (fun j => (supportGenerators rowLabels colLabels).get j i) parameters
    have leftSame := bagSum_congr op left values generatedValues (fun i nonzero => by
      have inactive : ¬ (left i = 0 ∧ right i = 0) := fun h => nonzero h.1
      simpa only [sharingImages, if_neg inactive] using images i)
    have rightSame := bagSum_congr op right values generatedValues (fun i nonzero => by
      have inactive : ¬ (left i = 0 ∧ right i = 0) := fun h => nonzero h.2
      simpa only [sharingImages, if_neg inactive] using images i)
    have balanced : Structural.Indexed.Eq sig (bagSum op left generatedValues)
        (bagSum op right generatedValues) := by
      apply (bagSum_balance profile op left right generatedValues).mpr
      intro a
      simp only [generatedValues, count_bagSum]
      exact balanced_images left right _ (fun j =>
        supportGenerators_sound left right rowLabels colLabels rowCounts colCounts _
          (List.get_mem _ j)) _
    exact leftSame.trans (balanced.trans rightSame.symm)

/- Computational regressions, NOT evidence for the general completeness theorem:
   2X = 3Y gives X = 3Z, Y = 2Z, including Z = empty.
   2X = A+Y retains every balanced support, including redundant presentations.
   A one-sided or empty occurrence grid has no nonempty support.
   No external solver is invoked while elaborating this file. -/
#guard ((supportGenerators (fun _ : Fin 2 => (0 : Fin 2))
  (fun _ : Fin 3 => (1 : Fin 2))).map
    (fun v => (List.finRange 2).map v)) == [[3, 2]]
#guard ((supportGenerators (fun _ : Fin 2 => (0 : Fin 3))
  (fun c : Fin 2 => (if c = 0 then 1 else 2 : Fin 3))).map
    (fun v => (List.finRange 3).map v)) ==
      [[1, 2, 0], [1, 1, 1], [1, 1, 1], [1, 0, 2], [2, 2, 2]]
#guard (booleanMatrices 2 3).length == 64
#guard (supportGenerators (fun _ : Fin 1 => (0 : Fin 1))
  (fun c : Fin 0 => c.elim0)).length == 0
#guard (supportGenerators (fun r : Fin 0 => r.elim0)
  (fun c : Fin 0 => c.elim0) (n := 0)).length == 0

end FiniteSharing

/-! ## Exhaustive singleton requirements (CERTIFICATION.md §4.4)

Input: a coefficient sum of arbitrary bag terms, after finite sharing.
ZERO: every positive-coefficient term must be empty; coefficient zero is ignored.
ATOM-CHOOSE: exactly one coefficient-ONE term supplies the target singleton;
every other positive-coefficient term is empty. Enumerate ALL such indices.
This includes explicit singleton terms: their surviving equation with the target
is decomposed by the existing free-head rule, yielding a payload equation modulo B.
Repeated variables belong in the coefficients, not an assumption of linearity.

The rules are exhaustive because mass is a natural-number invariant: a singleton
has mass one, and c copies contribute c times the term's mass. They terminate
locally: finitely many indices, and the search can mark that requirement processed.
Replay may retain the original equation as a hypothesis; that is not a search loop.
These are general semantic metatheorems, not an automatic whole-system solver.
-/
namespace AtomProcessing

theorem mass_copies (profile : Profile sig) {s} (op : sig.ACUOp s)
    (k : Nat) (a : Tree sig s) : mass profile (bagCopies op k a) = k * mass profile a := by
  induction k with
  | zero => simp only [bagCopies, mass_zero, Nat.zero_mul]
  | succ k ih => simp only [bagCopies, mass_add, ih, Nat.succ_mul, Nat.add_comm]

theorem copies_zero (profile : Profile sig) {s} (op : sig.ACUOp s)
    (k : Nat) (a : Tree sig s) :
    Structural.Indexed.Eq sig (bagCopies op k a) (zero sig op) ↔
      (k ≠ 0 → Structural.Indexed.Eq sig a (zero sig op)) := by
  constructor
  · intro same positive
    have count := mass_congr profile same
    rw [mass_copies, mass_zero] at count
    have empty : mass profile a = 0 := (Nat.mul_eq_zero.mp count).resolve_left positive
    exact zero_of_mass profile a op empty
  · intro empty
    by_cases hk : k = 0
    · subst k; exact .refl _
    · have count := mass_congr profile (empty hk)
      rw [mass_zero] at count
      apply zero_of_mass profile _ op
      rw [mass_copies, count, Nat.mul_zero]

theorem copies_atom (profile : Profile sig) {s} (op : sig.ACUOp s)
    (k : Nat) (a target : Tree sig s) (atom : mass profile target = 1) :
    Structural.Indexed.Eq sig (bagCopies op k a) target ↔
      k = 1 ∧ Structural.Indexed.Eq sig a target := by
  have one : Structural.Indexed.Eq sig (bagCopies op 1 a) a :=
    .trans (.comm op a (zero sig op)) (.unit op a)
  constructor
  · intro same
    have count := mass_congr profile same
    rw [mass_copies, atom] at count
    have hk : k = 1 := Nat.eq_one_of_mul_eq_one_right count
    exact ⟨hk, one.symm.trans (hk ▸ same)⟩
  · rintro ⟨rfl, same⟩; exact one.trans same

theorem sum_zero (profile : Profile sig) {s n} (op : sig.ACUOp s)
    (coeff : FiniteSharing.Vector n) (values : Fin n → Tree sig s) :
    Structural.Indexed.Eq sig (FiniteSharing.bagSum op coeff values) (zero sig op) ↔
      ∀ i, coeff i ≠ 0 → Structural.Indexed.Eq sig (values i) (zero sig op) := by
  induction n with
  | zero => exact ⟨fun _ i => Fin.elim0 i, fun _ => .refl _⟩
  | succ n ih =>
    constructor
    · intro same
      have count := mass_congr profile same
      rw [FiniteSharing.bagSum, mass_add, mass_zero] at count
      have hl : mass profile (bagCopies op (coeff 0) (values 0)) = 0 := by omega
      have hr : mass profile (FiniteSharing.bagSum op (fun i => coeff i.succ)
          (fun i => values i.succ)) = 0 := by omega
      exact Fin.cases ((copies_zero profile op _ _).mp (zero_of_mass profile _ op hl))
        ((ih _ _).mp (zero_of_mass profile _ op hr))
    · intro empty
      exact .trans (.congr (sig.add op)
        (.cons ((copies_zero profile op _ _).mpr (empty 0))
          (.cons ((ih _ _).mpr (fun i => empty i.succ)) .nil))) (.unit op _)

theorem sum_atom (profile : Profile sig) {s n} (op : sig.ACUOp s)
    (coeff : FiniteSharing.Vector n) (values : Fin n → Tree sig s)
    (target : Tree sig s) (atom : mass profile target = 1) :
    Structural.Indexed.Eq sig (FiniteSharing.bagSum op coeff values) target ↔
      ∃ j, coeff j = 1 ∧ Structural.Indexed.Eq sig (values j) target ∧
        ∀ i, i ≠ j → coeff i ≠ 0 → Structural.Indexed.Eq sig (values i) (zero sig op) := by
  induction n with
  | zero =>
    constructor
    · intro same
      have count := mass_congr profile same
      simp only [FiniteSharing.bagSum, mass_zero, atom] at count
      exact False.elim (Nat.noConfusion count)
    · rintro ⟨j, _⟩; exact Fin.elim0 j
  | succ n ih =>
    have casesRule := split_atom profile op (bagCopies op (coeff 0) (values 0))
      (FiniteSharing.bagSum op (fun i => coeff i.succ) (fun i => values i.succ)) target atom
    constructor
    · intro same
      rcases casesRule.mp same with ⟨hl, hr⟩ | ⟨hl, hr⟩
      · obtain ⟨j, degree, chosen, others⟩ := (ih _ _).mp hr
        refine ⟨j.succ, degree, chosen, ?_⟩
        exact Fin.cases (fun _ => (copies_zero profile op _ _).mp hl)
          (fun i different => others i (fun equal => different (congrArg Fin.succ equal)))
      · obtain ⟨degree, chosen⟩ := (copies_atom profile op _ _ _ atom).mp hl
        refine ⟨0, degree, chosen, ?_⟩
        exact Fin.cases (fun different => False.elim (different rfl))
          (fun i _ => (sum_zero profile op _ _).mp hr i)
    · rintro ⟨j, degree, chosen, others⟩
      refine Fin.cases (motive := fun j => coeff j = 1 → Structural.Indexed.Eq sig (values j) target →
        (∀ i, i ≠ j → coeff i ≠ 0 → Structural.Indexed.Eq sig (values i) (zero sig op)) →
        Structural.Indexed.Eq sig (FiniteSharing.bagSum op coeff values) target) ?_ ?_ j degree chosen others
      · intro degree chosen others
        exact casesRule.mpr (.inr ⟨(copies_atom profile op _ _ _ atom).mpr ⟨degree, chosen⟩,
          (sum_zero profile op _ _).mpr (fun i => others i.succ (Fin.succ_ne_zero i))⟩)
      · intro j degree chosen others
        exact casesRule.mpr (.inl ⟨(copies_zero profile op _ _).mpr
          (others 0 (Ne.symm (Fin.succ_ne_zero j))),
          (ih _ _).mpr ⟨j, degree, chosen, fun i different =>
            others i.succ (fun equal => different (Fin.succ_inj.mp equal))⟩⟩)

end AtomProcessing

end DirectCertification

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
  -- Forward existing decidable metadata through opaque registration projections.
  -- This is generated here, not a new user registration obligation.
  for source in [
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

private theorem variables_eval (reg : Registration sig) {Γ Δ}
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

private theorem apply_congr (reg : Registration sig) {ss s} (f : sig.Symbol ss s)
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

private theorem args_trans (reg : Registration sig) {ss} {a b c : Args reg.Carrier ss}
    (h : ArgsRel (fun s => NativeEq sig reg (s := s)) ss a b)
    (k : ArgsRel (fun s => NativeEq sig reg (s := s)) ss b c) :
    ArgsRel (fun s => NativeEq sig reg (s := s)) ss a c := by
  induction ss with
  | nil => trivial
  | cons s ss ih => exact ⟨.trans h.1 k.1, ih h.2 k.2⟩

private theorem args_refl (reg : Registration sig) {Γ} (values : Args reg.Carrier Γ) :
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

private theorem Variable.eval_congr (reg : Registration sig) {Γ s} (v : Variable Γ s)
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

end Substitution

end DirectCertification

/-! ## Certificates over Bakery's ordinary registered datatypes

Only this section depends on Bakery. Definitions below are INPUT/ANSWER DATA,
not problem-specific proof lemmas. Each certification proof is one explicit
application of the general checker to a finite proof tree plus soundness traces.
No Maude process, proof-search tactic, or hidden registration obligation runs.

The data terms use generated constructor identifiers solely as a future dump
would. The readable native theorems immediately below use the user constructors.
Handwritten proposals are deliberate here: dump/parser/search engineering is
deferred until the general semantic rules and finite-sharing theorem stabilize.
-/

namespace DirectCertification.Bakery

open BakeryACU Structural.Indexed BakeryACU.BakeryTheory.Generated
open Substitution Substitution.Worklist

derive_direct_profile profile for BakeryTheory.certified

/- Nonlinear Bakery certificate, by ONE application of the general rule.
The occurrence grid is (P,P) against (Q,Q,Q), so the computed family has exactly
one support with degrees (3,2): P =B Z+Z+Z and Q =B Z+Z, including Z = empty.
nativeBagSum writes the coefficient equation 2P =B 3Q using ONLY the ordinary
registered ProcSet.empty/union constructors; trailing units are harmless modulo B.
The let-bound data below belong to a future FiniteSharing dump, not extra lemmas
for this problem. Count/disjointness proofs are finite syntactic case checks.
No completeness premise, payload restriction, or proof-search tactic is used.
-/
theorem nonlinear_sharing_certificate (values : Fin 2 → ProcSet) :
    let left : FiniteSharing.Vector 2 := Fin.cases 2 (fun _ => 0)
    let right : FiniteSharing.Vector 2 := Fin.cases 0 (fun _ => 3)
    let rows : Fin 2 → Fin 2 := fun _ => 0
    let cols : Fin 3 → Fin 2 := fun _ => 1
    let generators := FiniteSharing.supportGenerators rows cols
    NativeEq Sig registration (nativeBagSum registration Operator.acu left values)
      (nativeBagSum registration Operator.acu right values) ↔
      ∃ parameters : Fin generators.length → ProcSet,
        ∃ passthrough : Fin 2 → ProcSet,
          ∀ i, NativeEq Sig registration (s := Tag.s2) (values i)
            (nativeSharingImages registration Operator.acu left right generators parameters passthrough i) :=
  finiteSharing_native (sig := Sig) profile registration (s := Tag.s2)
    (n := 2) (rows := 2) (cols := 3) Operator.acu
    (Fin.cases 2 (fun _ => 0) : FiniteSharing.Vector 2)
    (Fin.cases 0 (fun _ => 3) : FiniteSharing.Vector 2)
    (fun _ : Fin 2 => (0 : Fin 2)) (fun _ : Fin 3 => (1 : Fin 2))
    (Fin.cases rfl (fun i => Fin.cases rfl (fun j => Fin.elim0 j) i))
    (Fin.cases rfl (fun i => Fin.cases rfl (fun j => Fin.elim0 j) i))
    (Fin.cases (Or.inr rfl) (fun i => Fin.cases (Or.inl rfl) (fun j => Fin.elim0 j) i)) values

/-- Data for singleton(wait(ticket)); no semantic assumption about the payload. -/
def waitingAtom {Γ} (ticket : Term Sig Γ Tag.s0) : Term Sig Γ Tag.s2 :=
  .app Symbol.c6 (.cons (.app Symbol.c3 (.cons ticket .nil)) .nil)

/- One equation, TWO necessary unifiers:

     P + Q =B singleton(wait(n))

     σ₀(n,P,Q) = (N, empty, singleton(wait(N)))
     σ₁(n,P,Q) = (N, singleton(wait(N)), empty)

N is fresh; the same N fills every occurrence of the ticket in its family.
Both branches are included. The infinitely many possible tickets are not
enumerated: the constructor has mass one for EVERY assignment to its payload.
-/
def atomicProblem : Problem Sig [Tag.s0, Tag.s2, Tag.s2] :=
  equation (add Operator.acu (.var (.there .here)) (.var (.there (.there .here))))
    (waitingAtom (.var .here))

def atomicAnswers : List (Answer Sig [Tag.s0, Tag.s2, Tag.s2]) :=
  [{ parameters := [Tag.s0]
     images := .cons (.var .here)
       (.cons (zero Operator.acu) (.cons (waitingAtom (.var .here)) .nil)) },
   { parameters := [Tag.s0]
     images := .cons (.var .here)
       (.cons (waitingAtom (.var .here)) (.cons (zero Operator.acu) .nil)) }]

/- Finite certificate tree, directly translatable to a future rule dump:

     ATOM-CHOOSE / SplitAtom(P,Q,singleton(wait(n)))
       branch P=empty, Q=singleton(wait(n)):
         COVER(answer=0, β(N)=n, input-vector=(n,P,Q))
       branch P=singleton(wait(n)), Q=empty:
         COVER(answer=1, β(N)=n, input-vector=(n,P,Q))

Each COVER proves the WHOLE vector from that branch's hypotheses. Separately,
UNIT proves σ₀ sound; COMM then UNIT proves σ₁ sound. The checker combines them
into the semantic iff, not merely a proof that both proposed answers unify.
-/
theorem atomic_exact_data :
    ∀ values, atomicProblem.Holds registration values ↔
      Solutions registration atomicAnswers values :=
  Worklist.exact registration (profile := profile) atomicProblem atomicAnswers
    (.split Operator.acu (.var (.there .here)) (.var (.there (.there .here)))
      Symbol.c6 rfl (.cons (.app Symbol.c3 (.cons (.var .here) .nil)) .nil)
      (.hyp ⟨0, of_decide_eq_true rfl⟩)
      (.cover ⟨0, of_decide_eq_true rfl⟩ (.cons (.var .here) .nil)
        (.cons (.axiom (.refl (.var .here)))
          (.cons (.hyp ⟨0, of_decide_eq_true rfl⟩)
            (.cons (.hyp ⟨1, of_decide_eq_true rfl⟩) .nil))))
      (.cover ⟨1, of_decide_eq_true rfl⟩ (.cons (.var .here) .nil)
        (.cons (.axiom (.refl (.var .here)))
          (.cons (.hyp ⟨0, of_decide_eq_true rfl⟩)
            (.cons (.hyp ⟨1, of_decide_eq_true rfl⟩) .nil)))))
    (.cons (.unit Operator.acu (waitingAtom (.var .here)))
      (.cons (.trans (.comm Operator.acu (waitingAtom (.var .here)) (zero Operator.acu))
        (.unit Operator.acu (waitingAtom (.var .here)))) .nil))

/-- Readable native statement of the same general two-way splitting rule. -/
theorem atomic_certificate (n : Nat) (P Q : ProcSet) :
    ProcSet.union P Q =[BakeryTheory.certified] ProcSet.singleton (.wait n) ↔
      (P =[BakeryTheory.certified] ProcSet.empty ∧
        Q =[BakeryTheory.certified] ProcSet.singleton (.wait n)) ∨
      (P =[BakeryTheory.certified] ProcSet.singleton (.wait n) ∧
        Q =[BakeryTheory.certified] ProcSet.empty) :=
  split_native profile registration Operator.acu P Q (ProcSet.singleton (.wait n)) rfl

/- Answer-guided nonlinear certificate (CERTIFICATION.md §9.1).

     E = { kP =B kQ }, k>0; native proposal σ(P,Q)=(R,R).
     Pick β(R)=P. From E, MULTIPLICITY-CANCEL derives P=B Q.
     REFLEXIVITY proves P=B σ(P)β; SYMMETRY proves Q=B σ(Q)β.
     EARLY-COVER closes the entire branch, with NO sharing-grid expansion.

Soundness is a separate reflexive equality trace after applying σ. This works
for EVERY positive k, not just one tested coefficient or a linear fragment.
It demonstrates accepted targeted evidence, not an implemented automatic search.
-/
def repeatedProblem (k : Nat) : Problem Sig [Tag.s2, Tag.s2] :=
  equation (copies Operator.acu k (.var .here))
    (copies Operator.acu k (.var (.there .here)))

def diagonalAnswers : List (Answer Sig [Tag.s2, Tag.s2]) :=
  [{ parameters := [Tag.s2]
     images := .cons (.var .here) (.cons (.var .here) .nil) }]

theorem repeated_exact_data (k : Nat) (positive : 0 < k) :
    ∀ values, (repeatedProblem k).Holds registration values ↔
      Solutions registration diagonalAnswers values :=
  Worklist.exact registration (profile := profile) (repeatedProblem k) diagonalAnswers
    (.cover ⟨0, of_decide_eq_true rfl⟩ (.cons (.var .here) .nil)
      (.cons (.axiom (.refl (.var .here)))
        (.cons (.symm (.multiplicity Operator.acu k positive (.var .here)
          (.var (.there .here)) (.hyp ⟨0, of_decide_eq_true rfl⟩))) .nil)))
    (.cons (.copies_substitution (sig := Sig) (Γ := [Tag.s2, Tag.s2]) (Δ := [Tag.s2])
      Operator.acu k (.var .here) (.var (.there .here))
      (diagonalAnswers.get ⟨0, of_decide_eq_true rfl⟩).images (.refl (.var .here))) .nil)

/-- Native presentation: k-fold union has exactly the diagonal family.
The positive-k guard is mathematical, not a hidden constraint on bag variables. -/
theorem repeated_certificate (k : Nat) (positive : 0 < k) (P Q : ProcSet) :
    NativeEq Sig registration (s := Tag.s2)
      (nativeRepeat registration Operator.acu k P)
      (nativeRepeat registration Operator.acu k Q) ↔
      ∃ R : ProcSet, P =[BakeryTheory.certified] R ∧ Q =[BakeryTheory.certified] R :=
  (multiplicity_native profile registration Operator.acu k positive P Q).trans
    (share_native registration (s := Tag.s2) P Q)

/- A contradictory payload equation must not become a guessed "no answers".
The trace decomposes singleton first and then proves wait/crit free-head clash.
Its empty answer set is complete because every original solution is impossible.
-/
def clashProblem : Problem Sig [Tag.s0, Tag.s0] :=
  equation (waitingAtom (.var .here))
    (.app Symbol.c6 (.cons (.app Symbol.c4 (.cons (.var (.there .here)) .nil)) .nil))

theorem clash_exact_data :
    ∀ values, clashProblem.Holds registration values ↔
      Solutions registration ([] : List (Answer Sig [Tag.s0, Tag.s0])) values :=
  Worklist.exact registration (profile := profile) clashProblem []
    (.clash Symbol.c3 Symbol.c4 rfl rfl
      (fun same => nomatch same)
      (.cons (.var .here) .nil) (.cons (.var (.there .here)) .nil)
      (.decompose (profile := profile) (Γ := [Tag.s0, Tag.s0]) Symbol.c6 rfl
        (.cons (.app Symbol.c3 (.cons (.var .here) .nil)) .nil)
        (.cons (.app Symbol.c4 (.cons (.var (.there .here)) .nil)) .nil)
        .here (.hyp ⟨0, of_decide_eq_true rfl⟩)))
    .nil

/- Actual typed replay, not just the semantic rule instantiated in a theorem.

Original scope = [ticket : Nat, P : ProcSet, Q : ProcSet].
The Slots table skips ticket and selects P,Q ONCE. The occurrence coefficients
are 2P =B 3Q. One support gives Z, so the generated open image vector is
  (ticket, 3Z, 2Z), modulo trailing registered units.
The generated context retains the old scope after Z; unused old P,Q indices are
harmless internal passthrough slots, not extra constraints or extra solutions.

COMPLETENESS dump: FiniteSharing -> Cover(the sole generated answer, identity β).
SOUNDNESS dump: FiniteSharing(the SAME layout/Slots) -> end.
The top proof is exactly these data constructors. General rule metatheorems above
handle the semantic reasoning; no problem-specific supporting lemma/tactic/hole.
-/
def nonlinearSlots : Sharing.Slots Tag.s2 [Tag.s0, Tag.s2, Tag.s2] 2 :=
  .skip (.take (.take .nil))

def nonlinearLeft : FiniteSharing.Vector 2 := fun i => if i = 0 then 2 else 0
def nonlinearRight : FiniteSharing.Vector 2 := fun i => if i = 0 then 0 else 3

def nonlinearProblem : Problem Sig [Tag.s0, Tag.s2, Tag.s2] :=
  Sharing.problem Operator.acu nonlinearSlots nonlinearLeft nonlinearRight

def nonlinearAnswers : List (Answer Sig [Tag.s0, Tag.s2, Tag.s2]) :=
  [Sharing.answer Operator.acu nonlinearSlots nonlinearLeft nonlinearRight
    (FiniteSharing.supportGenerators (fun _ : Fin 2 => (0 : Fin 2)) (fun _ : Fin 3 => (1 : Fin 2)))]

theorem nonlinear_replay_certificate :
    ∀ values, nonlinearProblem.Holds registration values ↔ Solutions registration nonlinearAnswers values :=
  Worklist.exact registration (profile := profile) nonlinearProblem nonlinearAnswers
    (.sharing (sig := Sig) (s := Tag.s2) (Γ := [Tag.s0, Tag.s2, Tag.s2])
      (n := 2) (rows := 2) (cols := 3) Operator.acu nonlinearSlots
      nonlinearLeft nonlinearRight
      (fun _ : Fin 2 => (0 : Fin 2)) (fun _ : Fin 3 => (1 : Fin 2))
      (Fin.cases rfl (fun i => Fin.cases rfl (fun j => Fin.elim0 j) i))
      (Fin.cases rfl (fun i => Fin.cases rfl (fun j => Fin.elim0 j) i))
      (Fin.cases (Or.inr rfl) (fun i => Fin.cases (Or.inl rfl) (fun j => Fin.elim0 j) i))
      (.hyp ⟨0, of_decide_eq_true rfl⟩)
      (.cover ⟨0, of_decide_eq_true rfl⟩ (Terms.identity _)
        (.cons (.axiom (.refl _)) (.cons (.axiom (.refl _)) (.cons (.axiom (.refl _)) .nil)))))
    (.sharing (sig := Sig) (s := Tag.s2) (inputs := [Tag.s0, Tag.s2, Tag.s2])
      (n := 2) (rows := 2) (cols := 3) profile Operator.acu nonlinearSlots
      nonlinearLeft nonlinearRight
      (fun _ : Fin 2 => (0 : Fin 2)) (fun _ : Fin 3 => (1 : Fin 2))
      (Fin.cases rfl (fun i => Fin.cases rfl (fun j => Fin.elim0 j) i))
      (Fin.cases rfl (fun i => Fin.cases rfl (fun j => Fin.elim0 j) i))
      (Fin.cases (Or.inr rfl) (fun i => Fin.cases (Or.inl rfl) (fun j => Fin.elim0 j) i)) .nil)

/- Coefficient-aware ATOM-CHOOSE with TWO answers, not two handpicked branches:

   2P + Q + R =B singleton(wait(n))
   → j=Q: P=0, Q=singleton(wait(n)), R=0
   → j=R: P=0, Q=0, R=singleton(wait(n))

Complete.atom requests a child for EVERY coefficient-one index. There is no
P branch (its coefficient is two), and no external supplied-list coverage premise.
Soundness is the general, generated sum_choice equality trace for each answer.
-/
def choiceSlots : Sharing.Slots Tag.s2 [Tag.s0, Tag.s2, Tag.s2, Tag.s2] 3 :=
  .skip (.take (.take (.take .nil)))

def choiceCoefficients : FiniteSharing.Vector 3 := fun i => if i = 0 then 2 else 1

def choiceTerms (i : Fin 3) : Term Sig [Tag.s0, Tag.s2, Tag.s2, Tag.s2] Tag.s2 :=
  .var (choiceSlots.variable i)

def choiceProblem : Problem Sig [Tag.s0, Tag.s2, Tag.s2, Tag.s2] :=
  equation (Sharing.sum Operator.acu choiceCoefficients choiceTerms) (waitingAtom (.var .here))

def choiceAnswers : List (Answer Sig [Tag.s0, Tag.s2, Tag.s2, Tag.s2]) :=
  [{ parameters := [Tag.s0]
     images := .cons (.var .here) (.cons (zero Operator.acu)
       (.cons (waitingAtom (.var .here)) (.cons (zero Operator.acu) .nil))) },
   { parameters := [Tag.s0]
     images := .cons (.var .here) (.cons (zero Operator.acu)
       (.cons (zero Operator.acu) (.cons (waitingAtom (.var .here)) .nil))) }]

theorem coefficient_choice_certificate :
    ∀ values, choiceProblem.Holds registration values ↔ Solutions registration choiceAnswers values :=
  Worklist.exact registration (profile := profile) choiceProblem choiceAnswers
    (.atom Operator.acu choiceCoefficients choiceTerms Symbol.c6 rfl
      (.cons (.app Symbol.c3 (.cons (.var .here) .nil)) .nil)
      (.hyp ⟨0, of_decide_eq_true rfl⟩)
      (Fin.cases (fun impossible => False.elim ((of_decide_eq_true rfl : (2 : Nat) ≠ 1) impossible))
        (Fin.cases (fun _ =>
          .cover ⟨0, of_decide_eq_true rfl⟩ (.cons (.var .here) .nil)
            (.cons (.axiom (.refl _)) (.cons (.hyp ⟨0, of_decide_eq_true rfl⟩)
              (.cons (.hyp ⟨1, of_decide_eq_true rfl⟩) (.cons (.hyp ⟨2, of_decide_eq_true rfl⟩) .nil)))))
          (Fin.cases (fun _ =>
            .cover ⟨1, of_decide_eq_true rfl⟩ (.cons (.var .here) .nil)
              (.cons (.axiom (.refl _)) (.cons (.hyp ⟨0, of_decide_eq_true rfl⟩)
                (.cons (.hyp ⟨1, of_decide_eq_true rfl⟩) (.cons (.hyp ⟨2, of_decide_eq_true rfl⟩) .nil)))))
            (fun j => Fin.elim0 j)))))
    (.cons (.sum_choice Operator.acu (waitingAtom (.var .here)) choiceCoefficients
      ⟨1, of_decide_eq_true rfl⟩ rfl)
      (.cons (.sum_choice Operator.acu (waitingAtom (.var .here)) choiceCoefficients
        ⟨2, of_decide_eq_true rfl⟩ rfl) .nil))

/- ATOM-ONE exposes a payload equation, not a literal-equality shortcut:

   singleton(wait(n)) + 2P =B singleton(wait(m))
   → P=0 and singleton(wait(n)) =B singleton(wait(m))
   → wait(n) =B wait(m) → n =B m → cover (N,N,0).

All stages are existing/general rule data. No separate problem proof lemma.
-/
def payloadCoefficients : FiniteSharing.Vector 2 := fun i => if i = 0 then 1 else 2

def payloadTerms : Fin 2 → Term Sig [Tag.s0, Tag.s0, Tag.s2] Tag.s2 :=
  Fin.cases (waitingAtom (.var .here)) (Fin.cases (.var (.there (.there .here))) Fin.elim0)

def payloadProblem : Problem Sig [Tag.s0, Tag.s0, Tag.s2] :=
  equation (Sharing.sum Operator.acu payloadCoefficients payloadTerms)
    (waitingAtom (.var (.there .here)))

def payloadAnswers : List (Answer Sig [Tag.s0, Tag.s0, Tag.s2]) :=
  [{ parameters := [Tag.s0]
     images := .cons (.var .here) (.cons (.var .here) (.cons (zero Operator.acu) .nil)) }]

theorem payload_requirement_certificate :
    ∀ values, payloadProblem.Holds registration values ↔ Solutions registration payloadAnswers values :=
  Worklist.exact registration (profile := profile) payloadProblem payloadAnswers
    (.atom Operator.acu payloadCoefficients payloadTerms Symbol.c6 rfl
      (.cons (.app Symbol.c3 (.cons (.var (.there .here)) .nil)) .nil)
      (.hyp ⟨0, of_decide_eq_true rfl⟩)
      (Fin.cases (fun _ =>
        .cover ⟨0, of_decide_eq_true rfl⟩ (.cons (.var .here) .nil)
          (.cons (.axiom (.refl _))
            (.cons (.symm (.decompose (profile := profile) (Γ := [Tag.s0, Tag.s0, Tag.s2]) Symbol.c3 rfl
              (.cons (.var .here) .nil) (.cons (.var (.there .here)) .nil) .here
              (.decompose (profile := profile) (Γ := [Tag.s0, Tag.s0, Tag.s2]) Symbol.c6 rfl
                (.cons (.app Symbol.c3 (.cons (.var .here) .nil)) .nil)
                (.cons (.app Symbol.c3 (.cons (.var (.there .here)) .nil)) .nil) .here
                (.hyp ⟨0, of_decide_eq_true rfl⟩))))
              (.cons (.hyp ⟨1, of_decide_eq_true rfl⟩) .nil))))
        (Fin.cases (fun impossible => False.elim ((of_decide_eq_true rfl : (2 : Nat) ≠ 1) impossible))
          (fun i => Fin.elim0 i))))
    (.cons (.sum_choice Operator.acu (waitingAtom (.var .here)) payloadCoefficients
      ⟨0, of_decide_eq_true rfl⟩ rfl) .nil)

/- ZERO preserves a canceled/inactive variable:
   0P + 2Q =B empty → Q=empty, P arbitrary. -/
def zeroCoefficients : FiniteSharing.Vector 2 := fun i => if i = 0 then 0 else 2

def zeroTerms : Fin 2 → Term Sig [Tag.s2, Tag.s2] Tag.s2 :=
  Fin.cases (.var .here) (Fin.cases (.var (.there .here)) Fin.elim0)

def zeroProblem : Problem Sig [Tag.s2, Tag.s2] :=
  equation (Sharing.sum Operator.acu zeroCoefficients zeroTerms) (zero Operator.acu)

def zeroAnswers : List (Answer Sig [Tag.s2, Tag.s2]) :=
  [{ parameters := [Tag.s2]
     images := .cons (.var .here) (.cons (zero Operator.acu) .nil) }]

theorem zero_requirement_certificate :
    ∀ values, zeroProblem.Holds registration values ↔ Solutions registration zeroAnswers values :=
  Worklist.exact registration (profile := profile) zeroProblem zeroAnswers
    (.zero Operator.acu zeroCoefficients zeroTerms (.hyp ⟨0, of_decide_eq_true rfl⟩)
      (.cover ⟨0, of_decide_eq_true rfl⟩ (.cons (.var .here) .nil)
        (.cons (.axiom (.refl _)) (.cons (.hyp ⟨1, of_decide_eq_true rfl⟩) .nil))))
    (.cons (Equality.sum_zero (sig := Sig) (Γ := [Tag.s2]) Operator.acu zeroCoefficients) .nil)

/- No coefficient-one supplier: 2P =B singleton(wait(n)) has NO solution.
No bounded search failure or assumption that Maude reported no answers is used. -/
theorem impossible_requirement_certificate :
    ∀ values, (equation (Sharing.sum Operator.acu (fun _ : Fin 1 => 2)
      (fun _ => (.var (.there .here) : Term Sig [Tag.s0, Tag.s2] Tag.s2)))
      (waitingAtom (.var .here))).Holds registration values ↔
      Solutions registration ([] : List (Answer Sig [Tag.s0, Tag.s2])) values :=
  Worklist.exact registration (profile := profile) _ []
    (.atom Operator.acu (fun _ : Fin 1 => 2) (fun _ => .var (.there .here)) Symbol.c6 rfl
      (.cons (.app Symbol.c3 (.cons (.var .here) .nil)) .nil)
      (.hyp ⟨0, of_decide_eq_true rfl⟩)
      (fun _ impossible => False.elim ((of_decide_eq_true rfl : (2 : Nat) ≠ 1) impossible)))
    .nil

/- BIND across a whole many-sorted equation system:

  scope (n,P,Q), equations P =B Q and Q =B singleton(wait(n))
  bind P:=Q → scope (n,Q), images (n,Q,Q), BOTH equations substituted
  bind Q:=singleton(wait(n)) → scope (n), images (n,[wait(n)],[wait(n)])
  cover the generated answer using identity β.

The bag variables are removed even though their equality is modulo B, not Lean
literal equality. No assumption identifying raw constructor trees is introduced.
-/
def bindFirst : Binding.Removal Tag.s2 [Tag.s0, Tag.s2, Tag.s2] [Tag.s0, Tag.s2] :=
  .there .here

def bindSecond : Binding.Removal Tag.s2 [Tag.s0, Tag.s2] [Tag.s0] := .there .here

def bindSystem : List (Problem Sig [Tag.s0, Tag.s2, Tag.s2]) :=
  [Binding.problem bindFirst (.var (.there .here)),
   equation (.var (.there (.there .here))) (waitingAtom (.var .here))]

def bindAnswers : List (Answer Sig [Tag.s0, Tag.s2, Tag.s2]) :=
  [{ parameters := [Tag.s0]
     images := ((Terms.identity [Tag.s0, Tag.s2, Tag.s2]).subst
       (bindFirst.substitution (.var (.there .here)))).subst
       (bindSecond.substitution (waitingAtom (.var .here))) }]

theorem binding_system_certificate :
    ∀ values, Worklist.Holds registration bindSystem values ↔ Solutions registration bindAnswers values :=
  Worklist.exact_system registration (profile := profile) bindSystem bindAnswers
    (.bind bindFirst (.var (.there .here)) (.hyp ⟨0, of_decide_eq_true rfl⟩)
      (.bind bindSecond (waitingAtom (.var .here)) (.hyp ⟨1, of_decide_eq_true rfl⟩)
        (.cover ⟨0, of_decide_eq_true rfl⟩ (.cons (.var .here) .nil)
          (.cons (.axiom (.refl _)) (.cons (.axiom (.refl _)) (.cons (.axiom (.refl _)) .nil))))))
    (.cons (.cons (.refl _) .nil) (.cons (.cons (.refl _) .nil) .nil))

/- PURIFY followed by BIND, over ordinary Bakery constructors:

  [wait(n)] =B [wait(m)]
  → A =B [wait(n)], A =B [wait(m)]                 PURIFY
  → [wait(m)] =B [wait(n)], [wait(m)] =B [wait(m)] BIND A:=[wait(m)]
  → m =B n → cover answer (N,N).                 DECOMPOSE/COVER

The fresh A is completely internal. The original variables n,m remain shared;
the proof is one explicit replay term, not supporting problem-specific lemmas.
-/
def purifiedTerm : Term Sig [Tag.s0, Tag.s0] Tag.s2 := waitingAtom (.var .here)

def purifiedTemplate : Problem Sig [Tag.s2, Tag.s0, Tag.s0] :=
  equation (.var .here) (waitingAtom (.var (.there (.there .here))))

def purifiedProblem : Problem Sig [Tag.s0, Tag.s0] :=
  Worklist.Purification.source purifiedTerm purifiedTemplate

def purifiedAnswers : List (Answer Sig [Tag.s0, Tag.s0]) :=
  [{ parameters := [Tag.s0]
     images := .cons (.var .here) (.cons (.var .here) .nil) }]

theorem purification_binding_certificate :
    ∀ values, purifiedProblem.Holds registration values ↔ Solutions registration purifiedAnswers values :=
  Worklist.exact registration (profile := profile) purifiedProblem purifiedAnswers
    (.purify purifiedTerm purifiedTemplate [] []
      (.bind (.here : Binding.Removal Tag.s2 [Tag.s2, Tag.s0, Tag.s0] [Tag.s0, Tag.s0])
        (waitingAtom (.var (.there .here))) (.hyp ⟨1, of_decide_eq_true rfl⟩)
        (.cover ⟨0, of_decide_eq_true rfl⟩ (.cons (.var .here) .nil)
          (.cons (.axiom (.refl _))
            (.cons (.decompose (profile := profile) (Γ := [Tag.s0, Tag.s0]) Symbol.c3 rfl
              (.cons (.var (.there .here)) .nil) (.cons (.var .here) .nil) .here
              (.decompose (profile := profile) (Γ := [Tag.s0, Tag.s0]) Symbol.c6 rfl
                (.cons (.app Symbol.c3 (.cons (.var (.there .here)) .nil)) .nil)
                (.cons (.app Symbol.c3 (.cons (.var .here) .nil)) .nil) .here
                (.hyp ⟨0, of_decide_eq_true rfl⟩))) .nil)))))
    (.cons (.refl _) .nil)

/- Automatic scope and occurrence checks, still over the SAME registered terms.
The selector traverses the signature generically. These guards are regression
tests, not the metatheorem justifying the FREE-OCCURS rule. -/
def cyclicNat : Problem Sig [Tag.s0] :=
  equation (.var .here) (.app Symbol.c1 (.cons (.var .here) .nil))

def cancellableBag : Problem Sig [Tag.s2, Tag.s2] :=
  equation (.var .here) (add Operator.acu (.var .here) (.var (.there .here)))

def freeHeadClash : Problem Sig [Tag.s0] :=
  equation (.app Symbol.c3 (.cons (.var .here) .nil)) (.app Symbol.c4 (.cons (.var .here) .nil))

#guard (Binding.prepare (sig := Sig) (Γ := [Tag.s0, Tag.s2]) (.there .here)
  (waitingAtom (.var .here))).isSome
#guard !(Binding.prepare (sig := Sig) (Γ := [Tag.s0]) .here cyclicNat.right).isSome
#guard !(Binding.prepare (sig := Sig) (Γ := [Tag.s2, Tag.s2]) .here cancellableBag.right).isSome
#guard (FreeOccurs.findProper profile (.here : Variable [Tag.s0] Tag.s0) cyclicNat.right).isSome
#guard !(FreeOccurs.findProper profile (.here : Variable [Tag.s2, Tag.s2] Tag.s2)
  cancellableBag.right).isSome
#guard (Worklist.closeFree profile [] (Terms.identity [Tag.s0]) [cyclicNat]
  ⟨0, of_decide_eq_true rfl⟩).isSome
#guard !(Worklist.closeFree profile [] (Terms.identity [Tag.s2, Tag.s2]) [cancellableBag]
  ⟨0, of_decide_eq_true rfl⟩).isSome
#guard match FreePhase.classify profile (.var (.there .here) : Term Sig [Tag.s0, Tag.s2] Tag.s2)
    (waitingAtom (.var .here)) with
  | .bind .. => true
  | _ => false
#guard match FreePhase.classify profile (waitingAtom (.var .here) : Term Sig [Tag.s0, Tag.s2] Tag.s2)
    (.var (.there .here)) with
  | .orient (.bind ..) => true
  | _ => false
#guard match FreePhase.classify profile (waitingAtom (.var .here) : Term Sig [Tag.s0, Tag.s0] Tag.s2)
    (waitingAtom (.var (.there .here))) with
  | .decompose .. => true
  | _ => false
#guard match FreePhase.classify profile cancellableBag.left cancellableBag.right with
  | .postpone => true
  | _ => false
#guard (Worklist.closeFree profile [] (Terms.identity [Tag.s0]) [equation cyclicNat.right cyclicNat.left]
  ⟨0, of_decide_eq_true rfl⟩).isSome

/- Actual unconstrained certification of n =B succ(n), without supplying the
occurrence path. The algorithm discovers it, constructs Complete.occurs, and
the general checker proves the semantic empty-answer certificate. -/
theorem automatic_occurs_certificate :
    ∀ values, cyclicNat.Holds registration values ↔
      Solutions registration ([] : List (Answer Sig [Tag.s0])) values :=
  Worklist.exact registration (profile := profile) cyclicNat []
    ((Worklist.closeFree profile [] (Terms.identity [Tag.s0]) [cyclicNat]
      ⟨0, of_decide_eq_true rfl⟩).get (of_decide_eq_true rfl)) .nil

theorem automatic_clash_certificate :
    ∀ values, freeHeadClash.Holds registration values ↔
      Solutions registration ([] : List (Answer Sig [Tag.s0])) values :=
  Worklist.exact registration (profile := profile) freeHeadClash []
    ((Worklist.closeFree profile [] (Terms.identity [Tag.s0]) [freeHeadClash]
      ⟨0, of_decide_eq_true rfl⟩).get (of_decide_eq_true rfl)) .nil

-- Kernel audits: standard Lean axioms are acceptable; sorryAx is not.
#print axioms atomic_exact_data
#print axioms repeated_exact_data
#print axioms clash_exact_data
#print axioms Worklist.exact_system
#print axioms multiplicity_cancel
#print axioms FiniteSharing.boolean_transport_exists
#print axioms FiniteSharing.minimal_nonempty_boolean_support
#print axioms FiniteSharing.boolean_supports_exact
#print axioms FiniteSharing.supportGenerators_exact
#print axioms FiniteSharing.bags_generated
#print axioms finiteSharing_native
#print axioms nonlinear_sharing_certificate
#print axioms Sharing.complete
#print axioms Sharing.sound
#print axioms nonlinear_replay_certificate
#print axioms AtomProcessing.sum_zero
#print axioms AtomProcessing.sum_atom
#print axioms coefficient_choice_certificate
#print axioms payload_requirement_certificate
#print axioms zero_requirement_certificate
#print axioms impossible_requirement_certificate
#print axioms Binding.complete
#print axioms Binding.sound
#print axioms binding_system_certificate
#print axioms Worklist.Purification.exact
#print axioms purification_binding_certificate
#print axioms Binding.lower_sound
#print axioms FreeOccurs.Proper.sound
#print axioms automatic_occurs_certificate
#print axioms automatic_clash_certificate

end DirectCertification.Bakery
