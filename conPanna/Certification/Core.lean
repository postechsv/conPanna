import conPanna.Structural

/-! General constructor/ACU semantics. Precompiled independently of replay. -/

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

theorem perm_cancel_prefix {α : Type} (front : List α) {xs ys : List α}
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

theorem count_flatten_repeat {s} (op : sig.ACUOp s) (k : Nat)
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

theorem eqs_refl {ss} (args : Trees sig ss) : Eqs sig args args := by
  induction ss with
  | nil => cases args; exact .nil
  | cons s ss ih => cases args with
    | cons a rest => exact .cons (.refl _) (ih rest)

theorem eqs_symm {ss} {a b : Trees sig ss} (h : Eqs sig a b) : Eqs sig b a := by
  induction ss with
  | nil => cases h; exact .nil
  | cons s ss ih => cases h with
    | cons h k => exact .cons (.symm h) (ih k)

theorem eqs_trans {ss} {a b c : Trees sig ss}
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


end DirectCertification
