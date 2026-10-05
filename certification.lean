import examples.bakery_acu

/-!
# Direct, rule-based unification certificates

This file contains four clearly separated parts:
1. GENERAL METATHEOREMS: correctness of the rules for any registered signature.
2. SYNTACTIC METADATA: constructor classification, generated without user proofs.
3. REPLAY: finite certificate data, dump format, and kernel-checked acceptance.
4. CERTIFICATES: ordinary, tactic-free proof terms over Bakery's own datatypes.

The new Substitution section supplies arbitrary many-sorted image vectors,
finite ACU equality traces, and answer-indexed factorization/coverage data.
Native export preserves actual substitutions without template compaction.
Native Maude matching proposes generic answer indices and β substitutions;
object-level Maude generates primitive equality traces for those suggestions.
Lean reconstructs typed Factor/Soundness data and
the kernel checks it. The one-tail and four-bag mutation examples combine this
fetched data with the proved general Exchange/Mutate completeness rules.
The Worklist section additionally replays finite completeness trees over the
actual equation worklist. For the nonlinear example, Maude emits BOTH Mutate/
Split branches and their equality consequences; no reference-completeness
lemma or handwritten problem proof remains. Search control is still bounded.
OLD restricted control traces remain only as checked regression fixtures.

The current milestone is answer-directed certification of ONE explicit atom
and ONE bag tail per side, including a free frame that identifies head parameters.
The generic coverage theorem below reduces an
unbounded bag obligation to two head-equality guards. It does not recompute a
complete set of ACU unifiers. Finite dump/replay now supports the one-hole
atom-context fragment. FrameCancel additionally handles two rigid fields and a
bag field with a repeated field/payload variable. FrameClash handles distinct
free heads under a common atomic wrapper, eliminating the matched branch.
Native Maude answers guide object-level certificate
search in certification.maude. General multi-head coverage remains future work;
no native Maude answer is trusted as a completeness proof.
Free-constructor decomposition/clash are now proved for arbitrary arities.
Rigid-sort reflection is generated from the constructor dependency graph,
allowing ordinary equality only when no ACU operation is reachable.

The equality is the existing Structural.Indexed.NativeEq, written
`=[BakeryTheory.certified]`. We introduce no second equality or user-model
encoding. Lists/quotients appear only inside proofs of the general metatheorems.

A future Maude dump can name each general rule and its arguments. Reconstruction
then builds the corresponding Lean application; it does not run a Lean tactic.
The Bakery example fetches actual native answers and an accumulated Maude trace.
The OLD object-level search boundary accepts only the two canonical shapes,
up to parameter renaming and binary-summand order. The independent general
exporter accepts any well-sorted constructor substitution and retains EVERY
image. Acceptance as an exact answer set still requires checked soundness and
coverage data; exporting syntax is NOT certification. This is not production
narrowing. Only kernel-checked semantic metatheorems certify fetched DATA.
There is no custom proof tactic; object-level Maude rules do the trace search.

References:
* Comon–Lescanne, Equational Problems and Disunification (1989), §§3–4:
  https://doi.org/10.1016/S0747-7171(89)80017-3
  Separation of rules from control, and preservation of the WHOLE solution set.
* Fernández, AC Complement Problems (1996), §§3.3 and 4:
  finite symbolic coverage tests, and preservation of shared-variable
  correlations. The ACU reduction here is proved independently: the paper's
  linear AC theorem is NOT silently applied to nonlinear shared remainders.

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

end DirectCertification

/-! ## Automatic syntactic metadata (prototype command, eventually library code)

The registered signature already knows every constructor and which symbols are
the ACU operation/unit. This command enumerates them and computes the finite
sort-dependency graph. A sort is rigid only if no constructor path reaches an
ACU sort (cycles such as Nat -> Nat are allowed). All resulting metadata fields
are checked by constructor cases/reduction. There is no semantic field for the
user to prove and no problem-specific theorem name in the generator.
-/

open Lean Meta Elab Command in
elab "derive_direct_profile " name:ident " for " theory:ident : command => do
  let (theoryName, symbolNames, zeroHeads, addHeads, rigidSorts) ← liftTermElabM do
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
    -- Dependency analysis is purely syntactic. Starting with ACU result sorts,
    -- propagate non-rigidity backwards through ALL constructor arguments.
    -- In particular a free Conf constructor containing a bag is not rigid.
    let mut tags : Array Name := #[]
    let mut dependencies : Array (Expr × Array Expr) := #[]
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
      for tag in #[output] ++ inputs do
        let some tagName := tag.constName? | throwError "sort tags must be nullary constructors"
        unless tags.contains tagName do tags := tags.push tagName
    let mut blocked := resultSorts
    for _ in [:tags.size] do
      for (output, inputs) in dependencies do
        if inputs.any blocked.contains && !blocked.contains output then
          blocked := blocked.push output
    return (theoryName, symbolInfo.ctors, zeros, adds,
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

/-! ### Answer-directed one-tail coverage

These are GENERAL metatheorems, not extra user registration obligations.
The two proposed families are kept fixed. Their guards may include payload
bindings/restrictions; those must not be thrown away when reading an answer.
Only the two head cases are checked, not the infinitely many possible tails.
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

/-- The proposed answer set. The parameters of the crossed family include ONE
shared native bag N, not two independently chosen bags. G/H record any extra
candidate restrictions. This is just a proposition, not a second term language.

For the matched family, a=B b is still a head equation. Decomposing a free head
into payload bindings is a separate rule, NOT assumed or silently certified.
-/
def answers (reg : Registration sig) {s} (op : sig.ACUOp s)
    (a b : reg.Carrier s) (G H : Prop) (x y : reg.Carrier s) : Prop :=
  (G ∧ NativeEq sig reg a b ∧ NativeEq sig reg x y) ∨
  (H ∧ ∃ n : reg.Carrier s,
    NativeEq sig reg x (reg.apply (sig.add op) (b, n, PUnit.unit)) ∧
    NativeEq sig reg y (reg.apply (sig.add op) (a, n, PUnit.unit)))

/-- Arbitrary guards can restrict a sound family but never introduce junk. -/
theorem answers_sound (profile : Profile sig) (reg : Registration sig) {s}
    (op : sig.ACUOp s) (a b : reg.Carrier s) (G H : Prop)
    (ha : mass profile (reg.quote s a) = 1)
    (hb : mass profile (reg.quote s b) = 1) :
    ∀ x y, answers reg op a b G H x y →
      NativeEq sig reg (reg.apply (sig.add op) (a, x, PUnit.unit))
        (reg.apply (sig.add op) (b, y, PUnit.unit)) :=
  fun x y proposed => (exchange_native profile reg op a b x y ha hb).mpr
    (Or.elim proposed (fun matched => .inl matched.2)
      (fun crossed => .inr crossed.2))

/-- MAIN COVERAGE REDUCTION: an iff, not just a sufficient heuristic.

  fixed answers = [matched family with guard G; crossed family with guard H]

  ALL bag solutions are covered by these answers
  ================================================================= Coverage
  (a=B b -> G) AND (a!=B b -> H)

Necessity tests two minimal solutions:
* a=B b: X=Y=0. The crossed family cannot cover an empty tail because b is
  nonempty. Thus the matched guard MUST hold.
* a!=B b: X=b, Y=a. The matched family is impossible, so H MUST hold.
Sufficiency uses Exchange and cancellation, carrying an arbitrary shared N.

This is the ACU-specific step eliminating the infinite tails from a negative
"no missed solution" obligation. Future replay need only certify the RHS
guards, plus the syntactic shape of the proposed families. The guard H is NOT
the condition a!=B b: the crossed family can also solve equal-head instances.
-/
theorem coverage_iff (profile : Profile sig) (reg : Registration sig) {s}
    (op : sig.ACUOp s) (a b : reg.Carrier s) (G H : Prop)
    (ha : mass profile (reg.quote s a) = 1)
    (hb : mass profile (reg.quote s b) = 1) :
    (∀ x y, NativeEq sig reg (reg.apply (sig.add op) (a, x, PUnit.unit))
        (reg.apply (sig.add op) (b, y, PUnit.unit)) →
      answers reg op a b G H x y) ↔
      ((NativeEq sig reg a b → G) ∧ (¬ NativeEq sig reg a b → H)) := by
  let z := reg.apply (sig.zero op) PUnit.unit
  constructor
  · intro complete
    constructor
    · intro hab
      have input : NativeEq sig reg (reg.apply (sig.add op) (a, z, PUnit.unit))
          (reg.apply (sig.add op) (b, z, PUnit.unit)) :=
        native_add_congr reg op hab (native_refl reg z)
      rcases complete z z input with ⟨g, _⟩ | ⟨_, n, hx, _⟩
      · exact g
      · simp only [z, NativeEq, reg.quote_apply, Args.quote] at hx
        have count := mass_congr profile hx
        change mass profile (zero sig op) =
          mass profile (add sig op (reg.quote s b) (reg.quote s n)) at count
        rw [mass_zero, mass_add, hb] at count
        omega
    · intro different
      have input := native_comm reg op a b
      rcases complete b a input with ⟨_, hab, _⟩ | ⟨h, _⟩
      · exact False.elim (different hab)
      · exact h
  · rintro ⟨matchedGuard, crossedGuard⟩ x y input
    classical
    by_cases hab : NativeEq sig reg a b
    · have tails : NativeEq sig reg x y := (cancel_native profile reg op b x y).mp
        (native_trans reg (native_add_congr reg op (native_symm reg hab)
          (native_refl reg x)) input)
      exact .inl ⟨matchedGuard hab, hab, tails⟩
    · rcases (exchange_native profile reg op a b x y ha hb).mp input with matched | crossed
      · exact False.elim (hab matched.1)
      · exact .inr ⟨crossedGuard hab, crossed⟩

/-- Aggregate the two INDEPENDENT certificates. No correctness claim about
Maude, no hidden user proof, and no feasibility test is used in aggregation. -/
theorem exact_of_coverage (profile : Profile sig) (reg : Registration sig) {s}
    (op : sig.ACUOp s) (a b : reg.Carrier s) (G H : Prop)
    (ha : mass profile (reg.quote s a) = 1)
    (hb : mass profile (reg.quote s b) = 1)
    (guards : (NativeEq sig reg a b → G) ∧ (¬ NativeEq sig reg a b → H)) :
    ∀ x y, NativeEq sig reg (reg.apply (sig.add op) (a, x, PUnit.unit))
        (reg.apply (sig.add op) (b, y, PUnit.unit)) ↔
      answers reg op a b G H x y :=
  fun x y => ⟨(coverage_iff profile reg op a b G H ha hb).mpr guards x y,
    answers_sound profile reg op a b G H ha hb x y⟩

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

private theorem args_trans (reg : Registration sig) {ss} {a b c : Args reg.Carrier ss}
    (h : ArgsRel (fun s => NativeEq sig reg (s := s)) ss a b)
    (k : ArgsRel (fun s => NativeEq sig reg (s := s)) ss b c) :
    ArgsRel (fun s => NativeEq sig reg (s := s)) ss a c := by
  induction ss with
  | nil => trivial
  | cons s ss ih => exact ⟨.trans h.1 k.1, ih h.2 k.2⟩

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

/-- One finite equality trace for EACH proposed substitution. A proposal cannot
be accepted merely because other members cover the problem: junk is rejected. -/
inductive Soundness {inputs : List Sorts} (problem : Problem sig inputs) : List (Answer sig inputs) → Type where
  | nil : Soundness problem []
  | cons {answer rest}
      (proof : Equality sig answer.parameters
        (problem.left.subst answer.images) (problem.right.subst answer.images))
      (tail : Soundness problem rest) : Soundness problem (answer :: rest)

theorem Soundness.sound (reg : Registration sig) {inputs} {problem : Problem sig inputs}
    {proposed : List (Answer sig inputs)} (proof : Soundness problem proposed) :
    ∀ values, Solutions reg proposed values → problem.Holds reg values := by
  induction proof with
  | nil => rintro _ ⟨_, impossible, _⟩; cases impossible
  | @cons answer rest equality tail ih =>
      rintro values ⟨candidate, member, fresh, images⟩
      rcases List.mem_cons.mp member with same | member
      · cases same
        have equation := equality.sound reg fresh
        rw [Term.eval_subst, Term.eval_subst] at equation
        exact .trans (problem.left.eval_congr reg images)
          (.trans equation (.symm (problem.right.eval_congr reg images)))
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

  E ⊢ images = normalized       normalized = proposed[i] β
  ======================================================= Emit/Factor
                      E ; images ⇒ proposed

These are finite DATA constructors, not proof search tactics. Mutate introduces
four fresh indices and lifts every old index uniformly. It NEVER renames two
occurrences independently. Split requires BOTH children. Emit requires checked
equational consequences of E, then the existing checked factor certificate.
-/
namespace Worklist

def Holds (reg : Registration sig) {Γ} (eqs : List (Problem sig Γ))
    (values : Args reg.Carrier Γ) : Prop := ∀ p ∈ eqs, p.Holds reg values

mutual
  inductive Derives (sig : Signature Sorts) {Γ} (eqs : List (Problem sig Γ)) :
      {s : Sorts} → Term sig Γ s → Term sig Γ s → Type where
    | axiom {s a b} : Equality sig Γ (s := s) a b → Derives sig eqs a b
    | hyp (index : Fin eqs.length) : Derives sig eqs (eqs.get index).left (eqs.get index).right
    | symm {s a b} : Derives sig eqs (s := s) a b → Derives sig eqs b a
    | trans {s a b c} : Derives sig eqs (s := s) a b → Derives sig eqs b c → Derives sig eqs a c
    | congr {ss s} (f : sig.Symbol ss s) {a b : Terms sig Γ ss} :
        DerivesArgs sig eqs a b → Derives sig eqs (.app f a) (.app f b)
  inductive DerivesArgs (sig : Signature Sorts) {Γ} (eqs : List (Problem sig Γ)) :
      {ss : List Sorts} → Terms sig Γ ss → Terms sig Γ ss → Type where
    | nil : DerivesArgs sig eqs .nil .nil
    | cons {s ss a b as bs} : Derives sig eqs (s := s) a b →
        DerivesArgs sig eqs (ss := ss) as bs → DerivesArgs sig eqs (.cons a as) (.cons b bs)
end

theorem Derives.sound (reg : Registration sig) {Γ eqs s a b}
    (proof : Derives sig (Γ := Γ) eqs (s := s) a b) (values : Args reg.Carrier Γ)
    (input : Holds reg eqs values) : NativeEq sig reg (a.eval reg values) (b.eval reg values) := by
  refine Derives.rec
    (motive_1 := fun {s} a b _ => NativeEq sig reg (a.eval reg values) (b.eval reg values))
    (motive_2 := fun {ss} as bs _ =>
      ArgsRel (fun s => NativeEq sig reg (s := s)) ss (as.eval reg values) (bs.eval reg values))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ proof
  · intro s a b h; exact h.sound reg values
  · intro index; exact input _ (List.get_mem _ _)
  · intro s a b h ih; exact .symm ih
  · intro s a b c h k ih ik; exact .trans ih ik
  · intro ss s f as bs h ih; exact apply_congr reg f ih
  · trivial
  · intro s ss a b as bs h k ih ik; exact ⟨ih, ik⟩

theorem DerivesArgs.sound (reg : Registration sig) {Γ eqs ss a b}
    (proof : DerivesArgs sig (Γ := Γ) eqs (ss := ss) a b) (values : Args reg.Carrier Γ)
    (input : Holds reg eqs values) :
    ArgsRel (fun s => NativeEq sig reg (s := s)) ss (a.eval reg values) (b.eval reg values) :=
  match proof with
  | .nil => True.intro
  | .cons h rest => ⟨h.sound reg values input, rest.sound reg values input⟩

def equation {Γ s} (a b : Term sig Γ s) : Problem sig Γ := ⟨s, a, b⟩

def lift4 {Γ s} : Terms sig (s :: s :: s :: s :: Γ) Γ :=
  Terms.variables _ Γ (fun v => .there (.there (.there (.there v))))

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

inductive Complete (profile : Profile sig) {inputs} (proposed : List (Answer sig inputs)) :
    {Γ : List Sorts} → Terms sig Γ inputs → List (Problem sig Γ) → Type where
  | emit {Γ images eqs} (index : Fin proposed.length) (normalized : Terms sig Γ inputs)
      (derived : DerivesArgs sig eqs images normalized)
      (factor : Factor (⟨Γ, normalized⟩ : Answer sig inputs) (proposed.get index)) :
      Complete profile proposed images eqs
  | mutate {Γ images eqs s} (op : sig.ACUOp s) (a b c d : Term sig Γ s)
      (selected : Derives sig eqs (add op a b) (add op c d))
      (child : Complete profile proposed (images.subst lift4) (mutated op a b c d eqs)) :
      Complete profile proposed images eqs
  | split {Γ images eqs ss s} (op : sig.ACUOp s) (x y : Term sig Γ s)
      (f : sig.Symbol ss s) (free : profile.view f = .atom f) (args : Terms sig Γ ss)
      (selected : Derives sig eqs (add op x y) (.app f args))
      (left : Complete profile proposed images
        (equation x (zero op) :: equation y (.app f args) :: eqs))
      (right : Complete profile proposed images
        (equation x (.app f args) :: equation y (zero op) :: eqs)) :
      Complete profile proposed images eqs

theorem Complete.sound (reg : Registration sig) {profile : Profile sig} {inputs proposed Γ images eqs}
    (proof : Complete profile (inputs := inputs) proposed (Γ := Γ) images eqs) :
    ∀ values, Holds reg eqs values → Solutions reg proposed (images.eval reg values) := by
  induction proof with
  | emit index normalized derived factor =>
    intro values input
    exact ⟨_, List.get_mem _ _, factor.sound reg ⟨values, derived.sound reg values input⟩⟩
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

/-! ## Finite certificates and native kernel replay

Scope of this replay format: C(a)+X =B C(b)+Y, where C is a one-hole
constructor context with a rigid parameter sort. C supports arbitrary arities;
other arguments are fixed registered trees. There are no Bakery names here.
The FrameCancel extension below supports correlated parameters in a free frame.

This is NOT another user term language or equality. Contexts describe positions
in the EXISTING registered signature and evaluate directly with its native
registration. There is no encode/decode adequacy obligation for the user.

Both input and candidate families are data. Families below encode ENTIRE fixed
substitution templates, not labels attached to unchecked arbitrary bindings.
The external boundary below recognizes these templates exactly, including
shared parameters; additional bindings are rejected, not discarded.
-/

namespace Replay

mutual
  /-- A typed one-hole context. The hole's native sort is r. -/
  inductive Context (sig : Signature Sorts) (r : Sorts) : Sorts → Type where
    | hole : Context sig r r
    | app {ss s} (f : sig.Symbol ss s) (args : ArgumentContext sig r ss) : Context sig r s
  /-- Exactly one argument contains the hole; all others are fixed native syntax.
  This zipper has no constructor-arity bound or problem-specific carrier map. -/
  inductive ArgumentContext (sig : Signature Sorts) (r : Sorts) : List Sorts → Type where
    | focus {s ss} (context : Context sig r s) (rest : Trees sig ss) :
        ArgumentContext sig r (s :: ss)
    | before {s ss} (first : Tree sig s) (rest : ArgumentContext sig r ss) :
        ArgumentContext sig r (s :: ss)
end

mutual
  def Context.eval (reg : Registration sig) {r s} (context : Context sig r s)
      (parameter : reg.Carrier r) : reg.Carrier s :=
    match context with
    | .hole => parameter
    | .app f args => reg.apply f (args.eval reg parameter)
  def ArgumentContext.eval (reg : Registration sig) {r ss}
      (args : ArgumentContext sig r ss) (parameter : reg.Carrier r) : Args reg.Carrier ss :=
    match args with
    | .focus context rest => (context.eval reg parameter, rest.eval reg.toAlgebra)
    | .before first rest => (first.eval reg.toAlgebra, rest.eval reg parameter)
end

/-- External head trace: rule tags and argument positions ONLY.
No fields contain Lean proofs, functions, expressions, or theorem names. -/
inductive HeadCertificate where
  | rigid
  | clash
  | decompose (argument : Nat) (next : HeadCertificate)
  deriving Repr, DecidableEq

/-- COMPLETE canonical substitution templates for the four input variables:

matched: { a -> K, b -> K, X -> Z, Y -> Z }, fresh K,Z
crossed: { a -> a, b -> b, X -> C(b)+N, Y -> C(a)+N }, fresh N

In particular the two occurrences of each fresh parameter are shared.
This milestone does not accept arbitrary Maude substitutions by tagging them.
-/
inductive Family where
  | matched | crossed
  deriving Repr, DecidableEq

/-- The coverage trace has TWO mandatory leaves. Each leaf identifies the
proposed substitution template that covers its case. Swapped/wrong leaves are
rejected, rather than assuming a sound family is also complete. -/
inductive Certificate where
  | coverage (head : HeadCertificate) (equalCase unequalCase : Family)
  | cancellation (family : Family)
  | frameCancel (first second : HeadCertificate) (tail : Certificate)
  | frameClash (first second apart : HeadCertificate) (family : Family)
  deriving Repr, DecidableEq

/-- Small first-order dump grammar, mirrored by certification.maude constructors.
These printers serialize DATA only; external I/O is kept in its own section. -/
def HeadCertificate.dump : HeadCertificate → String
  | .rigid => "rigid"
  | .clash => "clash"
  | .decompose position next => "decompose(" ++ toString position ++ "," ++ next.dump ++ ")"

def Family.dump : Family → String
  | .matched => "matched"
  | .crossed => "crossed"

def Certificate.dump : Certificate → String
  | .coverage head equalCase unequalCase =>
      "coverage(" ++ head.dump ++ ",emit(" ++ equalCase.dump ++ "),emit(" ++
        unequalCase.dump ++ "))"
  | .cancellation family => "cancellation(emit(" ++ family.dump ++ "))"
  | .frameCancel first second tail =>
      "frameCancel(" ++ first.dump ++ "," ++ second.dump ++ "," ++ tail.dump ++ ")"
  | .frameClash first second apart family =>
      "frameClash(" ++ first.dump ++ "," ++ second.dump ++ "," ++ apart.dump ++
        ",emit(" ++ family.dump ++ "))"

private theorem args_refl (reg : Registration sig) {ss} (args : Args reg.Carrier ss) :
    ArgsRel (fun s => NativeEq sig reg (s := s)) ss args args := by
  induction ss with
  | nil => trivial
  | cons s ss ih => exact ⟨.refl _, ih args.2⟩

mutual
  /-- Proof-producing replay, NOT proof search. Every step must fit the actual
  constructor metadata and the explicitly supplied argument position. -/
  def replayHead (profile : Profile sig) (reg : Registration sig) {r s}
      (context : Context sig r s) (cert : HeadCertificate) :
      Option (PLift (∀ a b, NativeEq sig reg (context.eval reg a) (context.eval reg b) ↔ a = b)) :=
    match context, cert with
    | .hole, .rigid =>
        if rigid : profile.rigid r = true then
          some ⟨rigid_native profile reg rigid⟩
        else none
    | .app f args, .decompose position next =>
        match free : profile.view f with
        | .atom _ => do
            let children ← replayArguments profile reg args position next
            return ⟨fun a b => (decompose_native profile reg f free
              (args.eval reg a) (args.eval reg b)).trans (children.down a b)⟩
        | _ => none
    | _, _ => none
  def replayArguments (profile : Profile sig) (reg : Registration sig) {r ss}
      (args : ArgumentContext sig r ss) (position : Nat) (cert : HeadCertificate) :
      Option (PLift (∀ a b, ArgsRel (fun s => NativeEq sig reg (s := s)) ss
        (args.eval reg a) (args.eval reg b) ↔ a = b)) :=
    match args, position with
    | .focus context rest, 0 => do
        let child ← replayHead profile reg context cert
        return ⟨fun a b => ⟨fun h => (child.down a b).mp h.1,
          fun h => ⟨(child.down a b).mpr h, args_refl reg (rest.eval reg.toAlgebra)⟩⟩⟩
    | .before _first rest, n + 1 => do
        let tail ← replayArguments profile reg rest n cert
        return ⟨fun a b => ⟨fun h => (tail.down a b).mp h.2,
          fun h => ⟨.refl _, (tail.down a b).mpr h⟩⟩⟩
    | _, _ => none
end

/-- A hole alone need not be atomic; root atomicity must be checked separately.
Every non-ACU constructor has mass one, independently of the hole's value. -/
def atomic (profile : Profile sig) (reg : Registration sig) {r s}
    (context : Context sig r s) :
    Option (PLift (∀ a, mass profile (reg.quote s (context.eval reg a)) = 1)) :=
  match context with
  | .hole => none
  | .app f args => match free : profile.view f with
    | .atom _ => some ⟨fun a => by
        simp only [Context.eval, reg.quote_apply]
        simp [mass, Tree.eval, measure, free]⟩
    | _ => none

def Family.Holds (reg : Registration sig) {r s} (context : Context sig r s)
    (op : sig.ACUOp s) (family : Family)
    (a b : reg.Carrier r) (x y : reg.Carrier s) : Prop :=
  match family with
  | .matched => ∃ k : reg.Carrier r, ∃ z : reg.Carrier s,
      a = k ∧ b = k ∧ NativeEq sig reg x z ∧ NativeEq sig reg y z
  | .crossed => ∃ n : reg.Carrier s,
      NativeEq sig reg x (reg.apply (sig.add op) (context.eval reg b, n, PUnit.unit)) ∧
      NativeEq sig reg y (reg.apply (sig.add op) (context.eval reg a, n, PUnit.unit))

/-- Semantics of the ENTIRE externally proposed family list. Order and
duplicates are irrelevant; omitting a family is not. -/
def Solutions (reg : Registration sig) {r s} (context : Context sig r s)
    (op : sig.ACUOp s) (proposed : List Family)
    (a b : reg.Carrier r) (x y : reg.Carrier s) : Prop :=
  ∃ family, family ∈ proposed ∧ family.Holds reg context op a b x y

theorem solutions_iff (reg : Registration sig) {r s} (context : Context sig r s)
    (op : sig.ACUOp s) (proposed : List Family)
    (matched : Family.matched ∈ proposed) (crossed : Family.crossed ∈ proposed)
    (a b : reg.Carrier r) (x y : reg.Carrier s) :
    Solutions reg context op proposed a b x y ↔
      Family.Holds reg context op .matched a b x y ∨
      Family.Holds reg context op .crossed a b x y :=
  ⟨fun ⟨family, _, images⟩ => match family with
      | .matched => .inl images
      | .crossed => .inr images,
    fun images => Or.elim images
      (fun h => ⟨.matched, matched, h⟩) (fun h => ⟨.crossed, crossed, h⟩)⟩

/-- Generic aggregation from replayed head equality and finite coverage. This
is a semantic metatheorem, not an input-specific certificate or a new solver. -/
theorem families_exact (profile : Profile sig) (reg : Registration sig) {r s}
    (context : Context sig r s) (op : sig.ACUOp s) (proposed : List Family)
    (matched : Family.matched ∈ proposed) (crossed : Family.crossed ∈ proposed)
    (head : ∀ a b, NativeEq sig reg (context.eval reg a) (context.eval reg b) ↔ a = b)
    (atom : ∀ a, mass profile (reg.quote s (context.eval reg a)) = 1) :
    ∀ a b x y,
      NativeEq sig reg (reg.apply (sig.add op) (context.eval reg a, x, PUnit.unit))
        (reg.apply (sig.add op) (context.eval reg b, y, PUnit.unit)) ↔
      Solutions reg context op proposed a b x y := by
  intro a b x y
  have coverage := exact_of_coverage profile reg op
    (context.eval reg a) (context.eval reg b) True True (atom a) (atom b)
    ⟨fun _ => True.intro, fun _ => True.intro⟩ x y
  apply Iff.trans _ (solutions_iff reg context op proposed matched crossed a b x y).symm
  refine coverage.trans ⟨?_, ?_⟩
  · rintro (⟨_, heads, tails⟩ | ⟨_, remainder⟩)
    · exact .inl ⟨a, x, rfl, ((head a b).mp heads).symm, .refl _, .symm tails⟩
    · exact .inr remainder
  · rintro (⟨k, z, ha, hb, hx, hy⟩ | remainder)
    · exact .inl ⟨True.intro, (head a b).mpr (ha.trans hb.symm), .trans hx (.symm hy)⟩
    · exact .inr ⟨True.intro, remainder⟩

def replay (profile : Profile sig) (reg : Registration sig) {r s}
    (context : Context sig r s) (op : sig.ACUOp s) (proposed : List Family)
    (cert : Certificate) :
    Option (PLift (∀ a b x y,
      NativeEq sig reg (reg.apply (sig.add op) (context.eval reg a, x, PUnit.unit))
        (reg.apply (sig.add op) (context.eval reg b, y, PUnit.unit)) ↔
      Solutions reg context op proposed a b x y)) :=
  match cert with
  | .coverage head .matched .crossed => do
      let isAtom ← atomic profile reg context
      let headProof ← replayHead profile reg context head
      if hm : Family.matched ∈ proposed then
        if hc : Family.crossed ∈ proposed then
          some ⟨families_exact profile reg context op proposed hm hc headProof.down isAtom.down⟩
        else none
      else none
  | _ => none

def accepts (profile : Profile sig) (reg : Registration sig) {r s}
    (context : Context sig r s) (op : sig.ACUOp s) (proposed : List Family)
    (cert : Certificate) : Bool := (replay profile reg context op proposed cert).isSome

/-- The kernel-checked acceptance theorem. Checking traverses finite data and
generated metadata; it never calls Maude, searches for unifiers, or trusts a
reported success flag. `.mp` yields completeness and `.mpr` soundness. -/
theorem replay_exact (profile : Profile sig) (reg : Registration sig) {r s}
    (context : Context sig r s) (op : sig.ACUOp s) (proposed : List Family)
    (cert : Certificate) (accepted : accepts profile reg context op proposed cert = true) :
    ∀ a b x y,
      NativeEq sig reg (reg.apply (sig.add op) (context.eval reg a, x, PUnit.unit))
        (reg.apply (sig.add op) (context.eval reg b, y, PUnit.unit)) ↔
      Solutions reg context op proposed a b x y := by
  cases result : replay profile reg context op proposed cert with
  | none => simp [accepts, result] at accepted
  | some proof => exact proof.down

/-! ### Cancellation under a free frame (general rules, not Bakery lemmas)

  C(a)+X =B C(a)+Y
  ============================== Cancel
  X =B Y

Matched is a complete family here; Crossed may still be emitted by native Maude
and is sound but redundant. This differs from independent head parameters,
where BOTH families are needed. We retain the WHOLE proposed answer list.

  f(n,a,C(a)+X) =B f(m,b,C(b)+Y)
  ==================================================== FrameCancel
  n=m AND a=b AND Cancel(C(a)+X =B C(a)+Y)

This frame schema supports ANY free constructor with two rigid fields and a
bag field, not Conf by name. It makes repeated payload/field variables explicit.
This is a supported rule schema, not an arity limit on general decomposition.
-/

theorem same_families_exact (profile : Profile sig) (reg : Registration sig) {r s}
    (context : Context sig r s) (op : sig.ACUOp s) (proposed : List Family)
    (matched : Family.matched ∈ proposed) (a : reg.Carrier r) (x y : reg.Carrier s) :
    NativeEq sig reg (reg.apply (sig.add op) (context.eval reg a, x, PUnit.unit))
      (reg.apply (sig.add op) (context.eval reg a, y, PUnit.unit)) ↔
      Solutions reg context op proposed a a x y := by
  apply (cancel_native profile reg op (context.eval reg a) x y).trans
  constructor
  · intro tails
    exact ⟨.matched, matched, a, x, rfl, rfl, .refl _, .symm tails⟩
  · rintro ⟨family, _, images⟩
    cases family with
    | matched =>
        rcases images with ⟨_, _, _, _, hx, hy⟩
        exact .trans hx (.symm hy)
    | crossed =>
        rcases images with ⟨_, hx, hy⟩
        exact .trans hx (.symm hy)

def replaySame (profile : Profile sig) (reg : Registration sig) {r s}
    (context : Context sig r s) (op : sig.ACUOp s) (proposed : List Family)
    (cert : Certificate) : Option (PLift (∀ a x y,
      NativeEq sig reg (reg.apply (sig.add op) (context.eval reg a, x, PUnit.unit))
        (reg.apply (sig.add op) (context.eval reg a, y, PUnit.unit)) ↔
      Solutions reg context op proposed a a x y)) :=
  match cert with
  | .cancellation .matched =>
      if hm : Family.matched ∈ proposed then
        some ⟨same_families_exact profile reg context op proposed hm⟩
      else none
  | _ => none

def FrameSolutions (reg : Registration sig) {u r s} (context : Context sig r s)
    (op : sig.ACUOp s) (proposed : List Family)
    (n m : reg.Carrier u) (a b : reg.Carrier r) (x y : reg.Carrier s) : Prop :=
  n = m ∧ a = b ∧ Solutions reg context op proposed a a x y

theorem framed_heads_iff (profile : Profile sig) (reg : Registration sig) {u r s v}
    (f : sig.Symbol [u, r, s] v)
    (free : profile.view f = .atom f)
    (rigidFirst : profile.rigid u = true) (rigidSecond : profile.rigid r = true)
    (left right : reg.Carrier r → reg.Carrier s) (op : sig.ACUOp s)
    (n m : reg.Carrier u) (a b : reg.Carrier r) (x y : reg.Carrier s) :
    NativeEq sig reg
      (reg.apply f (n, a, reg.apply (sig.add op) (left a, x, PUnit.unit), PUnit.unit))
      (reg.apply f (m, b, reg.apply (sig.add op) (right b, y, PUnit.unit), PUnit.unit)) ↔
      n = m ∧ a = b ∧ NativeEq sig reg
        (reg.apply (sig.add op) (left a, x, PUnit.unit))
        (reg.apply (sig.add op) (right a, y, PUnit.unit)) := by
  apply (decompose_native profile reg f free _ _).trans
  constructor
  · rintro ⟨hn, ha, bags, _⟩
    have first := (rigid_native profile reg rigidFirst n m).mp hn
    have second := (rigid_native profile reg rigidSecond a b).mp ha
    cases second
    exact ⟨first, rfl, bags⟩
  · rintro ⟨first, second, output⟩
    cases first; cases second
    exact ⟨.refl _, .refl _, output, True.intro⟩

theorem framed_same_exact (profile : Profile sig) (reg : Registration sig) {u r s v}
    (f : sig.Symbol [u, r, s] v) (free : profile.view f = .atom f)
    (rigidFirst : profile.rigid u = true) (rigidSecond : profile.rigid r = true)
    (context : Context sig r s) (op : sig.ACUOp s) (proposed : List Family)
    (tail : ∀ a x y,
      NativeEq sig reg (reg.apply (sig.add op) (context.eval reg a, x, PUnit.unit))
        (reg.apply (sig.add op) (context.eval reg a, y, PUnit.unit)) ↔
      Solutions reg context op proposed a a x y)
    (n m : reg.Carrier u) (a b : reg.Carrier r) (x y : reg.Carrier s) :
    NativeEq sig reg
      (reg.apply f (n, a, reg.apply (sig.add op) (context.eval reg a, x, PUnit.unit), PUnit.unit))
      (reg.apply f (m, b, reg.apply (sig.add op) (context.eval reg b, y, PUnit.unit), PUnit.unit)) ↔
      FrameSolutions reg context op proposed n m a b x y :=
  (framed_heads_iff profile reg f free rigidFirst rigidSecond
    (context.eval reg) (context.eval reg) op n m a b x y).trans
      ⟨fun h => ⟨h.1, h.2.1, (tail a x y).mp h.2.2⟩,
        fun h => ⟨h.1, h.2.1, (tail a x y).mpr h.2.2⟩⟩

def replayFrame (profile : Profile sig) (reg : Registration sig) {u r s v}
    (f : sig.Symbol [u, r, s] v) (context : Context sig r s)
    (op : sig.ACUOp s) (proposed : List Family) (cert : Certificate) :
    Option (PLift (∀ n m a b x y,
      NativeEq sig reg
        (reg.apply f (n, a, reg.apply (sig.add op) (context.eval reg a, x, PUnit.unit), PUnit.unit))
        (reg.apply f (m, b, reg.apply (sig.add op) (context.eval reg b, y, PUnit.unit), PUnit.unit)) ↔
      FrameSolutions reg context op proposed n m a b x y)) :=
  match cert with
  | .frameCancel .rigid .rigid tail => match free : profile.view f with
    | .atom _ =>
        if first : profile.rigid u = true then
          if second : profile.rigid r = true then do
            let tailProof ← replaySame profile reg context op proposed tail
            return ⟨framed_same_exact profile reg f free first second context op proposed tailProof.down⟩
          else none
        else none
  | _ => none

def acceptsFrame (profile : Profile sig) (reg : Registration sig) {u r s v}
    (f : sig.Symbol [u, r, s] v) (context : Context sig r s)
    (op : sig.ACUOp s) (proposed : List Family) (cert : Certificate) : Bool :=
  (replayFrame profile reg f context op proposed cert).isSome

theorem replay_frame_exact (profile : Profile sig) (reg : Registration sig) {u r s v}
    (f : sig.Symbol [u, r, s] v) (context : Context sig r s)
    (op : sig.ACUOp s) (proposed : List Family) (cert : Certificate)
    (accepted : acceptsFrame profile reg f context op proposed cert = true) :
    ∀ n m a b x y,
      NativeEq sig reg
        (reg.apply f (n, a, reg.apply (sig.add op) (context.eval reg a, x, PUnit.unit), PUnit.unit))
        (reg.apply f (m, b, reg.apply (sig.add op) (context.eval reg b, y, PUnit.unit), PUnit.unit)) ↔
      FrameSolutions reg context op proposed n m a b x y := by
  cases result : replayFrame profile reg f context op proposed cert with
  | none => simp [acceptsFrame, result] at accepted
  | some proof => exact proof.down

/-- Presentation of the ENTIRE accepted framed answer set with its actual
shared substitution parameters. This is a generic logical presentation rule. -/
theorem frame_solutions_iff (reg : Registration sig) {u r s} (context : Context sig r s)
    (op : sig.ACUOp s) (proposed : List Family)
    (matched : Family.matched ∈ proposed) (crossed : Family.crossed ∈ proposed)
    (n m : reg.Carrier u) (a b : reg.Carrier r) (x y : reg.Carrier s) :
    FrameSolutions reg context op proposed n m a b x y ↔
      (∃ k : reg.Carrier u, ∃ l : reg.Carrier r, ∃ z : reg.Carrier s,
        n = k ∧ m = k ∧ a = l ∧ b = l ∧ NativeEq sig reg x z ∧ NativeEq sig reg y z) ∨
      (∃ k : reg.Carrier u, ∃ l : reg.Carrier r, ∃ rest : reg.Carrier s,
        n = k ∧ m = k ∧ a = l ∧ b = l ∧
          NativeEq sig reg x (reg.apply (sig.add op) (context.eval reg l, rest, PUnit.unit)) ∧
          NativeEq sig reg y (reg.apply (sig.add op) (context.eval reg l, rest, PUnit.unit))) := by
  constructor
  · rintro ⟨hn, ha, solutions⟩
    rcases (solutions_iff reg context op proposed matched crossed a a x y).mp solutions with
      ⟨l, z, hl, _, hx, hy⟩ | ⟨rest, hx, hy⟩
    · exact .inl ⟨n, l, z, rfl, hn.symm, hl, ha.symm.trans hl, hx, hy⟩
    · exact .inr ⟨n, a, rest, rfl, hn.symm, rfl, ha.symm, hx, hy⟩
  · rintro (⟨k, l, z, hn, hm, ha, hb, hx, hy⟩ | ⟨k, l, rest, hn, hm, ha, hb, hx, hy⟩)
    · exact ⟨hn.trans hm.symm, ha.trans hb.symm,
        .matched, matched, l, z, ha, ha, hx, hy⟩
    · cases ha
      exact ⟨hn.trans hm.symm, hb.symm, .crossed, crossed, rest, hx, hy⟩

/-! ### Distinct heads and crossed-only coverage

  A(a)+X =B D(a)+Y       A(a) !=B D(a)       both heads atomic
  ========================================================= Clash + Exchange
  EXISTS R, X =B D(a)+R AND Y =B A(a)+R

The matched branch is impossible, NOT omitted on Maude's authority. A finite
Clash trace proves that fact against native registered constructors. The common
wrapper can have arbitrary arity. This fragment supports a ground or unary inner
head; extending that pattern grammar is separate from the general Clash theorem.
-/

inductive InnerHead (sig : Signature Sorts) (r t : Sorts) where
  | unary (symbol : sig.Symbol [r] t)
  | fixed (tree : Tree sig t)

private structure NativeHead (reg : Registration sig) (r t : Sorts) where
  sorts : List Sorts
  symbol : sig.Symbol sorts t
  arguments : reg.Carrier r → Args reg.Carrier sorts

private def InnerHead.native (reg : Registration sig) {r t} : InnerHead sig r t → NativeHead reg r t
  | .unary f => ⟨[r], f, fun a => (a, PUnit.unit)⟩
  | .fixed (.app f args) => ⟨_, f, fun _ => args.eval reg.toAlgebra⟩

def InnerHead.eval (reg : Registration sig) {r t} (head : InnerHead sig r t)
    (a : reg.Carrier r) : reg.Carrier t :=
  let root := head.native reg
  reg.apply root.symbol (root.arguments a)

def InnerHead.code (profile : Profile sig) {r t} : InnerHead sig r t → Nat
  | .unary f => profile.code f
  | .fixed (.app f _) => profile.code f

structure HeadPair (sig : Signature Sorts) (r t s : Sorts) where
  outer : Context sig t s
  left : InnerHead sig r t
  right : InnerHead sig r t

def HeadPair.leftTerm (reg : Registration sig) {r t s} (pair : HeadPair sig r t s)
    (a : reg.Carrier r) : reg.Carrier s := pair.outer.eval reg (pair.left.eval reg a)

def HeadPair.rightTerm (reg : Registration sig) {r t s} (pair : HeadPair sig r t s)
    (a : reg.Carrier r) : reg.Carrier s := pair.outer.eval reg (pair.right.eval reg a)

private def reflectionPath : HeadCertificate → Option HeadCertificate
  | .clash => some .rigid
  | .decompose position next => return .decompose position (← reflectionPath next)
  | .rigid => none

private def freeHead? (profile : Profile sig) {ss s} (f : sig.Symbol ss s) :
    Option (PLift (profile.view f = .atom f)) :=
  match profile.view f with
  | .atom _ => some ⟨rfl⟩
  | _ => none

/-- Recheck free-head metadata and code inequality. Unequal codes imply unequal
sorted constructors by congruence; the code function needs no adequacy axiom.
Reflection currently requires the INNER sort to be rigid (Mode in Bakery).
It does not replace equality of the surrounding bag by literal equality. -/
def replayApart (profile : Profile sig) (reg : Registration sig) {r t s}
    (pair : HeadPair sig r t s) (cert : HeadCertificate) :
    Option (PLift (∀ a b, ¬ NativeEq sig reg (pair.leftTerm reg a) (pair.rightTerm reg b))) := do
  let path ← reflectionPath cert
  let reflected ← replayHead profile reg pair.outer path
  let left := pair.left.native reg
  let right := pair.right.native reg
  let hl ← freeHead? profile left.symbol
  let hr ← freeHead? profile right.symbol
  if different : profile.code left.symbol ≠ profile.code right.symbol then
    let apart := clash_native profile reg left.symbol right.symbol hl.down hr.down
      (fun same => different (congrArg (fun tagged => profile.code tagged.2) same))
    return ⟨fun a b outerEq => apart (left.arguments a) (right.arguments b) (by
      have equal := (reflected.down (pair.left.eval reg a) (pair.right.eval reg b)).mp outerEq
      exact Eq.mp
        (congrArg (fun v => NativeEq sig reg (pair.left.eval reg a) v) equal) (.refl _))⟩
  else none

def CrossOutput (reg : Registration sig) {u r t s} (pair : HeadPair sig r t s)
    (op : sig.ACUOp s) (n m : reg.Carrier u) (a b : reg.Carrier r) (x y : reg.Carrier s) : Prop :=
  ∃ k : reg.Carrier u, ∃ l : reg.Carrier r, ∃ rest : reg.Carrier s,
    n = k ∧ m = k ∧ a = l ∧ b = l ∧
      NativeEq sig reg x (reg.apply (sig.add op) (pair.rightTerm reg l, rest, PUnit.unit)) ∧
      NativeEq sig reg y (reg.apply (sig.add op) (pair.leftTerm reg l, rest, PUnit.unit))

theorem framed_cross_exact (profile : Profile sig) (reg : Registration sig) {u r t s v}
    (f : sig.Symbol [u, r, s] v) (free : profile.view f = .atom f)
    (first : profile.rigid u = true) (second : profile.rigid r = true)
    (pair : HeadPair sig r t s) (op : sig.ACUOp s)
    (atom : ∀ p, mass profile (reg.quote s (pair.outer.eval reg p)) = 1)
    (apart : ∀ a b, ¬ NativeEq sig reg (pair.leftTerm reg a) (pair.rightTerm reg b))
    (n m : reg.Carrier u) (a b : reg.Carrier r) (x y : reg.Carrier s) :
    NativeEq sig reg
      (reg.apply f (n, a, reg.apply (sig.add op) (pair.leftTerm reg a, x, PUnit.unit), PUnit.unit))
      (reg.apply f (m, b, reg.apply (sig.add op) (pair.rightTerm reg b, y, PUnit.unit), PUnit.unit)) ↔
      CrossOutput reg pair op n m a b x y := by
  apply (framed_heads_iff profile reg f free first second
    (pair.leftTerm reg) (pair.rightTerm reg) op n m a b x y).trans
  constructor
  · rintro ⟨hn, ha, input⟩
    rcases (exchange_native profile reg op (pair.leftTerm reg a) (pair.rightTerm reg a)
      x y (atom _) (atom _)).mp input with ⟨heads, _⟩ | ⟨rest, hx, hy⟩
    · exact False.elim (apart a a heads)
    · exact ⟨n, a, rest, rfl, hn.symm, rfl, ha.symm, hx, hy⟩
  · rintro ⟨k, l, rest, hn, hm, ha, hb, hx, hy⟩
    cases ha; cases hb
    exact ⟨hn.trans hm.symm, rfl,
      (exchange_native profile reg op (pair.leftTerm reg a) (pair.rightTerm reg a)
        x y (atom _) (atom _)).mpr (.inr ⟨rest, hx, hy⟩)⟩

/-- The entire supported proposal is one crossed template, possibly repeated.
Matched entries are rejected, not silently erased/reinterpreted. Empty proposals,
non-atomic wrappers, equal heads and wrong trace positions all fail. -/
def replayFrameClash (profile : Profile sig) (reg : Registration sig) {u r t s v}
    (f : sig.Symbol [u, r, s] v) (pair : HeadPair sig r t s) (op : sig.ACUOp s)
    (proposed : List Family) (cert : Certificate) : Option (PLift (∀ n m a b x y,
      NativeEq sig reg
        (reg.apply f (n, a, reg.apply (sig.add op) (pair.leftTerm reg a, x, PUnit.unit), PUnit.unit))
        (reg.apply f (m, b, reg.apply (sig.add op) (pair.rightTerm reg b, y, PUnit.unit), PUnit.unit)) ↔
      CrossOutput reg pair op n m a b x y)) :=
  match cert with
  | .frameClash .rigid .rigid head .crossed => match free : profile.view f with
    | .atom _ =>
        if first : profile.rigid u = true then
          if second : profile.rigid r = true then
            if Family.crossed ∈ proposed && !(Family.matched ∈ proposed) then do
              let atom ← atomic profile reg pair.outer
              let apart ← replayApart profile reg pair head
              return ⟨framed_cross_exact profile reg f free first second pair op atom.down apart.down⟩
            else none
          else none
        else none
  | _ => none

def acceptsFrameClash (profile : Profile sig) (reg : Registration sig) {u r t s v}
    (f : sig.Symbol [u, r, s] v) (pair : HeadPair sig r t s) (op : sig.ACUOp s)
    (proposed : List Family) (cert : Certificate) : Bool :=
  (replayFrameClash profile reg f pair op proposed cert).isSome

theorem replay_frame_clash_exact (profile : Profile sig) (reg : Registration sig) {u r t s v}
    (f : sig.Symbol [u, r, s] v) (pair : HeadPair sig r t s) (op : sig.ACUOp s)
    (proposed : List Family) (cert : Certificate)
    (accepted : acceptsFrameClash profile reg f pair op proposed cert = true) :
    ∀ n m a b x y,
      NativeEq sig reg
        (reg.apply f (n, a, reg.apply (sig.add op) (pair.leftTerm reg a, x, PUnit.unit), PUnit.unit))
        (reg.apply f (m, b, reg.apply (sig.add op) (pair.rightTerm reg b, y, PUnit.unit), PUnit.unit)) ↔
      CrossOutput reg pair op n m a b x y := by
  cases result : replayFrameClash profile reg f pair op proposed cert with
  | none => simp [acceptsFrameClash, result] at accepted
  | some proof => exact proof.down

/-! ### Connect the existing Exchange rule to generic substitution data

These are reference BRANCHES generated by a proved rule, not a proposed/native
answer list. The proposed list may have a different order, variable numbering,
or redundant answers. Generic Factor leaves establish its coverage below.
-/
namespace Reference

open Substitution

mutual
  def treeTerm {Γ s} : Tree sig s → Term sig Γ s
    | .app f args => .app f (treeTerms args)
  def treeTerms {Γ ss} : Trees sig ss → Terms sig Γ ss
    | .nil => .nil
    | .cons first rest => .cons (treeTerm first) (treeTerms rest)
end

mutual
  def plug {Γ r s} (context : Context sig r s) (term : Term sig Γ r) : Term sig Γ s :=
    match context with
    | .hole => term
    | .app f args => .app f (plugArgs args term)
  def plugArgs {Γ r ss} (args : ArgumentContext sig r ss) (term : Term sig Γ r) : Terms sig Γ ss :=
    match args with
    | .focus context rest => .cons (plug context term) (treeTerms rest)
    | .before first rest => .cons (treeTerm first) (plugArgs rest term)
end

theorem treeTerm_eval (reg : Registration sig) {Γ s} (term : Tree sig s)
    (values : Args reg.Carrier Γ) : (treeTerm term).eval reg values = term.eval reg.toAlgebra := by
  refine Tree.rec
    (motive_1 := fun {s} a => (treeTerm a).eval reg values = a.eval reg.toAlgebra)
    (motive_2 := fun {ss} as => (treeTerms as).eval reg values = as.eval reg.toAlgebra)
    ?_ ?_ ?_ term
  · intro ss s f args ih; exact congrArg (reg.apply f) ih
  · rfl
  · intro s ss a rest ha hr; simp only [treeTerms, Terms.eval, Trees.eval, ha, hr]

theorem plug_eval (reg : Registration sig) {Γ r s} (context : Context sig r s)
    (term : Term sig Γ r) (values : Args reg.Carrier Γ) :
    (plug context term).eval reg values = context.eval reg (term.eval reg values) := by
  refine Context.rec
    (motive_1 := fun {s} c => (plug c term).eval reg values = c.eval reg (term.eval reg values))
    (motive_2 := fun {ss} args => (plugArgs args term).eval reg values = args.eval reg (term.eval reg values))
    ?_ ?_ ?_ ?_ context
  · rfl
  · intro ss s f args ih; exact congrArg (reg.apply f) ih
  · intro s ss c rest ih
    have fixed : (treeTerms (Γ := Γ) rest).eval reg values = rest.eval reg.toAlgebra := by
      induction ss with
      | nil => cases rest; rfl
      | cons s ss ih => cases rest with
        | cons first tail => simp only [treeTerms, Terms.eval, Trees.eval, treeTerm_eval, ih tail]
    simp only [plugArgs, Terms.eval, ArgumentContext.eval, ih, fixed]
  · intro s ss first rest ih
    simp only [plugArgs, Terms.eval, ArgumentContext.eval, treeTerm_eval, ih]

def exchangeProblem {r s} (context : Context sig r s) (op : sig.ACUOp s) :
    Problem sig [r, s, r, s] where
  sort := s
  left := Substitution.add op (plug context (.var .here)) (.var (.there .here))
  right := Substitution.add op (plug context (.var (.there (.there .here))))
    (.var (.there (.there (.there .here))))

def exchangeMatched {r s} : Answer sig [r, s, r, s] where
  parameters := [r, s]
  images := .cons (.var .here) (.cons (.var (.there .here))
    (.cons (.var .here) (.cons (.var (.there .here)) .nil)))

def exchangeCrossed {r s} (context : Context sig r s) (op : sig.ACUOp s) : Answer sig [r, s, r, s] where
  parameters := [r, s, r]
  images := .cons (.var .here)
    (.cons (Substitution.add op (.var (.there .here)) (plug context (.var (.there (.there .here)))))
      (.cons (.var (.there (.there .here)))
        (.cons (Substitution.add op (.var (.there .here)) (plug context (.var .here))) .nil)))

def exchangeBranches {r s} (context : Context sig r s) (op : sig.ACUOp s) : List (Answer sig [r, s, r, s]) :=
  [exchangeMatched, exchangeCrossed context op]

theorem exchange_complete (profile : Profile sig) (reg : Registration sig) {r s}
    (context : Context sig r s) (op : sig.ACUOp s)
    (head : ∀ a b, NativeEq sig reg (context.eval reg a) (context.eval reg b) ↔ a = b)
    (atom : ∀ a, mass profile (reg.quote s (context.eval reg a)) = 1) :
    ∀ values, (exchangeProblem context op).Holds reg values →
      Substitution.Solutions reg (exchangeBranches context op) values := by
  rintro ⟨a, x, b, y, _⟩ input
  simp only [Problem.Holds, exchangeProblem, Substitution.add, Term.eval, Terms.eval,
    Variable.eval, plug_eval] at input
  rcases (exchange_native profile reg op (context.eval reg a) (context.eval reg b)
    x y (atom a) (atom b)).mp input with ⟨heads, tails⟩ | ⟨rest, hx, hy⟩
  · have hab := (head a b).mp heads
    refine ⟨exchangeMatched, List.mem_cons_self, (a, x, PUnit.unit), ?_⟩
    subst b
    exact ⟨.refl _, .refl _, .refl _, .symm tails, True.intro⟩
  · refine ⟨exchangeCrossed context op, List.mem_cons_of_mem _ List.mem_cons_self,
      (a, rest, b, PUnit.unit), ?_⟩
    simpa only [exchangeCrossed, Substitution.add, Term.eval, Terms.eval, Variable.eval,
      plug_eval] using
      (show NativeEq sig reg a a ∧
        NativeEq sig reg x (reg.apply (sig.add op) (rest, context.eval reg b, PUnit.unit)) ∧
        NativeEq sig reg b b ∧
        NativeEq sig reg y (reg.apply (sig.add op) (rest, context.eval reg a, PUnit.unit)) ∧ True from
        ⟨.refl _, .trans hx (native_comm reg op _ _), .refl _,
          .trans hy (native_comm reg op _ _), True.intro⟩)

def mutationProblem {s} (op : sig.ACUOp s) : Problem sig [s, s, s, s] where
  sort := s
  left := Substitution.add op (.var .here) (.var (.there .here))
  right := Substitution.add op (.var (.there (.there .here)))
    (.var (.there (.there (.there .here))))

def mutationAnswer {s} (op : sig.ACUOp s) : Answer sig [s, s, s, s] where
  parameters := [s, s, s, s]
  images := .cons (Substitution.add op (.var .here) (.var (.there .here)))
    (.cons (Substitution.add op (.var (.there (.there .here))) (.var (.there (.there (.there .here)))))
      (.cons (Substitution.add op (.var .here) (.var (.there (.there .here))))
        (.cons (Substitution.add op (.var (.there .here)) (.var (.there (.there (.there .here))))) .nil)))

theorem mutation_complete (profile : Profile sig) (reg : Registration sig) {s}
    (op : sig.ACUOp s) :
    ∀ values, (mutationProblem op).Holds reg values →
      Substitution.Solutions reg [mutationAnswer op] values := by
  rintro ⟨x, y, a, rest, _⟩ input
  rcases (mutate_native profile reg op x y a rest).mp input with ⟨p, q, r, t, hx, hy, ha, hr⟩
  exact ⟨mutationAnswer op, List.mem_cons_self, (p, q, r, t, PUnit.unit),
    hx, hy, ha, hr, True.intro⟩

end Reference

/-! ## External data boundary — no semantic proofs or search in Lean

Native Maude proposes actual substitutions. We recognize EVERY image, including
the shared fresh parameters, before compacting a family to its complete template.
The object-level rules cover both head cases, or apply cancellation when the
frame's field equations identify the heads. Redundant answers are not discarded.
The returned trace is decoded, not replaced by oneTailTrace or a local solver.
Only replay_exact supplies a proof; all parsing/export code is untrusted.
Unsupported native answers fail explicitly rather than being dropped.
-/
namespace External

open Lean Lean.Meta Maude

/-- A native one-tail query, inferred from the two translated input terms. -/
structure Input where
  variables : Array MaudeVariable
  a : MaudeTerm
  b : MaudeTerm
  x : MaudeTerm
  y : MaudeTerm
  head : MaudeTerm
  rightHead? : Option MaudeTerm := none
  add : Name
  bag : Name
  sameParameters : Bool := false
  counterPair? : Option (MaudeTerm × MaudeTerm) := none

private partial def replace (term source target : MaudeTerm) : MaudeTerm :=
  if term == source then target else match term with
    | .variable _ _ => term
    | .application f s args => .application f s (args.map (replace · source target))

private partial def oneHole (head parameter : MaudeTerm) : Bool × Nat :=
  match head with
  | .variable _ _ => (head == parameter, 1)
  | .application _ _ args => args.foldl (fun (valid, count) arg =>
      let (ok, n) := oneHole arg parameter
      (valid && ok, count + n)) (true, 0)

def input (left right : TranslatedPattern) (different : Bool := false) : Except String Input := do
  let [a, x] := left.variables.toList | throw "expected two variables on the left"
  let [b, y] := right.variables.toList | throw "expected two variables on the right"
  let av := MaudeTerm.variable a.maudeName a.sort
  let bv := MaudeTerm.variable b.maudeName b.sort
  let xv := MaudeTerm.variable x.maudeName x.sort
  let yv := MaudeTerm.variable y.maudeName y.sort
  let .application add bag #[ha, tail] := left.term | throw "expected C(a)+X"
  let .application add' bag' #[hb, tail'] := right.term | throw "expected C(b)+Y"
  unless add == add' && bag == bag' && x.sort == bag && y.sort == bag &&
      a.sort == b.sort && tail == xv && tail' == yv do
    throw "unsupported one-tail query or different head contexts"
  if different then
    let (leftOK, leftHoles) := oneHole ha av
    let (rightOK, rightHoles) := oneHole hb bv
    unless leftOK && rightOK && leftHoles ≤ 1 && rightHoles ≤ 1 && replace ha av bv != hb do
      throw "unsupported distinct-head query"
  else
    unless oneHole ha av == (true, 1) && replace ha av bv == hb do
      throw "unsupported one-tail query or different head contexts"
  return {
    variables := left.variables ++ right.variables, a := av, b := bv
    x := xv, y := yv, head := ha, rightHead? := if different then some hb else none
    add := add, bag := bag }

/-- Infer a free three-field frame with a repeated second-field/head parameter.
No constructor name is special. Counter images must be independent of the head
parameter; forgetting that test would silently widen an overrestricted answer. -/
def framedInput (left right : TranslatedPattern) (different : Bool := false) : Except String Input := do
  let [n, a, x] := left.variables.toList | throw "expected three variables on the left"
  let [m, b, y] := right.variables.toList | throw "expected three variables on the right"
  let .application f s #[nv, av, bags] := left.term | throw "expected a three-field frame"
  let .application g t #[mv, bv, bags'] := right.term | throw "expected a three-field frame"
  unless f == g && s == t && n.sort == m.sort &&
      nv == .variable n.maudeName n.sort && mv == .variable m.maudeName m.sort &&
      av == .variable a.maudeName a.sort && bv == .variable b.maudeName b.sort do
    throw "unsupported framed query"
  let spec ← input { term := bags, variables := #[a, x] }
    { term := bags', variables := #[b, y] } different
  return { spec with
    variables := left.variables ++ right.variables
    sameParameters := true, counterPair? := some (nv, mv) }

private def image (candidate : MaudeUnifier) (inputVariable : MaudeTerm) : MaudeTerm :=
  match inputVariable with
  | .variable name _ => match candidate.bindings.find? (·.domain.maudeName == name) with
    | some binding => binding.image
    | none => inputVariable
  | _ => inputVariable

private def sumIs (spec : Input) (actual first second : MaudeTerm) : Bool :=
  actual == .application spec.add spec.bag #[first, second] ||
    actual == .application spec.add spec.bag #[second, first]

/-- Full template recognition, not classification by one convenient binding.
Alpha-renaming is allowed; crossed parameters must remain independent, and its
remainder must be the SAME variable in both bag images. No binding is ignored. -/
def recognize (spec : Input) (candidate : MaudeUnifier) : Except String Family := do
  let mut domains : List String := []
  for binding in candidate.bindings do
    unless spec.variables.any (fun v => v.maudeName == binding.domain.maudeName &&
        v.sort == binding.domain.sort) && !domains.contains binding.domain.maudeName do
      throw "unknown or repeated substitution domain"
    domains := binding.domain.maudeName :: domains
  let a := image candidate spec.a
  let b := image candidate spec.b
  let x := image candidate spec.x
  let y := image candidate spec.y
  let .variable _ parameterSort := spec.a | throw "invalid input parameter"
  let .variable an sa := a | throw "unsupported constrained parameter image"
  let .variable bn sb := b | throw "unsupported constrained parameter image"
  unless sa == parameterSort && sb == parameterSort do throw "parameter sort changed"
  if spec.sameParameters && a != b then throw "framed serving images must be shared"
  if let some (n, m) := spec.counterPair? then
    let counter := image candidate n
    let .variable _ cs := counter | throw "counter image is not a free parameter"
    let .variable _ ns := n | throw "invalid counter input"
    unless counter == image candidate m && cs == ns && counter != a && counter != b do
      throw "counter images must be shared and independent of serving"
  if a == b && x == y then
    if let .variable _ s := x then
      if spec.rightHead?.isSome then throw "matched answer cannot solve the distinct-head query"
      unless s == spec.bag && x != a do throw "matched remainder sort or independence changed"
      return .matched
  unless spec.sameParameters || an != bn do throw "crossed parameters must be independent"
  let .application f s #[first, second] := x | throw "unsupported crossed bag image"
  unless f == spec.add && s == spec.bag do throw "crossed image uses another operator"
  let headB := match spec.rightHead? with
    | some head => replace head spec.b b
    | none => replace spec.head spec.a b
  let headA := replace spec.head spec.a a
  let rest ← if first == headB then pure second else if second == headB then pure first
    else throw "crossed X image does not contain C(b)"
  let .variable _ rs := rest | throw "crossed remainder is not a free parameter"
  unless rs == spec.bag && sumIs spec y headA rest do
    throw "crossed images do not share the same remainder"
  return .crossed

/-- The existing native parser supplies typed constructor identities. This
wrapper additionally rejects unexplained text INSIDE any substitution block,
duplicate domains/indices, and output without a final process-exit marker. -/
def nativeAnswers (sorts : Array SortDecl) (spec : Input) (stdout : String) :
    Except String (List Family) := do
  let [_, exit] := stdout.splitOn "Bye." | throw "native output is truncated"
  unless exit.trim.isEmpty do throw "trailing native output"
  let mut inBlock := false
  for raw in stdout.splitOn "\n" do
    let line := raw.trim
    if line.startsWith "Unifier " then inBlock := true
    else if inBlock && !line.isEmpty && line != "Bye." &&
        (line.splitOn " --> ").length != 2 then
      throw "unrecognized text in native substitution block"
  let candidates ← Maude.parseUnifiers sorts spec.variables stdout
  let mut indices : List Nat := []
  let mut families := []
  for candidate in candidates do
    if indices.contains candidate.index then throw "repeated native unifier index"
    indices := candidate.index :: indices
    families := families ++ [← recognize spec candidate]
  return families

mutual
  /-- Export only search metadata. Replay rechecks it against the actual typed
  context; a dishonest 'free' or 'rigidHole' annotation cannot prove anything. -/
  def contextDump (profile : Profile sig) {r s} (context : Context sig r s) : String :=
    match context with
    | .hole => if profile.rigid r then "rigidHole" else "blocked"
    | .app f args => match profile.view f with
      | .atom _ => argumentsDump profile args 0
      | _ => "blocked"
  def argumentsDump (profile : Profile sig) {r ss} (args : ArgumentContext sig r ss)
      (position : Nat) : String := match args with
    | .focus context _ => s!"free({position},{contextDump profile context})"
    | .before _ rest => argumentsDump profile rest (position + 1)
end

private def familiesDump : List Family → String
  | [] => "nil"
  | first :: rest => s!"cons({first.dump},{familiesDump rest})"

private partial def decodeHead : Maude.Certification.Node → Except String HeadCertificate
  | .app "rigid" #[] => pure .rigid
  | .app "clash" #[] => pure .clash
  | .app "decompose" #[.num n, rest] => return .decompose n (← decodeHead rest)
  | _ => throw "unsupported head certificate"

private def decodeFamily : Maude.Certification.Node → Except String Family
  | .app "emit" #[.app "matched" #[]] => pure .matched
  | .app "emit" #[.app "crossed" #[]] => pure .crossed
  | _ => throw "unsupported coverage leaf"

private partial def decodeCertificate : Maude.Certification.Node → Except String Certificate
  | .app "coverage" #[head, equal, unequal] =>
      return .coverage (← decodeHead head) (← decodeFamily equal) (← decodeFamily unequal)
  | .app "cancellation" #[family] => return .cancellation (← decodeFamily family)
  | .app "frameCancel" #[first, second, tail] =>
      return .frameCancel (← decodeHead first) (← decodeHead second) (← decodeCertificate tail)
  | .app "frameClash" #[first, second, apart, family] =>
      return .frameClash (← decodeHead first) (← decodeHead second)
        (← decodeHead apart) (← decodeFamily family)
  | _ => throw "unsupported certificate reply"

/-- One bounded search result, echoing the WHOLE request. No solution and a
malformed/truncated certificate are failures, not empty successful certificates. -/
def searchReply (request stdout : String) : Except String Certificate := do
  let [before, after] := stdout.splitOn "R:Reply --> "
    | throw "expected exactly one certificate search result"
  unless (before.splitOn "Solution 1 (state ").length == 2 do
    throw "missing search solution heading"
  let [term, exit] := after.splitOn "Bye." | throw "truncated certificate search output"
  unless exit.trim.isEmpty do throw "trailing certificate search output"
  let .app "proposed" #[echo, certificate] ←
      Maude.Certification.parseNode term | throw "unsupported certificate reply"
  unless echo == (← Maude.Certification.parseNode request) do
    throw "certificate request echo changed"
  decodeCertificate certificate

structure Fetched where
  families : List Family
  trace : Certificate
  unifiers : Array MaudeUnifier
  -- Kept only for diagnostics/tamper tests; emit does not persist these strings.
  request : String
  nativeOutput : String
  searchOutput : String

/-- Native proposals, independently of any legacy family recognizer. Generic
export/replay accepts arbitrary well-sorted constructor image vectors. -/
def fetchNative (model : String) (sorts : Array SortDecl)
    (left right : TranslatedPattern) : IO (String × Array MaudeUnifier) := do
  let stdout ← Maude.runMaude model
    s!"unify in LEAN-MODEL : {left.term.render} =? {right.term.render} ."
  let unifiers ← IO.ofExcept (Maude.parseUnifiers sorts (left.variables ++ right.variables) stdout)
  return (stdout, unifiers)

/-- Legacy control fixture only. The GENERIC pipeline does not call this
recognizer, nor does it use a family label as a soundness/coverage certificate. -/
def fetchControlFixture (engine : String) (sorts : Array SortDecl)
    (left right : TranslatedPattern) (stdout context : String) (framed : Bool := false)
    (clashCodes? : Option (Nat × Nat) := none) : IO Fetched := do
  if clashCodes?.isSome && !framed then throw (IO.userError "clash requests require a frame")
  let spec ← IO.ofExcept
    (if framed then framedInput left right clashCodes?.isSome else input left right)
  let families ← IO.ofExcept (nativeAnswers sorts spec stdout)
  let request := match clashCodes? with
    | some (l, r) => s!"clashRequest({context},{l},{r},{familiesDump families})"
    | none =>
        let kind := if framed then "frameRequest" else "request"
        s!"{kind}({context},{familiesDump families})"
  let result ← Maude.runMaude engine
    s!"search [1, 64] in DIRECT-CERTIFICATION : start({request}) =>! R:Reply ."
  let trace ← IO.ofExcept (searchReply request result)
  let unifiers ← IO.ofExcept (Maude.parseUnifiers sorts spec.variables stdout)
  return { families, trace, unifiers, request, nativeOutput := stdout, searchOutput := result }

/- General reification: inspect the registered quote function to recover the
native sort/constructor identities. No c0/c1 numbering, carrier table, Bakery
name, family classification, or semantic bridge proof is hardcoded here. -/
private structure Layout where
  sortType : Expr
  signature : Expr
  sorts : Array (Name × Expr)
  symbols : Array (Name × Expr)

private def layout (reg : Expr) : MetaM Layout := do
  let ty ← whnf (← inferType reg)
  let #[sortType, signature] := ty.getAppArgs | throwError "expected an indexed registration"
  let some sortName := sortType.constName? | throwError "expected a finite generated sort datatype"
  let tags := (← getConstInfoInduct sortName).ctors
  let algebra ← mkAppM ``Structural.Indexed.Registration.toAlgebra #[reg]
  let mut sorts := #[]
  let mut symbols := #[]
  for tagName in tags do
    let tag := mkConst tagName
    let nativeType ← whnf (← mkAppM ``Structural.Indexed.Algebra.Carrier #[algebra, tag])
    let some nativeName := nativeType.constName? | throwError "expected a native datatype sort"
    sorts := sorts.push (nativeName, tag)
    for ctor in (← getConstInfoInduct nativeName).ctors do
      let symbol ← forallTelescopeReducing (← getConstInfo ctor).type fun args _ => do
        let native := mkAppN (mkConst ctor) args
        let quoted ← whnf (← mkAppM ``Structural.Indexed.Registration.quote #[reg, tag, native])
        unless quoted.getAppFn.constName? == some ``Structural.Indexed.Tree.app do
          throwError "registration quote did not expose a constructor"
        let fields := quoted.getAppArgs
        return fields[fields.size - 2]!
      symbols := symbols.push (ctor, symbol)
  return { sortType, signature, sorts, symbols }

private def Layout.tag (l : Layout) (name : Name) : MetaM Expr := do
  let some (_, tag) := l.sorts.find? (·.1 == name) | throwError "unregistered sort {name}"
  return tag

private def sortList (l : Layout) (names : Array Name) : MetaM Expr := do
  mkListLit l.sortType (← names.toList.mapM l.tag)

private def variableExpr (l : Layout) (names : Array Name) (index : Nat) : MetaM Expr := do
  let some name := names[index]? | throwError "variable index out of bounds"
  let tag ← l.tag name
  let tail ← sortList l (names.extract 1 names.size)
  if _h : index = 0 then
    return mkAppN (mkConst ``Substitution.Variable.here) #[l.sortType, tag, tail]
  else
    let child ← variableExpr l (names.extract 1 names.size) (index - 1)
    return mkAppN (mkConst ``Substitution.Variable.there)
      #[l.sortType, tag, ← l.tag names[0]!, tail, child]
termination_by index
decreasing_by omega

private def terms (l : Layout) (Γ : Expr) (items : Array (Expr × Expr)) : MetaM Expr := do
  let mut result := mkAppN (mkConst ``Substitution.Terms.nil) #[l.sortType, l.signature, Γ]
  let mut rest := []
  for (sort, term) in items.toList.reverse do
    result := mkAppN (mkConst ``Substitution.Terms.cons)
      #[l.sortType, l.signature, Γ, sort, ← mkListLit l.sortType rest, term, result]
    rest := sort :: rest
  return result

private partial def reify (l : Layout) (variables : Array (String × Name))
    (Γ : Expr) : MaudeTerm → MetaM (Expr × Expr)
  | .variable name sort => do
      let some index := variables.findIdx? (·.1 == name) | throwError "unknown variable {name}"
      unless variables[index]!.2 == sort do throwError "variable sort changed for {name}"
      let tag ← l.tag sort
      let v ← variableExpr l (variables.map (·.2)) index
      return (tag, mkAppN (mkConst ``Substitution.Term.var) #[l.sortType, l.signature, Γ, tag, v])
  | .application ctor result args => do
      let some (_, symbol) := l.symbols.find? (·.1 == ctor) | throwError "unregistered constructor {ctor}"
      let args ← args.mapM (reify l variables Γ)
      let argSorts ← mkListLit l.sortType (args.toList.map (·.1))
      let tag ← l.tag result
      return (tag, mkAppN (mkConst ``Substitution.Term.app)
        #[l.sortType, l.signature, Γ, argSorts, tag, symbol, ← terms l Γ args])

private partial def freshVariables (term : MaudeTerm) (known : Array (String × Name)) :
    MetaM (Array (String × Name)) := do
  match term with
  | .variable name sort =>
      if let some (_, otherSort) := known.find? (·.1 == name) then
        unless sort == otherSort do throwError "fresh variable {name} used at two sorts"
        return known
      return known.push (name, sort)
  | .application _ _ args => args.foldlM (fun known arg => freshVariables arg known) known

private def answerExpr (l : Layout) (inputs : Array MaudeVariable) (candidate : MaudeUnifier) : MetaM Expr := do
  let domains := candidate.bindings.map (·.domain.maudeName)
  unless domains.toList.eraseDups.length == domains.size &&
      candidate.bindings.all (fun b => inputs.any fun v =>
        v.maudeName == b.domain.maudeName && v.sort == b.domain.sort) do
    throwError "unknown, repeated, or wrongly sorted substitution domain"
  let images := inputs.map fun v => image candidate (.variable v.maudeName v.sort)
  let fresh ← images.foldlM (fun known term => freshVariables term known) #[]
  let Γ ← sortList l (fresh.map (·.2))
  let inputsΓ ← sortList l (inputs.map (·.sort))
  let images ← images.mapM (reify l fresh Γ)
  let value := mkAppN (mkConst ``Substitution.Answer.mk)
    #[l.sortType, l.signature, inputsΓ, Γ, ← terms l Γ images]
  -- inferType determines the emitted type. emitDefinition's kernel check then
  -- validates the entire value, including constructor arities and image sorts.
  let _ ← inferType value
  return value

private def problemExpr (l : Layout) (left right : TranslatedPattern) : MetaM Expr := do
  let inputs := left.variables ++ right.variables
  let variables := inputs.map fun v => (v.maudeName, v.sort)
  let Γ ← sortList l (inputs.map (·.sort))
  let (s, a) ← reify l variables Γ left.term
  let (t, b) ← reify l variables Γ right.term
  unless ← isDefEq s t do throwError "input equation has different result sorts"
  return mkAppN (mkConst ``Substitution.Problem.mk) #[l.sortType, l.signature, Γ, s, a, b]

private def familyExpr : Family → Expr
  | .matched => mkConst ``Family.matched
  | .crossed => mkConst ``Family.crossed

private def headExpr : HeadCertificate → Expr
  | .rigid => mkConst ``HeadCertificate.rigid
  | .clash => mkConst ``HeadCertificate.clash
  | .decompose n rest => mkApp2 (mkConst ``HeadCertificate.decompose) (mkNatLit n) (headExpr rest)

private def certificateExpr : Certificate → Expr
  | .coverage head equal unequal => mkApp3 (mkConst ``Certificate.coverage) (headExpr head)
      (familyExpr equal) (familyExpr unequal)
  | .cancellation family => mkApp (mkConst ``Certificate.cancellation) (familyExpr family)
  | .frameCancel first second tail => mkApp3 (mkConst ``Certificate.frameCancel)
      (headExpr first) (headExpr second) (certificateExpr tail)
  | .frameClash first second apart family => mkApp4 (mkConst ``Certificate.frameClash)
      (headExpr first) (headExpr second) (headExpr apart) (familyExpr family)

private def emitDefinition (name : Name) (value : Expr) : MetaM Unit := do
  let value ← instantiateMVars value
  let type ← instantiateMVars (← Lean.Meta.inferType value)
  if value.hasMVar || type.hasMVar then
    throwError "unresolved metavariable in certificate data {name}"
  Lean.addAndCompile <| .defnDecl {
    name, levelParams := []
    type, value, hints := .regular 0, safety := .safe }
  Lean.enableRealizationsForConst name

/-- Export an arbitrary native answer set, independently of legacy family
recognition/search. Every image is retained, including identity bindings. -/
def emitAnswers (pre : Name) (reg : Expr) (left right : TranslatedPattern)
    (unifiers : Array MaudeUnifier) : MetaM Unit := do
  let l ← layout reg
  let inputs := left.variables ++ right.variables
  unless (inputs.map (·.maudeName)).toList.eraseDups.length == inputs.size do
    throwError "input variable names are not disjoint/unique"
  let answerType := mkAppN (mkConst ``Substitution.Answer)
    #[l.sortType, l.signature, ← sortList l (inputs.map (·.sort))]
  let answers ← unifiers.toList.mapM (answerExpr l inputs)
  emitDefinition (pre ++ `answers) (← mkListLit answerType answers)
  emitDefinition (pre ++ `problem) (← problemExpr l left right)

/-- OLD regression data only, not the generic native-answer transport. -/
def emitControlFixture (pre : Name) (fetched : Fetched) : Lean.MetaM Unit := do
  let trace := certificateExpr fetched.trace
  for (name, value) in [(pre ++ `families, ← Lean.Meta.mkListLit (mkConst ``Family)
      (fetched.families.map familyExpr)), (pre ++ `trace, trace)] do
    emitDefinition name value

/- GENERIC WIRE BOUNDARY. Numeric IDs are local indices in the actual registered
signature. They never carry semantic authority. The reply supplies only finite
data: one primitive equality trace per answer, and one (index, β, image traces)
per reference branch. Lean checks their precise sorted endpoints before the
kernel checks the emitted definitions. No proof tactic runs here.

The reference branches must separately have a semantic completeness theorem.
Native Maude matching discovers β on the ENTIRE input-image vector. The
object-level engine produces primitive equality traces for each suggested β;
Lean then checks those traces. Failed matching is not a completeness proof.
-/
private abbrev Wire := Maude.Certification.Node

private partial def listItems (e : Expr) : MetaM (Array Expr) := do
  let e ← whnf e
  match e.getAppFn.constName? with
  | some ``List.nil => return #[]
  | some ``List.cons =>
    let a := e.getAppArgs
    return #[a[a.size - 2]!] ++ (← listItems a.back!)
  | _ => throwError "expected a finite constructor list"

private partial def vectorItems (e : Expr) : MetaM (Array (Expr × Expr)) := do
  let e ← whnf e
  match e.getAppFn.constName? with
  | some ``Substitution.Terms.nil => return #[]
  | some ``Substitution.Terms.cons =>
    let a := e.getAppArgs
    return #[(a[3]!, a[a.size - 2]!)] ++ (← vectorItems a.back!)
  | _ => throwError "expected a finite sorted term vector"

private def sameIndex (items : Array Expr) (e : Expr) : MetaM Nat := do
  for i in [:items.size] do
    if ← isDefEq items[i]! e then return i
  throwError "unregistered sort or constructor in certificate"

private def wireList (nil cons : String) (items : Array String) : String :=
  items.foldr (fun a rest => s!"{cons}({a},{rest})") nil

private partial def variableIndex (e : Expr) : MetaM Nat := do
  let e ← whnf e
  match e.getAppFn.constName? with
  | some ``Substitution.Variable.here => return 0
  | some ``Substitution.Variable.there => return 1 + (← variableIndex e.getAppArgs.back!)
  | _ => throwError "expected a finite sorted variable"

private partial def dumpTerm (l : Layout) (e : Expr) : MetaM String := do
  let e ← whnf e
  let a := e.getAppArgs
  match e.getAppFn.constName? with
  | some ``Substitution.Term.var => return s!"v({← variableIndex a.back!})"
  | some ``Substitution.Term.app =>
    let id ← sameIndex (l.symbols.map (·.2)) a[a.size - 2]!
    let args ← (← vectorItems a.back!).mapM (fun (_, t) => dumpTerm l t)
    return s!"node({id},{wireList "tsNil" "tsCons" args})"
  | _ => throwError "expected a registered constructor term"

private def dumpSorts (l : Layout) (e : Expr) : MetaM String := do
  let ids ← (← listItems e).mapM fun s => return toString (← sameIndex (l.sorts.map (·.2)) s)
  return wireList "nsNil" "nsCons" ids

private def field (name : Name) (e : Expr) : MetaM Expr := mkAppM name #[e]

private def dumpAnswer (l : Layout) (answer : Expr) : MetaM String := do
  let sorts ← dumpSorts l (← field ``Substitution.Answer.parameters answer)
  let images ← (← vectorItems (← field ``Substitution.Answer.images answer)).mapM
    (fun (_, t) => dumpTerm l t)
  return s!"answer({sorts},{wireList "tsNil" "tsCons" images})"

private def registeredOperators (l : Layout) : MetaM (Array (Nat × Nat × Expr)) := do
  let mut result := #[]
  for (_, tag) in l.sorts do
    let ty ← whnf (← mkAppM ``Signature.ACUOp #[l.signature, tag])
    let some name := ty.getAppFn.constName? | throwError "expected finite registered ACU operators"
    for ctor in (← getConstInfoInduct name).ctors do
      let op := mkConst ctor
      if ← isDefEq (← inferType op) ty then
        let add ← mkAppM ``Signature.add #[l.signature, op]
        let zero ← mkAppM ``Signature.zero #[l.signature, op]
        result := result.push (← sameIndex (l.symbols.map (·.2)) add,
          ← sameIndex (l.symbols.map (·.2)) zero, op)
  return result

private def genericRequest (l : Layout) (problem reference proposed : Expr)
    (hints : String := "hsNil") : MetaM String := do
  let ops ← registeredOperators l
  let ops := wireList "opsNil" "opsCons" (ops.map fun (a, z, _) => s!"acu({a},{z})")
  let inputSorts := (← inferType problem).getAppArgs.back!
  let p := s!"problem({← dumpSorts l inputSorts},{← dumpTerm l (← field ``Substitution.Problem.left problem)}," ++
    s!"{← dumpTerm l (← field ``Substitution.Problem.right problem)})"
  let ref ← (← listItems reference).mapM (dumpAnswer l)
  let prop ← (← listItems proposed).mapM (dumpAnswer l)
  return s!"gRequest({ops},{p},{wireList "asNil" "asCons" ref},{wireList "asNil" "asCons" prop},{hints})"

def dumpGeneric (reg problem reference proposed : Expr) : MetaM String := do
  genericRequest (← layout reg) problem reference proposed

/-- Reject changed requests, multiple results, missing exit markers and unknown
reply shapes. Equality/index/binding checks follow in the typed decoder. -/
def genericReply (request stdout : String) : Except String (Wire × Wire) := do
  let [before, after] := stdout.splitOn "G:GenericReply --> "
    | throw "expected exactly one generic certificate search result"
  unless (before.splitOn "Solution 1 (state ").length == 2 do throw "missing search solution heading"
  let [term, exit] := after.splitOn "Bye." | throw "truncated generic certificate output"
  unless exit.trim.isEmpty do throw "trailing generic certificate output"
  let .app "gProposed" #[echo, .app "gCertificate" #[sound, cover]] ←
      Maude.Certification.parseNode term | throw "unsupported generic certificate reply"
  unless echo == (← Maude.Certification.parseNode request) do throw "generic request echo changed"
  return (sound, cover)

private partial def wireItems (nil cons : String) : Wire → MetaM (Array Wire)
  | .app n #[] => if n == nil then pure #[] else throwError "unexpected certificate list tag {n}"
  | .app n #[a, rest] => do
    unless n == cons do throwError "unexpected certificate list tag {n}"
    return #[a] ++ (← wireItems nil cons rest)
  | _ => throwError "malformed certificate list"

private def contextNames (l : Layout) (Γ : Expr) : MetaM (Array Name) := do
  (← listItems Γ).mapM fun tag => do
    let i ← sameIndex (l.sorts.map (·.2)) tag
    return l.sorts[i]!.1

private partial def decodeTerm (l : Layout) (Γ : Expr) (wire : Wire) : MetaM (Expr × Expr) := do
  match wire with
  | .app "v" #[.num i] =>
    let names ← contextNames l Γ
    let some name := names[i]? | throwError "certificate variable index out of bounds"
    let s ← l.tag name
    return (s, mkAppN (mkConst ``Substitution.Term.var)
      #[l.sortType, l.signature, Γ, s, ← variableExpr l names i])
  | .app "node" #[.num i, args] =>
    let some (_, f) := l.symbols[i]? | throwError "certificate constructor index out of bounds"
    let ty ← inferType f
    let sorts := ty.getAppArgs[ty.getAppArgs.size - 2]!
    let s := ty.getAppArgs.back!
    let expected ← listItems sorts
    let raw ← wireItems "tsNil" "tsCons" args
    unless raw.size == expected.size do throwError "certificate constructor arity changed"
    let decoded ← raw.mapM (decodeTerm l Γ)
    for i in [:decoded.size] do
      unless ← isDefEq decoded[i]!.1 expected[i]! do throwError "certificate constructor argument sort changed"
    return (s, mkAppN (mkConst ``Substitution.Term.app)
      #[l.sortType, l.signature, Γ, sorts, s, f, ← terms l Γ decoded])
  | _ => throwError "unsupported term in certificate"

private def appView (e : Expr) : MetaM (Expr × Expr) := do
  let e ← whnf e
  unless e.getAppFn.constName? == some ``Substitution.Term.app do
    throwError "equality step expects a constructor application"
  let a := e.getAppArgs
  return (a[a.size - 2]!, a.back!)

private def operatorOf (l : Layout) (term : Expr) : MetaM Expr := do
  let (f, _) ← appView term
  let id ← sameIndex (l.symbols.map (·.2)) f
  let some (_, _, op) := (← registeredOperators l).find? (·.1 == id)
    | throwError "equality step uses an unregistered ACU operator"
  return op

mutual
  private partial def decodeEquality (l : Layout) (Γ left right : Expr) (wire : Wire) : MetaM Expr := do
    let s := (← inferType left).getAppArgs.back!
    let typeArgs := #[l.sortType, l.signature, Γ]
    let value ← match wire with
      | .app "eRefl" #[] => pure <| mkAppN (mkConst ``Substitution.Equality.refl) (typeArgs ++ #[s, left])
      | .app "eSym" #[p] => do
        let p ← decodeEquality l Γ right left p
        pure <| mkAppN (mkConst ``Substitution.Equality.symm) (typeArgs ++ #[s, right, left, p])
      | .app "eTrans" #[middle, p, q] => do
        let (t, mid) ← decodeTerm l Γ middle
        unless ← isDefEq s t do throwError "transitivity midpoint sort changed"
        let p ← decodeEquality l Γ left mid p
        let q ← decodeEquality l Γ mid right q
        pure <| mkAppN (mkConst ``Substitution.Equality.trans) (typeArgs ++ #[s, left, mid, right, p, q])
      | .app "eCongr" #[ps] => do
        let (f, as) ← appView left
        let (g, bs) ← appView right
        unless ← isDefEq f g do throwError "congruence constructor changed"
        let ss := (← inferType as).getAppArgs.back!
        let ps ← decodeEqualities l Γ as bs ps
        pure <| mkAppN (mkConst ``Substitution.Equality.congr) (typeArgs ++ #[ss, s, f, as, bs, ps])
      | .app "eComm" #[] => do
        let op ← operatorOf l left
        let (_, as) ← appView left
        let xs ← vectorItems as
        unless xs.size == 2 do throwError "commutativity requires two arguments"
        pure <| mkAppN (mkConst ``Substitution.Equality.comm) (typeArgs ++ #[s, op, xs[0]!.2, xs[1]!.2])
      | .app "eAssoc" #[] => do
        let op ← operatorOf l left
        let (_, as) ← appView left
        let xs ← vectorItems as
        unless xs.size == 2 do throwError "associativity requires two arguments"
        let (_, bs) ← appView xs[0]!.2
        let ys ← vectorItems bs
        unless ys.size == 2 do throwError "associativity requires a nested binary application"
        pure <| mkAppN (mkConst ``Substitution.Equality.assoc)
          (typeArgs ++ #[s, op, ys[0]!.2, ys[1]!.2, xs[1]!.2])
      | .app "eUnit" #[] => do
        let op ← operatorOf l left
        let (_, as) ← appView left
        let xs ← vectorItems as
        unless xs.size == 2 do throwError "unit step requires two arguments"
        pure <| mkAppN (mkConst ``Substitution.Equality.unit) (typeArgs ++ #[s, op, xs[1]!.2])
      | _ => throwError "unsupported equality certificate tag"
    let expected := mkAppN (mkConst ``Substitution.Equality) (typeArgs ++ #[s, left, right])
    unless ← isDefEq (← inferType value) expected do throwError "equality trace endpoints do not match"
    return value

  private partial def decodeEqualities (l : Layout) (Γ left right : Expr) (wire : Wire) : MetaM Expr := do
    let xs ← vectorItems left
    let ys ← vectorItems right
    let raw ← wireItems "esNil" "esCons" wire
    unless xs.size == ys.size && xs.size == raw.size do throwError "image equality trace count changed"
    let mut result := mkAppN (mkConst ``Substitution.Equalities.nil) #[l.sortType, l.signature, Γ]
    let mut as := mkAppN (mkConst ``Substitution.Terms.nil) #[l.sortType, l.signature, Γ]
    let mut bs := as
    let mut ss := []
    for i in (List.range xs.size).reverse do
      let (s, a) := xs[i]!
      let (t, b) := ys[i]!
      unless ← isDefEq s t do throwError "image equality sort changed"
      let p ← decodeEquality l Γ a b raw[i]!
      result := mkAppN (mkConst ``Substitution.Equalities.cons)
        #[l.sortType, l.signature, Γ, s, ← mkListLit l.sortType ss, a, b, as, bs, p, result]
      as ← terms l Γ (xs.extract i xs.size)
      bs ← terms l Γ (ys.extract i ys.size)
      ss := s :: ss
    return result
end

private def answerFields (answer : Expr) : MetaM (Expr × Expr) := do
  return (← field ``Substitution.Answer.parameters answer, ← field ``Substitution.Answer.images answer)

/-- Inverse of the native-term reifier, using distinct target/source variable
names. Repeated indices produce the SAME Maude variable at every occurrence. -/
private partial def nativeTerm (l : Layout) (variables : Array (String × Name))
    (e : Expr) : MetaM MaudeTerm := do
  let e ← whnf e
  let a := e.getAppArgs
  match e.getAppFn.constName? with
  | some ``Substitution.Term.var =>
    let i ← variableIndex a.back!
    let some (name, sort) := variables[i]? | throwError "native match variable out of bounds"
    return .variable name sort
  | some ``Substitution.Term.app =>
    let id ← sameIndex (l.symbols.map (·.2)) a[a.size - 2]!
    let result ← sameIndex (l.sorts.map (·.2)) a[4]!
    let args ← (← vectorItems a.back!).mapM (fun (_, t) => nativeTerm l variables t)
    return .application l.symbols[id]!.1 l.sorts[result]!.1 args
  | _ => throwError "expected a sorted constructor term for native matching"

/-- Reuse the production Maude exporter/parser/matcher. A synthetic FREE tuple
frames all input images in one query, so one β must satisfy every coordinate.
Source parameters remain rigid subject variables; target parameters alone may
be assigned. This is search DATA only; no matcher result is trusted as a proof.
Unused target parameters are rejected rather than assigned fabricated values. -/
private def nativeFactorHints (l : Layout) (problem reference proposed : Expr) : MetaM String := do
  let root ← sameIndex (l.sorts.map (·.2)) (← field ``Substitution.Problem.sort problem)
  let mut sorts ← Maude.collectSignature (mkConst l.sorts[root]!.1)
  let inputs ← contextNames l (← inferType problem).getAppArgs.back!
  let used := (sorts.flatMap fun s => #[s.leanName] ++ s.constructors.map (·.leanName)).map
    (fun n => match n with | .str _ s => s | _ => n.toString)
  let mut suffix := 0
  while used.contains s!"CertificationImageVector{suffix}" ||
      used.contains s!"certificationImages{suffix}" do
    suffix := suffix + 1
  let frameSort := Name.mkSimple s!"CertificationImageVector{suffix}"
  let frame := Name.mkSimple s!"certificationImages{suffix}"
  sorts := sorts.push {
    leanName := frameSort
    constructors := #[{ leanName := frame, fields := inputs, result := frameSort }] }
  let operators ← (← registeredOperators l).mapM fun (add, unitId, _) => do
    return ({ leanName := l.symbols[add]!.1, laws :=
      #[.associative, .commutative, .identity l.symbols[unitId]!.1] } : OperatorDecl)
  let model := Maude.renderModule sorts operators
  let targets ← listItems proposed
  let mut hints := #[]
  for source in ← listItems reference do
    let (Γ, sourceImages) ← answerFields source
    let names ← contextNames l Γ
    let fixed := names.mapIdx fun i s => (s!"S{i}", s)
    let subject ← (← vectorItems sourceImages).mapM (fun (_, t) => nativeTerm l fixed t)
    let mut hint := "hFailed"
    for i in [:targets.size] do
      let (Δ, targetImages) ← answerFields targets[i]!
      let names ← contextNames l Δ
      let bindable := names.mapIdx fun j s => (s!"T{j}", s)
      let pattern ← (← vectorItems targetImages).mapM (fun (_, t) => nativeTerm l bindable t)
      -- expression/leanName are unused by the raw parser; they carry no proof.
      let variables := (bindable ++ fixed).mapIdx fun j (name, sort) =>
        ({ expression := .bvar j, leanName := .mkSimple name, maudeName := name, sort } : MaudeVariable)
      let candidates ← Maude.matchTranslated sorts model variables
        (.application frame frameSort pattern) (.application frame frameSort subject)
      for candidate in candidates do
        let mut beta := #[]
        let mut complete := true
        for (name, sort) in bindable do
          match candidate.bindings.find? (·.domain.maudeName == name) with
          | none => complete := false
          | some binding =>
            unless binding.domain.sort == sort do throwError "native matcher changed a parameter sort"
            let (_, term) ← reify l fixed Γ binding.image
            beta := beta.push (← dumpTerm l term)
        if complete then
          hint := s!"hint({i},{wireList "tsNil" "tsCons" beta})"
          break
      if hint != "hFailed" then break
    hints := hints.push hint
  return wireList "hsNil" "hsCons" hints

/-- Decode DATA only. Theorem selection stays outside this boundary: semantic
completeness of the reference is supplied by the general Exchange/Mutate rules. -/
private def decodeGeneric (l : Layout) (problem reference proposed : Expr)
    (soundWire coverWire : Wire) : MetaM (Expr × Expr) := do
  let inputs := (← inferType problem).getAppArgs.back!
  let answerType := mkAppN (mkConst ``Substitution.Answer) #[l.sortType, l.signature, inputs]
  let proposals ← listItems proposed
  let sources ← listItems reference
  let soundRaw ← wireItems "esNil" "esCons" soundWire
  let coverRaw ← wireItems "fsNil" "fsCons" coverWire
  unless soundRaw.size == proposals.size && coverRaw.size == sources.size do
    throwError "certificate answer/reference count changed"
  let left ← field ``Substitution.Problem.left problem
  let right ← field ``Substitution.Problem.right problem
  let mut sound := mkAppN (mkConst ``Substitution.Soundness.nil) #[l.sortType, l.signature, inputs, problem]
  for i in (List.range proposals.size).reverse do
    let answer := proposals[i]!
    let (Γ, images) ← answerFields answer
    let a ← mkAppM ``Substitution.Term.subst #[images, left]
    let b ← mkAppM ``Substitution.Term.subst #[images, right]
    let p ← decodeEquality l Γ a b soundRaw[i]!
    let rest ← mkListLit answerType (proposals.extract (i + 1) proposals.size).toList
    sound := mkAppN (mkConst ``Substitution.Soundness.cons)
      #[l.sortType, l.signature, inputs, problem, answer, rest, p, sound]
  let mut cover := mkAppN (mkConst ``Substitution.Coverage.nil) #[l.sortType, l.signature, inputs, proposed]
  for i in (List.range sources.size).reverse do
    let .app "factor" #[.num index, betaRaw, equalRaw] := coverRaw[i]!
      | throwError "unsupported factorization certificate"
    let some target := proposals[index]? | throwError "coverage answer index out of bounds"
    let source := sources[i]!
    let (Γ, images) ← answerFields source
    let (Δ, targetImages) ← answerFields target
    let expected ← listItems Δ
    let betaRaw ← wireItems "tsNil" "tsCons" betaRaw
    unless betaRaw.size == expected.size do throwError "factorization parameter count changed"
    let betaItems ← betaRaw.mapM (decodeTerm l Γ)
    for j in [:expected.size] do
      unless ← isDefEq betaItems[j]!.1 expected[j]! do throwError "factorization parameter sort changed"
    let beta ← terms l Γ betaItems
    let composed ← mkAppM ``Substitution.Terms.subst #[targetImages, beta]
    let ps ← decodeEqualities l Γ images composed equalRaw
    let factor := mkAppN (mkConst ``Substitution.Factor.mk)
      #[l.sortType, l.signature, inputs, source, target, beta, ps]
    let n := mkNatLit proposals.size
    let bound ← mkDecideProof (← mkLt (mkNatLit index) n)
    let fin := mkAppN (mkConst ``Fin.mk) #[n, mkNatLit index, bound]
    let rest ← mkListLit answerType (sources.extract (i + 1) sources.size).toList
    cover := mkAppN (mkConst ``Substitution.Coverage.cons)
      #[l.sortType, l.signature, inputs, proposed, source, rest, fin, factor, cover]
  -- Meta.check catches ill-typed constructor applications too; kernel checking
  -- emitted safe definitions remains the final acceptance boundary.
  check sound
  check cover
  return (sound, cover)

structure GenericFetched where
  request : String
  output : String

/-- Read-only replay, also used by adversarial tests. A failed check emits no
definition and cannot introduce a semantic assumption. -/
def checkGenericData (reg problem reference proposed : Expr) (sound cover : Wire) : MetaM Unit := do
  let _ ← decodeGeneric (← layout reg) problem reference proposed sound cover

private def genericData (l : Layout) (problem reference proposed : Expr)
    (engine : String) : MetaM (GenericFetched × Expr × Expr) := do
  let request ← genericRequest l problem reference proposed
    (← nativeFactorHints l problem reference proposed)
  let output ← Maude.runMaude engine
    s!"search [1, 64] in GENERIC-CERTIFICATION : gStart({request}) =>! G:GenericReply ."
  let (soundRaw, coverRaw) ← Lean.ofExcept (genericReply request output)
  let (sound, cover) ← decodeGeneric l problem reference proposed soundRaw coverRaw
  return ({ request, output }, sound, cover)

def fetchGeneric (pre : Name) (reg problem reference proposed : Expr)
    (engine : String) : MetaM GenericFetched := do
  let (fetched, sound, cover) ← genericData (← layout reg) problem reference proposed engine
  emitDefinition (pre ++ `soundness) sound
  emitDefinition (pre ++ `coverage) cover
  return fetched

mutual
  private partial def decodeDerives (l : Layout) (Γ eqs left right : Expr) (wire : Wire) : MetaM Expr := do
    let s := (← inferType left).getAppArgs.back!
    let typeArgs := #[l.sortType, l.signature, Γ, eqs]
    let result ← match wire with
    | .app "eHyp" #[.num i] => do
      let n := (← listItems eqs).size
      unless i < n do throwError "worklist hypothesis index out of bounds"
      let fin := mkAppN (mkConst ``Fin.mk) #[mkNatLit n, mkNatLit i,
        ← mkDecideProof (← mkLt (mkNatLit i) (mkNatLit n))]
      pure <| mkAppN (mkConst ``Substitution.Worklist.Derives.hyp) (typeArgs ++ #[fin])
    | .app "eSym" #[p] => do
      let p ← decodeDerives l Γ eqs right left p
      pure <| mkAppN (mkConst ``Substitution.Worklist.Derives.symm) (typeArgs ++ #[s, right, left, p])
    | .app "eTrans" #[middle, p, q] => do
      let (t, mid) ← decodeTerm l Γ middle
      unless ← isDefEq s t do throwError "worklist midpoint sort changed"
      let p ← decodeDerives l Γ eqs left mid p
      let q ← decodeDerives l Γ eqs mid right q
      pure <| mkAppN (mkConst ``Substitution.Worklist.Derives.trans) (typeArgs ++ #[s, left, mid, right, p, q])
    | .app "eCongr" #[ps] => do
      let (f, as) ← appView left
      let (g, bs) ← appView right
      unless ← isDefEq f g do throwError "worklist congruence changed constructor"
      let ss := (← inferType as).getAppArgs.back!
      let ps ← decodeDerivesArgs l Γ eqs as bs ps
      pure <| mkAppN (mkConst ``Substitution.Worklist.Derives.congr) (typeArgs ++ #[ss, s, f, as, bs, ps])
    | _ => do
      let p ← decodeEquality l Γ left right wire
      pure <| mkAppN (mkConst ``Substitution.Worklist.Derives.axiom) (typeArgs ++ #[s, left, right, p])
    let expected := mkAppN (mkConst ``Substitution.Worklist.Derives) (typeArgs ++ #[s, left, right])
    unless ← isDefEq (← inferType result) expected do throwError "worklist consequence endpoints changed"
    return result

  private partial def decodeDerivesArgs (l : Layout) (Γ eqs left right : Expr) (wire : Wire) : MetaM Expr := do
    let xs ← vectorItems left
    let ys ← vectorItems right
    let raw ← wireItems "esNil" "esCons" wire
    unless xs.size == ys.size && xs.size == raw.size do throwError "worklist image trace count changed"
    let typeArgs := #[l.sortType, l.signature, Γ, eqs]
    let mut result := mkAppN (mkConst ``Substitution.Worklist.DerivesArgs.nil) typeArgs
    for i in (List.range xs.size).reverse do
      let (s, a) := xs[i]!
      let (t, b) := ys[i]!
      unless ← isDefEq s t do throwError "worklist image sort changed"
      let p ← decodeDerives l Γ eqs a b raw[i]!
      let as ← terms l Γ (xs.extract (i + 1) xs.size)
      let bs ← terms l Γ (ys.extract (i + 1) ys.size)
      let ss ← mkListLit l.sortType ((xs.extract (i + 1) xs.size).toList.map (·.1))
      result := mkAppN (mkConst ``Substitution.Worklist.DerivesArgs.cons)
        (typeArgs ++ #[s, ss, a, b, as, bs, p, result])
    return result
end

private def decodeVector (l : Layout) (Γ ss : Expr) (wire : Wire) : MetaM Expr := do
  let expected ← listItems ss
  let raw ← wireItems "tsNil" "tsCons" wire
  unless expected.size == raw.size do throwError "worklist vector arity changed"
  let items ← raw.mapM (decodeTerm l Γ)
  for i in [:items.size] do
    unless ← isDefEq items[i]!.1 expected[i]! do throwError "worklist vector sort changed"
  terms l Γ items

private def wireOperator (l : Layout) (index : Nat) : MetaM Expr := do
  let some (_, _, op) := (← registeredOperators l).find? (·.1 == index)
    | throwError "worklist step uses an unregistered ACU symbol"
  return op

/-- Replay a general tree against the CURRENT scope/worklist. No node is selected
by a Bakery shape. Leaf search uses the production native matcher; its factor
data is still checked by the existing generic decoder and the final kernel. -/
private partial def decodeComplete (l : Layout) (profile problem proposed : Expr)
    (Γ images eqs : Expr) (wire : Wire) (engine : String) : MetaM Expr := do
  let inputs := (← inferType problem).getAppArgs.back!
  let typeArgs := #[l.sortType, l.signature, profile, inputs, proposed, Γ, images, eqs]
  let result ← match wire with
  | .app "cLeaf" #[normalizedRaw, derivedRaw] => do
    let normalized ← decodeVector l Γ inputs normalizedRaw
    let derived ← decodeDerivesArgs l Γ eqs images normalized derivedRaw
    let source := mkAppN (mkConst ``Substitution.Answer.mk) #[l.sortType, l.signature, inputs, Γ, normalized]
    let reference ← mkListLit (← inferType source) [source]
    let (_, _, cover) ← genericData l problem reference proposed engine
    let fields := cover.getAppArgs
    unless cover.getAppFn.constName? == some ``Substitution.Coverage.cons do
      throwError "missing worklist leaf factor"
    pure <| mkAppN (mkConst ``Substitution.Worklist.Complete.emit)
      (typeArgs ++ #[fields[fields.size - 3]!, normalized, derived, fields[fields.size - 2]!])
  | .app "cMutate" #[.num opId, a, b, c, d, selectedRaw, childRaw] => do
    let op ← wireOperator l opId
    let (s, a) ← decodeTerm l Γ a
    let (sb, b) ← decodeTerm l Γ b
    let (sc, c) ← decodeTerm l Γ c
    let (sd, d) ← decodeTerm l Γ d
    unless (← isDefEq s sb) && (← isDefEq s sc) && (← isDefEq s sd) do
      throwError "worklist mutation operand sorts changed"
    let left := mkAppN (mkConst ``Substitution.add) #[l.sortType, l.signature, Γ, s, op, a, b]
    let right := mkAppN (mkConst ``Substitution.add) #[l.sortType, l.signature, Γ, s, op, c, d]
    let selected ← decodeDerives l Γ eqs left right selectedRaw
    let lift := mkAppN (mkConst ``Substitution.Worklist.lift4) #[l.sortType, l.signature, Γ, s]
    let images' ← mkAppM ``Substitution.Terms.subst #[images, lift]
    let Γ' := (← inferType images').getAppArgs[2]!
    let eqs' := mkAppN (mkConst ``Substitution.Worklist.mutated)
      #[l.sortType, l.signature, Γ, s, op, a, b, c, d, eqs]
    let child ← decodeComplete l profile problem proposed Γ' images' eqs' childRaw engine
    pure <| mkAppN (mkConst ``Substitution.Worklist.Complete.mutate)
      (typeArgs ++ #[s, op, a, b, c, d, selected, child])
  | .app "cSplit" #[.num opId, x, y, atom, selectedRaw, leftRaw, rightRaw] => do
    let op ← wireOperator l opId
    let (s, x) ← decodeTerm l Γ x
    let (t, y) ← decodeTerm l Γ y
    let (u, atom) ← decodeTerm l Γ atom
    unless (← isDefEq s t) && (← isDefEq s u) do throwError "worklist split operand sorts changed"
    let (f, args) ← appView atom
    let ss := (← inferType args).getAppArgs.back!
    let view ← mkAppM ``Profile.view #[profile, f]
    let free := mkAppN (mkConst ``HeadView.atom) #[l.sortType, l.signature, ss, s, f]
    unless ← isDefEq view free do throwError "worklist split selected a non-atomic head"
    let metadata ← mkEqRefl view
    let sum := mkAppN (mkConst ``Substitution.add) #[l.sortType, l.signature, Γ, s, op, x, y]
    let selected ← decodeDerives l Γ eqs sum atom selectedRaw
    let zero := mkAppN (mkConst ``Substitution.zero) #[l.sortType, l.signature, Γ, s, op]
    let problemType := mkAppN (mkConst ``Substitution.Problem) #[l.sortType, l.signature, Γ]
    let originals := (← listItems eqs).toList
    let leftEqs ← mkListLit problemType ((← mkAppM ``Substitution.Worklist.equation #[x, zero]) ::
      (← mkAppM ``Substitution.Worklist.equation #[y, atom]) :: originals)
    let rightEqs ← mkListLit problemType ((← mkAppM ``Substitution.Worklist.equation #[x, atom]) ::
      (← mkAppM ``Substitution.Worklist.equation #[y, zero]) :: originals)
    let left ← decodeComplete l profile problem proposed Γ images leftEqs leftRaw engine
    let right ← decodeComplete l profile problem proposed Γ images rightEqs rightRaw engine
    pure <| mkAppN (mkConst ``Substitution.Worklist.Complete.split)
      (typeArgs ++ #[ss, s, op, x, y, f, metadata, args, selected, left, right])
  | _ => throwError "unsupported or incomplete worklist certificate tree"
  let expected := mkAppN (mkConst ``Substitution.Worklist.Complete) typeArgs
  unless ← isDefEq (← inferType result) expected do throwError "worklist tree does not match its sequent"
  return result

def completeReply (request stdout : String) : Except String Wire := do
  let [before, after] := stdout.splitOn "W:CReply --> "
    | throw "expected exactly one worklist certificate result"
  unless (before.splitOn "Solution 1 (state ").length == 2 do throw "missing worklist solution heading"
  let [term, exit] := after.splitOn "Bye." | throw "truncated worklist certificate"
  unless exit.trim.isEmpty do throw "trailing worklist certificate output"
  let .app "cProposed" #[echo, tree] ← Maude.Certification.parseNode term
    | throw "unsupported worklist reply"
  unless echo == (← Maude.Certification.parseNode request) do throw "worklist request echo changed"
  return tree

/-- Non-mutating replay entry point for malformed-certificate regression tests.
No declarations are emitted if any branch or equality fails validation. -/
def checkCompleteData (reg profile problem proposed : Expr) (tree : Wire) (engine : String) : MetaM Unit := do
  let l ← layout reg
  let Γ := (← inferType problem).getAppArgs.back!
  let images := mkAppN (mkConst ``Substitution.Terms.identity) #[l.sortType, l.signature, Γ]
  let eqs ← mkListLit (← inferType problem) [problem]
  check (← decodeComplete l profile problem proposed Γ images eqs tree engine)

def fetchComplete (pre : Name) (reg profile problem proposed : Expr) (engine : String) : MetaM GenericFetched := do
  let l ← layout reg
  let ops := wireList "opsNil" "opsCons" ((← registeredOperators l).map fun (a, z, _) => s!"acu({a},{z})")
  let Γ := (← inferType problem).getAppArgs.back!
  let s ← sameIndex (l.sorts.map (·.2)) (← field ``Substitution.Problem.sort problem)
  let request := s!"cRequest({ops},{← dumpSorts l Γ},{s}," ++
    s!"{← dumpTerm l (← field ``Substitution.Problem.left problem)}," ++
    s!"{← dumpTerm l (← field ``Substitution.Problem.right problem)})"
  let stdout ← Maude.runMaude engine
    s!"search [1, 64] in WORKLIST-CERTIFICATION : cStart({request}) =>! W:CReply ."
  let tree ← Lean.ofExcept (completeReply request stdout)
  let images := mkAppN (mkConst ``Substitution.Terms.identity) #[l.sortType, l.signature, Γ]
  let eqs ← mkListLit (← inferType problem) [problem]
  let proof ← decodeComplete l profile problem proposed Γ images eqs tree engine
  check proof
  emitDefinition (pre ++ `completeness) proof
  return { request, output := stdout }

end External

end Replay

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

/- Ordinary DATA, not proof lemmas or macros. The context identifies
   singleton(wait(_)) in the generated registered signature. The manual family
   list/trace are regression fixtures; the main theorem uses FETCHED data. -/
def oneTailContext : Replay.Context Sig Tag.s0 Tag.s2 :=
  .app Symbol.c6 (.focus (.app Symbol.c3 (.focus .hole .nil)) .nil)

def oneTailFamilies : List Replay.Family := [.matched, .crossed]

def oneTailTrace : Replay.Certificate :=
  .coverage (.decompose 0 (.decompose 0 .rigid)) .matched .crossed

-- Actual finite dump: coverage(decompose(0,decompose(0,rigid)),emit(matched),emit(crossed))
#eval oneTailTrace.dump

/- Actual TWO-engine experiment. Native unify receives the ordinary automatically
   exported Bakery signature. The certification engine receives validated native
   answers, not a predefined list or trace. Emitted declarations contain data,
   never a proof. The theorem below kernel-replays that fetched data with rfl.
   The source query explicitly uses the SAME singleton(wait(_)) context as the
   theorem. General query/context reification is not exposed as a user command.
   No production narrowing or core library code is changed by this experiment. -/
run_cmd Lean.Elab.Command.liftTermElabM do
  let sorts ← Maude.collectSignature (Lean.mkConst ``Conf)
  let model := Maude.renderModule sorts (← Maude.inspectTheory (Lean.mkConst ``BakeryTheory))
  let lhs ← Lean.Elab.Term.elabTerm
    (← `(fun (i : Nat) (P : ProcSet) => ProcSet.union (ProcSet.singleton (.wait i)) P)) none
  let rhs ← Lean.Elab.Term.elabTerm
    (← `(fun (j : Nat) (Q : ProcSet) => ProcSet.union (ProcSet.singleton (.wait j)) Q)) none
  let left ← Maude.translatePattern sorts "L" (← Unification.Problem.saturatePattern lhs)
  let right ← Maude.translatePattern sorts "R" (← Unification.Problem.saturatePattern rhs)
  let source := System.FilePath.mk (← Lean.getFileName)
  let engine ← IO.FS.readFile (source.parent.getD (System.FilePath.mk ".") / "certification.maude")
  let context := Replay.External.contextDump profile oneTailContext
  let (nativeOutput, nativeAnswers) ← Replay.External.fetchNative model sorts left right
  Replay.External.emitAnswers `DirectCertification.Bakery.fetched
    (Lean.mkConst ``registration) left right nativeAnswers
  let reference ← Lean.Elab.Term.elabTerm
    (← `(Replay.Reference.exchangeBranches oneTailContext Operator.acu)) none
  let generic ← Replay.External.fetchGeneric `DirectCertification.Bakery.fetched
    (Lean.mkConst ``registration) (Lean.mkConst `DirectCertification.Bakery.fetched.problem)
    reference (Lean.mkConst `DirectCertification.Bakery.fetched.answers) engine
  unless !(Replay.External.genericReply generic.request (generic.output.replace "Bye." "")).isOk do
    throwError "accepted a truncated generic reply"
  unless !(Replay.External.genericReply generic.request (generic.output.replace "gRequest(" "changedRequest(")).isOk do
    throwError "accepted a changed generic request"
  let (sound, cover) ← Lean.ofExcept (Replay.External.genericReply generic.request generic.output)
  let .app "esCons" #[_, soundRest] := sound | throwError "missing generic soundness trace"
  let .app "fsCons" #[.app "factor" #[_, beta, images], coverRest] := cover
    | throwError "missing generic coverage trace"
  let badCases := [
    (Maude.Certification.Node.app "esCons" #[.app "eRefl" #[], soundRest], cover),
    (.app "esCons" #[.app "eHyp" #[.num 0], soundRest], cover),
    (sound, .app "fsCons" #[.app "factor" #[.num 9, beta, images], coverRest]),
    (sound, .app "fsCons" #[.app "factor" #[.num 0, beta, images], coverRest]),
    (sound, .app "fsCons" #[.app "factor" #[.num 1, .app "tsNil" #[], images], coverRest]),
    (sound, .app "fsNil" #[])]
  for (badSound, badCover) in badCases do
    let rejected ← try
      Replay.External.checkGenericData (Lean.mkConst ``registration)
        (Lean.mkConst `DirectCertification.Bakery.fetched.problem) reference
        (Lean.mkConst `DirectCertification.Bakery.fetched.answers) badSound badCover
      pure false
    catch _ => pure true
    unless rejected do throwError "accepted corrupt generic equality/index/β/count data"
  let fetched ← Replay.External.fetchControlFixture engine sorts left right nativeOutput context
  Replay.External.emitControlFixture `DirectCertification.Bakery.fetched fetched
  Lean.logInfo s!"Native families: {fetched.families.map Replay.Family.dump}; fetched trace: {fetched.trace.dump}"

  -- Tamper with actual native bindings, not a toy mock parser input.
  let spec ← Lean.ofExcept (Replay.External.input left right)
  let answers ← Lean.ofExcept (Maude.parseUnifiers sorts spec.variables fetched.nativeOutput)
  let some crossed := answers.toList.find? (fun answer =>
      match Replay.External.recognize spec answer with
      | .ok .crossed => true
      | _ => false) | throwError "native answer did not include the crossed template"
  let some firstBinding := crossed.bindings.toList.head? | throwError "empty native substitution"
  let duplicate := { crossed with bindings := crossed.bindings.push firstBinding }
  unless !(Replay.External.recognize spec duplicate).isOk do
    throwError "accepted a duplicate substitution domain"
  let .variable yName _ := spec.y | throwError "invalid tail variable"
  let altered := { crossed with bindings := crossed.bindings.map fun binding =>
    if binding.domain.maudeName == yName then
      { binding with image := match binding.image with
          | .application f s args => .application f s (args.map fun arg => match arg with
              | .variable _ sort => .variable "#different" sort
              | _ => arg)
          | term => term }
    else binding }
  unless !(Replay.External.recognize spec altered).isOk do
    throwError "accepted crossed images with different remainders"
  unless !(Replay.External.searchReply fetched.request
      (fetched.searchOutput.replace "free(0" "free(1")).isOk do
    throwError "accepted a changed request echo"
  unless !(Replay.External.searchReply fetched.request
      (fetched.searchOutput.replace "Bye." "")).isOk do
    throwError "accepted a truncated certificate reply"
  -- Search must FAIL when a sound but incomplete answer list is supplied.
  let missing := s!"request({context},cons(crossed,nil))"
  let failed ← Maude.runMaude engine
    s!"search [1, 64] in DIRECT-CERTIFICATION : start({missing}) =>! R:Reply ."
  unless !(Replay.External.searchReply missing failed).isOk do
    throwError "certification search regenerated the omitted matched family"

#eval fetched.trace.dump
#guard fetched.families.length == 2
#guard Replay.accepts profile registration oneTailContext Operator.acu fetched.families fetched.trace

/- A REAL Bakery narrowing equation, not just a residual bag equation:

   examples/bakery.lean: (exit next serving rest).lhs against
                        (critical next' serving' rest').term.

   Conf(next, serving, singleton(crit(serving))+P)
      =B Conf(next', serving', singleton(crit(serving'))+Q)

   We use the identical term shapes over the lightweight BakeryACU declarations
   already imported by this prototype; we do not import the safety proofs or
   their sorries. Constraints are deliberately absent: they are attached by
   narrowing, while this certificate is for the unconstrained term equation.

   Native Maude returns TWO families, not just the residual matched one:
   * next=next'=N, serving=serving'=M, P=Q=Z;
   * same counter equations, P=Q=singleton(crit(M))+R (redundant but sound).

   The payload M is shared with the second Conf field, not an independently
   quantified ticket. Both frames and ALL SIX input-variable images are checked.
-/
def criticalHeadContext : Replay.Context Sig Tag.s0 Tag.s2 :=
  .app Symbol.c6 (.focus (.app Symbol.c4 (.focus .hole .nil)) .nil)

run_cmd Lean.Elab.Command.liftTermElabM do
  let sorts ← Maude.collectSignature (Lean.mkConst ``Conf)
  let model := Maude.renderModule sorts (← Maude.inspectTheory (Lean.mkConst ``BakeryTheory))
  let lhs ← Lean.Elab.Term.elabTerm
    (← `(fun (next serving : Nat) (P : ProcSet) =>
      Conf.mk next serving (ProcSet.union (ProcSet.singleton (.crit serving)) P))) none
  let rhs ← Lean.Elab.Term.elabTerm
    (← `(fun (next' serving' : Nat) (Q : ProcSet) =>
      Conf.mk next' serving' (ProcSet.union (ProcSet.singleton (.crit serving')) Q))) none
  let left ← Maude.translatePattern sorts "L" (← Unification.Problem.saturatePattern lhs)
  let right ← Maude.translatePattern sorts "R" (← Unification.Problem.saturatePattern rhs)
  let source := System.FilePath.mk (← Lean.getFileName)
  let engine ← IO.FS.readFile (source.parent.getD (System.FilePath.mk ".") / "certification.maude")
  let context := Replay.External.contextDump profile criticalHeadContext
  let (nativeOutput, nativeAnswers) ← Replay.External.fetchNative model sorts left right
  Replay.External.emitAnswers `DirectCertification.Bakery.fetchedExitCritical
    (Lean.mkConst ``registration) left right nativeAnswers
  let _ ← Replay.External.fetchGeneric `DirectCertification.Bakery.fetchedExitCritical
    (Lean.mkConst ``registration) (Lean.mkConst `DirectCertification.Bakery.fetchedExitCritical.problem)
    (Lean.mkConst `DirectCertification.Bakery.fetchedExitCritical.answers)
    (Lean.mkConst `DirectCertification.Bakery.fetchedExitCritical.answers) engine
  -- This request needs a genuine nonidentity β: crossed source tail maps to
  -- the matched target's free process parameter. No family tag is transmitted.
  -- This declaration was just emitted, so resolve its Name directly rather
  -- than capturing a not-yet-existing identifier in a hygienic quotation.
  let index ← Lean.Elab.Term.elabTerm (← `((⟨1, of_decide_eq_true rfl⟩ : Fin 2))) none
  let matched ← Lean.Meta.mkAppM ``List.get
    #[Lean.mkConst `DirectCertification.Bakery.fetchedExitCritical.answers, index]
  let matchedOnly ← Lean.Meta.mkListLit (← Lean.Meta.inferType matched) [matched]
  let _ ← Replay.External.fetchGeneric `DirectCertification.Bakery.exitDominance
    (Lean.mkConst ``registration) (Lean.mkConst `DirectCertification.Bakery.fetchedExitCritical.problem)
    (Lean.mkConst `DirectCertification.Bakery.fetchedExitCritical.answers) matchedOnly engine
  let result ← Replay.External.fetchControlFixture engine sorts left right nativeOutput context true
  Replay.External.emitControlFixture `DirectCertification.Bakery.fetchedExitCritical result
  Lean.logInfo s!"Exit/critical native query: {left.term.render} =? {right.term.render}"
  Lean.logInfo s!"Native families: {result.families.map Replay.Family.dump}; fetched trace: {result.trace.dump}"

  -- Tamper tests on the REAL six-variable native answer, not toy data.
  let spec ← Lean.ofExcept (Replay.External.framedInput left right)
  let answers ← Lean.ofExcept (Maude.parseUnifiers sorts spec.variables result.nativeOutput)
  let some answer := answers.toList.head? | throwError "no native framed answer"
  let some (next, _) := spec.counterPair? | throwError "no framed counter pair"
  let .variable nextName _ := next | throwError "invalid framed counter variable"
  let .variable servingName _ := spec.a | throwError "invalid framed serving variable"
  let some servingBinding := answer.bindings.toList.find? (·.domain.maudeName == servingName)
    | throwError "no native serving image"
  let collapsed := { answer with bindings := answer.bindings.map fun binding =>
    if binding.domain.maudeName == nextName then { binding with image := servingBinding.image }
    else binding }
  unless !(Replay.External.recognize spec collapsed).isOk do
    throwError "accepted a next/serving correlation absent from the query"
  let .variable rightServingName _ := spec.b | throwError "invalid right serving variable"
  let broken := { answer with bindings := answer.bindings.map fun binding =>
    if binding.domain.maudeName == rightServingName then
      { binding with image := .variable "#unshared" binding.domain.sort }
    else binding }
  unless !(Replay.External.recognize spec broken).isOk do
    throwError "accepted unshared serving-field/payload images"

#eval fetchedExitCritical.trace.dump
#guard fetchedExitCritical.families.length == 2
#guard Replay.acceptsFrame profile registration Symbol.c8 criticalHeadContext Operator.acu
  fetchedExitCritical.families fetchedExitCritical.trace

-- Unlike the independent-head problem, the redundant crossed family may be
-- omitted here. Cancellation covers ALL shared-head solutions by matched alone.
#guard Replay.acceptsFrame profile registration Symbol.c8 criticalHeadContext Operator.acu
  [.matched] fetchedExitCritical.trace
#guard !(Replay.acceptsFrame profile registration Symbol.c8 criticalHeadContext Operator.acu
  [.crossed] fetchedExitCritical.trace)
#guard !(Replay.acceptsFrame profile registration Symbol.c8 criticalHeadContext Operator.acu
  fetchedExitCritical.families (.frameCancel (.decompose 0 .rigid) .rigid (.cancellation .matched)))

/- Two further equations from the Bakery narrowing term shapes. The shared
   frame identifies serving counters; wait/crit and idle/crit then CLASH.
   Native Maude supplies just the crossed family in each case. These typed
   contexts are prototype reification data, not semantic registration proofs.
   No claim of a general term-to-context translator is made here. -/
def enterCriticalHeads : Replay.HeadPair Sig Tag.s0 Tag.s1 Tag.s2 where
  outer := .app Symbol.c6 (.focus .hole .nil)
  left := .unary Symbol.c3
  right := .unary Symbol.c4

def wakeCriticalHeads : Replay.HeadPair Sig Tag.s0 Tag.s1 Tag.s2 where
  outer := .app Symbol.c6 (.focus .hole .nil)
  left := .fixed (.app Symbol.c2 .nil)
  right := .unary Symbol.c4

run_cmd Lean.Elab.Command.liftTermElabM do
  let sorts ← Maude.collectSignature (Lean.mkConst ``Conf)
  let model := Maude.renderModule sorts (← Maude.inspectTheory (Lean.mkConst ``BakeryTheory))
  let critical ← `(fun (next' serving' : Nat) (Q : ProcSet) =>
    Conf.mk next' serving' (ProcSet.union (ProcSet.singleton (.crit serving')) Q))
  let jobs := [
    ((← `(fun (next serving : Nat) (P : ProcSet) =>
      Conf.mk next serving (ProcSet.union (ProcSet.singleton (.wait serving)) P))),
      enterCriticalHeads, `DirectCertification.Bakery.fetchedEnterCritical),
    ((← `(fun (next serving : Nat) (P : ProcSet) =>
      Conf.mk next serving (ProcSet.union (ProcSet.singleton Mode.idle) P))),
      wakeCriticalHeads, `DirectCertification.Bakery.fetchedWakeCritical)]
  let source := System.FilePath.mk (← Lean.getFileName)
  let engine ← IO.FS.readFile (source.parent.getD (System.FilePath.mk ".") / "certification.maude")
  for (lhsSyntax, heads, pre) in jobs do
    let lhs ← Lean.Elab.Term.elabTerm lhsSyntax none
    let rhs ← Lean.Elab.Term.elabTerm critical none
    let left ← Maude.translatePattern sorts "L" (← Unification.Problem.saturatePattern lhs)
    let right ← Maude.translatePattern sorts "R" (← Unification.Problem.saturatePattern rhs)
    let context := Replay.External.contextDump profile heads.outer
    let (nativeOutput, nativeAnswers) ← Replay.External.fetchNative model sorts left right
    Replay.External.emitAnswers pre (Lean.mkConst ``registration) left right nativeAnswers
    let _ ← Replay.External.fetchGeneric pre (Lean.mkConst ``registration)
      (Lean.mkConst (pre ++ `problem)) (Lean.mkConst (pre ++ `answers)) (Lean.mkConst (pre ++ `answers)) engine
    let result ← Replay.External.fetchControlFixture engine sorts left right nativeOutput context true
      (some (heads.left.code profile, heads.right.code profile))
    Replay.External.emitControlFixture pre result
    Lean.logInfo s!"{pre}: {left.term.render} =? {right.term.render}"
    Lean.logInfo s!"Native families: {result.families.map Replay.Family.dump}; fetched trace: {result.trace.dump}"
    -- An oriented crossed answer must not be accepted with its tails swapped.
    let spec ← Lean.ofExcept (Replay.External.framedInput left right true)
    let answers ← Lean.ofExcept (Maude.parseUnifiers sorts spec.variables result.nativeOutput)
    let some answer := answers.toList.head? | throwError "no native clash answer"
    let .variable xName _ := spec.x | throwError "invalid left tail variable"
    let .variable yName _ := spec.y | throwError "invalid right tail variable"
    let some x := answer.bindings.toList.find? (·.domain.maudeName == xName)
      | throwError "no left tail image"
    let some y := answer.bindings.toList.find? (·.domain.maudeName == yName)
      | throwError "no right tail image"
    let swapped := { answer with bindings := answer.bindings.map fun binding =>
      if binding.domain.maudeName == xName then { binding with image := y.image }
      else if binding.domain.maudeName == yName then { binding with image := x.image }
      else binding }
    unless !(Replay.External.recognize spec swapped).isOk do
      throwError "accepted reversed crossed substitution images"

#guard fetchedEnterCritical.families == [.crossed]
#guard fetchedWakeCritical.families == [.crossed]
#guard Replay.acceptsFrameClash profile registration Symbol.c8 enterCriticalHeads Operator.acu
  fetchedEnterCritical.families fetchedEnterCritical.trace
#guard Replay.acceptsFrameClash profile registration Symbol.c8 wakeCriticalHeads Operator.acu
  fetchedWakeCritical.families fetchedWakeCritical.trace
#guard !(Replay.acceptsFrameClash profile registration Symbol.c8 enterCriticalHeads Operator.acu
  [] fetchedEnterCritical.trace)
#guard !(Replay.acceptsFrameClash profile registration Symbol.c8 enterCriticalHeads Operator.acu
  [.crossed, .matched] fetchedEnterCritical.trace)
#guard !(Replay.acceptsFrameClash profile registration Symbol.c8 enterCriticalHeads Operator.acu
  [.crossed] (.frameClash .rigid .rigid (.decompose 1 .clash) .crossed))
#guard !(Replay.acceptsFrameClash profile registration Symbol.c8
  { enterCriticalHeads with right := .unary Symbol.c3 } Operator.acu
  [.crossed] fetchedEnterCritical.trace)

/- This query is OUTSIDE the legacy matched/crossed recognizer. General export
   preserves Maude's actual four fresh parameters and every union image. -/
run_cmd Lean.Elab.Command.liftTermElabM do
  let sorts ← Maude.collectSignature (Lean.mkConst ``Conf)
  let model := Maude.renderModule sorts (← Maude.inspectTheory (Lean.mkConst ``BakeryTheory))
  let lhs ← Lean.Elab.Term.elabTerm (← `(fun (X Y : ProcSet) => ProcSet.union X Y)) none
  let rhs ← Lean.Elab.Term.elabTerm (← `(fun (A R : ProcSet) => ProcSet.union A R)) none
  let left ← Maude.translatePattern sorts "L" (← Unification.Problem.saturatePattern lhs)
  let right ← Maude.translatePattern sorts "R" (← Unification.Problem.saturatePattern rhs)
  let (_, answers) ← Replay.External.fetchNative model sorts left right
  Replay.External.emitAnswers `DirectCertification.Bakery.fetchedMutation
    (Lean.mkConst ``registration) left right answers
  let source := System.FilePath.mk (← Lean.getFileName)
  let engine ← IO.FS.readFile (source.parent.getD (System.FilePath.mk ".") / "certification.maude")
  let reference ← Lean.Elab.Term.elabTerm
    (← `([Replay.Reference.mutationAnswer (sig := Sig) Operator.acu])) none
  let _ ← Replay.External.fetchGeneric `DirectCertification.Bakery.fetchedMutation
    (Lean.mkConst ``registration) (Lean.mkConst `DirectCertification.Bakery.fetchedMutation.problem)
    reference (Lean.mkConst `DirectCertification.Bakery.fetchedMutation.answers) engine
  Lean.logInfo s!"Four-variable native query produced {answers.size} answer(s)."

#guard fetchedMutation.answers.length == 1
#guard (fetchedMutation.answers.get ⟨0, of_decide_eq_true rfl⟩).parameters.length == 4

/- Native matching regression: the whole vector
     [idle + Z, Z] <=? [B + (idle + C), B + C]
   needs associative regrouping, not just binary swaps. Both coordinates must
   share the SAME β(Z) = B+C. Changing the second coordinate to B+B must fail.
   This is a factorization test, NOT a claim that these branches are complete.
-/
run_cmd Lean.Elab.Command.liftTermElabM do
  let problem ← Lean.Elab.Term.elabTerm
    (← `(({ sort := Tag.s2, left := .var .here, right := .var .here } :
      Substitution.Problem Sig [Tag.s2, Tag.s2]))) none
  let proposed ← Lean.Elab.Term.elabTerm
    (← `(([{
      parameters := [Tag.s2]
      images := .cons
        (Substitution.add Operator.acu
          (.app Symbol.c6 (.cons (.app Symbol.c2 .nil) .nil)) (.var .here))
        (.cons (.var .here) .nil)
    }] : List (Substitution.Answer Sig [Tag.s2, Tag.s2])))) none
  let reference ← Lean.Elab.Term.elabTerm
    (← `(([{
      parameters := [Tag.s2, Tag.s2]
      images := .cons
        (Substitution.add Operator.acu (.var .here)
          (Substitution.add Operator.acu
            (.app Symbol.c6 (.cons (.app Symbol.c2 .nil) .nil)) (.var (.there .here))))
        (.cons (Substitution.add Operator.acu (.var .here) (.var (.there .here))) .nil)
    }] : List (Substitution.Answer Sig [Tag.s2, Tag.s2])))) none
  let source := System.FilePath.mk (← Lean.getFileName)
  let engine ← IO.FS.readFile (source.parent.getD (System.FilePath.mk ".") / "certification.maude")
  let _ ← Replay.External.fetchGeneric `DirectCertification.Bakery.regrouping
    (Lean.mkConst ``registration) problem reference proposed engine
  let incoherent ← Lean.Elab.Term.elabTerm
    (← `(([{
      parameters := [Tag.s2, Tag.s2]
      images := .cons
        (Substitution.add Operator.acu (.var .here)
          (Substitution.add Operator.acu
            (.app Symbol.c6 (.cons (.app Symbol.c2 .nil) .nil)) (.var (.there .here))))
        (.cons (Substitution.add Operator.acu (.var .here) (.var .here)) .nil)
    }] : List (Substitution.Answer Sig [Tag.s2, Tag.s2])))) none
  let rejected ← try
    let _ ← Replay.External.fetchGeneric `DirectCertification.Bakery.incoherent
      (Lean.mkConst ``registration) problem incoherent proposed engine
    pure false
  catch _ => pure true
  unless rejected do throwError "native matching lost shared-variable correlations"

/- A genuinely NONLINEAR problem: X occurs twice in the same ACU sum.
   Native unify returns X=idle+Z, Y=idle+(Z+Z). Nothing compacts this into a
   preselected family. Generic Maude replay proves soundness of the actual
   answer; a separate object-level search emits the full general Mutate/Split
   completeness tree. Neither direction contains handwritten problem reasoning.
   An empty reference in fetchGeneric requests SOUNDNESS ONLY; fetchComplete
   supplies the independent checked completeness tree.
-/
run_cmd Lean.Elab.Command.liftTermElabM do
  let sorts ← Maude.collectSignature (Lean.mkConst ``Conf)
  let model := Maude.renderModule sorts (← Maude.inspectTheory (Lean.mkConst ``BakeryTheory))
  let lhs ← Lean.Elab.Term.elabTerm (← `(fun (X : ProcSet) => ProcSet.union X X)) none
  let rhs ← Lean.Elab.Term.elabTerm
    (← `(fun (Y : ProcSet) => ProcSet.union (ProcSet.singleton Mode.idle) Y)) none
  let left ← Maude.translatePattern sorts "L" (← Unification.Problem.saturatePattern lhs)
  let right ← Maude.translatePattern sorts "R" (← Unification.Problem.saturatePattern rhs)
  let (_, answers) ← Replay.External.fetchNative model sorts left right
  Replay.External.emitAnswers `DirectCertification.Bakery.fetchedNonlinear
    (Lean.mkConst ``registration) left right answers
  let proposed := Lean.mkConst `DirectCertification.Bakery.fetchedNonlinear.answers
  let answerType := (← Lean.Meta.inferType proposed).getAppArgs.back!
  let source := System.FilePath.mk (← Lean.getFileName)
  let engine ← IO.FS.readFile (source.parent.getD (System.FilePath.mk ".") / "certification.maude")
  let _ ← Replay.External.fetchGeneric `DirectCertification.Bakery.fetchedNonlinear
    (Lean.mkConst ``registration) (Lean.mkConst `DirectCertification.Bakery.fetchedNonlinear.problem)
    (← Lean.Meta.mkListLit answerType []) proposed engine
  let problem := Lean.mkConst `DirectCertification.Bakery.fetchedNonlinear.problem
  let complete ← Replay.External.fetchComplete `DirectCertification.Bakery.fetchedNonlinear
    (Lean.mkConst ``registration) (Lean.mkConst ``profile) problem proposed engine
  unless !(Replay.External.completeReply complete.request (complete.output.replace "Bye." "")).isOk do
    throwError "accepted truncated completeness tree output"
  unless !(Replay.External.completeReply complete.request
      (complete.output.replace "cRequest(" "changedRequest(")).isOk do
    throwError "accepted changed completeness request"
  let tree ← Lean.ofExcept (Replay.External.completeReply complete.request complete.output)
  let .app "cMutate" #[op, a, b, c, d, selected, child] := tree
    | throwError "nonlinear certificate did not contain Mutate"
  let .app "cSplit" #[splitOp, x, y, atom, splitProof, leftChild, rightChild] := child
    | throwError "nonlinear certificate did not contain BOTH Split branches"
  let corrupted := [
    Maude.Certification.Node.app "cMutate" #[op, a, b, c, d, .app "eHyp" #[.num 99], child],
    .app "cMutate" #[op, a, c, c, d, selected, child],
    .app "cMutate" #[op, a, b, c, d, selected,
      .app "cSplit" #[splitOp, x, y, atom, splitProof, leftChild]],
    .app "cMutate" #[op, a, b, c, d, selected,
      .app "cSplit" #[splitOp, x, y, atom, splitProof, rightChild, rightChild]]]
  for bad in corrupted do
    let rejected ← try
      Replay.External.checkCompleteData (Lean.mkConst ``registration) (Lean.mkConst ``profile)
        problem proposed bad engine
      pure false
    catch _ => pure true
    unless rejected do throwError "accepted corrupt hypothesis, sharing, or Split branch in completeness tree"
  let missingRejected ← try
    let _ ← Replay.External.fetchComplete `DirectCertification.Bakery.missingNonlinear
      (Lean.mkConst ``registration) (Lean.mkConst ``profile) problem
      (← Lean.Meta.mkListLit answerType []) engine
    pure false
  catch _ => pure true
  unless missingRejected do throwError "completeness tree accepted an empty proposed answer set"
  Lean.logInfo s!"Nonlinear native query produced {answers.size} answer(s)."

#guard fetchedNonlinear.answers.length == 1
#guard (fetchedNonlinear.answers.get ⟨0, of_decide_eq_true rfl⟩).parameters.length == 1

-- Replay the primitive UNIT rule as well as the Assoc/Comm/Congruence steps
-- exercised above. This is typed signature data, not a Bakery-specific rule.
run_cmd Lean.Elab.Command.liftTermElabM do
  let problem ← Lean.Elab.Term.elabTerm
    (← `(({
      sort := Tag.s2
      left := Substitution.add Operator.acu (Substitution.zero Operator.acu) (.var .here)
      right := .var .here
    } : Substitution.Problem Sig [Tag.s2]))) none
  let answers ← Lean.Elab.Term.elabTerm
    (← `(([{ parameters := [Tag.s2], images := Substitution.Terms.identity [Tag.s2] }] :
      List (Substitution.Answer Sig [Tag.s2])))) none
  let source := System.FilePath.mk (← Lean.getFileName)
  let engine ← IO.FS.readFile (source.parent.getD (System.FilePath.mk ".") / "certification.maude")
  let result ← Replay.External.fetchGeneric `DirectCertification.Bakery.unitReplay
    (Lean.mkConst ``registration) problem answers answers engine
  -- Search itself must fail on a missing answer (not just reject its parser).
  let answerType ← Lean.Elab.Term.elabTerm (← `(Substitution.Answer Sig [Tag.s2])) none
  let missing ← Replay.External.dumpGeneric (Lean.mkConst ``registration)
    problem answers (← Lean.Meta.mkListLit answerType [])
  let failed ← Maude.runMaude engine
    s!"search [1, 64] in GENERIC-CERTIFICATION : gStart({missing}) =>! G:GenericReply ."
  unless !(Replay.External.genericReply missing failed).isOk do
    throwError "generic search accepted missing required answer"
  unless (Replay.External.genericReply result.request result.output).isOk do
    throwError "generic search rejected the unit certificate"

/- Checker regression tests, not helper lemmas for the certification proof.
   None of these checks is relied on as an oracle: replay_exact is proved above
   and the actual certificate below supplies kernel-checked acceptance by rfl.
-/

-- Correct trace; answer order and duplicate entries do not change the set.
#guard Replay.accepts profile registration oneTailContext Operator.acu
  [.crossed, .matched, .crossed] oneTailTrace

-- Reject an omitted family, even though each remaining family is sound.
#guard !(Replay.accepts profile registration oneTailContext Operator.acu [.crossed] oneTailTrace)
#guard !(Replay.accepts profile registration oneTailContext Operator.acu [.matched] oneTailTrace)

-- Reject the crossed family as a claimed cover of the equal-head minimal case.
#guard !(Replay.accepts profile registration oneTailContext Operator.acu oneTailFamilies
  (.coverage (.decompose 0 (.decompose 0 .rigid)) .crossed .crossed))

-- Reject a wrong argument position or an incomplete decomposition path.
#guard !(Replay.accepts profile registration oneTailContext Operator.acu oneTailFamilies
  (.coverage (.decompose 1 (.decompose 0 .rigid)) .matched .crossed))
#guard !(Replay.accepts profile registration oneTailContext Operator.acu oneTailFamilies
  (.coverage (.decompose 0 .rigid) .matched .crossed))

-- Positive arbitrary-arity test: the hole is Conf's SECOND field, not a unary
-- constructor chain or argument 0. The other native fields remain fixed.
#guard (Replay.replayHead profile registration
  (.app Symbol.c8 (.before (.app Symbol.c0 .nil)
    (.focus .hole (.cons (zero Sig Operator.acu) .nil))) : Replay.Context Sig Tag.s0 Tag.s3)
  (.decompose 1 .rigid)).isSome

-- A bare bag variable is not an explicit atom; its four-piece refinement is
-- outside this two-template replay format and must not be accepted.
#guard !(Replay.accepts profile registration
  (Replay.Context.hole : Replay.Context Sig Tag.s2 Tag.s2) Operator.acu oneTailFamilies
  (.coverage .rigid .matched .crossed))

-- Decomposing a free Conf head is valid, but reflecting its BAG hole to literal
-- equality is not. This tests the generated sort boundary inside replay itself.
#guard !((Replay.replayHead profile registration
  (.app Symbol.c8 (.before (.app Symbol.c0 .nil)
    (.before (.app Symbol.c0 .nil) (.focus .hole .nil))) : Replay.Context Sig Tag.s2 Tag.s3)
  (.decompose 2 .rigid)).isSome)

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

/- Proposed families for ONE equation:

     singleton(wait(i)) + P =B singleton(wait(j)) + Q

   matched: i=K, j=K, P=B Z, Q=B Z
   crossed: P=singleton(wait(j))+N, Q=singleton(wait(i))+N

   The fetched DATA trace says:
     decompose argument 0 of singleton
     decompose argument 0 of wait
     rigid equality on the resulting Nat hole
     cover equal heads by the matched template
     cover unequal heads by the crossed template

   Kernel replay checks these steps against oneTailContext, the generated
   profile, and the ENTIRE independently proposed fetched.families list. It
   checks root atomicity and shared-variable correlations too. No rule runs
   Mutate/Split to rediscover the families. All semantic reasoning is in the
   GENERAL metatheorems, not Bakery-specific helpers or user registration.
-/
theorem one_tail_certificate (i j : Nat) (P Q : ProcSet) :
    ProcSet.union (ProcSet.singleton (.wait i)) P =[BakeryTheory.certified]
      ProcSet.union (ProcSet.singleton (.wait j)) Q ↔
      (∃ K : Nat, ∃ Z : ProcSet,
        i = K ∧ j = K ∧ P =[BakeryTheory.certified] Z ∧ Q =[BakeryTheory.certified] Z) ∨
      (∃ N : ProcSet,
        P =[BakeryTheory.certified] ProcSet.union (ProcSet.singleton (.wait j)) N ∧
        Q =[BakeryTheory.certified] ProcSet.union (ProcSet.singleton (.wait i)) N) :=
  (Replay.replay_exact profile registration oneTailContext Operator.acu
    fetched.families fetched.trace rfl i j P Q).trans
      -- Present the entire accepted answer list as its named disjunction.
      (Replay.solutions_iff registration oneTailContext Operator.acu fetched.families
        (of_decide_eq_true rfl) (of_decide_eq_true rfl) i j P Q)

/- Full exit/critical unification certificate. This one proof term is the replay
   of the fetched FrameCancel rule followed by the GENERAL presentation rule.
   .mp is completeness; .mpr is soundness. No local helper lemma, tactic,
   feasibility reasoning or narrowing modification is involved. -/
theorem exit_critical_certificate (next serving next' serving' : Nat) (P Q : ProcSet) :
    Conf.mk next serving (ProcSet.union (ProcSet.singleton (.crit serving)) P)
      =[BakeryTheory.certified]
    Conf.mk next' serving' (ProcSet.union (ProcSet.singleton (.crit serving')) Q) ↔
      (∃ N M : Nat, ∃ Z : ProcSet,
        next = N ∧ next' = N ∧ serving = M ∧ serving' = M ∧
        P =[BakeryTheory.certified] Z ∧ Q =[BakeryTheory.certified] Z) ∨
      (∃ N M : Nat, ∃ R : ProcSet,
        next = N ∧ next' = N ∧ serving = M ∧ serving' = M ∧
        P =[BakeryTheory.certified] ProcSet.union (ProcSet.singleton (.crit M)) R ∧
        Q =[BakeryTheory.certified] ProcSet.union (ProcSet.singleton (.crit M)) R) :=
  (Replay.replay_frame_exact profile registration Symbol.c8 criticalHeadContext Operator.acu
    fetchedExitCritical.families fetchedExitCritical.trace rfl next next' serving serving' P Q).trans
      (Replay.frame_solutions_iff registration (u := Tag.s0) criticalHeadContext Operator.acu
        fetchedExitCritical.families (of_decide_eq_true rfl) (of_decide_eq_true rfl)
        next next' serving serving' P Q)

/- Full input equations, NOT residual bag equations. Inference trace:
     Decompose Conf; Rigid next; Rigid serving;
     Decompose singleton at position 0; Clash wait/crit (or idle/crit);
     Exchange; Emit the proposed crossed substitution.
   Replay of these GENERAL rules proves the displayed semantic iff:
   .mp certifies completeness and .mpr certifies soundness. The proof term
   contains no Bakery helper lemma, tactic, or trusted Maude assertion. -/
theorem enter_critical_certificate (next serving next' serving' : Nat) (P Q : ProcSet) :
    Conf.mk next serving (ProcSet.union (ProcSet.singleton (.wait serving)) P)
      =[BakeryTheory.certified]
    Conf.mk next' serving' (ProcSet.union (ProcSet.singleton (.crit serving')) Q) ↔
      ∃ N M : Nat, ∃ R : ProcSet,
        next = N ∧ next' = N ∧ serving = M ∧ serving' = M ∧
        P =[BakeryTheory.certified] ProcSet.union (ProcSet.singleton (.crit M)) R ∧
        Q =[BakeryTheory.certified] ProcSet.union (ProcSet.singleton (.wait M)) R :=
  Replay.replay_frame_clash_exact profile registration Symbol.c8 enterCriticalHeads Operator.acu
    fetchedEnterCritical.families fetchedEnterCritical.trace rfl next next' serving serving' P Q

theorem wake_critical_certificate (next serving next' serving' : Nat) (P Q : ProcSet) :
    Conf.mk next serving (ProcSet.union (ProcSet.singleton Mode.idle) P)
      =[BakeryTheory.certified]
    Conf.mk next' serving' (ProcSet.union (ProcSet.singleton (.crit serving')) Q) ↔
      ∃ N M : Nat, ∃ R : ProcSet,
        next = N ∧ next' = N ∧ serving = M ∧ serving' = M ∧
        P =[BakeryTheory.certified] ProcSet.union (ProcSet.singleton (.crit M)) R ∧
        Q =[BakeryTheory.certified] ProcSet.union (ProcSet.singleton Mode.idle) R :=
  Replay.replay_frame_clash_exact profile registration Symbol.c8 wakeCriticalHeads Operator.acu
    fetchedWakeCritical.families fetchedWakeCritical.trace rfl next next' serving serving' P Q

/- The two ACTUAL native substitutions, without replacing them by family tags.
   Reference Exchange emits matched then crossed. Native Maude emits crossed
   then matched, so Factor selects answer indices 1 then 0. Each β is identity
   here, and ALL input images are checked by the generic Equalities.refl rule.

   Soundness checks the actual substituted equation for BOTH proposals, using
   primitive Assoc/Comm/Congruence traces GENERATED BY MAUDE.
   Completeness combines the general Exchange metatheorem and those two Factor
   leaves. The proof is an ordinary term; no tactic/semantic user bridge/hole.
   Native matching supplies indices/β; object-level Maude emits equality steps.
   The theorem supplies reference completeness, never an external success flag.
-/
theorem one_tail_native_certificate :
    ∀ values, fetched.problem.Holds registration values ↔
      Substitution.Solutions registration fetched.answers values :=
  Substitution.exact_of_coverage registration fetched.problem
    (Replay.Reference.exchangeBranches oneTailContext Operator.acu) fetched.answers
    (Replay.Reference.exchange_complete profile registration oneTailContext Operator.acu
      ((Replay.replayHead profile registration oneTailContext
        (.decompose 0 (.decompose 0 .rigid))).get (of_decide_eq_true rfl)).down
      ((Replay.atomic profile registration oneTailContext).get (of_decide_eq_true rfl)).down)
    fetched.soundness fetched.coverage

-- The same general soundness-data constructors check the full framed answers.
-- There is no special soundness rule for exit, enter, wake, Conf, or ProcSet.
example : Substitution.Soundness fetchedExitCritical.problem fetchedExitCritical.answers :=
  fetchedExitCritical.soundness

example : Substitution.Soundness fetchedEnterCritical.problem fetchedEnterCritical.answers :=
  fetchedEnterCritical.soundness

example : Substitution.Soundness fetchedWakeCritical.problem fetchedWakeCritical.answers :=
  fetchedWakeCritical.soundness

/- A NON-IDENTITY factorization, now FOUND AND DUMPED BY MAUDE: native exit's
   redundant crossed answer (0) is an instance of its matched answer (1).
   β maps the target's process parameter to the source's WHOLE process image.
   This coverage alone does not assert that the reference is complete. -/
example : Substitution.Coverage
    [fetchedExitCritical.answers.get ⟨1, of_decide_eq_true rfl⟩]
    fetchedExitCritical.answers := exitDominance.coverage

/- A further native problem that the old two-template recognizer cannot accept:
     X+Y =B A+R.
   Mutate supplies one complete reference branch with FOUR fresh bags.
   Native Maude supplies its actual answer, preserved by the general exporter.
   The same soundness and answer-indexed Factor rules certify it; no extension
   of the family-tag parser or new semantic proof rule is required. -/
theorem mutation_native_certificate :
    ∀ values, fetchedMutation.problem.Holds registration values ↔
      Substitution.Solutions registration fetchedMutation.answers values :=
  Substitution.exact_of_coverage registration fetchedMutation.problem
    [Replay.Reference.mutationAnswer Operator.acu] fetchedMutation.answers
    (Replay.Reference.mutation_complete profile registration Operator.acu)
    fetchedMutation.soundness fetchedMutation.coverage

/- NONLINEAR completeness, with no problem-specific lemma or reference family.

   General rule trace (the same X is retained in BOTH residual equations):
     Mutate(X+X = a+Y)
       X = P+Q, X = R+T, a = P+R, Y = Q+T
     SplitAtom(P+R = a)
       branch 1: P=0, R=a  -> X=a+T, Y=a+(T+T) -> Emit Z=T
       branch 2: P=a, R=0  -> X=a+Q, Y=a+(Q+Q) -> Emit Z=Q

   Thus sharing is an equation to preserve, NOT a reason to treat occurrences
   as independent variables. Both branches are covered by the actual native
   answer. The ENTIRE tree above, including the equality consequences and both
   closing factors, comes from Maude and is checked by general kernel replay.
   The user proof below is only the general exactness metatheorem applied to
   those finite data. No problem-specific lemma or handwritten branch remains.

   Control is still a bounded pilot (one root Mutate, at most one Split). The
   general proof rules support arbitrary shared terms and recursive trees;
   this is NOT yet an automatic certifier for all ACU equations.
-/
theorem nonlinear_native_certificate :
    ∀ values, fetchedNonlinear.problem.Holds registration values ↔
      Substitution.Solutions registration fetchedNonlinear.answers values :=
  Substitution.Worklist.exact registration fetchedNonlinear.problem fetchedNonlinear.answers
    fetchedNonlinear.completeness fetchedNonlinear.soundness

/- Decompose also works when a free constructor contains NON-rigid payloads.
   Conf is not rigid: its process-field equality must stay modulo ACU.
   This is a regression against incorrectly replacing every free-head equality
   by literal Lean equality. All three fields use the SAME generic rule.
-/
theorem acu_payload_certificate (n serving : Nat) (P Q : ProcSet) :
    Conf.mk n serving P =[BakeryTheory.certified] Conf.mk n serving Q ↔
      P =[BakeryTheory.certified] Q :=
  let fields := decompose_native profile registration Symbol.c8 rfl
    (n, serving, P, PUnit.unit) (n, serving, Q, PUnit.unit)
  Iff.intro (fun input => (fields.mp input).2.2.1)
    (fun input => fields.mpr ⟨.refl _, .refl _, input, True.intro⟩)

/- Clash certificate: axioms for bags cannot identify distinct Mode heads.
   The sort-indexed constructor tags distinguish wait/crit independently of
   their arbitrary ticket payloads. `nomatch` checks distinct generated tags;
   it is not a Bakery-specific semantic theorem or a search tactic.
-/
theorem head_clash_certificate (i j : Nat) :
    ¬ (Mode.wait i =[BakeryTheory.certified] Mode.crit j) :=
  clash_native profile registration Symbol.c3 Symbol.c4 rfl rfl
    (fun same => nomatch (eq_of_heq (Sigma.mk.inj same).2))
    (i, PUnit.unit) (j, PUnit.unit)

/- Negative test: omitting the matched family is genuinely INCOMPLETE.
   The crossed family is sound, but misses the minimal solution P=Q=empty.
   Even though it has an arbitrary N, it cannot absorb the absent head.
   This proof uses the NECESSITY direction of Coverage, not a special-case
   analysis of Bakery constructors or a hand-written counterexample lemma.
-/
theorem missing_matched_rejected (n : Nat) :
    ¬ (∀ P Q : ProcSet,
      ProcSet.union (ProcSet.singleton (.wait n)) P =[BakeryTheory.certified]
        ProcSet.union (ProcSet.singleton (.wait n)) Q →
      ∃ N : ProcSet,
        P =[BakeryTheory.certified] ProcSet.union (ProcSet.singleton (.wait n)) N ∧
        Q =[BakeryTheory.certified] ProcSet.union (ProcSet.singleton (.wait n)) N) :=
  fun proposed =>
    ((coverage_iff profile registration Operator.acu
      (ProcSet.singleton (.wait n)) (ProcSet.singleton (.wait n))
      False True rfl rfl).mp
        (fun P Q input => Or.inr ⟨True.intro, proposed P Q input⟩)).1
      (.refl _)

-- Axiom audits should report only Lean's standard axioms, never sorryAx.
#print axioms one_tail_native_certificate
#print axioms mutation_native_certificate
#print axioms nonlinear_native_certificate
#print axioms Substitution.Worklist.Complete.sound
#print axioms Substitution.Coverage.sound
#print axioms Substitution.Soundness.sound
#print axioms atomic_certificate
#print axioms refinement_certificate
#print axioms one_tail_certificate
#print axioms exit_critical_certificate
#print axioms enter_critical_certificate
#print axioms wake_critical_certificate
#print axioms acu_payload_certificate
#print axioms head_clash_certificate
#print axioms missing_matched_rejected
#print axioms coverage_iff
#print axioms Replay.replay_exact
#print axioms Replay.replay_frame_exact
#print axioms Replay.replay_frame_clash_exact

end DirectCertification.Bakery
