import examples.bakery_acu

/-!
# Direct, rule-based unification certificates

This file contains four clearly separated parts:
1. GENERAL METATHEOREMS: correctness of the rules for any registered signature.
2. SYNTACTIC METADATA: constructor classification, generated without user proofs.
3. REPLAY: finite certificate data, dump format, and kernel-checked acceptance.
4. CERTIFICATES: ordinary, tactic-free proof terms over Bakery's own datatypes.

The current milestone is answer-directed certification of ONE explicit atom
and ONE bag tail per side. The generic coverage theorem below reduces an
unbounded bag obligation to two head-equality guards. It does not recompute a
complete set of ACU unifiers. Finite dump/replay now supports the one-hole
atom-context fragment. Native Maude answers now guide object-level certificate
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
The external boundary accepts ONLY the two exact canonical substitution shapes,
up to parameter renaming and the order of the two ACU summands. It rejects all
other bindings. This is a restricted experiment, not production narrowing.
The only trusted proof step is the kernel's replay_exact, applied to fetched DATA.
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
  let source := "def " ++ name.getId.toString ++
    " : DirectCertification.Profile " ++ signature ++ " where\n" ++
    "  view := fun f => match f with\n" ++ String.intercalate "\n" branches ++
    "\n  view_zero := by intro s op; cases op <;> rfl" ++
    "\n  view_add := by intro s op; cases op <;> rfl" ++
    "\n  unique := by intro s a b; cases a <;> cases b <;> rfl" ++
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

/-! ## Finite certificates and native kernel replay

Scope of this first replay format: C(a)+X =B C(b)+Y, where C is a one-hole
constructor context with a rigid parameter sort. C supports arbitrary arities;
other arguments are fixed registered trees. There are no Bakery names here.

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
  deriving Repr, DecidableEq

/-- Small first-order dump grammar, mirrored by certification.maude constructors.
These printers serialize DATA only; external I/O is kept in its own section. -/
def HeadCertificate.dump : HeadCertificate → String
  | .rigid => "rigid"
  | .decompose position next => "decompose(" ++ toString position ++ "," ++ next.dump ++ ")"

def Family.dump : Family → String
  | .matched => "matched"
  | .crossed => "crossed"

def Certificate.dump : Certificate → String
  | .coverage head equalCase unequalCase =>
      "coverage(" ++ head.dump ++ ",emit(" ++ equalCase.dump ++ "),emit(" ++
        unequalCase.dump ++ "))"

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

/-! ## External data boundary — no semantic proofs or search in Lean

Native Maude proposes actual substitutions. We recognize EVERY image, including
the shared fresh parameters, before compacting a family to its complete template.
The object-level rules then try to cover BOTH cases with the proposed templates.
The returned trace is decoded, not replaced by oneTailTrace or a local solver.
Only replay_exact supplies a proof; all parsing/export code is untrusted.
Unsupported native answers fail explicitly rather than being dropped.
-/
namespace External

open Lean Maude

/-- A native one-tail query, inferred from the two translated input terms. -/
structure Input where
  variables : Array MaudeVariable
  a : MaudeTerm
  b : MaudeTerm
  x : MaudeTerm
  y : MaudeTerm
  head : MaudeTerm
  add : Name
  bag : Name

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

def input (left right : TranslatedPattern) : Except String Input := do
  let [a, x] := left.variables.toList | throw "expected two variables on the left"
  let [b, y] := right.variables.toList | throw "expected two variables on the right"
  let av := MaudeTerm.variable a.maudeName a.sort
  let bv := MaudeTerm.variable b.maudeName b.sort
  let xv := MaudeTerm.variable x.maudeName x.sort
  let yv := MaudeTerm.variable y.maudeName y.sort
  let .application add bag #[ha, tail] := left.term | throw "expected C(a)+X"
  let .application add' bag' #[hb, tail'] := right.term | throw "expected C(b)+Y"
  unless add == add' && bag == bag' && x.sort == bag && y.sort == bag &&
      a.sort == b.sort && tail == xv && tail' == yv &&
      oneHole ha av == (true, 1) && replace ha av bv == hb do
    throw "unsupported one-tail query or different head contexts"
  return {
    variables := left.variables ++ right.variables, a := av, b := bv
    x := xv, y := yv, head := ha, add := add, bag := bag }

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
  if a == b && x == y then
    let .variable _ s := x | throw "matched bag image is not a free parameter"
    unless s == spec.bag do throw "matched remainder sort changed"
    return .matched
  unless an != bn do throw "crossed parameters must be independent"
  let .application f s #[first, second] := x | throw "unsupported crossed bag image"
  unless f == spec.add && s == spec.bag do throw "crossed image uses another operator"
  let headB := replace spec.head spec.a b
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
  | .app "decompose" #[.num n, rest] => return .decompose n (← decodeHead rest)
  | _ => throw "unsupported head certificate"

private def decodeFamily : Maude.Certification.Node → Except String Family
  | .app "emit" #[.app "matched" #[]] => pure .matched
  | .app "emit" #[.app "crossed" #[]] => pure .crossed
  | _ => throw "unsupported coverage leaf"

/-- One bounded search result, echoing the WHOLE request. No solution and a
malformed/truncated certificate are failures, not empty successful certificates. -/
def searchReply (request stdout : String) : Except String Certificate := do
  let [before, after] := stdout.splitOn "R:Reply --> "
    | throw "expected exactly one certificate search result"
  unless (before.splitOn "Solution 1 (state ").length == 2 do
    throw "missing search solution heading"
  let [term, exit] := after.splitOn "Bye." | throw "truncated certificate search output"
  unless exit.trim.isEmpty do throw "trailing certificate search output"
  let .app "proposed" #[echo, .app "coverage" #[head, equal, unequal]] ←
      Maude.Certification.parseNode term | throw "unsupported certificate reply"
  unless echo == (← Maude.Certification.parseNode request) do
    throw "certificate request echo changed"
  return .coverage (← decodeHead head) (← decodeFamily equal) (← decodeFamily unequal)

structure Fetched where
  families : List Family
  trace : Certificate
  -- Kept only for diagnostics/tamper tests; emit does not persist these strings.
  request : String
  nativeOutput : String
  searchOutput : String

/-- TWO engines: native unify proposes; object-level rewrite search certifies.
There is no scripted strategy or preselected certificate term. Search depth is
bounded, so failure is reported rather than hanging or inserting sorry. -/
def fetch (model engine : String) (sorts : Array SortDecl)
    (left right : TranslatedPattern) (context : String) : IO Fetched := do
  let spec ← IO.ofExcept (input left right)
  let stdout ← Maude.runMaude model
    s!"unify in LEAN-MODEL : {left.term.render} =? {right.term.render} ."
  let families ← IO.ofExcept (nativeAnswers sorts spec stdout)
  let request := s!"request({context},{familiesDump families})"
  let result ← Maude.runMaude engine
    s!"search [1, 64] in DIRECT-CERTIFICATION : start({request}) =>! R:Reply ."
  let trace ← IO.ofExcept (searchReply request result)
  return { families, trace, request, nativeOutput := stdout, searchOutput := result }

private def familyExpr : Family → Expr
  | .matched => mkConst ``Family.matched
  | .crossed => mkConst ``Family.crossed

private def headExpr : HeadCertificate → Expr
  | .rigid => mkConst ``HeadCertificate.rigid
  | .decompose n rest => mkApp2 (mkConst ``HeadCertificate.decompose) (mkNatLit n) (headExpr rest)

/-- Emit proofless constants ONLY. The theorem below must still kernel-check
acceptance against its typed context, with ordinary rfl, not native_decide. -/
def emit (pre : Name) (fetched : Fetched) : Lean.MetaM Unit := do
  let .coverage head equal unequal := fetched.trace
  let trace := mkApp3 (mkConst ``Certificate.coverage) (headExpr head)
    (familyExpr equal) (familyExpr unequal)
  for (name, value) in [(pre ++ `families, ← Lean.Meta.mkListLit (mkConst ``Family)
      (fetched.families.map familyExpr)), (pre ++ `trace, trace)] do
    Lean.addAndCompile <| .defnDecl {
      name, levelParams := []
      type := ← Lean.Meta.inferType value, value, hints := .regular 0, safety := .safe }
    Lean.enableRealizationsForConst name

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
  let fetched ← Replay.External.fetch model engine sorts left right context
  Replay.External.emit `DirectCertification.Bakery.fetched fetched
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
#print axioms atomic_certificate
#print axioms refinement_certificate
#print axioms one_tail_certificate
#print axioms acu_payload_certificate
#print axioms head_clash_certificate
#print axioms missing_matched_rejected
#print axioms coverage_iff
#print axioms Replay.replay_exact

end DirectCertification.Bakery
