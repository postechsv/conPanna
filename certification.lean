import examples.bakery_acu

/-!
# Direct, rule-based unification certificates

This file contains three clearly separated parts:
1. GENERAL METATHEOREMS: correctness of the rules for any registered signature.
2. SYNTACTIC METADATA: constructor classification, generated without user proofs.
3. CERTIFICATES: ordinary, tactic-free proof terms over Bakery's own datatypes.

The current milestone is answer-directed certification of ONE explicit atom
and ONE bag tail per side. The generic coverage theorem below reduces an
unbounded bag obligation to two head-equality guards. It does not recompute a
complete set of ACU unifiers. General multi-head coverage and finite dump/replay
remain future work; no native Maude answer is trusted as a completeness proof.

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

/- Proposed families for ONE equation:

     singleton(wait(i)) + P =B singleton(wait(j)) + Q

   matched: the heads are equal, P=Q
   crossed: P=singleton(wait(j))+N, Q=singleton(wait(i))+N

   Schematic future dump/replay:
     CheckAtomicHeads
     Coverage(matchedGuard=True, crossedGuard=True)
       ├─ heads equal     -> matched guard holds
       └─ heads unequal   -> crossed guard holds
     ExactOfCoverage

   The certificate below only applies general rules and logical constructors;
   it does NOT replay Mutate/Split to rediscover the supplied families.
   The arbitrary shared remainder is already handled by the general theorem.

   Boundary: this certifies the bag-level reduction. The matched head equation
   is retained explicitly. Turning it into i=j (and a native substitution
   i↦k,j↦k) needs the generic free-constructor decomposition rule, the NEXT
   milestone. We do not silently assume injectivity modulo structural axioms.
-/
theorem one_tail_certificate (i j : Nat) (P Q : ProcSet) :
    ProcSet.union (ProcSet.singleton (.wait i)) P =[BakeryTheory.certified]
      ProcSet.union (ProcSet.singleton (.wait j)) Q ↔
      (ProcSet.singleton (.wait i) =[BakeryTheory.certified]
          ProcSet.singleton (.wait j) ∧ P =[BakeryTheory.certified] Q) ∨
      (∃ N : ProcSet,
        P =[BakeryTheory.certified] ProcSet.union (ProcSet.singleton (.wait j)) N ∧
        Q =[BakeryTheory.certified] ProcSet.union (ProcSet.singleton (.wait i)) N) :=
  let certificate := exact_of_coverage profile registration Operator.acu
    (ProcSet.singleton (.wait i)) (ProcSet.singleton (.wait j)) True True rfl rfl
    -- Completeness is reduced to TWO FINITE GUARDS, independent of P,Q,N.
    ⟨fun _ => True.intro, fun _ => True.intro⟩ P Q
  Iff.intro
    -- Erase trivial guard annotations from the semantic answer proposition.
    (fun input => Or.elim (certificate.mp input)
      (fun matched => Or.inl matched.2) (fun crossed => Or.inr crossed.2))
    (fun output => certificate.mpr (Or.elim output
      (fun matched => Or.inl ⟨True.intro, matched⟩)
      (fun crossed => Or.inr ⟨True.intro, crossed⟩)))

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

-- Axiom audits should report only propext / Quot.sound, never sorryAx.
#print axioms atomic_certificate
#print axioms refinement_certificate
#print axioms one_tail_certificate
#print axioms missing_matched_rejected
#print axioms coverage_iff

end DirectCertification.Bakery
