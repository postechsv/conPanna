import conPanna.Structural

/-!
# Unconstrained unification certification: a proof-system prototype

Part 1 defines general inference rules and their semantic adequacy theorem.
Part 2 contains certification proofs written only by applying those rules.

The semantics is the library's `Structural.EqMod`. No Mathlib is imported.
Four general completeness metatheorems are left as `sorry`.

Inspiration: `ACU-certification.pdf`, *Order-sorted Equational Unification
Revisited*, Figure 1 and Lemma 5.5: represent alternatives by disjunctions of
conjunctions and prove that every inference step preserves the solution set.
Our `Derives.adequate` follows that compositional proof structure. The paper's
Theorem 5.9 assumes a complete unsorted unifier; the ACU splitting rule below
is an additional core-unification rule, not one of its sort-propagation rules.
-/

namespace Certification

open Structural

/-! ## Part 1. General proof system and metatheory -/

/-- A free term algebra with an ACU symbol and an ordinary pair constructor. -/
inductive Term where
  | atom : Nat → Term
  | empty : Term
  | add : Term → Term → Term
  | pair : Term → Term → Term

-- Registers the ordinary constructors for EqMod congruence as well.
instance : framework.State Term := ⟨⟩

structural B where
  assoc Term.add
  comm Term.add
  id Term.add Term.empty

open Term

/--
General ACU unification rule:
`a + b =[B] c + d` is represented exactly by the substitution

    a ↦ p + q,  b ↦ r + s,  c ↦ p + r,  d ↦ q + s.

The fresh components may be empty. Completeness uses the refinement property
of the *free* ACU algebra. It does not follow from ACU laws in arbitrary models.
-/
theorem acu_split_iff (a b c d : Term) :
    add a b =[B] add c d ↔
      ∃ p q r s : Term,
        a =[B] add p q ∧ b =[B] add r s ∧
        c =[B] add p r ∧ d =[B] add q s := by
  constructor
  · -- GENERAL METATHEOREM STILL TO PROVE:
    -- flatten free ACU terms into bags and split equal sums into four pieces.
    sorry
  · intro h
    obtain ⟨p, q, r, s, ha, hb, hc, hd⟩ := h
    have exchange :
        add (add p q) (add r s) =[B] add (add p r) (add q s) :=
      .trans (.assoc add p q (add r s)) <|
      .trans (.congr add (.ofEq rfl) (.symm (.assoc add q r s))) <|
      .trans (.congr add (.ofEq rfl)
        (.congr add (.comm add q r) (.ofEq rfl))) <|
      .trans (.congr add (.ofEq rfl) (.assoc add r q s))
        (.symm (.assoc add p r (add q s)))
    exact .trans (.congr add ha hb) <|
      .trans exchange (.symm (.congr add hc hd))

/-- Cancellation is valid in the free ACU algebra represented by `Term` and `B`.
It is not a consequence of the ACU axioms in every possible algebra. -/
theorem acu_cancel_iff (a b common : Term) :
    add a common =[B] add b common ↔ a =[B] b := by
  constructor
  · -- GENERAL COMPLETENESS: cancel equal bags from equal bag sums.
    sorry
  · intro h
    exact .congr add h (.ofEq rfl)

/-- A single atom must occur in exactly one of the two summands.
The two alternatives are a complete set of ground substitutions for `a, b`. -/
theorem acu_atom_iff (a b : Term) (k : Nat) :
    add a b =[B] atom k ↔
      (a =[B] empty ∧ b =[B] atom k) ∨
      (a =[B] atom k ∧ b =[B] empty) := by
  constructor
  · -- GENERAL COMPLETENESS: partition a singleton bag into two bags.
    sorry
  · intro h
    cases h with
    | inl h =>
        exact .trans (.congr add h.1 h.2) (.identityLeft add empty (atom k))
    | inr h =>
        exact .trans (.congr add h.1 h.2) (.identityRight add empty (atom k))

/-- Decomposition for the free pair constructor in this structural signature.
Only `add` has ACU laws; `pair` keeps its two arguments in order. -/
theorem pair_decompose_iff (a b c d : Term) :
    pair a b =[B] pair c d ↔ (a =[B] c ∧ b =[B] d) := by
  constructor
  · -- GENERAL COMPLETENESS: inversion for a free constructor modulo B.
    sorry
  · intro h
    exact EqMod.constructor
      (ConstructorCongruence.app
        (ConstructorCongruence.app (ConstructorCongruence.head pair) h.1) h.2)

/-!
### Reading the inference rules

Below, `P ==> Q` means `Derives P Q`, `a ~ b` means `a =[B] b`,
`+` means `Term.add`, and `0` means `Term.empty` (not `atom 0`).
`P, Q, ...` are formulas; `a, b, ...` are terms. Read a rule upwards when
constructing a certificate: to establish its conclusion, supply its premises.

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

  ----------------------------------- [Cancel]
     (a+c ~ b+c) ==> (a ~ b)

  ------------------------------------------------------- [Atom]
  (a+b ~ atom k) ==> (a ~ 0 ∧ b ~ atom k) ∨
                    (a ~ atom k ∧ b ~ 0)

  ------------------------------------------------------- [Decompose]
       pair(a,b) ~ pair(c,d) ==> (a ~ c) ∧ (b ~ d)

  ------------------------------------------------------- [Distribute]
  (P∨Q) ∧ (R∨S) ==> (P∧R) ∨ (P∧S) ∨ (Q∧R) ∨ (Q∧S)

The premise-free algebra rules stand for metatheorems proved once for the
free ACU theory. Their generality comes from their universally arbitrary terms,
not from trusting a particular solver result. Four completeness directions
remain admitted above; the example proofs inherit those admissions.

### Why this proves the semantic certificate

For fixed original variables, let `P` be the original equation system.
Let `Q` be the proposed unifier alternatives written as factorization formulas:

  (∃ fresh variables, x₁ ~ σ₁ ∧ ... ∧ xₙ ~ σₙ) ∨ ...

These are ordinary Lean propositions using the existing `EqMod` semantics.
A derivation is evidence of rule applications. `Derives.adequate` interprets
each application using its metatheorem, producing a Lean proof of `P ↔ Q`.

* `P → Q`: every semantic solution factors through some proposed σ (complete).
* `Q → P`: every instance of a proposed σ solves the equation system (sound).

An empty fresh-variable list gives a ground branch: just a conjunction of
factorization equations. The four-branch example below has this form.
Adequacy justifies any constructed derivation; it does not claim that these
few rules can solve every ACU problem or that proof search is implemented.
-/

/--
`Derives P Q` records solution-preserving transformations from `P` to `Q`.
Intermediate formulas may contain unsolved equations. A certification finishes
with `Q` explicitly written as existential substitution factorizations,
possibly in disjunction; the example below shows that final formula directly.

Lean binders represent original and fresh variables. The judgment is general:
it is not indexed by a particular problem, variable count, or proposed unifier.
-/
inductive Derives : Prop → Prop → Prop where
  | done {P : Prop} : Derives P P
  | trans {P Q R : Prop} :
      Derives P Q → Derives Q R → Derives P R
  | conj {P P' Q Q' : Prop} :
      Derives P P' → Derives Q Q' → Derives (P ∧ Q) (P' ∧ Q')
  | disj {P P' Q Q' : Prop} :
      Derives P P' → Derives Q Q' → Derives (P ∨ Q) (P' ∨ Q')
  | existsCongr {α : Type} {P Q : α → Prop} :
      (∀ x, Derives (P x) (Q x)) →
      Derives (∃ x, P x) (∃ x, Q x)
  | distribute {P Q R S : Prop} :
      Derives ((P ∨ Q) ∧ (R ∨ S))
        ((P ∧ R) ∨ (P ∧ S) ∨ (Q ∧ R) ∨ (Q ∧ S))
  /-- Normalize either side using the existing structural-equation proof rules. -/
  | rewrite {a a' b b' : Term} {Q : Prop} :
      a =[B] a' → b =[B] b' →
      Derives (a' =[B] b') Q → Derives (a =[B] b) Q
  /-- Introduce the fresh variables and substitution images for an ACU split. -/
  | acu_split (a b c d : Term) :
      Derives (add a b =[B] add c d)
        (∃ p q r s : Term,
          a =[B] add p q ∧ b =[B] add r s ∧
          c =[B] add p r ∧ d =[B] add q s)
  | acu_cancel (a b common : Term) :
      Derives (add a common =[B] add b common) (a =[B] b)
  | acu_atom (a b : Term) (k : Nat) :
      Derives (add a b =[B] atom k)
        ((a =[B] empty ∧ b =[B] atom k) ∨
          (a =[B] atom k ∧ b =[B] empty))
  | decompose (a b c d : Term) :
      Derives (pair a b =[B] pair c d) (a =[B] c ∧ b =[B] d)

/-- Every derivation preserves exactly all solutions: completeness and soundness. -/
theorem Derives.adequate {P Q : Prop} (proof : Derives P Q) : P ↔ Q := by
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
  | rewrite left right _ ih =>
      constructor
      · intro h
        exact ih.mp (.trans left.symm (.trans h right))
      · intro h
        exact .trans left (.trans (ih.mpr h) right.symm)
  | acu_split a b c d => exact acu_split_iff a b c d
  | acu_cancel a b common => exact acu_cancel_iff a b common
  | acu_atom a b k => exact acu_atom_iff a b k
  | decompose a b c d => exact pair_decompose_iff a b c d

/-- Extract the completeness half of a certification derivation. -/
theorem Derives.complete {P Q : Prop} (proof : Derives P Q) : P → Q :=
  proof.adequate.mp

/-- Extract the soundness half of a certification derivation. -/
theorem Derives.sound {P Q : Prop} (proof : Derives P Q) : Q → P :=
  proof.adequate.mpr

/-! ## Part 2. Certification proofs

### A unifier with fresh variables

Problem: `(x + empty) + y =[B] z + (empty + w)`.

Proposed unifier:
  x ↦ p + q, y ↦ r + s, z ↦ p + r, w ↦ q + s.

The forward implication below is completeness; the reverse is soundness.
There are no problem-specific helper lemmas or separately defined traces.
The proof inherits the admissions in the general adequacy theorem.
-/

example :
    ∀ x y z w : Term,
      add (add x empty) y =[B] add z (add empty w) ↔
        ∃ p q r s : Term,
          x =[B] add p q ∧ y =[B] add r s ∧
          z =[B] add p r ∧ w =[B] add q s := by
  intro x y z w
  -- Semantic goal P ↔ Q becomes the proof-system judgment Derives P Q.
  apply Derives.adequate
  -- Strip the two units, using the general structural-equation rules.
  apply Derives.rewrite
    (EqMod.congr add (EqMod.identityRight add empty x) (EqMod.ofEq rfl))
    (EqMod.congr add (EqMod.ofEq rfl) (EqMod.identityLeft add empty w))
  -- Certify the proposed unifier by the general ACU splitting rule.
  exact Derives.acu_split x y z w

/-!
### Four unifiers for one atomic unification problem

Original unification variables: x, y, z, w.
`common` is a shared rigid parameter; it is unchanged by every substitution.

Problem (one equation):
  pair((x + y) + common, z + (empty + w))
    ~ pair(atom 0 + common, atom 1)

The proof system's Decompose rule produces two intermediate equations;
these are not separate unification problems supplied by the user.

Proposed complete set of unifiers (no fresh variables needed):

              x          y          z          w
  σ₁        empty      atom 0      empty      atom 1
  σ₂        empty      atom 0      atom 1     empty
  σ₃        atom 0     empty       empty      atom 1
  σ₄        atom 0     empty       atom 1     empty

Each conjunction below says that the original assignment agrees modulo B
with one row. Thus the RHS is precisely "instance of σ₁ or σ₂ or σ₃ or σ₄".
The LHS uses the original EqMod semantics, not a predicate invented by the
proof system. Adequacy connects this semantic goal to the derivation below.

This example uses only general rules, with every step in the same proof.
It inherits the admitted general completeness metatheorems through adequacy.
-/

example :
    ∀ common x y z w : Term,
      pair (add (add x y) common) (add z (add empty w)) =[B]
        pair (add (atom 0) common) (atom 1) ↔
      ((x =[B] empty ∧ y =[B] atom 0) ∧
        (z =[B] empty ∧ w =[B] atom 1)) ∨
      ((x =[B] empty ∧ y =[B] atom 0) ∧
        (z =[B] atom 1 ∧ w =[B] empty)) ∨
      ((x =[B] atom 0 ∧ y =[B] empty) ∧
        (z =[B] empty ∧ w =[B] atom 1)) ∨
      ((x =[B] atom 0 ∧ y =[B] empty) ∧
        (z =[B] atom 1 ∧ w =[B] empty)) := by
  intro common x y z w
  -- Adequacy: it suffices to derive the displayed four unifier branches
  -- from the original single equation. It will supply BOTH implications.
  apply Derives.adequate

  -- Decompose the free pair constructor. The proof system now generates
  -- the two component equations as an intermediate conjunction.
  refine Derives.trans (Derives.decompose _ _ _ _) ?_

  -- Compose with Distribute: first obtain two alternatives per equation,
  -- then take their four combinations. No combination may be discarded.
  refine Derives.trans ?_ Derives.distribute
  apply Derives.conj
  · -- First equation: cancel the shared context, leaving x+y ~ atom 0.
    refine Derives.trans (Derives.acu_cancel (add x y) (atom 0) common) ?_
    -- Atom has two exhaustive choices: give atom 0 to x or to y.
    exact Derives.acu_atom x y 0
  · -- Second equation: normalize empty+w, leaving z+w ~ atom 1.
    apply Derives.rewrite
      (EqMod.congr add (EqMod.ofEq rfl) (EqMod.identityLeft add empty w))
      (EqMod.ofEq rfl)
    -- Atom again has two exhaustive choices: give atom 1 to z or to w.
    exact Derives.acu_atom z w 1

end Certification
