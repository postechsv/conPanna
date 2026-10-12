import Tiny.Expresso.core

/-!
Quotient experiment, separate from the existing unification implementation.
Generic judgments below use only ordinary equality. The model keeps its raw
relation explicit so the quotient does not erase the intended theory's presentation.
This example tests C, not ACU, and performs no symbolic recovery or external search.
-/
namespace QuotientPrototype

/-! ## Generic native definitions: no theory parameter, context readers, or encoding
The model's value types already account for structural equality.
-/
namespace Unification

universe u v w

structure Problem (α : Type u) (Γ : Type v) where
  lhs : Γ → α
  rhs : Γ → α

inductive Unifier (Γ : Type v) : Type (max v (w + 1)) where
  | subst (assignment : Γ) : Unifier Γ
  | bind {A : Type w} (body : A → Unifier Γ) : Unifier Γ

abbrev UnifierSet (Γ : Type v) := List (Unifier.{v, w} Γ)

variable {α : Type u} {Γ : Type v}

def Problem.unifies (problem : Problem α Γ) (γ : Γ) : Prop :=
  problem.lhs γ = problem.rhs γ

def Unifier.Covers : Unifier Γ → Γ → Prop
  | .subst images, assignment => assignment = images
  | .bind fresh, assignment => ∃ value, (fresh value).Covers assignment

def UnifierSet.Complete (problem : Problem α Γ) (solutions : UnifierSet Γ) : Prop :=
  ∀ γ, problem.unifies γ → ∃ σ, σ ∈ solutions ∧ σ.Covers γ

def Unifier.Sound (problem : Problem α Γ) : Unifier Γ → Prop
  | .subst assignment => problem.unifies assignment
  | .bind fresh => ∀ value, (fresh value).Sound problem

def UnifierSet.Sound (problem : Problem α Γ) (solutions : UnifierSet Γ) : Prop :=
  ∀ σ, σ ∈ solutions → σ.Sound problem

end Unification

/-! ## Model and quotient construction: potentially generated setup
The raw model is an ordered pair; its quotient is an unordered pair.
Because there are no nested pair constructors, identity and one swap already
form the entire C equivalence. No additional equations are assumed.
-/
namespace Bakery

inductive Status where
  | idle | wait | crit

inductive RawPair where
  | pair (left right : Status)

inductive B : RawPair → RawPair → Prop where
  | refl (a : RawPair) : B a a
  | comm (a b : Status) : B (.pair a b) (.pair b a)

def pairSetoid : Setoid RawPair where
  r := B
  iseqv :=
    ⟨B.refl,
     fun h => match h with
       | .refl a => .refl a
       | .comm a b => .comm b a,
     fun h₁ h₂ => match h₁, h₂ with
       | .refl _, h => h
       | .comm a b, .refl _ => .comm a b
       | .comm a b, .comm _ _ => .refl (.pair a b)⟩

abbrev PairState := Quotient pairSetoid

def pair (left right : Status) : PairState :=
  Quotient.mk pairSetoid (.pair left right)

-- The native operator and its individual commutativity axiom remain identifiable.
theorem pair_comm (a b : Status) : pair a b = pair b a :=
  Quotient.sound (B.comm a b)

/-- Exactness of this model's presentation, not merely a commutativity instance.
An instance alone would only establish some equations, not exclude extra ones.
This general constructor theorem is independent of the later unification problem.
-/
theorem pair_eq_iff (a b c d : Status) :
    pair a b = pair c d ↔ (a = c ∧ b = d) ∨ (a = d ∧ b = c) :=
  ⟨fun h => match Quotient.exact h with
    | .refl _ => Or.inl ⟨rfl, rfl⟩
    | .comm _ _ => Or.inr ⟨rfl, rfl⟩,
   fun h => match h with
    | Or.inl ⟨rfl, rfl⟩ => rfl
    | Or.inr ⟨rfl, rfl⟩ => pair_comm _ _⟩

/-! ## User-level congruence and substitution
The outer configuration is NOT itself a quotient. Its pair field is one.
Every function on PairState respects its equality automatically.
-/

structure Conf where
  serving : Nat
  procs : PairState

example (n : Nat) (p q : PairState) (h : p = q) :
    Conf.mk n p = Conf.mk n q :=
  congrArg (Conf.mk n) h

example (n : Nat) :
    Conf.mk n (pair .idle .wait) = Conf.mk n (pair .wait .idle) :=
  congrArg (Conf.mk n) (pair_comm .idle .wait)

-- Assignment packages can mix an ordinary sort and a quotient sort.
example (n : Nat) :
    (Unification.Unifier.subst (n, pair .wait .idle)).Covers (n, pair .idle .wait) :=
  congrArg (fun p => (n, p)) (pair_comm .idle .wait)

-- Ordinary Lean substitution, with no custom modulo-equality tactic.
example (p q : PairState) (h : p = q) (condition : PairState → Prop)
    (hp : condition p) : condition q := by
  subst q
  exact hp

/-! ## User-level unification: native terms and two binder-based answers
Only the quotient sort's ordinary equality is visible here.
-/
open Unification

def problem : Problem PairState (Status × Status × Status) where
  lhs := fun (X, Y, _) => pair X Y
  rhs := fun (_, _, Z) => pair .idle Z

def unifier1 : Unifier (Status × Status × Status) :=
  .bind (fun u : Status => .subst ⟨.idle, u, u⟩)

def unifier2 : Unifier (Status × Status × Status) :=
  .bind (fun u : Status => .subst ⟨u, .idle, u⟩)

def solutions : UnifierSet (Status × Status × Status) := [unifier1, unifier2]

theorem complete : UnifierSet.Complete problem solutions := by
  rintro ⟨X, Y, Z⟩ h
  rcases (pair_eq_iff X Y .idle Z).mp h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨unifier1, List.Mem.head [unifier2], ⟨Y, rfl⟩⟩
  · exact ⟨unifier2, List.Mem.tail _ (List.Mem.head []), ⟨X, rfl⟩⟩

theorem sound : UnifierSet.Sound problem solutions := by
  intro σ hσ
  cases hσ with
  | head => exact fun _ => rfl
  | tail _ hσ =>
    cases hσ with
    | head => exact fun u => pair_comm u .idle
    | tail _ hσ => cases hσ

end Bakery
end QuotientPrototype
