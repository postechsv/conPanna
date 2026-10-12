import Tiny.Expresso.core
import Tiny.conPanna.Unification.Problem

/-!
A single-process Bakery slice for reading the native core at the user level.
It keeps ticket allocation and service, but omits process bags and ACU.
This is a semantics demonstration, not a proof of the full Bakery protocol.
The first examples use ordinary equality; the final example uses commutativity.
There are no wrappers, tactics, or external calls.
-/
namespace TinyBakery

open Expresso

inductive Mode where
  | idle
  | wait (ticket : Nat)
  | crit (ticket : Nat)

structure Conf where
  next : Nat
  serving : Nat
  mode : Mode

/-! ## Symbolic patterns
`bind` means existential membership, not a concrete choice of ticket.
The condition in an atom belongs to that same ticket assignment.
-/

def initial : Patt Conf :=
  .bind (fun n : Nat => .atom ⟨n, n, .idle⟩)

def waiting : Patt Conf :=
  .bind (fun n : Nat => .atom ⟨n + 1, n, .wait n⟩ (n < n + 1))

def critical : Patt Conf :=
  .bind (fun n : Nat => .atom ⟨n + 1, n, .crit n⟩ (n < n + 1))

def bakeryInv : Patt Conf :=
  .disj initial (.disj waiting critical)

--#reduce bakeryInv

/-! ## Parameterized rules and their one-step choice
The same bound ticket occurs on both sides and in the rule condition.
`bakerySystem` permits one of the three steps, not their sequential execution.
-/

def wake : System Conf :=
  .bind (fun n : Nat => .rule ⟨n, n, .idle⟩ ⟨n + 1, n, .wait n⟩)

def enter : System Conf :=
  .bind (fun n : Nat =>
    .rule ⟨n + 1, n, .wait n⟩ ⟨n + 1, n, .crit n⟩ (n < n + 1))

def exit : System Conf :=
  .bind (fun n : Nat => .rule ⟨n + 1, n, .crit n⟩ ⟨n + 1, n + 1, .idle⟩)

def bakerySystem : System Conf :=
  .choice wake (.choice enter exit)

/-! ## Reading membership and transitions
These equivalences are just the recursive definitions, with no proof search.
-/

example (state : Conf) : waiting.holds Eq state ↔
    ∃ n : Nat, Conf.mk (n + 1) n (.wait n) = state ∧ n < n + 1 :=
  Iff.rfl

example : Subsumes Eq waiting bakeryInv :=
  fun _ hwaiting => Or.inr (Or.inl hwaiting)

/-! ## A completeness claim with two unifiers
A separate two-process Bakery slice, keeping only idle/wait/critical modes.
Its pair is commutative, not associative. The quotient makes structural equality
ordinary equality, with no constructor encoding or registration in unification.
-/
namespace PairUnification

open Unification

inductive Status where
  | idle | wait | crit

inductive RawPairState where
  | pair (left right : Status) : RawPairState -- comm

/-! ### Native structural equality (not part of the completeness proof) -/

-- One theory B supplies pair commutativity; it has no equations on Status.
-- For this nonrecursive pair, identity and one swap already form the full equivalence.
inductive B : RawPairState → RawPairState → Prop where
  | refl (a : RawPairState) : B a a
  | comm (a b : Status) : B (.pair a b) (.pair b a)

def pairSetoid : Setoid RawPairState where
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

theorem pair_comm (a b : Status) : pair a b = pair b a :=
  Quotient.sound (B.comm a b)

-- The existing core works unchanged with Eq on quotient-valued states.
example : (Patt.atom (pair .idle .wait)).holds Eq (pair .wait .idle) :=
  ⟨pair_comm .idle .wait, True.intro⟩

/-! ### User-facing problem and proposed answer
Γ packages the three original variables X, Y, Z. Each answer binds its own U.
Here Γ is the anonymous tuple `Status × Status × Status`, in that order.
-/

-- pair X Y =[B] pair idle Z
-- On PairState, this is now ordinary equality. No context readers are needed.
def problem : Problem PairState (Status × Status × Status) where
  lhs := fun (X, Y, _) => pair X Y
  rhs := fun (_, _, Z) => pair .idle Z

def unifier1 : Unifier (Status × Status × Status) :=
  .bind (fun u : Status => .subst ⟨.idle, u, u⟩)

def unifier2 : Unifier (Status × Status × Status) :=
  .bind (fun u : Status => .subst ⟨u, .idle, u⟩)

def solutions : UnifierSet (Status × Status × Status) := [unifier1, unifier2]

-- Every solution of the displayed equation is an instance of one of these two families.
-- Expanded meaning (ordinary equality accounts for each sort's theory):
--   ∀ x y z, pair x y = pair idle z →
--     (∃ u, x = idle ∧ y = u ∧ z = u) ∨
--     (∃ u, x = u ∧ y = idle ∧ z = u).
example : UnifierSet.Complete problem solutions := by

  unfold UnifierSet.Complete UnifierSet.Covers solutions

  unfold problem

  unfold Problem.unifies
  sorry

end PairUnification

end TinyBakery
