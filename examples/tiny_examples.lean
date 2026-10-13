import Tiny.Expresso.core
import Tiny.conPanna.Unification.Problem
import Init.Data.List.Perm

/-!
Two independent examples: Bakery first, then a commutative pair.
Bakery includes a single-process semantics slice and an ACU process-bag
unification example, not a proof of the full Bakery protocol.
There are no custom tactics or external calls.
-/
namespace TinyBakery

open Expresso

inductive Mode where
  | idle
  | wait (ticket : Nat)
  | crit (ticket : Nat)

/-! ## Process-bag model and manual quotient setup
The user's datatype visibly declares all three constructors. The following
generated ACU relation and quotient are written manually for now; later they
should be generated from this declaration and its ACU annotation.
There is no idempotence or extra equation on process contents.
-/
inductive RawProcSet where
  | empty
  | singleton (process : Mode)
  | union (left right : RawProcSet) -- ACU, with empty as unit

-- Manual setup: the LEAST equivalence closed under union and the ACU axioms.
-- Mode/ticket equality remains ordinary equality; only union has equations.
inductive B : RawProcSet → RawProcSet → Prop where
  | refl (a : RawProcSet) : B a a
  | symm {a b} : B a b → B b a
  | trans {a b c} : B a b → B b c → B a c
  | congr {a a' b b'} : B a a' → B b b' → B (.union a b) (.union a' b')
  | assoc (a b c) : B (.union (.union a b) c) (.union a (.union b c))
  | comm (a b) : B (.union a b) (.union b a)
  | unit_left (a) : B (.union .empty a) a
  | unit_right (a) : B (.union a .empty) a

def procSetoid : Setoid RawProcSet where
  r := B
  iseqv := ⟨B.refl, B.symm, B.trans⟩

abbrev ProcSet := Quotient procSetoid

-- Native operations are precisely the user's constructors lifted to the quotient.
def ProcSet.empty : ProcSet := Quotient.mk procSetoid .empty

def ProcSet.singleton (process : Mode) : ProcSet :=
  Quotient.mk procSetoid (.singleton process)

def ProcSet.union (left right : ProcSet) : ProcSet :=
  Quotient.liftOn₂ left right
    (fun ps qs => Quotient.mk procSetoid (.union ps qs))
    (fun _ _ _ _ hp hq => Quotient.sound (B.congr hp hq))

-- An interpretation for the proof below, not the model's datatype or equality.
def RawProcSet.contents : RawProcSet → List Mode
  | .empty => []
  | .singleton a => [a]
  | .union a b => a.contents ++ b.contents

structure Conf where
  next : Nat
  serving : Nat
  procs : ProcSet

/-! ## Symbolic patterns
`bind` means existential membership, not a concrete choice of ticket.
The condition in an atom belongs to that same ticket assignment.
-/

def initial : Patt Conf :=
  .bind (fun n : Nat => .atom ⟨n, n, ProcSet.singleton .idle⟩)

def waiting : Patt Conf :=
  .bind (fun n : Nat => .atom ⟨n + 1, n, ProcSet.singleton (.wait n)⟩ (n < n + 1))

def critical : Patt Conf :=
  .bind (fun n : Nat => .atom ⟨n + 1, n, ProcSet.singleton (.crit n)⟩ (n < n + 1))

def bakeryInv : Patt Conf :=
  .disj initial (.disj waiting critical)

--#reduce bakeryInv

/-! ## Parameterized rules and their one-step choice
The same bound ticket occurs on both sides and in the rule condition.
`bakerySystem` permits one of the three steps, not their sequential execution.
-/

def wake : System Conf :=
  .bind (fun n : Nat =>
    .rule ⟨n, n, ProcSet.singleton .idle⟩ ⟨n + 1, n, ProcSet.singleton (.wait n)⟩)

def enter : System Conf :=
  .bind (fun n : Nat =>
    .rule ⟨n + 1, n, ProcSet.singleton (.wait n)⟩
      ⟨n + 1, n, ProcSet.singleton (.crit n)⟩ (n < n + 1))

def exit : System Conf :=
  .bind (fun n : Nat =>
    .rule ⟨n + 1, n, ProcSet.singleton (.crit n)⟩ ⟨n + 1, n + 1, ProcSet.singleton .idle⟩)

def bakerySystem : System Conf :=
  .choice wake (.choice enter exit)

/-! ## ACU unification: provided answers and a native completeness proof -/
open Unification

open ProcSet
open RawProcSet (contents)

-- The original variables are (n, P, Q); n is a free ticket, P and Q are ACU bags.
-- ⟨n + 1, n, union P Q⟩ = ⟨n + 1, n, singleton (wait n)⟩
-- The equation is on native configurations, whose process field is an ACU quotient.
def problem : Problem Conf (Nat × ProcSet × ProcSet) :=
  .bind fun (N, P, Q) =>
    (⟨N + 1, N, union P Q⟩, ⟨N + 1, N, singleton (.wait N)⟩)

-- Provided answers, not computed by this proof:
-- σ₁: n ↦ u, P ↦ empty, Q ↦ singleton (wait u)
-- σ₂: n ↦ u, P ↦ singleton (wait u), Q ↦ empty
def unifier1 : Unifier (Nat × ProcSet × ProcSet) :=
  .bind (fun u : Nat => .subst ⟨u, empty, singleton (.wait u)⟩)

def unifier2 : Unifier (Nat × ProcSet × ProcSet) :=
  .bind (fun u : Nat => .subst ⟨u, singleton (.wait u), empty⟩)

def solutions : UnifierSet (Nat × ProcSet × ProcSet) := [unifier1, unifier2]

-- Completeness only: every concrete solution is covered by a provided answer.
-- All reasoning is here, with no separate decomposition/certification theorem.
example : UnifierSet.Complete problem solutions := by
  --unfold problem
  rintro ⟨N?, P?, Q?⟩ h
  -- Ordinary projection exposes structural equality of the quotient-valued field.
  have hprocs : union P? Q? = singleton (.wait N?) := congrArg Conf.procs h
  clear h

  -- low level certification
  have hcases :
      (P? = empty ∧ Q? = singleton (.wait N?)) ∨
      (P? = singleton (.wait N?) ∧ Q? = empty) := by
    -- Choose arbitrary raw constructor trees, not flattened-list model values.
    revert hprocs
    refine Quotient.inductionOn₂ P? Q? ?_
    intro P Q h
    have hB : B (.union P Q) (.singleton (.wait N?)) := Quotient.exact h

    -- Every generated ACU step preserves contents up to permutation.
    have preserves : ∀ {a b}, B a b → List.Perm (contents a) (contents b) := by
      intro a b hab
      induction hab with
      | refl a => exact List.Perm.refl _
      | symm _ ih => exact ih.symm
      | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
      | congr _ _ ih₁ ih₂ => exact ih₁.append ih₂
      | assoc a b c => exact List.Perm.of_eq (List.append_assoc _ _ _)
      | comm a b => exact List.perm_append_comm
      | unit_left a => exact List.Perm.refl _
      | unit_right a => exact List.Perm.of_eq (List.append_nil _)

    -- An empty/singleton contents list reconstructs the corresponding raw ACU class.
    -- Both inductions stay inside this certificate; no auxiliary theorem is declared.
    have empty_case : ∀ a, contents a = [] → B a .empty := by
      intro a
      induction a with
      | empty => intro _; exact B.refl _
      | singleton a => intro h; cases h
      | union a b iha ihb =>
        intro h
        rcases List.append_eq_nil_iff.mp h with ⟨ha, hb⟩
        exact B.trans (B.congr (iha ha) (ihb hb)) (B.unit_left _)

    have singleton_case : ∀ a process, contents a = [process] → B a (.singleton process) := by
      intro a
      induction a with
      | empty => intro process h; cases h
      | singleton a =>
        intro process h
        cases h
        exact B.refl _
      | union a b iha ihb =>
        intro process h
        rcases List.append_eq_singleton_iff.mp h with ⟨ha, hb⟩ | ⟨ha, hb⟩
        · exact B.trans (B.congr (empty_case a ha) (ihb process hb)) (B.unit_left _)
        · exact B.trans (B.congr (iha process ha) (empty_case b hb)) (B.unit_right _)

    -- unification problem in list representation
    have hlist : contents P ++ contents Q = [Mode.wait N?] := (preserves hB).eq_singleton
    -- note the goal represents the proposed answer (two unifiers)

    rcases List.append_eq_singleton_iff.mp hlist with ⟨hp, hq⟩ | ⟨hp, hq⟩
    · exact Or.inl ⟨Quotient.sound (empty_case P hp),
        Quotient.sound (singleton_case Q (.wait N?) hq)⟩
    · exact Or.inr ⟨Quotient.sound (singleton_case P (.wait N?) hp),
        Quotient.sound (empty_case Q hq)⟩

  -- Back at quotient level: select the supplied unifier and its fresh ticket witness.
  rcases hcases with ⟨hP, hQ⟩ | ⟨hP, hQ⟩
  · exact ⟨unifier1, List.Mem.head [unifier2], ⟨N?, Prod.ext rfl (Prod.ext hP hQ)⟩⟩
  · exact ⟨unifier2, List.Mem.tail _ (List.Mem.head []),
      ⟨N?, Prod.ext rfl (Prod.ext hP hQ)⟩⟩

end TinyBakery

/-! ## A commutative pair: completeness with two unifiers
The pair is commutative, not associative. The quotient makes structural equality
ordinary equality, with no constructor encoding or registration in unification.
-/
namespace PairUnification

open Expresso Unification

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
def problem : Problem PairState (Status × Status × Status) :=
  .bind fun (X, Y, Z) => (pair X Y, pair .idle Z)

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
  unfold problem
  unfold solutions unifier1 unifier2
  rintro ⟨X, Y, Z⟩ h
  unfold Problem.unifies at h
  -- Quotient equality exposes either identity or the swap generating B.
  have hB : B (.pair X Y) (.pair .idle Z) := Quotient.exact h
  cases hB with
  | refl => exact ⟨unifier1, List.Mem.head [unifier2], ⟨Y, rfl⟩⟩
  | comm => exact ⟨unifier2, List.Mem.tail _ (List.Mem.head []), ⟨X, rfl⟩⟩

end PairUnification
