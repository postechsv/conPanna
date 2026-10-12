import Tiny.Expresso.core

/-!
A single-process Bakery slice for reading the native core at the user level.
It keeps ticket allocation and service, but omits process bags and ACU.
This is a semantics demonstration, not a proof of the full Bakery protocol.
Only ordinary equality is used; there are no wrappers, tactics, or external calls.
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


end TinyBakery
