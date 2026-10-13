import Tiny.Expresso.core
import Tiny.Expresso.ACU
import Tiny.conPanna.Unification.Problem
import Tiny.conPanna.Unification.Certification.Multiset

/-!
Bakery: a single-process semantics slice and ACU process-bag unification
examples, not a proof of the full Bakery protocol.
There are no custom tactics or external calls.
-/

namespace TinyBakery

open Expresso

inductive Mode where
  | idle
  | wait (ticket : Nat)
  | crit (ticket : Nat)

/-! ## Process-bag model
Registering an ACU sort, as in Maude's
  `op _+_ : ProcSet ProcSet -> ProcSet [assoc comm id: ∅]`.
Values are written `∅`, `{p}` and `P + Q`; equality is modulo ACU.
There is no idempotence or extra equation on process contents.
-/
abbrev ProcSet := ACU Mode

structure Conf where
  next : Nat
  serving : Nat
  procs : ProcSet

/-! ## Symbolic patterns
`bind` means existential membership, not a concrete choice of ticket.
The condition in an atom belongs to that same ticket assignment.
-/

def initial : Patt Conf :=
  .bind (fun n : Nat => .atom ⟨n, n, {.idle}⟩)

def waiting : Patt Conf :=
  .bind (fun n : Nat => .atom ⟨n + 1, n, {.wait n}⟩ (n < n + 1))

def critical : Patt Conf :=
  .bind (fun n : Nat => .atom ⟨n + 1, n, {.crit n}⟩ (n < n + 1))

def bakeryInv : Patt Conf :=
  .disj initial (.disj waiting critical)

--#reduce bakeryInv

/-! ## Parameterized rules and their one-step choice
The same bound ticket occurs on both sides and in the rule condition.
`bakerySystem` permits one of the three steps, not their sequential execution.
-/

def wake : System Conf :=
  .bind (fun n : Nat =>
    .rule ⟨n, n, {.idle}⟩ ⟨n + 1, n, {.wait n}⟩)

def enter : System Conf :=
  .bind (fun n : Nat =>
    .rule ⟨n + 1, n, {.wait n}⟩
      ⟨n + 1, n, {.crit n}⟩ (n < n + 1))

def exit : System Conf :=
  .bind (fun n : Nat =>
    .rule ⟨n + 1, n, {.crit n}⟩ ⟨n + 1, n + 1, {.idle}⟩)

def bakerySystem : System Conf :=
  .choice wake (.choice enter exit)

/-! ## ACU unification: provided answers and certified completeness
Each proof below is a short certificate in the generic calculus:
  DECOMP (free constructor fields) → REFINE / ATOM (ACU) → COVER.
COVER names the provided unifier and its fresh-variable witness, then checks the
remaining equality by ACU laws. No list or multiset reasoning appears here.
-/
open Unification

-- Original variables (N?, P?, Q?): N? is a free ticket, P? and Q? are ACU bags.
-- ⟨N? + 1, N?, P? + Q?⟩ = ⟨N? + 1, N?, {wait N?}⟩
-- The equation is on native configurations, whose process field is an ACU quotient.
def problem : Problem Conf (Nat × ProcSet × ProcSet) :=
  .bind fun (N?, P?, Q?) =>
    (⟨N? + 1, N?, P? + Q?⟩, ⟨N? + 1, N?, {.wait N?}⟩)

-- Provided answers, not computed by this proof; each binds a fresh N!:
-- σ₁: N? ↦ N!, P? ↦ ∅,         Q? ↦ {wait N!}
-- σ₂: N? ↦ N!, P? ↦ {wait N!}, Q? ↦ ∅
def unifier1 : Unifier (Nat × ProcSet × ProcSet) :=
  .bind fun N! => .subst ⟨N!, ∅, {.wait N!}⟩

def unifier2 : Unifier (Nat × ProcSet × ProcSet) :=
  .bind fun N! => .subst ⟨N!, {.wait N!}, ∅⟩

def solutions : UnifierSet (Nat × ProcSet × ProcSet) := [unifier1, unifier2]

-- Completeness only: every concrete solution is covered by a provided answer.
example : UnifierSet.Complete problem solutions := by
  rintro ⟨N?, P?, Q?⟩ h
  -- DECOMP: `Conf` is free, so its process fields are equal.
  have hprocs : P? + Q? = {.wait N?} := congrArg Conf.procs h
  -- ATOM: one side holds the process, the other is empty.
  rcases ACU.plus_eq_elem.mp hprocs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  -- COVER: (answer, fresh witness N! := N?).
  · exact ⟨unifier1, List.Mem.head _, N?, rfl⟩
  · exact ⟨unifier2, List.Mem.tail _ (List.Mem.head _), N?, rfl⟩

/-! ### A problem needing REFINE: unknown bags on both sides
`P? + Q? = {wait N?} + R?`, original variables (N?, P?, Q?, R?).
Provided answers, both over the same fresh context (N!, B!, D!):
  σ₁: N? ↦ N!,  P? ↦ B!,              Q? ↦ {wait N!} + D!,  R? ↦ B! + D!
  σ₂: N? ↦ N!,  P? ↦ {wait N!} + B!,  Q? ↦ D!,              R? ↦ B! + D!
-/
def problem2 : Problem ProcSet (Nat × ProcSet × ProcSet × ProcSet) :=
  .bind fun (N?, P?, Q?, R?) => (P? + Q?, {.wait N?} + R?)

def unifier2_1 : Unifier (Nat × ProcSet × ProcSet × ProcSet) :=
  .bind fun (N!, B!, D!) => .subst ⟨N!, B!, {Mode.wait N!} + D!, B! + D!⟩

def unifier2_2 : Unifier (Nat × ProcSet × ProcSet × ProcSet) :=
  .bind fun (N!, B!, D!) => .subst ⟨N!, {Mode.wait N!} + B!, D!, B! + D!⟩

def solutions2 : UnifierSet (Nat × ProcSet × ProcSet × ProcSet) := [unifier2_1, unifier2_2]

example : UnifierSet.Complete problem2 solutions2 := by
  rintro ⟨N?, P?, Q?, R?⟩ h
  have h : P? + Q? = {.wait N?} + R? := h
  -- REFINE: fresh cells A! B! C! D! with
  --   P? = A! + B!, Q? = C! + D!, {wait N?} = A! + C!, R? = B! + D!.
  obtain ⟨A!, B!, C!, D!, rfl, rfl, hw, rfl⟩ := ACU.refine h
  -- ATOM on the cells of {wait N?}.
  rcases ACU.plus_eq_elem.mp hw.symm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  -- COVER: (answer, witness (N!, B!, D!) := (N?, B!, D!)), checked modulo ACU.
  · exact ⟨unifier2_1, List.Mem.head _, (N?, B!, D!), by show _ = _; ac_rfl⟩
  · exact ⟨unifier2_2, List.Mem.tail _ (List.Mem.head _), (N?, B!, D!),
      by show _ = _; ac_rfl⟩

end TinyBakery
