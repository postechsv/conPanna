import Tiny.Expresso.core
import Tiny.Expresso.ACU
import Tiny.conPanna.Unification
import Tiny.conPanna.Unification.Certification.Calculus
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

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
The condition in a patch belongs to that same ticket assignment.
-/

def initial : Pattern Conf :=
  .patch (.bind fun n : Nat => { state := ⟨n, n, {.idle}⟩ })

def waiting : Pattern Conf :=
  .patch (.bind fun n : Nat => ⟨⟨n + 1, n, {.wait n}⟩, n < n + 1⟩)

def critical : Pattern Conf :=
  .patch (.bind fun n : Nat => ⟨⟨n + 1, n, {.crit n}⟩, n < n + 1⟩)

def bakeryInv : Pattern Conf :=
  .disj initial (.disj waiting critical)

--#reduce bakeryInv

/-! ## Parameterized rules and their one-step choice
The same bound ticket occurs on both sides and in the rule condition.
`bakerySystem` permits one of the three steps, not their sequential execution.
-/

def wake : System Conf :=
  .rule (.bind fun n : Nat =>
    { lhs := ⟨n, n, {.idle}⟩, rhs := ⟨n + 1, n, {.wait n}⟩ })

def enter : System Conf :=
  .rule (.bind fun n : Nat =>
    ⟨⟨n + 1, n, {.wait n}⟩, ⟨n + 1, n, {.crit n}⟩, n < n + 1⟩)

def exit : System Conf :=
  .rule (.bind fun n : Nat =>
    { lhs := ⟨n + 1, n, {.crit n}⟩, rhs := ⟨n + 1, n + 1, {.idle}⟩ })

def bakerySystem : System Conf :=
  .choice wake (.choice enter exit)

/-! ## ACU unification: provided answers and certified completeness
Each proof is a certificate: paper rules applied to the judgment
`⟨α ; E ; D⟩ ⊩ answers`, starting from the problem (`start_iff`).
SOLVE's data (P, B) is read off the answers; COVER names an answer and its
witness for the fresh variables.
-/
open Unification Certification

-- Original variables (N?, P?, Q?): N? is a free ticket, P? and Q? are ACU bags.
-- ⟨N? + 1, N?, P? + Q?⟩ = ⟨N? + 1, N?, {wait N?}⟩
-- The equation is on native configurations, whose process field is an ACU quotient.
def problem : Problem Conf (Nat × ProcSet × ProcSet) :=
  .bind fun (N?, P?, Q?) =>
    (⟨N? + 1, N?, P? + Q?⟩, ⟨N? + 1, N?, {.wait N?}⟩)

-- Provided answers, not computed by this proof; each binds a variable U1!:
-- σ₁: N? ↦ U1!, P? ↦ ∅,          Q? ↦ {wait U1!}
-- σ₂: N? ↦ U1!, P? ↦ {wait U1!}, Q? ↦ ∅
def unifier1 : Unifier (Nat × ProcSet × ProcSet) :=
  .bind fun U1! => ⟨U1!, ∅, {.wait U1!}⟩

def unifier2 : Unifier (Nat × ProcSet × ProcSet) :=
  .bind fun U1! => ⟨U1!, {.wait U1!}, ∅⟩

def solutions : UnifierSet (Nat × ProcSet × ProcSet) := [unifier1, unifier2]

-- Completeness only: every concrete solution is covered by a provided answer.
example : complete problem solutions := by
  rw [← start_iff]
  -- ⟨id ; ⟨N?+1, N?, P? + Q?⟩ = ⟨N?+1, N?, {wait N?}⟩ ; ∅⟩
  -- DECOMP: `Conf` is free, so its process fields are equal.
  refine decomp (fun (N?, P?, Q?) => P? + Q? = {.wait N?}) (fun _ h => congrArg Conf.procs h) ?_
  -- ⟨id ; P? + Q? = {wait N?} ; ∅⟩
  -- SOLVE: one alien class wait N?; per element p + q = 1 at wait N?, p + q = 0 elsewhere.
  --   P = {(1,0), (0,1)},  B = {}  (no fresh bags).
  refine solve (V := fun (_, P?, Q?) => ![P?, Q?]) (rest := fun (N?, _, _) => N?)
    (glue := fun N? V => (N?, V 0, V 1)) (hglue := fun _ => rfl)
    (a := fun N? => ![Mode.wait N?]) (L := ![1, 1]) (R := ![0, 0]) (La := ![0]) (Ra := ![1])
    (E' := fun _ => True) (P := fun _ => [![1, 0], ![0, 1]]) (B := Fin.elim0)
    (cp := fun _ _ => false)
    ?hE ?S0 ?S1p ?S1b (S2_single _ _ _ _ _ ?S2) ?S3 ?next
  case hE =>
    intro ⟨N?, P?, Q?⟩ h _
    refine ⟨?_, trivial, fun c c' hc _ => absurd (Subsingleton.elim c c') hc⟩
    simpa [side, sum, copies, List.ofFn_succ, ACU.plus_unit, ACU.unit_plus] using h
  case S0 => decide
  case S1p => decide
  case S1b => decide
  case S2 => intro c v h; fin_cases c; simp [dot, Below, List.ofFn_succ, Fin.forall_fin_two] at h ⊢; omega
  case S3 => intro v h hv; simp [dot, List.ofFn_succ, Fin.exists_fin_two] at h hv; omega
  case next =>
    intro π hπ; simp [choices] at hπ
    rcases hπ with rfl | rfl
    -- leaf ⟨P? ↦ {wait N?}, Q? ↦ ∅ ; ∅ ; ∅⟩: COVER with unifier2, U1! := N?.
    · exact cover unifier2 (.tail _ (.head _)) fun (N?, _) _ _ =>
        ⟨N?, by simp [theta, sum, copies, ACU.plus_unit]; rfl⟩
    -- leaf ⟨P? ↦ ∅, Q? ↦ {wait N?} ; ∅ ; ∅⟩: COVER with unifier1, U1! := N?.
    · exact cover unifier1 (.head _) fun (N?, _) _ _ =>
        ⟨N?, by simp [theta, sum, copies, ACU.plus_unit]; rfl⟩

/-! ### Unknown bags on both sides
`P? + Q? = {wait N?} + R?`, original variables (N?, P?, Q?, R?).
Provided answers, both over the variables (U1!, U2!, U3!):
  σ₁: N? ↦ U1!,  P? ↦ U2!,               Q? ↦ {wait U1!} + U3!,  R? ↦ U2! + U3!
  σ₂: N? ↦ U1!,  P? ↦ {wait U1!} + U2!,  Q? ↦ U3!,               R? ↦ U2! + U3!
-/
def problem2 : Problem ProcSet (Nat × ProcSet × ProcSet × ProcSet) :=
  .bind fun (N?, P?, Q?, R?) => (P? + Q?, {.wait N?} + R?)

def unifier2_1 : Unifier (Nat × ProcSet × ProcSet × ProcSet) :=
  .bind fun (U1!, U2!, U3!) => ⟨U1!, U2!, {Mode.wait U1!} + U3!, U2! + U3!⟩

def unifier2_2 : Unifier (Nat × ProcSet × ProcSet × ProcSet) :=
  .bind fun (U1!, U2!, U3!) => ⟨U1!, {Mode.wait U1!} + U2!, U3!, U2! + U3!⟩

def solutions2 : UnifierSet (Nat × ProcSet × ProcSet × ProcSet) := [unifier2_1, unifier2_2]

example : complete problem2 solutions2 := by
  rw [← start_iff]
  -- ⟨id ; P? + Q? = {wait N?} + R? ; ∅⟩
  -- SOLVE: one alien class wait N?; per element p + q = r + 1 at wait N?, p + q = r elsewhere.
  --   P = {(1,0,0), (0,1,0)},  B = {(1,0,1), (0,1,1)}  (fresh Z1, Z2).
  refine solve (V := fun (_, P?, Q?, R?) => ![P?, Q?, R?]) (rest := fun (N?, _, _, _) => N?)
    (glue := fun N? V => (N?, V 0, V 1, V 2)) (hglue := fun _ => rfl)
    (a := fun N? => ![Mode.wait N?]) (L := ![1, 1, 0]) (R := ![0, 0, 1]) (La := ![0]) (Ra := ![1])
    (E' := fun _ => True) (P := fun _ => [![1, 0, 0], ![0, 1, 0]])
    (B := fun (j : Fin 2) => if j = 0 then ![1, 0, 1] else ![0, 1, 1])
    (cp := fun _ _ => false)
    ?hE ?S0 ?S1p ?S1b (S2_single _ _ _ _ _ ?S2) ?S3 ?next
  case hE =>
    intro ⟨N?, P?, Q?, R?⟩ h _
    have h : P? + Q? = {.wait N?} + R? := h
    refine ⟨?_, trivial, fun c c' hc _ => absurd (Subsingleton.elim c c') hc⟩
    simp [side, sum, copies, List.ofFn_succ, ACU.plus_unit, ACU.unit_plus]
    rw [h, ACU.plus_comm]
  case S0 => decide
  case S1p => decide
  case S1b => decide
  case S2 =>
    intro c v h; fin_cases c; simp [dot, List.ofFn_succ] at h
    by_cases h0 : 1 ≤ v 0
    · exact ⟨![1, 0, 0], by simp, fun i => by fin_cases i <;> (simp; try omega)⟩
    · exact ⟨![0, 1, 0], by simp, fun i => by fin_cases i <;> (simp; try omega)⟩
  case S3 =>
    intro v h hv; simp [dot, List.ofFn_succ, Fin.exists_fin_succ] at h hv
    by_cases h0 : 1 ≤ v 0
    · exact ⟨0, fun i => by fin_cases i <;> (simp; try omega)⟩
    · exact ⟨1, fun i => by fin_cases i <;> (simp; try omega)⟩
  case next =>
    intro π hπ; simp [choices] at hπ
    rcases hπ with rfl | rfl
    -- leaf ⟨P? ↦ {wait N?} + Z1, Q? ↦ Z2, R? ↦ Z1 + Z2 ; ∅ ; ∅⟩
    -- COVER with unifier2_2: U1! := N?, U2! := Z1, U3! := Z2.
    · exact cover unifier2_2 (.tail _ (.head _)) fun (N?, Z) _ _ =>
        ⟨(N?, Z 0, Z 1), by
          obtain ⟨Z1, Z2, rfl⟩ : ∃ b d, Z = ![b, d] := ⟨Z 0, Z 1, funext fun i => by fin_cases i <;> rfl⟩
          simp [theta, sum, copies, ACU.plus_unit, ACU.unit_plus]
          refine Prod.ext rfl (Prod.ext ?_ (Prod.ext ?_ ?_)) <;> ac_rfl⟩
    -- leaf ⟨P? ↦ Z1, Q? ↦ {wait N?} + Z2, R? ↦ Z1 + Z2 ; ∅ ; ∅⟩
    -- COVER with unifier2_1: U1! := N?, U2! := Z1, U3! := Z2.
    · exact cover unifier2_1 (.head _) fun (N?, Z) _ _ =>
        ⟨(N?, Z 0, Z 1), by
          obtain ⟨Z1, Z2, rfl⟩ : ∃ b d, Z = ![b, d] := ⟨Z 0, Z 1, funext fun i => by fin_cases i <;> rfl⟩
          simp [theta, sum, copies, ACU.plus_unit, ACU.unit_plus]
          refine Prod.ext rfl (Prod.ext ?_ (Prod.ext ?_ ?_)) <;> ac_rfl⟩

end TinyBakery
