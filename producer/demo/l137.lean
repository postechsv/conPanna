import Tiny.conPanna.Unification.Certification.Tactics

/-!
Bakery, the L137 example. The claim (model, problem) is written by the user;
the answers and the proof below are what the compiler emits from `l137.deriv`.
-/

open Unification Certification

namespace Demo.L137

/-! ## Claim -/

inductive Mode where
  | idle
  | wait (ticket : Nat)
  | crit (ticket : Nat)

abbrev ProcSet := ACU Mode

structure Conf where
  next : Nat
  serving : Nat
  procs : ProcSet

def problem : Problem Conf (Nat × ProcSet × ProcSet) :=
  .bind fun (N?, P?, Q?) => (⟨N? + 1, N?, P? + Q?⟩, ⟨N? + 1, N?, {.wait N?}⟩)

/-! ## Generated from l137.deriv -/

def answer0 : Unifier (Nat × ProcSet × ProcSet) :=
  .bind fun U1! => .subst ⟨U1!, ∅, {Mode.wait U1!}⟩
def answer1 : Unifier (Nat × ProcSet × ProcSet) :=
  .bind fun U1! => .subst ⟨U1!, {Mode.wait U1!}, ∅⟩
def answers : UnifierSet (Nat × ProcSet × ProcSet) := [answer0, answer1]

theorem complete : UnifierSet.Complete problem answers := by
  rw [← start_iff]
  -- ⊢ - | Conf(N?+1, N?, P? + Q?) = Conf(N?+1, N?, {wait(N?)}) | -
  -- decomp  ==>  N?+1 = N?+1; N? = N?; P? + Q? = {wait(N?)}
  refine decomp (fun (N?, P?, Q?) => N? + 1 = N? + 1 ∧ N? = N? ∧ P? + Q? = {Mode.wait N?})
    (fun (N?, P?, Q?) h => by acu_free [problem]) ?_
  -- delete N?+1 = N?+1
  refine decomp (fun (N?, P?, Q?) => N? = N? ∧ P? + Q? = {Mode.wait N?})
    (fun (N?, P?, Q?) h => by acu_free) ?_
  -- delete N? = N?
  refine decomp (fun (N?, P?, Q?) => P? + Q? = {Mode.wait N?})
    (fun (N?, P?, Q?) h => by acu_free) ?_
  -- ⊢ - | P? + Q? = {wait(N?)} | -
  -- solve P? + Q? = {wait(N?)}
  refine solve (V := fun (_, P?, Q?) => ![P?, Q?]) (rest := fun (N?, _, _) => N?)
    (glue := fun N? V => (N?, V 0, V 1)) (hglue := fun _ => rfl)
    (a := fun N? => ![Mode.wait N?]) (L := ![1, 1]) (R := ![0, 0]) (La := ![0]) (Ra := ![1])
    (E' := fun _ => True) (cp := fun _ _ => false) (P := ![[![1, 0], ![0, 1]]]) (B := ![])
    (fun (N?, P?, Q?) h _ => ⟨by acu_side h, trivial, by acu_distinct⟩)
    (by decide) (by decide) (by decide)
    (S2_of_list _ _ _ _ _ _ [[0]] (by decide) (by acu_cliques)) (by acu_basis) ?_
  intro π hπ; simp [choices] at hπ; rcases hπ with rfl | rfl
  · -- branch [(1,0)]: P? := {wait(N?)}, Q? := ∅
    -- cover answer 1 with U1! := N?
    exact cover answer1 (by simp [answers]) fun (N?, Z) _ _ => ⟨N?, by acu_cover⟩
  · -- branch [(0,1)]: P? := ∅, Q? := {wait(N?)}
    -- cover answer 0 with U1! := N?
    exact cover answer0 (by simp [answers]) fun (N?, Z) _ _ => ⟨N?, by acu_cover⟩

end Demo.L137
