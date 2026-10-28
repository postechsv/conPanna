import conPanna.Unification.Certification.Tactics

/-!
Bakery, the L137 example. The claim (model, problem) is written by the user;
the compiler appends the answers and the proof, from `l137.deriv`.
-/

/- certify
{
  "namespace": "Demo.L137",
  "context": "Nat × ProcSet × ProcSet",
  "vars": [
    "N?",
    "P?",
    "Q?"
  ],
  "ops": {
    "<_,_,_>": "Conf.mk",
    "s": "({0} + 1)",
    "wait": "Mode.wait",
    "idle": "Mode.idle",
    "crit": "Mode.crit"
  }
}
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

/-! ## Generated from l137.deriv by producer/tools/compile.py -/

def answer0 : Unifier (Nat × ProcSet × ProcSet) :=
  .bind fun U1! => ⟨U1!, ∅, {Mode.wait U1!}⟩
def answer1 : Unifier (Nat × ProcSet × ProcSet) :=
  .bind fun U1! => ⟨U1!, {Mode.wait U1!}, ∅⟩
def answers : UnifierSet (Nat × ProcSet × ProcSet) :=
  [answer0, answer1]

theorem complete : Unification.complete problem answers := by
  rw [← start_iff]
  -- ⊢ - | Conf.mk (N? + 1) N? (P? + Q?) = Conf.mk (N? + 1) N? {Mode.wait N?} | -
  checkpoint
  -- decomp Conf.mk (N? + 1) N? (P? + Q?) = Conf.mk (N? + 1) N? {Mode.wait N?}
  refine decomp [fun (N?, _, _) => (N? + 1) = (N? + 1), fun (N?, _, _) => N? = N?, fun (N?, P?, Q?) => P? + Q? = {Mode.wait N?}]
      (fun (N?, P?, Q?) h => by acu_decomp [problem, Conf.mk.injEq]) ?_
  -- ⊢ - | (N? + 1) = (N? + 1); N? = N?; P? + Q? = {Mode.wait N?} | -
  checkpoint
  -- delete (N? + 1) = (N? + 1)
  refine delete ?_
  -- ⊢ - | N? = N?; P? + Q? = {Mode.wait N?} | -
  checkpoint
  -- delete N? = N?
  refine delete ?_
  -- ⊢ - | P? + Q? = {Mode.wait N?} | -
  checkpoint
  -- solve P? + Q? = {Mode.wait N?}
  refine solve
      { V := fun (_, P?, Q?) => ![P?, Q?], rest := fun (N?, _, _) => N?,
        glue := fun N? V => (N?, V 0, V 1), hglue := fun _ => rfl }
      (fun N? => ![Mode.wait N?])
      { L := ![1, 1], R := ![0, 0], La := ![0], Ra := ![1], cp := fun _ _ => false }
      { P := ![[![1, 0], ![0, 1]]], B := ![] }
      ⟨by decide, by decide, by decide,
        S2_of_list _ _ _ _ _ _ [[0]] (by decide) (by acu_cliques), by acu_basis⟩
      (fun (N?, P?, Q?) h => by try simp only [unifiedBy, problem] at h; acu_side h)
      (fun (N?, P?, Q?) h hD => by acu_distinct) ?_
  intro π hπ; simp [choices] at hπ; rcases hπ with rfl | rfl
  · -- branch (1,0)
    refine rename (fun N? => (N?, ![]))
        (fun (N?, Z) => N?)
        (fun (N?, Z) => Prod.ext rfl (funext fun i => i.elim0)) ?_
    -- ⊢ P? := {Mode.wait N?}, Q? := ∅ | - | -
    checkpoint
    -- cover answer 1 with U1! := N?
    exact cover answer1 (by simp [answers]) fun N? _ _ => ⟨N?, by acu_cover⟩
  · -- branch (0,1)
    refine rename (fun N? => (N?, ![]))
        (fun (N?, Z) => N?)
        (fun (N?, Z) => Prod.ext rfl (funext fun i => i.elim0)) ?_
    -- ⊢ P? := ∅, Q? := {Mode.wait N?} | - | -
    checkpoint
    -- cover answer 0 with U1! := N?
    exact cover answer0 (by simp [answers]) fun N? _ _ => ⟨N?, by acu_cover⟩

end Demo.L137
