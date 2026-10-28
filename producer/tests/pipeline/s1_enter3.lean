import conPanna.Unification.Certification.Tactics

/-! Rule ENTER against a state with 3 further waiting processes. -/

/- certify
{
  "namespace": "Pipeline.S1Enter3",
  "context": "Nat × ProcSet × Nat × Nat × Nat × Nat × ProcSet",
  "vars": [
    "K?",
    "P?",
    "N?",
    "M1?",
    "M2?",
    "M3?",
    "Q?"
  ],
  "ops": {
    "<_,_,_>": "Conf.mk",
    "s": "({0} + 1)",
    "z": "0",
    "wait": "Mode.wait",
    "idle": "Mode.idle",
    "crit": "Mode.crit"
  }
}
-/

open Unification Certification

namespace Pipeline.S1Enter3

inductive Mode where
  | idle
  | wait (ticket : Nat)
  | crit (ticket : Nat)

abbrev ProcSet := ACU Mode

structure Conf where
  next : Nat
  serving : Nat
  procs : ProcSet

def problem : Problem Conf (Nat × ProcSet × Nat × Nat × Nat × Nat × ProcSet) :=
  .bind fun (K?, P?, N?, M1?, M2?, M3?, Q?) =>
    (⟨K? + 1, K?, {Mode.wait K?} + P?⟩, ⟨N? + 1, N?, {Mode.wait N?} + {Mode.idle} + {Mode.wait M1?} + {Mode.wait M2?} + {Mode.wait M3?} + Q?⟩)

/-! ## Generated from s1_enter3.deriv by producer/tools/compile.py -/

def answer0 : Unifier (Nat × ProcSet × Nat × Nat × Nat × Nat × ProcSet) :=
  .bind fun (U1!, U2!, U3!, U4!) => ⟨U1!, {Mode.idle} + {Mode.wait U1!} + {Mode.wait U2!} + {Mode.wait U3!} + {Mode.wait U4!}, U1!, U2!, U3!, U4!, {Mode.wait U1!}⟩
def answer1 : Unifier (Nat × ProcSet × Nat × Nat × Nat × Nat × ProcSet) :=
  .bind fun (U1!, U2!, U3!, U4!, U5!) => ⟨U1!, {Mode.idle} + U5! + {Mode.wait U1!} + {Mode.wait U2!} + {Mode.wait U3!} + {Mode.wait U4!}, U1!, U2!, U3!, U4!, U5! + {Mode.wait U1!}⟩
def answer2 : Unifier (Nat × ProcSet × Nat × Nat × Nat × Nat × ProcSet) :=
  .bind fun (U1!, U2!, U3!, U4!) => ⟨U1!, {Mode.idle} + {Mode.wait U2!} + {Mode.wait U3!} + {Mode.wait U4!}, U1!, U2!, U3!, U4!, ∅⟩
def answer3 : Unifier (Nat × ProcSet × Nat × Nat × Nat × Nat × ProcSet) :=
  .bind fun (U1!, U2!, U3!, U4!, U5!) => ⟨U1!, {Mode.idle} + U2! + {Mode.wait U3!} + {Mode.wait U4!} + {Mode.wait U5!}, U1!, U3!, U4!, U5!, U2!⟩
def answer4 : Unifier (Nat × ProcSet × Nat × Nat × Nat × Nat × ProcSet) :=
  .bind fun (U1!, U2!, U3!) => ⟨U1!, {Mode.idle} + {Mode.wait U1!} + {Mode.wait U2!} + {Mode.wait U3!}, U1!, U1!, U2!, U3!, ∅⟩
def answer5 : Unifier (Nat × ProcSet × Nat × Nat × Nat × Nat × ProcSet) :=
  .bind fun (U1!, U2!, U3!, U4!) => ⟨U2!, {Mode.idle} + U1! + {Mode.wait U2!} + {Mode.wait U3!} + {Mode.wait U4!}, U2!, U2!, U3!, U4!, U1!⟩
def answer6 : Unifier (Nat × ProcSet × Nat × Nat × Nat × Nat × ProcSet) :=
  .bind fun (U1!, U2!, U3!) => ⟨U2!, {Mode.idle} + {Mode.wait U1!} + {Mode.wait U2!} + {Mode.wait U3!}, U2!, U1!, U2!, U3!, ∅⟩
def answer7 : Unifier (Nat × ProcSet × Nat × Nat × Nat × Nat × ProcSet) :=
  .bind fun (U1!, U2!, U3!, U4!) => ⟨U3!, {Mode.idle} + U1! + {Mode.wait U2!} + {Mode.wait U3!} + {Mode.wait U4!}, U3!, U2!, U3!, U4!, U1!⟩
def answer8 : Unifier (Nat × ProcSet × Nat × Nat × Nat × Nat × ProcSet) :=
  .bind fun (U1!, U2!, U3!) => ⟨U3!, {Mode.idle} + {Mode.wait U1!} + {Mode.wait U2!} + {Mode.wait U3!}, U3!, U1!, U2!, U3!, ∅⟩
def answer9 : Unifier (Nat × ProcSet × Nat × Nat × Nat × Nat × ProcSet) :=
  .bind fun (U1!, U2!, U3!, U4!) => ⟨U4!, {Mode.idle} + U1! + {Mode.wait U2!} + {Mode.wait U3!} + {Mode.wait U4!}, U4!, U2!, U3!, U4!, U1!⟩
def answers : UnifierSet (Nat × ProcSet × Nat × Nat × Nat × Nat × ProcSet) :=
  [answer0, answer1, answer2, answer3, answer4, answer5, answer6, answer7, answer8, answer9]

theorem complete : Unification.complete problem answers := by
  rw [← start_iff]
  -- ⊢ - | Conf.mk (K? + 1) K? ({Mode.wait K?} + P?) = Conf.mk (N? + 1) N? ({Mode.wait N?} + {Mode.idle} + {Mode.wait M1?} + {Mode.wait M2?} + {Mode.wait M3?} + Q?) | -
  checkpoint
  -- decomp Conf.mk (K? + 1) K? ({Mode.wait K?} + P?) = Conf.mk (N? + 1) N? ({Mode.wait N?} + {Mode.idle} + {Mode.wait M1?} + {Mode.wait M2?} + {Mode.wait M3?} + Q?)
  refine decomp [fun (K?, _, N?, _, _, _, _) => (K? + 1) = (N? + 1), fun (K?, _, N?, _, _, _, _) => K? = N?, fun (K?, P?, N?, M1?, M2?, M3?, Q?) => {Mode.wait K?} + P? = {Mode.wait N?} + {Mode.idle} + {Mode.wait M1?} + {Mode.wait M2?} + {Mode.wait M3?} + Q?]
      (fun (K?, P?, N?, M1?, M2?, M3?, Q?) h => by acu_decomp [problem, Conf.mk.injEq]) ?_
  -- ⊢ - | (K? + 1) = (N? + 1); K? = N?; {Mode.wait K?} + P? = {Mode.wait N?} + {Mode.idle} + {Mode.wait M1?} + {Mode.wait M2?} + {Mode.wait M3?} + Q? | -
  checkpoint
  -- decomp (K? + 1) = (N? + 1)
  refine decomp [fun (K?, _, N?, _, _, _, _) => K? = N?]
      (fun (K?, P?, N?, M1?, M2?, M3?, Q?) h => by acu_decomp [problem]) ?_
  -- ⊢ - | K? = N?; K? = N?; {Mode.wait K?} + P? = {Mode.wait N?} + {Mode.idle} + {Mode.wait M1?} + {Mode.wait M2?} + {Mode.wait M3?} + Q? | -
  checkpoint
  -- elim N? := K?
  refine elim (fun (K?, P?, M1?, M2?, M3?, Q?) => (K?, P?, K?, M1?, M2?, M3?, Q?))
      (fun (K?, P?, N?, M1?, M2?, M3?, Q?) h => ⟨(K?, P?, M1?, M2?, M3?, Q?), by acu_elim [problem]⟩) ?_
  -- ⊢ N? := K? | K? = K?; P? + {Mode.wait K?} = {Mode.idle} + Q? + {Mode.wait K?} + {Mode.wait M1?} + {Mode.wait M2?} + {Mode.wait M3?} | -
  checkpoint
  -- delete K? = K?
  refine delete ?_
  -- ⊢ N? := K? | P? + {Mode.wait K?} = {Mode.idle} + Q? + {Mode.wait K?} + {Mode.wait M1?} + {Mode.wait M2?} + {Mode.wait M3?} | -
  checkpoint
  -- solve P? + {Mode.wait K?} = {Mode.idle} + Q? + {Mode.wait K?} + {Mode.wait M1?} + {Mode.wait M2?} + {Mode.wait M3?}
  refine solve
      { V := fun (_, P?, _, _, _, Q?) => ![P?, Q?], rest := fun (K?, _, M1?, M2?, M3?, _) => (K?, M1?, M2?, M3?),
        glue := fun (K?, M1?, M2?, M3?) V => (K?, V 0, M1?, M2?, M3?, V 1), hglue := fun _ => rfl }
      (fun (K?, M1?, M2?, M3?) => ![Mode.wait K?, Mode.idle, Mode.wait M1?, Mode.wait M2?, Mode.wait M3?])
      { L := ![1, 0], R := ![0, 1], La := ![1, 0, 0, 0, 0], Ra := ![1, 1, 1, 1, 1], cp := fun c c' => (c == 0 && c' == 2) || (c == 2 && c' == 0) || (c == 0 && c' == 3) || (c == 3 && c' == 0) || (c == 0 && c' == 4) || (c == 4 && c' == 0) || (c == 2 && c' == 3) || (c == 3 && c' == 2) || (c == 2 && c' == 4) || (c == 4 && c' == 2) || (c == 3 && c' == 4) || (c == 4 && c' == 3) }
      { P := ![[![0, 0]], [![1, 0]], [![1, 0]], [![1, 0]], [![1, 0]]], B := ![![1, 1]] }
      ⟨by decide, by decide, by decide,
        S2_of_list _ _ _ _ _ _ [[0], [1], [2], [3], [4], [0, 2], [0, 3], [0, 4], [2, 3], [2, 4], [3, 4], [0, 2, 3], [0, 2, 4], [0, 3, 4], [2, 3, 4], [0, 2, 3, 4]] (by decide) (by acu_cliques), by acu_basis⟩
      (fun (K?, P?, M1?, M2?, M3?, Q?) h => by try simp only [unifiedBy, problem] at h; acu_side h)
      (fun (K?, P?, M1?, M2?, M3?, Q?) h hD => by acu_distinct) ?_
  intro π hπ; simp [choices] at hπ; subst hπ
  -- branch (0,0) (1,0) (1,0) (1,0) (1,0)
  refine rename (fun (K?, M1?, M2?, M3?, Z1) => ((K?, M1?, M2?, M3?), ![Z1]))
      (fun ((K?, M1?, M2?, M3?), Z) => (K?, M1?, M2?, M3?, Z 0))
      (fun ((K?, M1?, M2?, M3?), Z) => Prod.ext rfl (funext fun i => by fin_cases i; rfl)) ?_
  -- ⊢ N? := K?, P? := {Mode.idle} + Z1 + {Mode.wait M1?} + {Mode.wait M2?} + {Mode.wait M3?}, Q? := Z1 | - | -
  checkpoint
  -- cover answer 3 with U1! := K?, U2! := Z1, U3! := M1?, U4! := M2?, U5! := M3?
  exact cover answer3 (by simp [answers]) fun (K?, M1?, M2?, M3?, Z1) _ _ => ⟨(K?, Z1, M1?, M2?, M3?), by acu_cover⟩

end Pipeline.S1Enter3
