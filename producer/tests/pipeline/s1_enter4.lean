import Tiny.conPanna.Unification.Certification.Tactics

/-! Rule ENTER against a state with 4 further waiting processes. -/

/- certify
{
  "namespace": "Pipeline.S1Enter4",
  "context": "Nat × ProcSet × Nat × Nat × Nat × Nat × Nat × ProcSet",
  "vars": [
    "K?",
    "P?",
    "N?",
    "M1?",
    "M2?",
    "M3?",
    "M4?",
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

namespace Pipeline.S1Enter4

inductive Mode where
  | idle
  | wait (ticket : Nat)
  | crit (ticket : Nat)

abbrev ProcSet := ACU Mode

structure Conf where
  next : Nat
  serving : Nat
  procs : ProcSet

def problem : Problem Conf (Nat × ProcSet × Nat × Nat × Nat × Nat × Nat × ProcSet) :=
  .bind fun (K?, P?, N?, M1?, M2?, M3?, M4?, Q?) =>
    (⟨K? + 1, K?, {Mode.wait K?} + P?⟩, ⟨N? + 1, N?, {Mode.wait N?} + {Mode.idle} + {Mode.wait M1?} + {Mode.wait M2?} + {Mode.wait M3?} + {Mode.wait M4?} + Q?⟩)

/-! ## Generated from s1_enter4.deriv by producer/tools/compile.py -/

def answer0 : Unifier (Nat × ProcSet × Nat × Nat × Nat × Nat × Nat × ProcSet) :=
  .bind fun (U1!, U2!, U3!, U4!, U5!) => .subst ⟨U1!, {Mode.idle} + {Mode.wait U1!} + {Mode.wait U2!} + {Mode.wait U3!} + {Mode.wait U4!} + {Mode.wait U5!}, U1!, U2!, U3!, U4!, U5!, {Mode.wait U1!}⟩
def answer1 : Unifier (Nat × ProcSet × Nat × Nat × Nat × Nat × Nat × ProcSet) :=
  .bind fun (U1!, U2!, U3!, U4!, U5!, U6!) => .subst ⟨U1!, {Mode.idle} + U6! + {Mode.wait U1!} + {Mode.wait U2!} + {Mode.wait U3!} + {Mode.wait U4!} + {Mode.wait U5!}, U1!, U2!, U3!, U4!, U5!, U6! + {Mode.wait U1!}⟩
def answer2 : Unifier (Nat × ProcSet × Nat × Nat × Nat × Nat × Nat × ProcSet) :=
  .bind fun (U1!, U2!, U3!, U4!, U5!) => .subst ⟨U1!, {Mode.idle} + {Mode.wait U2!} + {Mode.wait U3!} + {Mode.wait U4!} + {Mode.wait U5!}, U1!, U2!, U3!, U4!, U5!, ∅⟩
def answer3 : Unifier (Nat × ProcSet × Nat × Nat × Nat × Nat × Nat × ProcSet) :=
  .bind fun (U1!, U2!, U3!, U4!, U5!, U6!) => .subst ⟨U1!, {Mode.idle} + U2! + {Mode.wait U3!} + {Mode.wait U4!} + {Mode.wait U5!} + {Mode.wait U6!}, U1!, U3!, U4!, U5!, U6!, U2!⟩
def answer4 : Unifier (Nat × ProcSet × Nat × Nat × Nat × Nat × Nat × ProcSet) :=
  .bind fun (U1!, U2!, U3!, U4!) => .subst ⟨U1!, {Mode.idle} + {Mode.wait U1!} + {Mode.wait U2!} + {Mode.wait U3!} + {Mode.wait U4!}, U1!, U1!, U2!, U3!, U4!, ∅⟩
def answer5 : Unifier (Nat × ProcSet × Nat × Nat × Nat × Nat × Nat × ProcSet) :=
  .bind fun (U1!, U2!, U3!, U4!, U5!) => .subst ⟨U2!, {Mode.idle} + U1! + {Mode.wait U2!} + {Mode.wait U3!} + {Mode.wait U4!} + {Mode.wait U5!}, U2!, U2!, U3!, U4!, U5!, U1!⟩
def answer6 : Unifier (Nat × ProcSet × Nat × Nat × Nat × Nat × Nat × ProcSet) :=
  .bind fun (U1!, U2!, U3!, U4!) => .subst ⟨U2!, {Mode.idle} + {Mode.wait U1!} + {Mode.wait U2!} + {Mode.wait U3!} + {Mode.wait U4!}, U2!, U1!, U2!, U3!, U4!, ∅⟩
def answer7 : Unifier (Nat × ProcSet × Nat × Nat × Nat × Nat × Nat × ProcSet) :=
  .bind fun (U1!, U2!, U3!, U4!, U5!) => .subst ⟨U3!, {Mode.idle} + U1! + {Mode.wait U2!} + {Mode.wait U3!} + {Mode.wait U4!} + {Mode.wait U5!}, U3!, U2!, U3!, U4!, U5!, U1!⟩
def answer8 : Unifier (Nat × ProcSet × Nat × Nat × Nat × Nat × Nat × ProcSet) :=
  .bind fun (U1!, U2!, U3!, U4!) => .subst ⟨U3!, {Mode.idle} + {Mode.wait U1!} + {Mode.wait U2!} + {Mode.wait U3!} + {Mode.wait U4!}, U3!, U1!, U2!, U3!, U4!, ∅⟩
def answer9 : Unifier (Nat × ProcSet × Nat × Nat × Nat × Nat × Nat × ProcSet) :=
  .bind fun (U1!, U2!, U3!, U4!, U5!) => .subst ⟨U4!, {Mode.idle} + U1! + {Mode.wait U2!} + {Mode.wait U3!} + {Mode.wait U4!} + {Mode.wait U5!}, U4!, U2!, U3!, U4!, U5!, U1!⟩
def answer10 : Unifier (Nat × ProcSet × Nat × Nat × Nat × Nat × Nat × ProcSet) :=
  .bind fun (U1!, U2!, U3!, U4!) => .subst ⟨U4!, {Mode.idle} + {Mode.wait U1!} + {Mode.wait U2!} + {Mode.wait U3!} + {Mode.wait U4!}, U4!, U1!, U2!, U3!, U4!, ∅⟩
def answer11 : Unifier (Nat × ProcSet × Nat × Nat × Nat × Nat × Nat × ProcSet) :=
  .bind fun (U1!, U2!, U3!, U4!, U5!) => .subst ⟨U5!, {Mode.idle} + U1! + {Mode.wait U2!} + {Mode.wait U3!} + {Mode.wait U4!} + {Mode.wait U5!}, U5!, U2!, U3!, U4!, U5!, U1!⟩
def answers : UnifierSet (Nat × ProcSet × Nat × Nat × Nat × Nat × Nat × ProcSet) :=
  [answer0, answer1, answer2, answer3, answer4, answer5, answer6, answer7, answer8, answer9, answer10, answer11]

theorem complete : UnifierSet.Complete problem answers := by
  rw [← start_iff]
  -- ⊢ - | Conf.mk (K? + 1) K? ({Mode.wait K?} + P?) = Conf.mk (N? + 1) N? ({Mode.wait N?} + {Mode.idle} + {Mode.wait M1?} + {Mode.wait M2?} + {Mode.wait M3?} + {Mode.wait M4?} + Q?) | -
  -- decomp Conf.mk (K? + 1) K? ({Mode.wait K?} + P?) = Conf.mk (N? + 1) N? ({Mode.wait N?} + {Mode.idle} + {Mode.wait M1?} + {Mode.wait M2?} + {Mode.wait M3?} + {Mode.wait M4?} + Q?)
  refine decomp (fun (K?, P?, N?, M1?, M2?, M3?, M4?, Q?) => (K? + 1) = (N? + 1) ∧ K? = N? ∧ {Mode.wait K?} + P? = {Mode.wait N?} + {Mode.idle} + {Mode.wait M1?} + {Mode.wait M2?} + {Mode.wait M3?} + {Mode.wait M4?} + Q?)
      (fun (K?, P?, N?, M1?, M2?, M3?, M4?, Q?) h => by acu_free [problem]) ?_
  -- ⊢ - | (K? + 1) = (N? + 1); K? = N?; {Mode.wait K?} + P? = {Mode.wait N?} + {Mode.idle} + {Mode.wait M1?} + {Mode.wait M2?} + {Mode.wait M3?} + {Mode.wait M4?} + Q? | -
  -- decomp (K? + 1) = (N? + 1)
  refine decomp (fun (K?, P?, N?, M1?, M2?, M3?, M4?, Q?) => K? = N? ∧ K? = N? ∧ {Mode.wait K?} + P? = {Mode.wait N?} + {Mode.idle} + {Mode.wait M1?} + {Mode.wait M2?} + {Mode.wait M3?} + {Mode.wait M4?} + Q?)
      (fun (K?, P?, N?, M1?, M2?, M3?, M4?, Q?) h => by acu_free [problem]) ?_
  -- ⊢ - | K? = N?; K? = N?; {Mode.wait K?} + P? = {Mode.wait N?} + {Mode.idle} + {Mode.wait M1?} + {Mode.wait M2?} + {Mode.wait M3?} + {Mode.wait M4?} + Q? | -
  -- elim N? := K?
  refine elim (fun (K?, P?, M1?, M2?, M3?, M4?, Q?) => (K?, P?, K?, M1?, M2?, M3?, M4?, Q?))
      (fun (K?, P?, M1?, M2?, M3?, M4?, Q?) => K? = K? ∧ P? + {Mode.wait K?} = {Mode.idle} + Q? + {Mode.wait K?} + {Mode.wait M1?} + {Mode.wait M2?} + {Mode.wait M3?} + {Mode.wait M4?})
      (fun (K?, P?, N?, M1?, M2?, M3?, M4?, Q?) h => ⟨(K?, P?, M1?, M2?, M3?, M4?, Q?), by acu_free [problem], by acu_free [problem]⟩) ?_
  -- ⊢ N? := K? | K? = K?; P? + {Mode.wait K?} = {Mode.idle} + Q? + {Mode.wait K?} + {Mode.wait M1?} + {Mode.wait M2?} + {Mode.wait M3?} + {Mode.wait M4?} | -
  -- delete K? = K?
  refine decomp (fun (K?, P?, M1?, M2?, M3?, M4?, Q?) => P? + {Mode.wait K?} = {Mode.idle} + Q? + {Mode.wait K?} + {Mode.wait M1?} + {Mode.wait M2?} + {Mode.wait M3?} + {Mode.wait M4?})
      (fun (K?, P?, M1?, M2?, M3?, M4?, Q?) h => by acu_free [problem]) ?_
  -- ⊢ N? := K? | P? + {Mode.wait K?} = {Mode.idle} + Q? + {Mode.wait K?} + {Mode.wait M1?} + {Mode.wait M2?} + {Mode.wait M3?} + {Mode.wait M4?} | -
  -- solve P? + {Mode.wait K?} = {Mode.idle} + Q? + {Mode.wait K?} + {Mode.wait M1?} + {Mode.wait M2?} + {Mode.wait M3?} + {Mode.wait M4?}
  refine solve (V := fun (_, P?, _, _, _, _, Q?) => ![P?, Q?]) (rest := fun (K?, _, M1?, M2?, M3?, M4?, _) => (K?, M1?, M2?, M3?, M4?))
      (glue := fun (K?, M1?, M2?, M3?, M4?) V => (K?, V 0, M1?, M2?, M3?, M4?, V 1)) (hglue := fun _ => rfl)
      (a := fun (K?, M1?, M2?, M3?, M4?) => ![Mode.wait K?, Mode.idle, Mode.wait M1?, Mode.wait M2?, Mode.wait M3?, Mode.wait M4?]) (L := ![1, 0]) (R := ![0, 1]) (La := ![1, 0, 0, 0, 0, 0]) (Ra := ![1, 1, 1, 1, 1, 1])
      (E' := fun (_, _, _, _, _, _, _) => True) (cp := fun c c' => (c == 0 && c' == 2) || (c == 2 && c' == 0) || (c == 0 && c' == 3) || (c == 3 && c' == 0) || (c == 0 && c' == 4) || (c == 4 && c' == 0) || (c == 0 && c' == 5) || (c == 5 && c' == 0) || (c == 2 && c' == 3) || (c == 3 && c' == 2) || (c == 2 && c' == 4) || (c == 4 && c' == 2) || (c == 2 && c' == 5) || (c == 5 && c' == 2) || (c == 3 && c' == 4) || (c == 4 && c' == 3) || (c == 3 && c' == 5) || (c == 5 && c' == 3) || (c == 4 && c' == 5) || (c == 5 && c' == 4))
      (P := ![[![0, 0]], [![1, 0]], [![1, 0]], [![1, 0]], [![1, 0]], [![1, 0]]]) (B := ![![1, 1]])
      (fun (K?, P?, M1?, M2?, M3?, M4?, Q?) h hD => ⟨by try simp only [State.start, Problem.unifies, problem] at h; acu_side h, trivial, by acu_distinct⟩)
      (by decide) (by decide) (by decide)
      (S2_of_list _ _ _ _ _ _ [[0], [1], [2], [3], [4], [5], [0, 2], [0, 3], [0, 4], [0, 5], [2, 3], [2, 4], [2, 5], [3, 4], [3, 5], [4, 5], [0, 2, 3], [0, 2, 4], [0, 2, 5], [0, 3, 4], [0, 3, 5], [0, 4, 5], [2, 3, 4], [2, 3, 5], [2, 4, 5], [3, 4, 5], [0, 2, 3, 4], [0, 2, 3, 5], [0, 2, 4, 5], [0, 3, 4, 5], [2, 3, 4, 5], [0, 2, 3, 4, 5]] (by decide) (by acu_cliques)) (by acu_basis) ?_
  intro π hπ; simp [choices] at hπ; subst hπ
  -- branch (0,0) (1,0) (1,0) (1,0) (1,0) (1,0)
  refine rename (fun (K?, M1?, M2?, M3?, M4?, Z1) => ((K?, M1?, M2?, M3?, M4?), ![Z1]))
      (fun ((K?, M1?, M2?, M3?, M4?), Z) => (K?, M1?, M2?, M3?, M4?, Z 0))
      (fun ((K?, M1?, M2?, M3?, M4?), Z) => Prod.ext rfl (funext fun i => by fin_cases i; rfl)) ?_
  -- ⊢ N? := K?, P? := {Mode.idle} + Z1 + {Mode.wait M1?} + {Mode.wait M2?} + {Mode.wait M3?} + {Mode.wait M4?}, Q? := Z1 | - | -
  -- cover answer 3 with U1! := K?, U2! := Z1, U3! := M1?, U4! := M2?, U5! := M3?, U6! := M4?
  exact cover answer3 (by simp [answers]) fun (K?, M1?, M2?, M3?, M4?, Z1) _ _ => ⟨(K?, Z1, M1?, M2?, M3?, M4?), by acu_cover⟩

end Pipeline.S1Enter4
