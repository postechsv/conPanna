import conPanna.Unification.Certification.Tactics

/-! Rule ENTER against a state with 2 further waiting processes. -/

/- certify
{
  "namespace": "Pipeline.S1Enter2",
  "context": "Nat × ProcSet × Nat × Nat × Nat × ProcSet",
  "vars": [
    "K?",
    "P?",
    "N?",
    "M1?",
    "M2?",
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

namespace Pipeline.S1Enter2

inductive Mode where
  | idle
  | wait (ticket : Nat)
  | crit (ticket : Nat)

abbrev ProcSet := ACU Mode

structure Conf where
  next : Nat
  serving : Nat
  procs : ProcSet

def problem : Problem Conf (Nat × ProcSet × Nat × Nat × Nat × ProcSet) :=
  .bind fun (K?, P?, N?, M1?, M2?, Q?) =>
    (⟨K? + 1, K?, {Mode.wait K?} + P?⟩, ⟨N? + 1, N?, {Mode.wait N?} + {Mode.idle} + {Mode.wait M1?} + {Mode.wait M2?} + Q?⟩)

/-! ## Generated from s1_enter2.deriv by producer/tools/compile.py -/

def answer0 : Unifier (Nat × ProcSet × Nat × Nat × Nat × ProcSet) :=
  .bind fun (U1!, U2!, U3!) => ⟨U1!, {Mode.idle} + {Mode.wait U1!} + {Mode.wait U2!} + {Mode.wait U3!}, U1!, U2!, U3!, {Mode.wait U1!}⟩
def answer1 : Unifier (Nat × ProcSet × Nat × Nat × Nat × ProcSet) :=
  .bind fun (U1!, U2!, U3!, U4!) => ⟨U1!, {Mode.idle} + U4! + {Mode.wait U1!} + {Mode.wait U2!} + {Mode.wait U3!}, U1!, U2!, U3!, U4! + {Mode.wait U1!}⟩
def answer2 : Unifier (Nat × ProcSet × Nat × Nat × Nat × ProcSet) :=
  .bind fun (U1!, U2!, U3!) => ⟨U1!, {Mode.idle} + {Mode.wait U2!} + {Mode.wait U3!}, U1!, U2!, U3!, ∅⟩
def answer3 : Unifier (Nat × ProcSet × Nat × Nat × Nat × ProcSet) :=
  .bind fun (U1!, U2!, U3!, U4!) => ⟨U1!, {Mode.idle} + U2! + {Mode.wait U3!} + {Mode.wait U4!}, U1!, U3!, U4!, U2!⟩
def answer4 : Unifier (Nat × ProcSet × Nat × Nat × Nat × ProcSet) :=
  .bind fun (U1!, U2!) => ⟨U1!, {Mode.idle} + {Mode.wait U1!} + {Mode.wait U2!}, U1!, U1!, U2!, ∅⟩
def answer5 : Unifier (Nat × ProcSet × Nat × Nat × Nat × ProcSet) :=
  .bind fun (U1!, U2!, U3!) => ⟨U2!, {Mode.idle} + U1! + {Mode.wait U2!} + {Mode.wait U3!}, U2!, U2!, U3!, U1!⟩
def answer6 : Unifier (Nat × ProcSet × Nat × Nat × Nat × ProcSet) :=
  .bind fun (U1!, U2!) => ⟨U2!, {Mode.idle} + {Mode.wait U1!} + {Mode.wait U2!}, U2!, U1!, U2!, ∅⟩
def answer7 : Unifier (Nat × ProcSet × Nat × Nat × Nat × ProcSet) :=
  .bind fun (U1!, U2!, U3!) => ⟨U3!, {Mode.idle} + U1! + {Mode.wait U2!} + {Mode.wait U3!}, U3!, U2!, U3!, U1!⟩
def answers : UnifierSet (Nat × ProcSet × Nat × Nat × Nat × ProcSet) :=
  [answer0, answer1, answer2, answer3, answer4, answer5, answer6, answer7]

theorem complete : Unification.complete problem answers := by
  rw [← start_iff]
  -- ⊢ - | Conf.mk (K? + 1) K? ({Mode.wait K?} + P?) = Conf.mk (N? + 1) N? ({Mode.wait N?} + {Mode.idle} + {Mode.wait M1?} + {Mode.wait M2?} + Q?) | -
  checkpoint
  -- decomp Conf.mk (K? + 1) K? ({Mode.wait K?} + P?) = Conf.mk (N? + 1) N? ({Mode.wait N?} + {Mode.idle} + {Mode.wait M1?} + {Mode.wait M2?} + Q?)
  refine decomp (fun (K?, P?, N?, M1?, M2?, Q?) => (K? + 1) = (N? + 1) ∧ K? = N? ∧ {Mode.wait K?} + P? = {Mode.wait N?} + {Mode.idle} + {Mode.wait M1?} + {Mode.wait M2?} + Q?)
      (fun (K?, P?, N?, M1?, M2?, Q?) h => by acu_free [problem]) ?_
  -- ⊢ - | (K? + 1) = (N? + 1); K? = N?; {Mode.wait K?} + P? = {Mode.wait N?} + {Mode.idle} + {Mode.wait M1?} + {Mode.wait M2?} + Q? | -
  checkpoint
  -- decomp (K? + 1) = (N? + 1)
  refine decomp (fun (K?, P?, N?, M1?, M2?, Q?) => K? = N? ∧ K? = N? ∧ {Mode.wait K?} + P? = {Mode.wait N?} + {Mode.idle} + {Mode.wait M1?} + {Mode.wait M2?} + Q?)
      (fun (K?, P?, N?, M1?, M2?, Q?) h => by acu_free [problem]) ?_
  -- ⊢ - | K? = N?; K? = N?; {Mode.wait K?} + P? = {Mode.wait N?} + {Mode.idle} + {Mode.wait M1?} + {Mode.wait M2?} + Q? | -
  checkpoint
  -- elim N? := K?
  refine elim (fun (K?, P?, M1?, M2?, Q?) => (K?, P?, K?, M1?, M2?, Q?))
      (fun (K?, P?, M1?, M2?, Q?) => K? = K? ∧ P? + {Mode.wait K?} = {Mode.idle} + Q? + {Mode.wait K?} + {Mode.wait M1?} + {Mode.wait M2?})
      (fun (K?, P?, N?, M1?, M2?, Q?) h => ⟨(K?, P?, M1?, M2?, Q?), by acu_free [problem], by acu_free [problem]⟩) ?_
  -- ⊢ N? := K? | K? = K?; P? + {Mode.wait K?} = {Mode.idle} + Q? + {Mode.wait K?} + {Mode.wait M1?} + {Mode.wait M2?} | -
  checkpoint
  -- delete K? = K?
  refine decomp (fun (K?, P?, M1?, M2?, Q?) => P? + {Mode.wait K?} = {Mode.idle} + Q? + {Mode.wait K?} + {Mode.wait M1?} + {Mode.wait M2?})
      (fun (K?, P?, M1?, M2?, Q?) h => by acu_free [problem]) ?_
  -- ⊢ N? := K? | P? + {Mode.wait K?} = {Mode.idle} + Q? + {Mode.wait K?} + {Mode.wait M1?} + {Mode.wait M2?} | -
  checkpoint
  -- solve P? + {Mode.wait K?} = {Mode.idle} + Q? + {Mode.wait K?} + {Mode.wait M1?} + {Mode.wait M2?}
  refine solve (V := fun (_, P?, _, _, Q?) => ![P?, Q?]) (rest := fun (K?, _, M1?, M2?, _) => (K?, M1?, M2?))
      (glue := fun (K?, M1?, M2?) V => (K?, V 0, M1?, M2?, V 1)) (hglue := fun _ => rfl)
      (a := fun (K?, M1?, M2?) => ![Mode.wait K?, Mode.idle, Mode.wait M1?, Mode.wait M2?]) (L := ![1, 0]) (R := ![0, 1]) (La := ![1, 0, 0, 0]) (Ra := ![1, 1, 1, 1])
      (E' := fun (_, _, _, _, _) => True) (cp := fun c c' => (c == 0 && c' == 2) || (c == 2 && c' == 0) || (c == 0 && c' == 3) || (c == 3 && c' == 0) || (c == 2 && c' == 3) || (c == 3 && c' == 2))
      (P := ![[![0, 0]], [![1, 0]], [![1, 0]], [![1, 0]]]) (B := ![![1, 1]])
      (fun (K?, P?, M1?, M2?, Q?) h hD => ⟨by try simp only [State.start, unifiedBy, problem] at h; acu_side h, trivial, by acu_distinct⟩)
      (by decide) (by decide) (by decide)
      (S2_of_list _ _ _ _ _ _ [[0], [1], [2], [3], [0, 2], [0, 3], [2, 3], [0, 2, 3]] (by decide) (by acu_cliques)) (by acu_basis) ?_
  intro π hπ; simp [choices] at hπ; subst hπ
  -- branch (0,0) (1,0) (1,0) (1,0)
  refine rename (fun (K?, M1?, M2?, Z1) => ((K?, M1?, M2?), ![Z1]))
      (fun ((K?, M1?, M2?), Z) => (K?, M1?, M2?, Z 0))
      (fun ((K?, M1?, M2?), Z) => Prod.ext rfl (funext fun i => by fin_cases i; rfl)) ?_
  -- ⊢ N? := K?, P? := {Mode.idle} + Z1 + {Mode.wait M1?} + {Mode.wait M2?}, Q? := Z1 | - | -
  checkpoint
  -- cover answer 3 with U1! := K?, U2! := Z1, U3! := M1?, U4! := M2?
  exact cover answer3 (by simp [answers]) fun (K?, M1?, M2?, Z1) _ _ => ⟨(K?, Z1, M1?, M2?), by acu_cover⟩

end Pipeline.S1Enter2
