import Tiny.conPanna.Unification.Certification.Tactics

/-!
Bakery transition: rule ENTER's left side against a three-process state. The
claim (model, problem) is written by the user; the answers and the proof below
are what the compiler emits from `enter.deriv`.
-/

open Unification Certification

namespace Demo.Enter

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

abbrev Γ₀ := Nat × ProcSet × Nat × Nat × ProcSet

-- < K?+1, K?, {wait K?} + P? >  =?  < N?+1, N?, {wait N?} + {idle} + {wait M?} + Q? >
def problem : Problem Conf Γ₀ :=
  .bind fun (K?, P?, N?, M?, Q?) =>
    (⟨K? + 1, K?, {Mode.wait K?} + P?⟩, ⟨N? + 1, N?, {Mode.wait N?} + {Mode.idle} + {Mode.wait M?} + Q?⟩)

/-! ## Generated from enter.deriv -/

def answer0 : Unifier Γ₀ := .bind fun (U1!, U2!) =>
  .subst ⟨U1!, {Mode.idle} + {Mode.wait U1!} + {Mode.wait U2!}, U1!, U2!, {Mode.wait U1!}⟩
def answer1 : Unifier Γ₀ := .bind fun (U1!, U2!, U3!) =>
  .subst ⟨U1!, {Mode.idle} + U3! + {Mode.wait U1!} + {Mode.wait U2!}, U1!, U2!, U3! + {Mode.wait U1!}⟩
def answer2 : Unifier Γ₀ := .bind fun (U1!, U2!) =>
  .subst ⟨U1!, {Mode.idle} + {Mode.wait U2!}, U1!, U2!, ∅⟩
def answer3 : Unifier Γ₀ := .bind fun (U1!, U2!, U3!) =>
  .subst ⟨U1!, {Mode.idle} + U2! + {Mode.wait U3!}, U1!, U3!, U2!⟩
def answer4 : Unifier Γ₀ := .bind fun U1! =>
  .subst ⟨U1!, {Mode.idle} + {Mode.wait U1!}, U1!, U1!, ∅⟩
def answer5 : Unifier Γ₀ := .bind fun (U1!, U2!) =>
  .subst ⟨U2!, {Mode.idle} + U1! + {Mode.wait U2!}, U2!, U2!, U1!⟩
def answers : UnifierSet Γ₀ := [answer0, answer1, answer2, answer3, answer4, answer5]

theorem complete : UnifierSet.Complete problem answers := by
  rw [← start_iff]
  -- ⊢ - | Conf(K?+1, K?, {wait(K?)} + P?) = Conf(N?+1, N?, {wait(N?)} + {idle} + {wait(M?)} + Q?) | -
  -- decomp  ==>  K?+1 = N?+1; K? = N?; {wait(K?)} + P? = {wait(N?)} + {idle} + {wait(M?)} + Q?
  refine decomp (fun (K?, P?, N?, M?, Q?) => K? + 1 = N? + 1 ∧ K? = N? ∧
      {Mode.wait K?} + P? = {Mode.wait N?} + {Mode.idle} + {Mode.wait M?} + Q?)
    (fun (K?, P?, N?, M?, Q?) h => by acu_free [problem]) ?_
  -- decomp K?+1 = N?+1  ==>  K? = N?
  refine decomp (fun (K?, P?, N?, M?, Q?) => K? = N? ∧ K? = N? ∧
      {Mode.wait K?} + P? = {Mode.wait N?} + {Mode.idle} + {Mode.wait M?} + Q?)
    (fun (K?, P?, N?, M?, Q?) h => by acu_free) ?_
  -- elim N? := K?
  refine elim (fun (K?, P?, M?, Q?) => (K?, P?, K?, M?, Q?))
    (fun (K?, P?, M?, Q?) => K? = K? ∧
      P? + {Mode.wait K?} = {Mode.idle} + Q? + {Mode.wait M?} + {Mode.wait K?})
    (fun (K?, P?, N?, M?, Q?) h => ⟨(K?, P?, M?, Q?), by acu_free, by acu_free⟩) ?_
  -- delete K? = K?
  refine decomp (fun (K?, P?, M?, Q?) =>
      P? + {Mode.wait K?} = {Mode.idle} + Q? + {Mode.wait M?} + {Mode.wait K?})
    (fun (K?, P?, M?, Q?) h => by acu_free) ?_
  -- ⊢ N? := K? | P? + {wait(K?)} = {idle} + Q? + {wait(M?)} + {wait(K?)} | -
  -- solve: aliens wait(K?) idle wait(M?), compatible 0~2
  refine solve (V := fun (_, P?, _, Q?) => ![P?, Q?]) (rest := fun (K?, _, M?, _) => (K?, M?))
    (glue := fun (K?, M?) V => (K?, V 0, M?, V 1)) (hglue := fun _ => rfl)
    (a := fun (K?, M?) => ![Mode.wait K?, Mode.idle, Mode.wait M?])
    (L := ![1, 0]) (R := ![0, 1]) (La := ![1, 0, 0]) (Ra := ![1, 1, 1])
    (E' := fun _ => True) (cp := fun c c' => (c == 0 && c' == 2) || (c == 2 && c' == 0))
    (P := ![[![0, 0]], [![1, 0]], [![1, 0]]]) (B := ![![1, 1]])
    (fun (K?, P?, M?, Q?) h _ => ⟨by acu_side h, trivial, by acu_distinct⟩)
    (by decide) (by decide) (by decide)
    (S2_of_list _ _ _ _ _ _ [[0], [1], [2], [0, 2]] (by decide) (by acu_cliques)) (by acu_basis) ?_
  intro π hπ; simp [choices] at hπ; subst hπ
  -- branch [(0,0) (1,0) (1,0)]: P? := {idle} + Z1 + {wait(M?)}, Q? := Z1
  -- cover answer 3 with U1! := K?, U2! := Z1, U3! := M?
  exact cover answer3 (by simp [answers]) fun ((K?, M?), Z) _ _ => by
    obtain ⟨Z1, rfl⟩ : ∃ a, Z = ![a] := ⟨Z 0, funext fun i => by fin_cases i; rfl⟩
    exact ⟨(K?, Z1, M?), by acu_cover⟩

end Demo.Enter
