import conPanna.Unification.Certification.Tactics

/-!
Bakery transition: rule ENTER's left side against a three-process state. The
claim (model, problem) is written by the user;
producer/tools/compile.py appends the answers and the proof from `enter.deriv`.
-/

/- certify
{
  "namespace": "Demo.Enter",
  "context": "Γ₀",
  "vars": [
    "K?",
    "P?",
    "N?",
    "M?",
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

/-! ## Generated from enter.deriv by producer/tools/compile.py -/

def answer0 : Unifier (Γ₀) :=
  .bind fun (U1!, U2!) => ⟨U1!, {Mode.idle} + {Mode.wait U1!} + {Mode.wait U2!}, U1!, U2!, {Mode.wait U1!}⟩
def answer1 : Unifier (Γ₀) :=
  .bind fun (U1!, U2!, U3!) => ⟨U1!, {Mode.idle} + U3! + {Mode.wait U1!} + {Mode.wait U2!}, U1!, U2!, U3! + {Mode.wait U1!}⟩
def answer2 : Unifier (Γ₀) :=
  .bind fun (U1!, U2!) => ⟨U1!, {Mode.idle} + {Mode.wait U2!}, U1!, U2!, ∅⟩
def answer3 : Unifier (Γ₀) :=
  .bind fun (U1!, U2!, U3!) => ⟨U1!, {Mode.idle} + U2! + {Mode.wait U3!}, U1!, U3!, U2!⟩
def answer4 : Unifier (Γ₀) :=
  .bind fun U1! => ⟨U1!, {Mode.idle} + {Mode.wait U1!}, U1!, U1!, ∅⟩
def answer5 : Unifier (Γ₀) :=
  .bind fun (U1!, U2!) => ⟨U2!, {Mode.idle} + U1! + {Mode.wait U2!}, U2!, U2!, U1!⟩
def answers : UnifierSet (Γ₀) :=
  [answer0, answer1, answer2, answer3, answer4, answer5]

theorem complete : Unification.complete problem answers := by
  rw [← start_iff]
  -- ⊢ - | Conf.mk (K? + 1) K? ({Mode.wait K?} + P?) = Conf.mk (N? + 1) N? ({Mode.wait N?} + {Mode.idle} + {Mode.wait M?} + Q?) | -
  checkpoint
  -- decomp Conf.mk (K? + 1) K? ({Mode.wait K?} + P?) = Conf.mk (N? + 1) N? ({Mode.wait N?} + {Mode.idle} + {Mode.wait M?} + Q?)
  refine decomp [fun (K?, _, N?, _, _) => (K? + 1) = (N? + 1), fun (K?, _, N?, _, _) => K? = N?, fun (K?, P?, N?, M?, Q?) => {Mode.wait K?} + P? = {Mode.wait N?} + {Mode.idle} + {Mode.wait M?} + Q?]
      (fun (K?, P?, N?, M?, Q?) h => by acu_decomp [problem, Conf.mk.injEq]) ?_
  -- ⊢ - | (K? + 1) = (N? + 1); K? = N?; {Mode.wait K?} + P? = {Mode.wait N?} + {Mode.idle} + {Mode.wait M?} + Q? | -
  checkpoint
  -- decomp (K? + 1) = (N? + 1)
  refine decomp [fun (K?, _, N?, _, _) => K? = N?]
      (fun (K?, P?, N?, M?, Q?) h => by acu_decomp [problem]) ?_
  -- ⊢ - | K? = N?; K? = N?; {Mode.wait K?} + P? = {Mode.wait N?} + {Mode.idle} + {Mode.wait M?} + Q? | -
  checkpoint
  -- elim N? := K?
  refine elim (fun (K?, P?, M?, Q?) => (K?, P?, K?, M?, Q?))
      (fun (K?, P?, N?, M?, Q?) h => ⟨(K?, P?, M?, Q?), by acu_elim [problem]⟩) ?_
  -- ⊢ N? := K? | K? = K?; P? + {Mode.wait K?} = {Mode.idle} + Q? + {Mode.wait M?} + {Mode.wait K?} | -
  checkpoint
  -- delete K? = K?
  refine delete ?_
  -- ⊢ N? := K? | P? + {Mode.wait K?} = {Mode.idle} + Q? + {Mode.wait M?} + {Mode.wait K?} | -
  checkpoint
  -- solve P? + {Mode.wait K?} = {Mode.idle} + Q? + {Mode.wait M?} + {Mode.wait K?}
  refine solve
      { V := fun (_, P?, _, Q?) => ![P?, Q?], rest := fun (K?, _, M?, _) => (K?, M?),
        glue := fun (K?, M?) V => (K?, V 0, M?, V 1) }
      (fun (K?, M?) => ![Mode.wait K?, Mode.idle, Mode.wait M?])
      { L := ![1, 0], R := ![0, 1], La := ![1, 0, 0], Ra := ![1, 1, 1], compatible := [(0, 2)] }
      { P := ![[![0, 0]], [![1, 0]], [![1, 0]]], B := ![![1, 1]] }
      ⟨by decide, by decide, by decide,
        S2_of_list _ _ _ _ _ _ [[0], [1], [2], [0, 2]] (by decide) (by acu_cliques), by acu_basis⟩
      (fun (K?, P?, M?, Q?) h => by try simp only [unifiedBy, problem] at h; acu_side h)
      (fun (K?, P?, M?, Q?) h hD => by acu_distinct) ?_
  acu_branches
  -- branch (0,0) (1,0) (1,0)
  refine rename (fun (K?, M?, Z1) => ((K?, M?), ![Z1]))
      (fun ((K?, M?), Z) => (K?, M?, Z 0))
      (fun ((K?, M?), Z) => Prod.ext rfl (funext fun i => by fin_cases i; rfl)) ?_
  -- ⊢ N? := K?, P? := {Mode.idle} + Z1 + {Mode.wait M?}, Q? := Z1 | - | -
  checkpoint
  -- cover answer 3 with U1! := K?, U2! := Z1, U3! := M?
  exact cover answer3 (by simp [answers]) fun (K?, M?, Z1) _ _ => ⟨(K?, Z1, M?), by acu_cover⟩

end Demo.Enter
