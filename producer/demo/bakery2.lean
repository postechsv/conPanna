import conPanna.Unification.Certification.Tactics

/-!
Bakery, unknown bags on both sides. The claim (model, problem) is written by the
user; the compiler appends the answers and the proof, from `bakery2.deriv`.
-/

/- certify
{
  "namespace": "Demo.Bakery2",
  "context": "Nat × ProcSet × ProcSet × ProcSet",
  "vars": [
    "N?",
    "P?",
    "Q?",
    "R?"
  ],
  "ops": {
    "wait": "Mode.wait",
    "idle": "Mode.idle",
    "crit": "Mode.crit"
  }
}
-/

open Unification Certification

namespace Demo.Bakery2

/-! ## Claim -/

inductive Mode where
  | idle
  | wait (ticket : Nat)
  | crit (ticket : Nat)

abbrev ProcSet := ACU Mode

def problem : Problem ProcSet (Nat × ProcSet × ProcSet × ProcSet) :=
  .bind fun (N?, P?, Q?, R?) => (P? + Q?, {.wait N?} + R?)

/-! ## Generated from bakery2.deriv by producer/tools/compile.py -/

def answer0 : Unifier (Nat × ProcSet × ProcSet × ProcSet) :=
  .bind fun U1! => ⟨U1!, ∅, {Mode.wait U1!}, ∅⟩
def answer1 : Unifier (Nat × ProcSet × ProcSet × ProcSet) :=
  .bind fun (U1!, U2!) => ⟨U2!, ∅, U1! + {Mode.wait U2!}, U1!⟩
def answer2 : Unifier (Nat × ProcSet × ProcSet × ProcSet) :=
  .bind fun (U1!, U2!) => ⟨U2!, U1!, {Mode.wait U2!}, U1!⟩
def answer3 : Unifier (Nat × ProcSet × ProcSet × ProcSet) :=
  .bind fun (U1!, U2!, U3!) => ⟨U2!, U1!, U3! + {Mode.wait U2!}, U1! + U3!⟩
def answer4 : Unifier (Nat × ProcSet × ProcSet × ProcSet) :=
  .bind fun U1! => ⟨U1!, {Mode.wait U1!}, ∅, ∅⟩
def answer5 : Unifier (Nat × ProcSet × ProcSet × ProcSet) :=
  .bind fun (U1!, U2!) => ⟨U2!, {Mode.wait U2!}, U1!, U1!⟩
def answer6 : Unifier (Nat × ProcSet × ProcSet × ProcSet) :=
  .bind fun (U1!, U2!) => ⟨U2!, U1! + {Mode.wait U2!}, ∅, U1!⟩
def answer7 : Unifier (Nat × ProcSet × ProcSet × ProcSet) :=
  .bind fun (U1!, U2!, U3!) => ⟨U2!, U3! + {Mode.wait U2!}, U1!, U1! + U3!⟩
def answers : UnifierSet (Nat × ProcSet × ProcSet × ProcSet) :=
  [answer0, answer1, answer2, answer3, answer4, answer5, answer6, answer7]

theorem complete : Unification.complete problem answers := by
  rw [← start_iff]
  -- ⊢ - | P? + Q? = {Mode.wait N?} + R? | -
  checkpoint
  -- solve P? + Q? = {Mode.wait N?} + R?
  refine solve
      { V := fun (_, P?, Q?, R?) => ![P?, Q?, R?], rest := fun (N?, _, _, _) => N?,
        glue := fun N? V => (N?, V 0, V 1, V 2), hglue := fun _ => rfl }
      (fun N? => ![Mode.wait N?])
      { L := ![1, 1, 0], R := ![0, 0, 1], La := ![0], Ra := ![1], cp := fun _ _ => false }
      { P := ![[![1, 0, 0], ![0, 1, 0]]], B := ![![1, 0, 1], ![0, 1, 1]] }
      ⟨by decide, by decide, by decide,
        S2_of_list _ _ _ _ _ _ [[0]] (by decide) (by acu_cliques), by acu_basis⟩
      (fun (N?, P?, Q?, R?) h => by try simp only [unifiedBy, problem] at h; acu_side h)
      (fun (N?, P?, Q?, R?) h hD => by acu_distinct) ?_
  intro π hπ; simp [choices] at hπ; rcases hπ with rfl | rfl
  · -- branch (1,0,0)
    refine rename (fun (N?, Z1, Z2) => (N?, ![Z1, Z2]))
        (fun (N?, Z) => (N?, Z 0, Z 1))
        (fun (N?, Z) => Prod.ext rfl (funext fun i => by fin_cases i <;> rfl)) ?_
    -- ⊢ P? := Z1 + {Mode.wait N?}, Q? := Z2, R? := Z1 + Z2 | - | -
    checkpoint
    -- cover answer 7 with U1! := Z2, U2! := N?, U3! := Z1
    exact cover answer7 (by simp [answers]) fun (N?, Z1, Z2) _ _ => ⟨(Z2, N?, Z1), by acu_cover⟩
  · -- branch (0,1,0)
    refine rename (fun (N?, Z1, Z2) => (N?, ![Z1, Z2]))
        (fun (N?, Z) => (N?, Z 0, Z 1))
        (fun (N?, Z) => Prod.ext rfl (funext fun i => by fin_cases i <;> rfl)) ?_
    -- ⊢ P? := Z1, Q? := Z2 + {Mode.wait N?}, R? := Z1 + Z2 | - | -
    checkpoint
    -- cover answer 3 with U1! := Z1, U2! := N?, U3! := Z2
    exact cover answer3 (by simp [answers]) fun (N?, Z1, Z2) _ _ => ⟨(Z1, N?, Z2), by acu_cover⟩

end Demo.Bakery2
