import Tiny.conPanna.Unification.Certification.Tactics

/-!
Paper §6.2, nonlinear. The claim (model, problem) is written by the user;
the compiler appends the answers and the proof, from `nonlinear.deriv`.
-/

/- certify
{
  "namespace": "Demo.Nonlinear",
  "context": "Bag × Bag × Bag",
  "vars": [
    "X?",
    "Y?",
    "Z?"
  ],
  "ops": {}
}
-/

open Unification Certification

namespace Demo.Nonlinear

/-! ## Claim -/

inductive Elem where
  | a
  | b

abbrev Bag := ACU Elem

def problem : Problem Bag (Bag × Bag × Bag) :=
  .bind fun (X?, Y?, Z?) => (X? + Y?, Z? + Z?)

/-! ## Generated from nonlinear.deriv by producer/tools/compile.py -/

def answer0 : Unifier (Bag × Bag × Bag) :=
  .subst ⟨∅, ∅, ∅⟩
def answer1 : Unifier (Bag × Bag × Bag) :=
  .bind fun U1! => .subst ⟨U1! + U1!, ∅, U1!⟩
def answer2 : Unifier (Bag × Bag × Bag) :=
  .bind fun U1! => .subst ⟨U1!, U1!, U1!⟩
def answer3 : Unifier (Bag × Bag × Bag) :=
  .bind fun (U1!, U2!) => .subst ⟨U1! + U2! + U2!, U1!, U1! + U2!⟩
def answer4 : Unifier (Bag × Bag × Bag) :=
  .bind fun U1! => .subst ⟨∅, U1! + U1!, U1!⟩
def answer5 : Unifier (Bag × Bag × Bag) :=
  .bind fun (U1!, U2!) => .subst ⟨U1! + U1!, U2! + U2!, U1! + U2!⟩
def answer6 : Unifier (Bag × Bag × Bag) :=
  .bind fun (U1!, U2!) => .subst ⟨U1!, U1! + U2! + U2!, U1! + U2!⟩
def answer7 : Unifier (Bag × Bag × Bag) :=
  .bind fun (U1!, U2!, U3!) => .subst ⟨U1! + U1! + U2!, U2! + U3! + U3!, U1! + U2! + U3!⟩
def answers : UnifierSet (Bag × Bag × Bag) :=
  [answer0, answer1, answer2, answer3, answer4, answer5, answer6, answer7]

theorem complete : UnifierSet.Complete problem answers := by
  rw [← start_iff]
  -- ⊢ - | X? + Y? = Z? + Z? | -
  -- solve X? + Y? = Z? + Z?
  refine solve (V := fun (X?, Y?, Z?) => ![X?, Y?, Z?]) (rest := fun (X?, Y?, Z?) => ())
      (glue := fun _ V => (V 0, V 1, V 2)) (hglue := fun _ => rfl)
      (a := fun _ => ![]) (L := ![1, 1, 0]) (R := ![0, 0, 2]) (La := ![]) (Ra := ![])
      (E' := fun _ => True) (cp := fun _ _ => false)
      (P := ![]) (B := ![![2, 0, 1], ![1, 1, 1], ![0, 2, 1]])
      (fun (X?, Y?, Z?) h hD => ⟨by simp only [State.start, Problem.unifies, problem] at h; acu_side h, trivial, by acu_distinct⟩)
      (by decide) (by decide) (by decide)
      (S2_of_list _ _ _ _ _ _ [] (by decide) (by acu_cliques)) (by acu_basis) ?_
  intro π hπ; simp [choices] at hπ; subst hπ
  -- branch 
  -- ⊢ X? := Z1 + Z1 + Z2, Y? := Z2 + Z3 + Z3, Z? := Z1 + Z2 + Z3 | - | -
  -- cover answer 7 with U1! := Z1, U2! := Z2, U3! := Z3
  exact cover answer7 (by simp [answers]) fun (_, Z) _ _ => by
    obtain ⟨Z1, Z2, Z3, rfl⟩ : ∃ x0 x1 x2, Z = ![x0, x1, x2] :=
      ⟨Z 0, Z 1, Z 2, funext fun i => by fin_cases i <;> rfl⟩
    exact ⟨(Z1, Z2, Z3), by acu_cover⟩

end Demo.Nonlinear
