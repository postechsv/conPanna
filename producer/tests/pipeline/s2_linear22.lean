import Tiny.conPanna.Unification.Certification.Tactics

/-! A linear equation with 2 and 2 bag variables. -/

/- certify
{
  "namespace": "Pipeline.S2Linear22",
  "context": "Bag × Bag × Bag × Bag",
  "vars": [
    "X1?",
    "X2?",
    "Y1?",
    "Y2?"
  ],
  "ops": {}
}
-/

open Unification Certification

namespace Pipeline.S2Linear22

inductive Elem where
  | a

abbrev Bag := ACU Elem

def problem : Problem Bag (Bag × Bag × Bag × Bag) :=
  .bind fun (X1?, X2?, Y1?, Y2?) =>
    (X1? + X2?, Y1? + Y2?)

/-! ## Generated from s2_linear22.deriv by producer/tools/compile.py -/

def answer0 : Unifier (Bag × Bag × Bag × Bag) :=
  .subst ⟨∅, ∅, ∅, ∅⟩
def answer1 : Unifier (Bag × Bag × Bag × Bag) :=
  .bind fun U1! => .subst ⟨U1!, ∅, U1!, ∅⟩
def answer2 : Unifier (Bag × Bag × Bag × Bag) :=
  .bind fun U1! => .subst ⟨∅, U1!, U1!, ∅⟩
def answer3 : Unifier (Bag × Bag × Bag × Bag) :=
  .bind fun (U1!, U2!) => .subst ⟨U1!, U2!, U1! + U2!, ∅⟩
def answer4 : Unifier (Bag × Bag × Bag × Bag) :=
  .bind fun U1! => .subst ⟨U1!, ∅, ∅, U1!⟩
def answer5 : Unifier (Bag × Bag × Bag × Bag) :=
  .bind fun (U1!, U2!) => .subst ⟨U1! + U2!, ∅, U1!, U2!⟩
def answer6 : Unifier (Bag × Bag × Bag × Bag) :=
  .bind fun (U1!, U2!) => .subst ⟨U2!, U1!, U1!, U2!⟩
def answer7 : Unifier (Bag × Bag × Bag × Bag) :=
  .bind fun (U1!, U2!, U3!) => .subst ⟨U2! + U3!, U1!, U1! + U3!, U2!⟩
def answer8 : Unifier (Bag × Bag × Bag × Bag) :=
  .bind fun U1! => .subst ⟨∅, U1!, ∅, U1!⟩
def answer9 : Unifier (Bag × Bag × Bag × Bag) :=
  .bind fun (U1!, U2!) => .subst ⟨U1!, U2!, U1!, U2!⟩
def answer10 : Unifier (Bag × Bag × Bag × Bag) :=
  .bind fun (U1!, U2!) => .subst ⟨∅, U1! + U2!, U1!, U2!⟩
def answer11 : Unifier (Bag × Bag × Bag × Bag) :=
  .bind fun (U1!, U2!, U3!) => .subst ⟨U1!, U2! + U3!, U1! + U3!, U2!⟩
def answer12 : Unifier (Bag × Bag × Bag × Bag) :=
  .bind fun (U1!, U2!) => .subst ⟨U1!, U2!, ∅, U1! + U2!⟩
def answer13 : Unifier (Bag × Bag × Bag × Bag) :=
  .bind fun (U1!, U2!, U3!) => .subst ⟨U2! + U3!, U1!, U2!, U1! + U3!⟩
def answer14 : Unifier (Bag × Bag × Bag × Bag) :=
  .bind fun (U1!, U2!, U3!) => .subst ⟨U1!, U2! + U3!, U2!, U1! + U3!⟩
def answer15 : Unifier (Bag × Bag × Bag × Bag) :=
  .bind fun (U1!, U2!, U3!, U4!) => .subst ⟨U1! + U3!, U2! + U4!, U1! + U2!, U3! + U4!⟩
def answers : UnifierSet (Bag × Bag × Bag × Bag) :=
  [answer0, answer1, answer2, answer3, answer4, answer5, answer6, answer7, answer8, answer9, answer10, answer11, answer12, answer13, answer14, answer15]

theorem complete : UnifierSet.Complete problem answers := by
  rw [← start_iff]
  -- ⊢ - | X1? + X2? = Y1? + Y2? | -
  -- solve X1? + X2? = Y1? + Y2?
  refine solve (V := fun (X1?, X2?, Y1?, Y2?) => ![X1?, X2?, Y1?, Y2?]) (rest := fun (_, _, _, _) => ())
      (glue := fun _ V => (V 0, V 1, V 2, V 3)) (hglue := fun _ => rfl)
      (a := fun _ => ![]) (L := ![1, 1, 0, 0]) (R := ![0, 0, 1, 1]) (La := ![]) (Ra := ![])
      (E' := fun (_, _, _, _) => True) (cp := fun _ _ => false)
      (P := ![]) (B := ![![1, 0, 1, 0], ![0, 1, 1, 0], ![1, 0, 0, 1], ![0, 1, 0, 1]])
      (fun (X1?, X2?, Y1?, Y2?) h hD => ⟨by try simp only [State.start, Problem.unifies, problem] at h; acu_side h, trivial, by acu_distinct⟩)
      (by decide) (by decide) (by decide)
      (S2_of_list _ _ _ _ _ _ [] (by decide) (by acu_cliques)) (by acu_basis) ?_
  intro π hπ; simp [choices] at hπ; subst hπ
  -- branch 
  refine rename (fun (Z1, Z2, Z3, Z4) => ((), ![Z1, Z2, Z3, Z4]))
      (fun (_, Z) => (Z 0, Z 1, Z 2, Z 3))
      (fun (_, Z) => Prod.ext rfl (funext fun i => by fin_cases i <;> rfl)) ?_
  -- ⊢ X1? := Z1 + Z3, X2? := Z2 + Z4, Y1? := Z1 + Z2, Y2? := Z3 + Z4 | - | -
  -- cover answer 15 with U1! := Z1, U2! := Z2, U3! := Z3, U4! := Z4
  exact cover answer15 (by simp [answers]) fun (Z1, Z2, Z3, Z4) _ _ => ⟨(Z1, Z2, Z3, Z4), by acu_cover⟩

end Pipeline.S2Linear22
