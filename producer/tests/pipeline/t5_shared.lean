import conPanna.Unification.Certification.Tactics

/-! A system sharing a bag variable: X? + Y? =? Z? + {a} and Y? =? W? + {b}. -/

/- certify
{
  "namespace": "Pipeline.T5",
  "context": "Bag × Bag × Bag × Bag",
  "vars": [
    "X?",
    "Y?",
    "Z?",
    "W?"
  ],
  "ops": {
    "a": "Elem.a",
    "b": "Elem.b"
  }
}
-/

open Unification Certification

namespace Pipeline.T5

inductive Elem where
  | a
  | b

abbrev Bag := ACU Elem

def problem : Problem (Bag × Bag) (Bag × Bag × Bag × Bag) :=
  .bind fun (X?, Y?, Z?, W?) => ((X? + Y?, Y?), (Z? + {Elem.a}, W? + {Elem.b}))

/-! ## Generated from t5_shared.deriv by producer/tools/compile.py -/

def answer0 : Unifier (Bag × Bag × Bag × Bag) :=
  .bind fun () => ⟨{Elem.a}, {Elem.b}, {Elem.b}, ∅⟩
def answer1 : Unifier (Bag × Bag × Bag × Bag) :=
  .bind fun U1! => ⟨{Elem.a} + U1!, {Elem.b}, {Elem.b} + U1!, ∅⟩
def answer2 : Unifier (Bag × Bag × Bag × Bag) :=
  .bind fun U1! => ⟨{Elem.a}, {Elem.b} + U1!, {Elem.b} + U1!, U1!⟩
def answer3 : Unifier (Bag × Bag × Bag × Bag) :=
  .bind fun (U1!, U2!) => ⟨{Elem.a} + U2!, {Elem.b} + U1!, {Elem.b} + U1! + U2!, U1!⟩
def answer4 : Unifier (Bag × Bag × Bag × Bag) :=
  .bind fun () => ⟨∅, {Elem.a} + {Elem.b}, {Elem.b}, {Elem.a}⟩
def answer5 : Unifier (Bag × Bag × Bag × Bag) :=
  .bind fun U1! => ⟨U1!, {Elem.a} + {Elem.b}, {Elem.b} + U1!, {Elem.a}⟩
def answer6 : Unifier (Bag × Bag × Bag × Bag) :=
  .bind fun U1! => ⟨∅, {Elem.a} + {Elem.b} + U1!, {Elem.b} + U1!, {Elem.a} + U1!⟩
def answer7 : Unifier (Bag × Bag × Bag × Bag) :=
  .bind fun (U1!, U2!) => ⟨U1!, {Elem.a} + {Elem.b} + U2!, {Elem.b} + U1! + U2!, {Elem.a} + U2!⟩
def answers : UnifierSet (Bag × Bag × Bag × Bag) :=
  [answer0, answer1, answer2, answer3, answer4, answer5, answer6, answer7]

theorem complete : Unification.complete problem answers := by
  rw [← start_iff]
  -- decomp the tuple equation of the claim
  refine decomp [fun (X?, Y?, Z?, _) => X? + Y? = Z? + {Elem.a}, fun (_, Y?, _, W?) => Y? = W? + {Elem.b}]
      (fun (X?, Y?, Z?, W?) h => by acu_decomp [problem, Prod.mk.injEq]) ?_
  -- ⊢ - | X? + Y? = Z? + {Elem.a}; Y? = W? + {Elem.b} | -
  checkpoint
  -- solve X? + Y? = Z? + {Elem.a}
  refine solve
      { V := fun (X?, Y?, Z?, _) => ![X?, Y?, Z?], rest := fun (_, _, _, W?) => W?,
        glue := fun W? V => (V 0, V 1, V 2, W?) }
      (fun _ => ![Elem.a])
      { L := ![1, 1, 0], R := ![0, 0, 1], La := ![0], Ra := ![1] }
      { P := ![[![1, 0, 0], ![0, 1, 0]]], B := ![![1, 0, 1], ![0, 1, 1]] }
      ⟨by decide, by decide, by decide,
        S2_of_list _ _ _ _ _ _ [[0]] (by decide) (by acu_cliques), by acu_basis⟩
      (fun (X?, Y?, Z?, W?) h => by try simp only [unifiedBy, problem] at h; acu_side h)
      (fun (X?, Y?, Z?, W?) h hD => by acu_distinct) ?_
  acu_branches
  · -- branch (1,0,0)
    refine rename (fun (W?, Z1, Z2) => (W?, ![Z1, Z2]))
        (fun (W?, Z) => (W?, Z 0, Z 1))
        (fun (W?, Z) => Prod.ext rfl (funext fun i => by fin_cases i <;> rfl)) ?_
    -- ⊢ X? := {Elem.a} + Z1, Y? := Z2, Z? := Z1 + Z2 | Z2 = {Elem.b} + W? | -
    checkpoint
    -- elim Z2 := {Elem.b} + W?
    refine elim (fun (W?, Z1) => (W?, Z1, {Elem.b} + W?))
        (fun (W?, Z1, Z2) h => ⟨(W?, Z1), by acu_elim [problem]⟩) ?_
    -- ⊢ X? := {Elem.a} + Z1, Y? := {Elem.b} + W?, Z? := {Elem.b} + W? + Z1 | - | -
    checkpoint
    -- cover answer 3 with U1! := W?, U2! := Z1
    exact cover answer3 (by simp [answers]) fun (W?, Z1) _ _ => ⟨(W?, Z1), by acu_cover⟩
  · -- branch (0,1,0)
    refine rename (fun (W?, Z1, Z2) => (W?, ![Z1, Z2]))
        (fun (W?, Z) => (W?, Z 0, Z 1))
        (fun (W?, Z) => Prod.ext rfl (funext fun i => by fin_cases i <;> rfl)) ?_
    -- ⊢ X? := Z1, Y? := {Elem.a} + Z2, Z? := Z1 + Z2 | {Elem.a} + Z2 = {Elem.b} + W? | -
    checkpoint
    -- solve {Elem.a} + Z2 = {Elem.b} + W?
    refine solve
        { V := fun (W?, _, Z2) => ![Z2, W?], rest := fun (_, Z1, _) => Z1,
          glue := fun Z1 V => (V 1, Z1, V 0) }
        (fun _ => ![Elem.a, Elem.b])
        { L := ![1, 0], R := ![0, 1], La := ![1, 0], Ra := ![0, 1] }
        { P := ![[![0, 1]], [![1, 0]]], B := ![![1, 1]] }
        ⟨by decide, by decide, by decide,
          S2_of_list _ _ _ _ _ _ [[0], [1]] (by decide) (by acu_cliques), by acu_basis⟩
        (fun (W?, Z1, Z2) h => by try simp only [unifiedBy, problem] at h; acu_side h)
        (fun (W?, Z1, Z2) h hD => by acu_distinct) ?_
    acu_branches
    -- branch (0,1) (1,0)
    refine rename (fun (Z1, Z3) => (Z1, ![Z3]))
        (fun (Z1, Z) => (Z1, Z 0))
        (fun (Z1, Z) => Prod.ext rfl (funext fun i => by fin_cases i; rfl)) ?_
    -- ⊢ W? := {Elem.a} + Z3, X? := Z1, Y? := {Elem.a} + {Elem.b} + Z3, Z? := {Elem.b} + Z1 + Z3 | - | -
    checkpoint
    -- cover answer 7 with U1! := Z1, U2! := Z3
    exact cover answer7 (by simp [answers]) fun (Z1, Z3) _ _ => ⟨(Z1, Z3), by acu_cover⟩

end Pipeline.T5
