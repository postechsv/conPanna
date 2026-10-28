import conPanna.Unification.Certification.Tactics

/-! The worked example of documentation/worked-example.html:
{box ({a} + X?)} + R? =? {box (Y? + W?)} + {box Z?}. -/

/- certify
{
  "namespace": "Pipeline.T7",
  "context": "Bag × Bag × Bag × Bag × Boxes",
  "vars": [
    "X?",
    "Y?",
    "W?",
    "Z?",
    "R?"
  ],
  "ops": {
    "a": "Elem.a",
    "b": "Elem.b",
    "{_}": "Box.box"
  }
}
-/

open Unification Certification

namespace Pipeline.T7

inductive Elem where
  | a
  | b

abbrev Bag := ACU Elem

inductive Box where
  | box (b : Bag)

abbrev Boxes := ACU Box

def problem : Problem Boxes (Bag × Bag × Bag × Bag × Boxes) :=
  .bind fun (X?, Y?, W?, Z?, R?) =>
    ({Box.box ({Elem.a} + X?)} + R?, {Box.box (Y? + W?)} + {Box.box Z?})

/-! ## Generated from t7_example.deriv by producer/tools/compile.py -/

def answer0 : Unifier (Bag × Bag × Bag × Bag × Boxes) :=
  .bind fun () => ⟨∅, ∅, ∅, {Elem.a}, {Box.box (∅)}⟩
def answer1 : Unifier (Bag × Bag × Bag × Bag × Boxes) :=
  .bind fun U1! => ⟨U1!, ∅, ∅, {Elem.a} + U1!, {Box.box (∅)}⟩
def answer2 : Unifier (Bag × Bag × Bag × Bag × Boxes) :=
  .bind fun U1! => ⟨∅, U1!, ∅, {Elem.a}, {Box.box U1!}⟩
def answer3 : Unifier (Bag × Bag × Bag × Bag × Boxes) :=
  .bind fun (U1!, U2!) => ⟨U1!, U2!, ∅, {Elem.a} + U1!, {Box.box U2!}⟩
def answer4 : Unifier (Bag × Bag × Bag × Bag × Boxes) :=
  .bind fun U1! => ⟨∅, ∅, U1!, {Elem.a}, {Box.box U1!}⟩
def answer5 : Unifier (Bag × Bag × Bag × Bag × Boxes) :=
  .bind fun (U1!, U2!) => ⟨U1!, ∅, U2!, {Elem.a} + U1!, {Box.box U2!}⟩
def answer6 : Unifier (Bag × Bag × Bag × Bag × Boxes) :=
  .bind fun (U1!, U2!) => ⟨∅, U1!, U2!, {Elem.a}, {Box.box (U1! + U2!)}⟩
def answer7 : Unifier (Bag × Bag × Bag × Bag × Boxes) :=
  .bind fun (U1!, U2!, U3!) => ⟨U1!, U2!, U3!, {Elem.a} + U1!, {Box.box (U2! + U3!)}⟩
def answer8 : Unifier (Bag × Bag × Bag × Bag × Boxes) :=
  .bind fun U1! => ⟨∅, {Elem.a}, ∅, U1!, {Box.box U1!}⟩
def answer9 : Unifier (Bag × Bag × Bag × Bag × Boxes) :=
  .bind fun (U1!, U2!) => ⟨U1!, {Elem.a} + U1!, ∅, U2!, {Box.box U2!}⟩
def answer10 : Unifier (Bag × Bag × Bag × Bag × Boxes) :=
  .bind fun (U1!, U2!) => ⟨U1!, {Elem.a}, U1!, U2!, {Box.box U2!}⟩
def answer11 : Unifier (Bag × Bag × Bag × Bag × Boxes) :=
  .bind fun (U1!, U2!, U3!) => ⟨U2! + U3!, {Elem.a} + U3!, U2!, U1!, {Box.box U1!}⟩
def answer12 : Unifier (Bag × Bag × Bag × Bag × Boxes) :=
  .bind fun U1! => ⟨∅, ∅, {Elem.a}, U1!, {Box.box U1!}⟩
def answer13 : Unifier (Bag × Bag × Bag × Bag × Boxes) :=
  .bind fun (U1!, U2!) => ⟨U1!, U1!, {Elem.a}, U2!, {Box.box U2!}⟩
def answer14 : Unifier (Bag × Bag × Bag × Bag × Boxes) :=
  .bind fun (U1!, U2!) => ⟨U1!, ∅, {Elem.a} + U1!, U2!, {Box.box U2!}⟩
def answer15 : Unifier (Bag × Bag × Bag × Bag × Boxes) :=
  .bind fun (U1!, U2!, U3!) => ⟨U2! + U3!, U2!, {Elem.a} + U3!, U1!, {Box.box U1!}⟩
def answers : UnifierSet (Bag × Bag × Bag × Bag × Boxes) :=
  [answer0, answer1, answer2, answer3, answer4, answer5, answer6, answer7, answer8, answer9, answer10, answer11, answer12, answer13, answer14, answer15]

theorem complete : Unification.complete problem answers := by
  rw [← start_iff]
  -- ⊢ - | {Box.box ({Elem.a} + X?)} + R? = {Box.box (Y? + W?)} + {Box.box Z?} | -
  checkpoint
  -- identify Box.box ({Elem.a} + X?) ~ Box.box Z?
  refine identify (fun (X?, _, _, _, _) => Box.box ({Elem.a} + X?)) (fun (_, _, _, Z?, _) => Box.box Z?) ?_ ?_
  · -- equal:
    -- ⊢ - | Box.box ({Elem.a} + X?) = Box.box Z?; {Box.box ({Elem.a} + X?)} + R? = {Box.box (Y? + W?)} + {Box.box Z?} | -
    checkpoint
    -- decomp Box.box ({Elem.a} + X?) = Box.box Z?
    refine decomp [fun (X?, _, _, Z?, _) => {Elem.a} + X? = Z?]
        (fun (X?, Y?, W?, Z?, R?) h => by acu_decomp [problem, Box.box.injEq]) ?_
    -- ⊢ - | {Elem.a} + X? = Z?; {Box.box ({Elem.a} + X?)} + R? = {Box.box (Y? + W?)} + {Box.box Z?} | -
    checkpoint
    -- elim Z? := {Elem.a} + X?
    refine elim (fun (X?, Y?, W?, R?) => (X?, Y?, W?, {Elem.a} + X?, R?))
        (fun (X?, Y?, W?, Z?, R?) h => ⟨(X?, Y?, W?, R?), by acu_elim [problem]⟩) ?_
    -- ⊢ Z? := {Elem.a} + X? | R? + {Box.box ({Elem.a} + X?)} = {Box.box ({Elem.a} + X?)} + {Box.box (Y? + W?)} | -
    checkpoint
    -- solve R? + {Box.box ({Elem.a} + X?)} = {Box.box ({Elem.a} + X?)} + {Box.box (Y? + W?)}
    refine solve
        { V := fun (_, _, _, R?) => ![R?], rest := fun (X?, Y?, W?, _) => (X?, Y?, W?),
          glue := fun (X?, Y?, W?) V => (X?, Y?, W?, V 0) }
        (fun (X?, Y?, W?) => ![Box.box ({Elem.a} + X?), Box.box (Y? + W?)])
        { L := ![1], R := ![0], La := ![1, 0], Ra := ![1, 1], compatible := [(0, 1)] }
        { P := ![[![0]], [![1]]], B := ![] }
        ⟨by decide, by decide, by decide,
          S2_of_list _ _ _ _ _ _ [[0], [1], [0, 1]] (by decide) (by acu_cliques), by acu_basis⟩
        (fun (X?, Y?, W?, R?) h => by (try simp only [unifiedBy, problem] at h); acu_side h)
        (fun (X?, Y?, W?, R?) h hD => by acu_distinct) ?_
    acu_branches
    -- branch (0) (1)
    refine rename (fun (X?, Y?, W?) => ((X?, Y?, W?), ![]))
        (fun ((X?, Y?, W?), Z) => (X?, Y?, W?))
        (fun ((X?, Y?, W?), Z) => Prod.ext rfl (funext fun i => i.elim0)) ?_
    -- ⊢ R? := {Box.box (Y? + W?)}, Z? := {Elem.a} + X? | - | -
    checkpoint
    -- cover answer 7 with U1! := X?, U2! := Y?, U3! := W?
    exact cover answer7 (by simp [answers]) fun (X?, Y?, W?) _ _ => ⟨(X?, Y?, W?), by acu_cover⟩
  · -- distinct:
    -- ⊢ - | {Box.box ({Elem.a} + X?)} + R? = {Box.box (Y? + W?)} + {Box.box Z?} | Box.box ({Elem.a} + X?) ≠ Box.box Z?
    checkpoint
    -- identify Box.box ({Elem.a} + X?) ~ Box.box (Y? + W?)
    refine identify (fun (X?, _, _, _, _) => Box.box ({Elem.a} + X?)) (fun (_, Y?, W?, _, _) => Box.box (Y? + W?)) ?_ ?_
    · -- equal:
      -- ⊢ - | Box.box ({Elem.a} + X?) = Box.box (Y? + W?); {Box.box ({Elem.a} + X?)} + R? = {Box.box (Y? + W?)} + {Box.box Z?} | Box.box ({Elem.a} + X?) ≠ Box.box Z?
      checkpoint
      -- decomp Box.box ({Elem.a} + X?) = Box.box (Y? + W?)
      refine decomp [fun (X?, Y?, W?, _, _) => {Elem.a} + X? = Y? + W?]
          (fun (X?, Y?, W?, Z?, R?) h => by acu_decomp [problem, Box.box.injEq]) ?_
      -- ⊢ - | {Elem.a} + X? = Y? + W?; {Box.box ({Elem.a} + X?)} + R? = {Box.box (Y? + W?)} + {Box.box Z?} | Box.box ({Elem.a} + X?) ≠ Box.box Z?
      checkpoint
      -- solve {Elem.a} + X? = Y? + W?
      refine solve
          { V := fun (X?, Y?, W?, _, _) => ![X?, Y?, W?], rest := fun (_, _, _, Z?, R?) => (Z?, R?),
            glue := fun (Z?, R?) V => (V 0, V 1, V 2, Z?, R?) }
          (fun (_, _) => ![Elem.a])
          { L := ![1, 0, 0], R := ![0, 1, 1], La := ![1], Ra := ![0] }
          { P := ![[![0, 1, 0], ![0, 0, 1]]], B := ![![1, 1, 0], ![1, 0, 1]] }
          ⟨by decide, by decide, by decide,
            S2_of_list _ _ _ _ _ _ [[0]] (by decide) (by acu_cliques), by acu_basis⟩
          (fun (X?, Y?, W?, Z?, R?) h => by (try simp only [unifiedBy, problem] at h); acu_side h)
          (fun (X?, Y?, W?, Z?, R?) h hD => by acu_distinct) ?_
      acu_branches
      · -- branch (0,1,0)
        refine rename (fun (Z?, R?, Z1, Z2) => ((Z?, R?), ![Z1, Z2]))
            (fun ((Z?, R?), Z) => (Z?, R?, Z 0, Z 1))
            (fun ((Z?, R?), Z) => Prod.ext rfl (funext fun i => by fin_cases i <;> rfl)) ?_
        -- ⊢ W? := Z2, X? := Z1 + Z2, Y? := {Elem.a} + Z1 | R? + {Box.box ({Elem.a} + Z1 + Z2)} = {Box.box Z?} + {Box.box ({Elem.a} + Z1 + Z2)} | Box.box ({Elem.a} + Z1 + Z2) ≠ Box.box Z?
        checkpoint
        -- solve R? + {Box.box ({Elem.a} + Z1 + Z2)} = {Box.box Z?} + {Box.box ({Elem.a} + Z1 + Z2)}
        refine solve
            { V := fun (_, R?, _, _) => ![R?], rest := fun (Z?, _, Z1, Z2) => (Z?, Z1, Z2),
              glue := fun (Z?, Z1, Z2) V => (Z?, V 0, Z1, Z2) }
            (fun (Z?, Z1, Z2) => ![Box.box ({Elem.a} + Z1 + Z2), Box.box Z?])
            { L := ![1], R := ![0], La := ![1, 0], Ra := ![1, 1] }
            { P := ![[![0]], [![1]]], B := ![] }
            ⟨by decide, by decide, by decide,
              S2_of_list _ _ _ _ _ _ [[0], [1]] (by decide) (by acu_cliques), by acu_basis⟩
            (fun (Z?, R?, Z1, Z2) h => by (try simp only [unifiedBy, problem] at h); acu_side h)
            (fun (Z?, R?, Z1, Z2) h hD => by acu_distinct) ?_
        acu_branches
        -- branch (0) (1)
        refine rename (fun (Z?, Z1, Z2) => ((Z?, Z1, Z2), ![]))
            (fun ((Z?, Z1, Z2), Z) => (Z?, Z1, Z2))
            (fun ((Z?, Z1, Z2), Z) => Prod.ext rfl (funext fun i => i.elim0)) ?_
        -- ⊢ R? := {Box.box Z?}, W? := Z2, X? := Z1 + Z2, Y? := {Elem.a} + Z1 | - | Box.box ({Elem.a} + Z1 + Z2) ≠ Box.box Z?
        checkpoint
        -- cover answer 11 with U1! := Z?, U2! := Z2, U3! := Z1
        exact cover answer11 (by simp [answers]) fun (Z?, Z1, Z2) _ _ => ⟨(Z?, Z2, Z1), by acu_cover⟩
      · -- branch (0,0,1)
        refine rename (fun (Z?, R?, Z1, Z2) => ((Z?, R?), ![Z1, Z2]))
            (fun ((Z?, R?), Z) => (Z?, R?, Z 0, Z 1))
            (fun ((Z?, R?), Z) => Prod.ext rfl (funext fun i => by fin_cases i <;> rfl)) ?_
        -- ⊢ W? := {Elem.a} + Z2, X? := Z1 + Z2, Y? := Z1 | R? + {Box.box ({Elem.a} + Z1 + Z2)} = {Box.box Z?} + {Box.box ({Elem.a} + Z1 + Z2)} | Box.box ({Elem.a} + Z1 + Z2) ≠ Box.box Z?
        checkpoint
        -- solve R? + {Box.box ({Elem.a} + Z1 + Z2)} = {Box.box Z?} + {Box.box ({Elem.a} + Z1 + Z2)}
        refine solve
            { V := fun (_, R?, _, _) => ![R?], rest := fun (Z?, _, Z1, Z2) => (Z?, Z1, Z2),
              glue := fun (Z?, Z1, Z2) V => (Z?, V 0, Z1, Z2) }
            (fun (Z?, Z1, Z2) => ![Box.box ({Elem.a} + Z1 + Z2), Box.box Z?])
            { L := ![1], R := ![0], La := ![1, 0], Ra := ![1, 1] }
            { P := ![[![0]], [![1]]], B := ![] }
            ⟨by decide, by decide, by decide,
              S2_of_list _ _ _ _ _ _ [[0], [1]] (by decide) (by acu_cliques), by acu_basis⟩
            (fun (Z?, R?, Z1, Z2) h => by (try simp only [unifiedBy, problem] at h); acu_side h)
            (fun (Z?, R?, Z1, Z2) h hD => by acu_distinct) ?_
        acu_branches
        -- branch (0) (1)
        refine rename (fun (Z?, Z1, Z2) => ((Z?, Z1, Z2), ![]))
            (fun ((Z?, Z1, Z2), Z) => (Z?, Z1, Z2))
            (fun ((Z?, Z1, Z2), Z) => Prod.ext rfl (funext fun i => i.elim0)) ?_
        -- ⊢ R? := {Box.box Z?}, W? := {Elem.a} + Z2, X? := Z1 + Z2, Y? := Z1 | - | Box.box ({Elem.a} + Z1 + Z2) ≠ Box.box Z?
        checkpoint
        -- cover answer 15 with U1! := Z?, U2! := Z1, U3! := Z2
        exact cover answer15 (by simp [answers]) fun (Z?, Z1, Z2) _ _ => ⟨(Z?, Z1, Z2), by acu_cover⟩
    · -- distinct:
      -- ⊢ - | {Box.box ({Elem.a} + X?)} + R? = {Box.box (Y? + W?)} + {Box.box Z?} | Box.box ({Elem.a} + X?) ≠ Box.box Z?; Box.box ({Elem.a} + X?) ≠ Box.box (Y? + W?)
      checkpoint
      -- solve {Box.box ({Elem.a} + X?)} + R? = {Box.box (Y? + W?)} + {Box.box Z?}
      refine solve
          { V := fun (_, _, _, _, R?) => ![R?], rest := fun (X?, Y?, W?, Z?, _) => (X?, Y?, W?, Z?),
            glue := fun (X?, Y?, W?, Z?) V => (X?, Y?, W?, Z?, V 0) }
          (fun (X?, Y?, W?, Z?) => ![Box.box ({Elem.a} + X?), Box.box (Y? + W?), Box.box Z?])
          { L := ![1], R := ![0], La := ![1, 0, 0], Ra := ![0, 1, 1], compatible := [(1, 2)] }
          { P := ![[], [![1]], [![1]]], B := ![] }
          ⟨by decide, by decide, by decide,
            S2_of_list _ _ _ _ _ _ [[0], [1], [2], [1, 2]] (by decide) (by acu_cliques), by acu_basis⟩
          (fun (X?, Y?, W?, Z?, R?) h => by (try simp only [unifiedBy, problem] at h); acu_side h)
          (fun (X?, Y?, W?, Z?, R?) h hD => by acu_distinct) ?_
      acu_branches

end Pipeline.T7
