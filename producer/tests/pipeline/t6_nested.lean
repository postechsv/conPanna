import conPanna.Unification.Certification.Tactics

/-! Nested bags: {box X?} + R? =? {box ({a} + Y?)} + {box {b}}. -/

/- certify
{
  "namespace": "Pipeline.T6",
  "context": "Bag × Bag × Boxes",
  "vars": [
    "X?",
    "Y?",
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

namespace Pipeline.T6

inductive Elem where
  | a
  | b

abbrev Bag := ACU Elem

inductive Box where
  | box (b : Bag)

abbrev Boxes := ACU Box

def problem : Problem Boxes (Bag × Bag × Boxes) :=
  .bind fun (X?, Y?, R?) =>
    ({Box.box X?} + R?, {Box.box ({Elem.a} + Y?)} + {Box.box {Elem.b}})

/-! ## Generated from t6_nested.deriv by producer/tools/compile.py -/

def answer0 : Unifier (Bag × Bag × Boxes) :=
  .bind fun () => ⟨{Elem.b}, ∅, {Box.box {Elem.a}}⟩
def answer1 : Unifier (Bag × Bag × Boxes) :=
  .bind fun U1! => ⟨{Elem.b}, U1!, {Box.box ({Elem.a} + U1!)}⟩
def answer2 : Unifier (Bag × Bag × Boxes) :=
  .bind fun () => ⟨{Elem.a}, ∅, {Box.box {Elem.b}}⟩
def answer3 : Unifier (Bag × Bag × Boxes) :=
  .bind fun U1! => ⟨{Elem.a} + U1!, U1!, {Box.box {Elem.b}}⟩
def answers : UnifierSet (Bag × Bag × Boxes) :=
  [answer0, answer1, answer2, answer3]

theorem complete : Unification.complete problem answers := by
  rw [← start_iff]
  -- ⊢ - | {Box.box X?} + R? = {Box.box ({Elem.a} + Y?)} + {Box.box {Elem.b}} | -
  checkpoint
  -- identify Box.box X? ~ Box.box {Elem.b}
  refine identify (fun (X?, _, _) => Box.box X?) (fun (_, _, _) => Box.box {Elem.b}) ?_ ?_
  · -- equal:
    -- ⊢ - | Box.box X? = Box.box {Elem.b}; {Box.box X?} + R? = {Box.box ({Elem.a} + Y?)} + {Box.box {Elem.b}} | -
    checkpoint
    -- decomp Box.box X? = Box.box {Elem.b}
    refine decomp [fun (X?, _, _) => X? = {Elem.b}]
        (fun (X?, Y?, R?) h => by acu_decomp [problem, Box.box.injEq]) ?_
    -- ⊢ - | X? = {Elem.b}; {Box.box X?} + R? = {Box.box ({Elem.a} + Y?)} + {Box.box {Elem.b}} | -
    checkpoint
    -- elim X? := {Elem.b}
    refine elim (fun (Y?, R?) => ({Elem.b}, Y?, R?))
        (fun (X?, Y?, R?) h => ⟨(Y?, R?), by acu_elim [problem]⟩) ?_
    -- ⊢ X? := {Elem.b} | R? + {Box.box {Elem.b}} = {Box.box {Elem.b}} + {Box.box ({Elem.a} + Y?)} | -
    checkpoint
    -- solve R? + {Box.box {Elem.b}} = {Box.box {Elem.b}} + {Box.box ({Elem.a} + Y?)}
    refine solve
        { V := fun (_, R?) => ![R?], rest := fun (Y?, _) => Y?,
          glue := fun Y? V => (Y?, V 0), hglue := fun _ => rfl }
        (fun Y? => ![Box.box {Elem.b}, Box.box ({Elem.a} + Y?)])
        { L := ![1], R := ![0], La := ![1, 0], Ra := ![1, 1], cp := fun c c' => (c == 0 && c' == 1) || (c == 1 && c' == 0) }
        { P := ![[![0]], [![1]]], B := ![] }
        ⟨by decide, by decide, by decide,
          S2_of_list _ _ _ _ _ _ [[0], [1], [0, 1]] (by decide) (by acu_cliques), by acu_basis⟩
        (fun (Y?, R?) h => by try simp only [unifiedBy, problem] at h; acu_side h)
        (fun (Y?, R?) h hD => by acu_distinct) ?_
    intro π hπ; simp [choices] at hπ; subst hπ
    -- branch (0) (1)
    refine rename (fun Y? => (Y?, ![]))
        (fun (Y?, Z) => Y?)
        (fun (Y?, Z) => Prod.ext rfl (funext fun i => i.elim0)) ?_
    -- ⊢ R? := {Box.box ({Elem.a} + Y?)}, X? := {Elem.b} | - | -
    checkpoint
    -- cover answer 1 with U1! := Y?
    exact cover answer1 (by simp [answers]) fun Y? _ _ => ⟨Y?, by acu_cover⟩
  · -- distinct:
    -- ⊢ - | {Box.box X?} + R? = {Box.box ({Elem.a} + Y?)} + {Box.box {Elem.b}} | Box.box X? ≠ Box.box {Elem.b}
    checkpoint
    -- identify Box.box X? ~ Box.box ({Elem.a} + Y?)
    refine identify (fun (X?, _, _) => Box.box X?) (fun (_, Y?, _) => Box.box ({Elem.a} + Y?)) ?_ ?_
    · -- equal:
      -- ⊢ - | Box.box X? = Box.box ({Elem.a} + Y?); {Box.box X?} + R? = {Box.box ({Elem.a} + Y?)} + {Box.box {Elem.b}} | Box.box X? ≠ Box.box {Elem.b}
      checkpoint
      -- decomp Box.box X? = Box.box ({Elem.a} + Y?)
      refine decomp [fun (X?, Y?, _) => X? = {Elem.a} + Y?]
          (fun (X?, Y?, R?) h => by acu_decomp [problem, Box.box.injEq]) ?_
      -- ⊢ - | X? = {Elem.a} + Y?; {Box.box X?} + R? = {Box.box ({Elem.a} + Y?)} + {Box.box {Elem.b}} | Box.box X? ≠ Box.box {Elem.b}
      checkpoint
      -- elim X? := {Elem.a} + Y?
      refine elim (fun (Y?, R?) => ({Elem.a} + Y?, Y?, R?))
          (fun (X?, Y?, R?) h => ⟨(Y?, R?), by acu_elim [problem]⟩) ?_
      -- ⊢ X? := {Elem.a} + Y? | R? + {Box.box ({Elem.a} + Y?)} = {Box.box {Elem.b}} + {Box.box ({Elem.a} + Y?)} | Box.box ({Elem.a} + Y?) ≠ Box.box {Elem.b}
      checkpoint
      -- solve R? + {Box.box ({Elem.a} + Y?)} = {Box.box {Elem.b}} + {Box.box ({Elem.a} + Y?)}
      refine solve
          { V := fun (_, R?) => ![R?], rest := fun (Y?, _) => Y?,
            glue := fun Y? V => (Y?, V 0), hglue := fun _ => rfl }
          (fun Y? => ![Box.box ({Elem.a} + Y?), Box.box {Elem.b}])
          { L := ![1], R := ![0], La := ![1, 0], Ra := ![1, 1], cp := fun _ _ => false }
          { P := ![[![0]], [![1]]], B := ![] }
          ⟨by decide, by decide, by decide,
            S2_of_list _ _ _ _ _ _ [[0], [1]] (by decide) (by acu_cliques), by acu_basis⟩
          (fun (Y?, R?) h => by try simp only [unifiedBy, problem] at h; acu_side h)
          (fun (Y?, R?) h hD => by acu_distinct) ?_
      intro π hπ; simp [choices] at hπ; subst hπ
      -- branch (0) (1)
      refine rename (fun Y? => (Y?, ![]))
          (fun (Y?, Z) => Y?)
          (fun (Y?, Z) => Prod.ext rfl (funext fun i => i.elim0)) ?_
      -- ⊢ R? := {Box.box {Elem.b}}, X? := {Elem.a} + Y? | - | Box.box ({Elem.a} + Y?) ≠ Box.box {Elem.b}
      checkpoint
      -- cover answer 3 with U1! := Y?
      exact cover answer3 (by simp [answers]) fun Y? _ _ => ⟨Y?, by acu_cover⟩
    · -- distinct:
      -- ⊢ - | {Box.box X?} + R? = {Box.box ({Elem.a} + Y?)} + {Box.box {Elem.b}} | Box.box X? ≠ Box.box {Elem.b}; Box.box X? ≠ Box.box ({Elem.a} + Y?)
      checkpoint
      -- solve {Box.box X?} + R? = {Box.box ({Elem.a} + Y?)} + {Box.box {Elem.b}}
      refine solve
          { V := fun (_, _, R?) => ![R?], rest := fun (X?, Y?, _) => (X?, Y?),
            glue := fun (X?, Y?) V => (X?, Y?, V 0), hglue := fun _ => rfl }
          (fun (X?, Y?) => ![Box.box X?, Box.box ({Elem.a} + Y?), Box.box {Elem.b}])
          { L := ![1], R := ![0], La := ![1, 0, 0], Ra := ![0, 1, 1], cp := fun c c' => (c == 1 && c' == 2) || (c == 2 && c' == 1) }
          { P := ![[], [![1]], [![1]]], B := ![] }
          ⟨by decide, by decide, by decide,
            S2_of_list _ _ _ _ _ _ [[0], [1], [2], [1, 2]] (by decide) (by acu_cliques), by acu_basis⟩
          (fun (X?, Y?, R?) h => by try simp only [unifiedBy, problem] at h; acu_side h)
          (fun (X?, Y?, R?) h hD => by acu_distinct) ?_
      intro π hπ; simp [choices] at hπ

end Pipeline.T6
