import Tiny.conPanna.Unification.Certification.Tactics

/-! A linear equation with 3 and 2 bag variables. -/

/- certify
{
  "namespace": "Pipeline.S2Linear32",
  "context": "Bag × Bag × Bag × Bag × Bag",
  "vars": [
    "X1?",
    "X2?",
    "X3?",
    "Y1?",
    "Y2?"
  ],
  "ops": {}
}
-/

open Unification Certification

namespace Pipeline.S2Linear32

inductive Elem where
  | a

abbrev Bag := ACU Elem

def problem : Problem Bag (Bag × Bag × Bag × Bag × Bag) :=
  .bind fun (X1?, X2?, X3?, Y1?, Y2?) =>
    (X1? + X2? + X3?, Y1? + Y2?)

/-! ## Generated from s2_linear32.deriv by producer/tools/compile.py -/

def answer0 : Unifier (Bag × Bag × Bag × Bag × Bag) :=
  .subst ⟨∅, ∅, ∅, ∅, ∅⟩
def answer1 : Unifier (Bag × Bag × Bag × Bag × Bag) :=
  .bind fun U1! => .subst ⟨U1!, ∅, ∅, U1!, ∅⟩
def answer2 : Unifier (Bag × Bag × Bag × Bag × Bag) :=
  .bind fun U1! => .subst ⟨∅, U1!, ∅, U1!, ∅⟩
def answer3 : Unifier (Bag × Bag × Bag × Bag × Bag) :=
  .bind fun (U1!, U2!) => .subst ⟨U1!, U2!, ∅, U1! + U2!, ∅⟩
def answer4 : Unifier (Bag × Bag × Bag × Bag × Bag) :=
  .bind fun U1! => .subst ⟨∅, ∅, U1!, U1!, ∅⟩
def answer5 : Unifier (Bag × Bag × Bag × Bag × Bag) :=
  .bind fun (U1!, U2!) => .subst ⟨U1!, ∅, U2!, U1! + U2!, ∅⟩
def answer6 : Unifier (Bag × Bag × Bag × Bag × Bag) :=
  .bind fun (U1!, U2!) => .subst ⟨∅, U1!, U2!, U1! + U2!, ∅⟩
def answer7 : Unifier (Bag × Bag × Bag × Bag × Bag) :=
  .bind fun (U1!, U2!, U3!) => .subst ⟨U1!, U2!, U3!, U1! + U2! + U3!, ∅⟩
def answer8 : Unifier (Bag × Bag × Bag × Bag × Bag) :=
  .bind fun U1! => .subst ⟨U1!, ∅, ∅, ∅, U1!⟩
def answer9 : Unifier (Bag × Bag × Bag × Bag × Bag) :=
  .bind fun (U1!, U2!) => .subst ⟨U1! + U2!, ∅, ∅, U1!, U2!⟩
def answer10 : Unifier (Bag × Bag × Bag × Bag × Bag) :=
  .bind fun (U1!, U2!) => .subst ⟨U2!, U1!, ∅, U1!, U2!⟩
def answer11 : Unifier (Bag × Bag × Bag × Bag × Bag) :=
  .bind fun (U1!, U2!, U3!) => .subst ⟨U2! + U3!, U1!, ∅, U1! + U3!, U2!⟩
def answer12 : Unifier (Bag × Bag × Bag × Bag × Bag) :=
  .bind fun (U1!, U2!) => .subst ⟨U2!, ∅, U1!, U1!, U2!⟩
def answer13 : Unifier (Bag × Bag × Bag × Bag × Bag) :=
  .bind fun (U1!, U2!, U3!) => .subst ⟨U2! + U3!, ∅, U1!, U1! + U3!, U2!⟩
def answer14 : Unifier (Bag × Bag × Bag × Bag × Bag) :=
  .bind fun (U1!, U2!, U3!) => .subst ⟨U3!, U1!, U2!, U1! + U2!, U3!⟩
def answer15 : Unifier (Bag × Bag × Bag × Bag × Bag) :=
  .bind fun (U1!, U2!, U3!, U4!) => .subst ⟨U3! + U4!, U1!, U2!, U1! + U2! + U4!, U3!⟩
def answer16 : Unifier (Bag × Bag × Bag × Bag × Bag) :=
  .bind fun U1! => .subst ⟨∅, U1!, ∅, ∅, U1!⟩
def answer17 : Unifier (Bag × Bag × Bag × Bag × Bag) :=
  .bind fun (U1!, U2!) => .subst ⟨U1!, U2!, ∅, U1!, U2!⟩
def answer18 : Unifier (Bag × Bag × Bag × Bag × Bag) :=
  .bind fun (U1!, U2!) => .subst ⟨∅, U1! + U2!, ∅, U1!, U2!⟩
def answer19 : Unifier (Bag × Bag × Bag × Bag × Bag) :=
  .bind fun (U1!, U2!, U3!) => .subst ⟨U1!, U2! + U3!, ∅, U1! + U3!, U2!⟩
def answer20 : Unifier (Bag × Bag × Bag × Bag × Bag) :=
  .bind fun (U1!, U2!) => .subst ⟨∅, U2!, U1!, U1!, U2!⟩
def answer21 : Unifier (Bag × Bag × Bag × Bag × Bag) :=
  .bind fun (U1!, U2!, U3!) => .subst ⟨U1!, U3!, U2!, U1! + U2!, U3!⟩
def answer22 : Unifier (Bag × Bag × Bag × Bag × Bag) :=
  .bind fun (U1!, U2!, U3!) => .subst ⟨∅, U2! + U3!, U1!, U1! + U3!, U2!⟩
def answer23 : Unifier (Bag × Bag × Bag × Bag × Bag) :=
  .bind fun (U1!, U2!, U3!, U4!) => .subst ⟨U1!, U3! + U4!, U2!, U1! + U2! + U4!, U3!⟩
def answer24 : Unifier (Bag × Bag × Bag × Bag × Bag) :=
  .bind fun (U1!, U2!) => .subst ⟨U1!, U2!, ∅, ∅, U1! + U2!⟩
def answer25 : Unifier (Bag × Bag × Bag × Bag × Bag) :=
  .bind fun (U1!, U2!, U3!) => .subst ⟨U2! + U3!, U1!, ∅, U2!, U1! + U3!⟩
def answer26 : Unifier (Bag × Bag × Bag × Bag × Bag) :=
  .bind fun (U1!, U2!, U3!) => .subst ⟨U1!, U2! + U3!, ∅, U2!, U1! + U3!⟩
def answer27 : Unifier (Bag × Bag × Bag × Bag × Bag) :=
  .bind fun (U1!, U2!, U3!, U4!) => .subst ⟨U1! + U3!, U2! + U4!, ∅, U1! + U2!, U3! + U4!⟩
def answer28 : Unifier (Bag × Bag × Bag × Bag × Bag) :=
  .bind fun (U1!, U2!, U3!) => .subst ⟨U1!, U2!, U3!, U3!, U1! + U2!⟩
def answer29 : Unifier (Bag × Bag × Bag × Bag × Bag) :=
  .bind fun (U1!, U2!, U3!, U4!) => .subst ⟨U3! + U4!, U1!, U2!, U2! + U3!, U1! + U4!⟩
def answer30 : Unifier (Bag × Bag × Bag × Bag × Bag) :=
  .bind fun (U1!, U2!, U3!, U4!) => .subst ⟨U1!, U3! + U4!, U2!, U2! + U3!, U1! + U4!⟩
def answer31 : Unifier (Bag × Bag × Bag × Bag × Bag) :=
  .bind fun (U1!, U2!, U3!, U4!, U5!) => .subst ⟨U2! + U4!, U3! + U5!, U1!, U1! + U2! + U3!, U4! + U5!⟩
def answer32 : Unifier (Bag × Bag × Bag × Bag × Bag) :=
  .bind fun U1! => .subst ⟨∅, ∅, U1!, ∅, U1!⟩
def answer33 : Unifier (Bag × Bag × Bag × Bag × Bag) :=
  .bind fun (U1!, U2!) => .subst ⟨U1!, ∅, U2!, U1!, U2!⟩
def answer34 : Unifier (Bag × Bag × Bag × Bag × Bag) :=
  .bind fun (U1!, U2!) => .subst ⟨∅, U1!, U2!, U1!, U2!⟩
def answer35 : Unifier (Bag × Bag × Bag × Bag × Bag) :=
  .bind fun (U1!, U2!, U3!) => .subst ⟨U1!, U2!, U3!, U1! + U2!, U3!⟩
def answer36 : Unifier (Bag × Bag × Bag × Bag × Bag) :=
  .bind fun (U1!, U2!) => .subst ⟨∅, ∅, U1! + U2!, U1!, U2!⟩
def answer37 : Unifier (Bag × Bag × Bag × Bag × Bag) :=
  .bind fun (U1!, U2!, U3!) => .subst ⟨U1!, ∅, U2! + U3!, U1! + U3!, U2!⟩
def answer38 : Unifier (Bag × Bag × Bag × Bag × Bag) :=
  .bind fun (U1!, U2!, U3!) => .subst ⟨∅, U1!, U2! + U3!, U1! + U3!, U2!⟩
def answer39 : Unifier (Bag × Bag × Bag × Bag × Bag) :=
  .bind fun (U1!, U2!, U3!, U4!) => .subst ⟨U1!, U2!, U3! + U4!, U1! + U2! + U4!, U3!⟩
def answer40 : Unifier (Bag × Bag × Bag × Bag × Bag) :=
  .bind fun (U1!, U2!) => .subst ⟨U1!, ∅, U2!, ∅, U1! + U2!⟩
def answer41 : Unifier (Bag × Bag × Bag × Bag × Bag) :=
  .bind fun (U1!, U2!, U3!) => .subst ⟨U2! + U3!, ∅, U1!, U2!, U1! + U3!⟩
def answer42 : Unifier (Bag × Bag × Bag × Bag × Bag) :=
  .bind fun (U1!, U2!, U3!) => .subst ⟨U1!, U3!, U2!, U3!, U1! + U2!⟩
def answer43 : Unifier (Bag × Bag × Bag × Bag × Bag) :=
  .bind fun (U1!, U2!, U3!, U4!) => .subst ⟨U3! + U4!, U1!, U2!, U1! + U3!, U2! + U4!⟩
def answer44 : Unifier (Bag × Bag × Bag × Bag × Bag) :=
  .bind fun (U1!, U2!, U3!) => .subst ⟨U1!, ∅, U2! + U3!, U2!, U1! + U3!⟩
def answer45 : Unifier (Bag × Bag × Bag × Bag × Bag) :=
  .bind fun (U1!, U2!, U3!, U4!) => .subst ⟨U1! + U3!, ∅, U2! + U4!, U1! + U2!, U3! + U4!⟩
def answer46 : Unifier (Bag × Bag × Bag × Bag × Bag) :=
  .bind fun (U1!, U2!, U3!, U4!) => .subst ⟨U1!, U2!, U3! + U4!, U2! + U3!, U1! + U4!⟩
def answer47 : Unifier (Bag × Bag × Bag × Bag × Bag) :=
  .bind fun (U1!, U2!, U3!, U4!, U5!) => .subst ⟨U2! + U4!, U1!, U3! + U5!, U1! + U2! + U3!, U4! + U5!⟩
def answer48 : Unifier (Bag × Bag × Bag × Bag × Bag) :=
  .bind fun (U1!, U2!) => .subst ⟨∅, U1!, U2!, ∅, U1! + U2!⟩
def answer49 : Unifier (Bag × Bag × Bag × Bag × Bag) :=
  .bind fun (U1!, U2!, U3!) => .subst ⟨U3!, U1!, U2!, U3!, U1! + U2!⟩
def answer50 : Unifier (Bag × Bag × Bag × Bag × Bag) :=
  .bind fun (U1!, U2!, U3!) => .subst ⟨∅, U2! + U3!, U1!, U2!, U1! + U3!⟩
def answer51 : Unifier (Bag × Bag × Bag × Bag × Bag) :=
  .bind fun (U1!, U2!, U3!, U4!) => .subst ⟨U1!, U3! + U4!, U2!, U1! + U3!, U2! + U4!⟩
def answer52 : Unifier (Bag × Bag × Bag × Bag × Bag) :=
  .bind fun (U1!, U2!, U3!) => .subst ⟨∅, U1!, U2! + U3!, U2!, U1! + U3!⟩
def answer53 : Unifier (Bag × Bag × Bag × Bag × Bag) :=
  .bind fun (U1!, U2!, U3!, U4!) => .subst ⟨U1!, U2!, U3! + U4!, U1! + U3!, U2! + U4!⟩
def answer54 : Unifier (Bag × Bag × Bag × Bag × Bag) :=
  .bind fun (U1!, U2!, U3!, U4!) => .subst ⟨∅, U1! + U3!, U2! + U4!, U1! + U2!, U3! + U4!⟩
def answer55 : Unifier (Bag × Bag × Bag × Bag × Bag) :=
  .bind fun (U1!, U2!, U3!, U4!, U5!) => .subst ⟨U1!, U2! + U4!, U3! + U5!, U1! + U2! + U3!, U4! + U5!⟩
def answer56 : Unifier (Bag × Bag × Bag × Bag × Bag) :=
  .bind fun (U1!, U2!, U3!) => .subst ⟨U1!, U2!, U3!, ∅, U1! + U2! + U3!⟩
def answer57 : Unifier (Bag × Bag × Bag × Bag × Bag) :=
  .bind fun (U1!, U2!, U3!, U4!) => .subst ⟨U3! + U4!, U1!, U2!, U3!, U1! + U2! + U4!⟩
def answer58 : Unifier (Bag × Bag × Bag × Bag × Bag) :=
  .bind fun (U1!, U2!, U3!, U4!) => .subst ⟨U1!, U3! + U4!, U2!, U3!, U1! + U2! + U4!⟩
def answer59 : Unifier (Bag × Bag × Bag × Bag × Bag) :=
  .bind fun (U1!, U2!, U3!, U4!, U5!) => .subst ⟨U2! + U4!, U3! + U5!, U1!, U2! + U3!, U1! + U4! + U5!⟩
def answer60 : Unifier (Bag × Bag × Bag × Bag × Bag) :=
  .bind fun (U1!, U2!, U3!, U4!) => .subst ⟨U1!, U2!, U3! + U4!, U3!, U1! + U2! + U4!⟩
def answer61 : Unifier (Bag × Bag × Bag × Bag × Bag) :=
  .bind fun (U1!, U2!, U3!, U4!, U5!) => .subst ⟨U2! + U4!, U1!, U3! + U5!, U2! + U3!, U1! + U4! + U5!⟩
def answer62 : Unifier (Bag × Bag × Bag × Bag × Bag) :=
  .bind fun (U1!, U2!, U3!, U4!, U5!) => .subst ⟨U1!, U2! + U4!, U3! + U5!, U2! + U3!, U1! + U4! + U5!⟩
def answer63 : Unifier (Bag × Bag × Bag × Bag × Bag) :=
  .bind fun (U1!, U2!, U3!, U4!, U5!, U6!) => .subst ⟨U1! + U4!, U2! + U5!, U3! + U6!, U1! + U2! + U3!, U4! + U5! + U6!⟩
def answers : UnifierSet (Bag × Bag × Bag × Bag × Bag) :=
  [answer0, answer1, answer2, answer3, answer4, answer5, answer6, answer7, answer8, answer9, answer10, answer11, answer12, answer13, answer14, answer15, answer16, answer17, answer18, answer19, answer20, answer21, answer22, answer23, answer24, answer25, answer26, answer27, answer28, answer29, answer30, answer31, answer32, answer33, answer34, answer35, answer36, answer37, answer38, answer39, answer40, answer41, answer42, answer43, answer44, answer45, answer46, answer47, answer48, answer49, answer50, answer51, answer52, answer53, answer54, answer55, answer56, answer57, answer58, answer59, answer60, answer61, answer62, answer63]

theorem complete : UnifierSet.Complete problem answers := by
  rw [← start_iff]
  -- ⊢ - | X1? + X2? + X3? = Y1? + Y2? | -
  -- solve X1? + X2? + X3? = Y1? + Y2?
  refine solve (V := fun (X1?, X2?, X3?, Y1?, Y2?) => ![X1?, X2?, X3?, Y1?, Y2?]) (rest := fun (_, _, _, _, _) => ())
      (glue := fun _ V => (V 0, V 1, V 2, V 3, V 4)) (hglue := fun _ => rfl)
      (a := fun _ => ![]) (L := ![1, 1, 1, 0, 0]) (R := ![0, 0, 0, 1, 1]) (La := ![]) (Ra := ![])
      (E' := fun (_, _, _, _, _) => True) (cp := fun _ _ => false)
      (P := ![]) (B := ![![1, 0, 0, 1, 0], ![0, 1, 0, 1, 0], ![0, 0, 1, 1, 0], ![1, 0, 0, 0, 1], ![0, 1, 0, 0, 1], ![0, 0, 1, 0, 1]])
      (fun (X1?, X2?, X3?, Y1?, Y2?) h hD => ⟨by try simp only [State.start, Problem.unifies, problem] at h; acu_side h, trivial, by acu_distinct⟩)
      (by decide) (by decide) (by decide)
      (S2_of_list _ _ _ _ _ _ [] (by decide) (by acu_cliques)) (by acu_basis) ?_
  intro π hπ; simp [choices] at hπ; subst hπ
  -- branch 
  refine rename (fun (Z1, Z2, Z3, Z4, Z5, Z6) => ((), ![Z1, Z2, Z3, Z4, Z5, Z6]))
      (fun (_, Z) => (Z 0, Z 1, Z 2, Z 3, Z 4, Z 5))
      (fun (_, Z) => Prod.ext rfl (funext fun i => by fin_cases i <;> rfl)) ?_
  -- ⊢ X1? := Z1 + Z4, X2? := Z2 + Z5, X3? := Z3 + Z6, Y1? := Z1 + Z2 + Z3, Y2? := Z4 + Z5 + Z6 | - | -
  -- cover answer 63 with U1! := Z1, U2! := Z2, U3! := Z3, U4! := Z4, U5! := Z5, U6! := Z6
  exact cover answer63 (by simp [answers]) fun (Z1, Z2, Z3, Z4, Z5, Z6) _ _ => ⟨(Z1, Z2, Z3, Z4, Z5, Z6), by acu_cover⟩

end Pipeline.S2Linear32
