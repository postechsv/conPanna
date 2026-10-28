import conPanna.Unification.Certification.Tactics

/-! The worked example of documentation/worked-example.html:
R? + {f ({a} + X?)} + {f Y?} =? S? + T? + {f ({a} + W?)}. -/

/- certify
{
  "namespace": "Pipeline.T7",
  "context": "Fruits × Fruits × Fruits × Baskets × Baskets × Baskets",
  "vars": ["X?", "Y?", "W?", "R?", "S?", "T?"],
  "ops": {"a": "Fruit.a", "b": "Fruit.b", "{_}": "Basket.f"}
}
-/

open Unification Certification

namespace Pipeline.T7

inductive Fruit where
  | a
  | b

abbrev Fruits := ACU Fruit

inductive Basket where
  | f (x : Fruits)

abbrev Baskets := ACU Basket

def problem : Problem Baskets (Fruits × Fruits × Fruits × Baskets × Baskets × Baskets) :=
  .bind fun (X?, Y?, W?, R?, S?, T?) =>
    (R? + {Basket.f ({Fruit.a} + X?)} + {Basket.f Y?}, S? + T? + {Basket.f ({Fruit.a} + W?)})

/-! ## Generated from t7_example.deriv by producer/tools/compile.py -/

def answer0 : Unifier (Fruits × Fruits × Fruits × Baskets × Baskets × Baskets) :=
  .bind fun U1! => ⟨∅, U1!, ∅, {Basket.f {Fruit.a}}, {Basket.f {Fruit.a}} + {Basket.f U1!}, ∅⟩
def answer1 : Unifier (Fruits × Fruits × Fruits × Baskets × Baskets × Baskets) :=
  .bind fun (U1!, U2!) => ⟨U2!, U1!, ∅, {Basket.f {Fruit.a}}, {Basket.f U1!} + {Basket.f ({Fruit.a} + U2!)}, ∅⟩
def answer2 : Unifier (Fruits × Fruits × Fruits × Baskets × Baskets × Baskets) :=
  .bind fun (U1!, U2!) => ⟨∅, U1!, U2!, {Basket.f ({Fruit.a} + U2!)}, {Basket.f {Fruit.a}} + {Basket.f U1!}, ∅⟩
def answer3 : Unifier (Fruits × Fruits × Fruits × Baskets × Baskets × Baskets) :=
  .bind fun (U1!, U2!, U3!) => ⟨U2!, U1!, U3!, {Basket.f ({Fruit.a} + U3!)}, {Basket.f U1!} + {Basket.f ({Fruit.a} + U2!)}, ∅⟩
def answer4 : Unifier (Fruits × Fruits × Fruits × Baskets × Baskets × Baskets) :=
  .bind fun (U1!, U2!) => ⟨∅, U1!, ∅, U2! + {Basket.f {Fruit.a}}, U2! + {Basket.f {Fruit.a}} + {Basket.f U1!}, ∅⟩
def answer5 : Unifier (Fruits × Fruits × Fruits × Baskets × Baskets × Baskets) :=
  .bind fun (U1!, U2!, U3!) => ⟨U2!, U1!, ∅, U3! + {Basket.f {Fruit.a}}, U3! + {Basket.f U1!} + {Basket.f ({Fruit.a} + U2!)}, ∅⟩
def answer6 : Unifier (Fruits × Fruits × Fruits × Baskets × Baskets × Baskets) :=
  .bind fun (U1!, U2!, U3!) => ⟨∅, U1!, U2!, U3! + {Basket.f ({Fruit.a} + U2!)}, U3! + {Basket.f {Fruit.a}} + {Basket.f U1!}, ∅⟩
def answer7 : Unifier (Fruits × Fruits × Fruits × Baskets × Baskets × Baskets) :=
  .bind fun (U1!, U2!, U3!, U4!) => ⟨U2!, U1!, U3!, U4! + {Basket.f ({Fruit.a} + U3!)}, U4! + {Basket.f U1!} + {Basket.f ({Fruit.a} + U2!)}, ∅⟩
def answer8 : Unifier (Fruits × Fruits × Fruits × Baskets × Baskets × Baskets) :=
  .bind fun (U1!, U2!) => ⟨∅, U1!, ∅, U2! + {Basket.f {Fruit.a}}, {Basket.f {Fruit.a}} + {Basket.f U1!}, U2!⟩
def answer9 : Unifier (Fruits × Fruits × Fruits × Baskets × Baskets × Baskets) :=
  .bind fun (U1!, U2!, U3!) => ⟨U2!, U1!, ∅, U3! + {Basket.f {Fruit.a}}, {Basket.f U1!} + {Basket.f ({Fruit.a} + U2!)}, U3!⟩
def answer10 : Unifier (Fruits × Fruits × Fruits × Baskets × Baskets × Baskets) :=
  .bind fun (U1!, U2!, U3!) => ⟨∅, U1!, U3!, U2! + {Basket.f ({Fruit.a} + U3!)}, {Basket.f {Fruit.a}} + {Basket.f U1!}, U2!⟩
def answer11 : Unifier (Fruits × Fruits × Fruits × Baskets × Baskets × Baskets) :=
  .bind fun (U1!, U2!, U3!, U4!) => ⟨U2!, U1!, U4!, U3! + {Basket.f ({Fruit.a} + U4!)}, {Basket.f U1!} + {Basket.f ({Fruit.a} + U2!)}, U3!⟩
def answer12 : Unifier (Fruits × Fruits × Fruits × Baskets × Baskets × Baskets) :=
  .bind fun (U1!, U2!, U3!) => ⟨∅, U1!, ∅, U2! + U3! + {Basket.f {Fruit.a}}, U3! + {Basket.f {Fruit.a}} + {Basket.f U1!}, U2!⟩
def answer13 : Unifier (Fruits × Fruits × Fruits × Baskets × Baskets × Baskets) :=
  .bind fun (U1!, U2!, U3!, U4!) => ⟨U2!, U1!, ∅, U3! + U4! + {Basket.f {Fruit.a}}, U4! + {Basket.f U1!} + {Basket.f ({Fruit.a} + U2!)}, U3!⟩
def answer14 : Unifier (Fruits × Fruits × Fruits × Baskets × Baskets × Baskets) :=
  .bind fun (U1!, U2!, U3!, U4!) => ⟨∅, U1!, U3!, U2! + U4! + {Basket.f ({Fruit.a} + U3!)}, U4! + {Basket.f {Fruit.a}} + {Basket.f U1!}, U2!⟩
def answer15 : Unifier (Fruits × Fruits × Fruits × Baskets × Baskets × Baskets) :=
  .bind fun (U1!, U2!, U3!, U4!, U5!) => ⟨U2!, U1!, U4!, U3! + U5! + {Basket.f ({Fruit.a} + U4!)}, U5! + {Basket.f U1!} + {Basket.f ({Fruit.a} + U2!)}, U3!⟩
def answer16 : Unifier (Fruits × Fruits × Fruits × Baskets × Baskets × Baskets) :=
  .bind fun U1! => ⟨∅, U1!, ∅, {Basket.f {Fruit.a}}, {Basket.f {Fruit.a}}, {Basket.f U1!}⟩
def answer17 : Unifier (Fruits × Fruits × Fruits × Baskets × Baskets × Baskets) :=
  .bind fun (U1!, U2!) => ⟨U2!, U1!, ∅, {Basket.f {Fruit.a}}, {Basket.f ({Fruit.a} + U2!)}, {Basket.f U1!}⟩
def answer18 : Unifier (Fruits × Fruits × Fruits × Baskets × Baskets × Baskets) :=
  .bind fun (U1!, U2!) => ⟨∅, U1!, U2!, {Basket.f ({Fruit.a} + U2!)}, {Basket.f {Fruit.a}}, {Basket.f U1!}⟩
def answer19 : Unifier (Fruits × Fruits × Fruits × Baskets × Baskets × Baskets) :=
  .bind fun (U1!, U2!, U3!) => ⟨U2!, U1!, U3!, {Basket.f ({Fruit.a} + U3!)}, {Basket.f ({Fruit.a} + U2!)}, {Basket.f U1!}⟩
def answer20 : Unifier (Fruits × Fruits × Fruits × Baskets × Baskets × Baskets) :=
  .bind fun (U1!, U2!) => ⟨∅, U1!, ∅, U2! + {Basket.f {Fruit.a}}, U2! + {Basket.f {Fruit.a}}, {Basket.f U1!}⟩
def answer21 : Unifier (Fruits × Fruits × Fruits × Baskets × Baskets × Baskets) :=
  .bind fun (U1!, U2!, U3!) => ⟨U2!, U1!, ∅, U3! + {Basket.f {Fruit.a}}, U3! + {Basket.f ({Fruit.a} + U2!)}, {Basket.f U1!}⟩
def answer22 : Unifier (Fruits × Fruits × Fruits × Baskets × Baskets × Baskets) :=
  .bind fun (U1!, U2!, U3!) => ⟨∅, U1!, U2!, U3! + {Basket.f ({Fruit.a} + U2!)}, U3! + {Basket.f {Fruit.a}}, {Basket.f U1!}⟩
def answer23 : Unifier (Fruits × Fruits × Fruits × Baskets × Baskets × Baskets) :=
  .bind fun (U1!, U2!, U3!, U4!) => ⟨U2!, U1!, U3!, U4! + {Basket.f ({Fruit.a} + U3!)}, U4! + {Basket.f ({Fruit.a} + U2!)}, {Basket.f U1!}⟩
def answer24 : Unifier (Fruits × Fruits × Fruits × Baskets × Baskets × Baskets) :=
  .bind fun (U1!, U2!) => ⟨∅, U1!, ∅, U2! + {Basket.f {Fruit.a}}, {Basket.f {Fruit.a}}, U2! + {Basket.f U1!}⟩
def answer25 : Unifier (Fruits × Fruits × Fruits × Baskets × Baskets × Baskets) :=
  .bind fun (U1!, U2!, U3!) => ⟨U2!, U1!, ∅, U3! + {Basket.f {Fruit.a}}, {Basket.f ({Fruit.a} + U2!)}, U3! + {Basket.f U1!}⟩
def answer26 : Unifier (Fruits × Fruits × Fruits × Baskets × Baskets × Baskets) :=
  .bind fun (U1!, U2!, U3!) => ⟨∅, U1!, U2!, U3! + {Basket.f ({Fruit.a} + U2!)}, {Basket.f {Fruit.a}}, U3! + {Basket.f U1!}⟩
def answer27 : Unifier (Fruits × Fruits × Fruits × Baskets × Baskets × Baskets) :=
  .bind fun (U1!, U2!, U3!, U4!) => ⟨U2!, U1!, U3!, U4! + {Basket.f ({Fruit.a} + U3!)}, {Basket.f ({Fruit.a} + U2!)}, U4! + {Basket.f U1!}⟩
def answer28 : Unifier (Fruits × Fruits × Fruits × Baskets × Baskets × Baskets) :=
  .bind fun (U1!, U2!, U3!) => ⟨∅, U1!, ∅, U2! + U3! + {Basket.f {Fruit.a}}, U2! + {Basket.f {Fruit.a}}, U3! + {Basket.f U1!}⟩
def answer29 : Unifier (Fruits × Fruits × Fruits × Baskets × Baskets × Baskets) :=
  .bind fun (U1!, U2!, U3!, U4!) => ⟨U2!, U1!, ∅, U3! + U4! + {Basket.f {Fruit.a}}, U3! + {Basket.f ({Fruit.a} + U2!)}, U4! + {Basket.f U1!}⟩
def answer30 : Unifier (Fruits × Fruits × Fruits × Baskets × Baskets × Baskets) :=
  .bind fun (U1!, U2!, U3!, U4!) => ⟨∅, U1!, U2!, U3! + U4! + {Basket.f ({Fruit.a} + U2!)}, U3! + {Basket.f {Fruit.a}}, U4! + {Basket.f U1!}⟩
def answer31 : Unifier (Fruits × Fruits × Fruits × Baskets × Baskets × Baskets) :=
  .bind fun (U1!, U2!, U3!, U4!, U5!) => ⟨U2!, U1!, U3!, U4! + U5! + {Basket.f ({Fruit.a} + U3!)}, U4! + {Basket.f ({Fruit.a} + U2!)}, U5! + {Basket.f U1!}⟩
def answer32 : Unifier (Fruits × Fruits × Fruits × Baskets × Baskets × Baskets) :=
  .bind fun U1! => ⟨∅, U1!, ∅, {Basket.f {Fruit.a}}, {Basket.f U1!}, {Basket.f {Fruit.a}}⟩
def answer33 : Unifier (Fruits × Fruits × Fruits × Baskets × Baskets × Baskets) :=
  .bind fun (U1!, U2!) => ⟨U2!, U1!, ∅, {Basket.f {Fruit.a}}, {Basket.f U1!}, {Basket.f ({Fruit.a} + U2!)}⟩
def answer34 : Unifier (Fruits × Fruits × Fruits × Baskets × Baskets × Baskets) :=
  .bind fun (U1!, U2!) => ⟨∅, U1!, U2!, {Basket.f ({Fruit.a} + U2!)}, {Basket.f U1!}, {Basket.f {Fruit.a}}⟩
def answer35 : Unifier (Fruits × Fruits × Fruits × Baskets × Baskets × Baskets) :=
  .bind fun (U1!, U2!, U3!) => ⟨U2!, U1!, U3!, {Basket.f ({Fruit.a} + U3!)}, {Basket.f U1!}, {Basket.f ({Fruit.a} + U2!)}⟩
def answer36 : Unifier (Fruits × Fruits × Fruits × Baskets × Baskets × Baskets) :=
  .bind fun (U1!, U2!) => ⟨∅, U1!, ∅, U2! + {Basket.f {Fruit.a}}, U2! + {Basket.f U1!}, {Basket.f {Fruit.a}}⟩
def answer37 : Unifier (Fruits × Fruits × Fruits × Baskets × Baskets × Baskets) :=
  .bind fun (U1!, U2!, U3!) => ⟨U2!, U1!, ∅, U3! + {Basket.f {Fruit.a}}, U3! + {Basket.f U1!}, {Basket.f ({Fruit.a} + U2!)}⟩
def answer38 : Unifier (Fruits × Fruits × Fruits × Baskets × Baskets × Baskets) :=
  .bind fun (U1!, U2!, U3!) => ⟨∅, U1!, U2!, U3! + {Basket.f ({Fruit.a} + U2!)}, U3! + {Basket.f U1!}, {Basket.f {Fruit.a}}⟩
def answer39 : Unifier (Fruits × Fruits × Fruits × Baskets × Baskets × Baskets) :=
  .bind fun (U1!, U2!, U3!, U4!) => ⟨U2!, U1!, U3!, U4! + {Basket.f ({Fruit.a} + U3!)}, U4! + {Basket.f U1!}, {Basket.f ({Fruit.a} + U2!)}⟩
def answer40 : Unifier (Fruits × Fruits × Fruits × Baskets × Baskets × Baskets) :=
  .bind fun (U1!, U2!) => ⟨∅, U1!, ∅, U2! + {Basket.f {Fruit.a}}, {Basket.f U1!}, U2! + {Basket.f {Fruit.a}}⟩
def answer41 : Unifier (Fruits × Fruits × Fruits × Baskets × Baskets × Baskets) :=
  .bind fun (U1!, U2!, U3!) => ⟨U2!, U1!, ∅, U3! + {Basket.f {Fruit.a}}, {Basket.f U1!}, U3! + {Basket.f ({Fruit.a} + U2!)}⟩
def answer42 : Unifier (Fruits × Fruits × Fruits × Baskets × Baskets × Baskets) :=
  .bind fun (U1!, U2!, U3!) => ⟨∅, U1!, U2!, U3! + {Basket.f ({Fruit.a} + U2!)}, {Basket.f U1!}, U3! + {Basket.f {Fruit.a}}⟩
def answer43 : Unifier (Fruits × Fruits × Fruits × Baskets × Baskets × Baskets) :=
  .bind fun (U1!, U2!, U3!, U4!) => ⟨U2!, U1!, U3!, U4! + {Basket.f ({Fruit.a} + U3!)}, {Basket.f U1!}, U4! + {Basket.f ({Fruit.a} + U2!)}⟩
def answer44 : Unifier (Fruits × Fruits × Fruits × Baskets × Baskets × Baskets) :=
  .bind fun (U1!, U2!, U3!) => ⟨∅, U1!, ∅, U2! + U3! + {Basket.f {Fruit.a}}, U2! + {Basket.f U1!}, U3! + {Basket.f {Fruit.a}}⟩
def answer45 : Unifier (Fruits × Fruits × Fruits × Baskets × Baskets × Baskets) :=
  .bind fun (U1!, U2!, U3!, U4!) => ⟨U2!, U1!, ∅, U3! + U4! + {Basket.f {Fruit.a}}, U3! + {Basket.f U1!}, U4! + {Basket.f ({Fruit.a} + U2!)}⟩
def answer46 : Unifier (Fruits × Fruits × Fruits × Baskets × Baskets × Baskets) :=
  .bind fun (U1!, U2!, U3!, U4!) => ⟨∅, U1!, U2!, U3! + U4! + {Basket.f ({Fruit.a} + U2!)}, U3! + {Basket.f U1!}, U4! + {Basket.f {Fruit.a}}⟩
def answer47 : Unifier (Fruits × Fruits × Fruits × Baskets × Baskets × Baskets) :=
  .bind fun (U1!, U2!, U3!, U4!, U5!) => ⟨U2!, U1!, U3!, U4! + U5! + {Basket.f ({Fruit.a} + U3!)}, U4! + {Basket.f U1!}, U5! + {Basket.f ({Fruit.a} + U2!)}⟩
def answer48 : Unifier (Fruits × Fruits × Fruits × Baskets × Baskets × Baskets) :=
  .bind fun U1! => ⟨∅, U1!, ∅, {Basket.f {Fruit.a}}, ∅, {Basket.f {Fruit.a}} + {Basket.f U1!}⟩
def answer49 : Unifier (Fruits × Fruits × Fruits × Baskets × Baskets × Baskets) :=
  .bind fun (U1!, U2!) => ⟨U2!, U1!, ∅, {Basket.f {Fruit.a}}, ∅, {Basket.f U1!} + {Basket.f ({Fruit.a} + U2!)}⟩
def answer50 : Unifier (Fruits × Fruits × Fruits × Baskets × Baskets × Baskets) :=
  .bind fun (U1!, U2!) => ⟨∅, U1!, U2!, {Basket.f ({Fruit.a} + U2!)}, ∅, {Basket.f {Fruit.a}} + {Basket.f U1!}⟩
def answer51 : Unifier (Fruits × Fruits × Fruits × Baskets × Baskets × Baskets) :=
  .bind fun (U1!, U2!, U3!) => ⟨U2!, U1!, U3!, {Basket.f ({Fruit.a} + U3!)}, ∅, {Basket.f U1!} + {Basket.f ({Fruit.a} + U2!)}⟩
def answer52 : Unifier (Fruits × Fruits × Fruits × Baskets × Baskets × Baskets) :=
  .bind fun (U1!, U2!) => ⟨∅, U1!, ∅, U2! + {Basket.f {Fruit.a}}, U2!, {Basket.f {Fruit.a}} + {Basket.f U1!}⟩
def answer53 : Unifier (Fruits × Fruits × Fruits × Baskets × Baskets × Baskets) :=
  .bind fun (U1!, U2!, U3!) => ⟨U2!, U1!, ∅, U3! + {Basket.f {Fruit.a}}, U3!, {Basket.f U1!} + {Basket.f ({Fruit.a} + U2!)}⟩
def answer54 : Unifier (Fruits × Fruits × Fruits × Baskets × Baskets × Baskets) :=
  .bind fun (U1!, U2!, U3!) => ⟨∅, U1!, U3!, U2! + {Basket.f ({Fruit.a} + U3!)}, U2!, {Basket.f {Fruit.a}} + {Basket.f U1!}⟩
def answer55 : Unifier (Fruits × Fruits × Fruits × Baskets × Baskets × Baskets) :=
  .bind fun (U1!, U2!, U3!, U4!) => ⟨U2!, U1!, U4!, U3! + {Basket.f ({Fruit.a} + U4!)}, U3!, {Basket.f U1!} + {Basket.f ({Fruit.a} + U2!)}⟩
def answer56 : Unifier (Fruits × Fruits × Fruits × Baskets × Baskets × Baskets) :=
  .bind fun (U1!, U2!) => ⟨∅, U1!, ∅, U2! + {Basket.f {Fruit.a}}, ∅, U2! + {Basket.f {Fruit.a}} + {Basket.f U1!}⟩
def answer57 : Unifier (Fruits × Fruits × Fruits × Baskets × Baskets × Baskets) :=
  .bind fun (U1!, U2!, U3!) => ⟨U2!, U1!, ∅, U3! + {Basket.f {Fruit.a}}, ∅, U3! + {Basket.f U1!} + {Basket.f ({Fruit.a} + U2!)}⟩
def answer58 : Unifier (Fruits × Fruits × Fruits × Baskets × Baskets × Baskets) :=
  .bind fun (U1!, U2!, U3!) => ⟨∅, U1!, U2!, U3! + {Basket.f ({Fruit.a} + U2!)}, ∅, U3! + {Basket.f {Fruit.a}} + {Basket.f U1!}⟩
def answer59 : Unifier (Fruits × Fruits × Fruits × Baskets × Baskets × Baskets) :=
  .bind fun (U1!, U2!, U3!, U4!) => ⟨U2!, U1!, U3!, U4! + {Basket.f ({Fruit.a} + U3!)}, ∅, U4! + {Basket.f U1!} + {Basket.f ({Fruit.a} + U2!)}⟩
def answer60 : Unifier (Fruits × Fruits × Fruits × Baskets × Baskets × Baskets) :=
  .bind fun (U1!, U2!, U3!) => ⟨∅, U1!, ∅, U2! + U3! + {Basket.f {Fruit.a}}, U2!, U3! + {Basket.f {Fruit.a}} + {Basket.f U1!}⟩
def answer61 : Unifier (Fruits × Fruits × Fruits × Baskets × Baskets × Baskets) :=
  .bind fun (U1!, U2!, U3!, U4!) => ⟨U2!, U1!, ∅, U3! + U4! + {Basket.f {Fruit.a}}, U3!, U4! + {Basket.f U1!} + {Basket.f ({Fruit.a} + U2!)}⟩
def answer62 : Unifier (Fruits × Fruits × Fruits × Baskets × Baskets × Baskets) :=
  .bind fun (U1!, U2!, U3!, U4!) => ⟨∅, U1!, U3!, U2! + U4! + {Basket.f ({Fruit.a} + U3!)}, U2!, U4! + {Basket.f {Fruit.a}} + {Basket.f U1!}⟩
def answer63 : Unifier (Fruits × Fruits × Fruits × Baskets × Baskets × Baskets) :=
  .bind fun (U1!, U2!, U3!, U4!, U5!) => ⟨U2!, U1!, U4!, U3! + U5! + {Basket.f ({Fruit.a} + U4!)}, U3!, U5! + {Basket.f U1!} + {Basket.f ({Fruit.a} + U2!)}⟩
def answer64 : Unifier (Fruits × Fruits × Fruits × Baskets × Baskets × Baskets) :=
  .bind fun () => ⟨∅, {Fruit.a}, ∅, ∅, {Basket.f {Fruit.a}}, ∅⟩
def answer65 : Unifier (Fruits × Fruits × Fruits × Baskets × Baskets × Baskets) :=
  .bind fun U1! => ⟨U1!, {Fruit.a}, ∅, ∅, {Basket.f ({Fruit.a} + U1!)}, ∅⟩
def answer66 : Unifier (Fruits × Fruits × Fruits × Baskets × Baskets × Baskets) :=
  .bind fun U1! => ⟨∅, {Fruit.a} + U1!, U1!, ∅, {Basket.f {Fruit.a}}, ∅⟩
def answer67 : Unifier (Fruits × Fruits × Fruits × Baskets × Baskets × Baskets) :=
  .bind fun (U1!, U2!) => ⟨U1!, {Fruit.a} + U2!, U2!, ∅, {Basket.f ({Fruit.a} + U1!)}, ∅⟩
def answer68 : Unifier (Fruits × Fruits × Fruits × Baskets × Baskets × Baskets) :=
  .bind fun U1! => ⟨∅, {Fruit.a}, ∅, U1!, U1! + {Basket.f {Fruit.a}}, ∅⟩
def answer69 : Unifier (Fruits × Fruits × Fruits × Baskets × Baskets × Baskets) :=
  .bind fun (U1!, U2!) => ⟨U2!, {Fruit.a}, ∅, U1!, U1! + {Basket.f ({Fruit.a} + U2!)}, ∅⟩
def answer70 : Unifier (Fruits × Fruits × Fruits × Baskets × Baskets × Baskets) :=
  .bind fun (U1!, U2!) => ⟨∅, {Fruit.a} + U2!, U2!, U1!, U1! + {Basket.f {Fruit.a}}, ∅⟩
def answer71 : Unifier (Fruits × Fruits × Fruits × Baskets × Baskets × Baskets) :=
  .bind fun (U1!, U2!, U3!) => ⟨U2!, {Fruit.a} + U3!, U3!, U1!, U1! + {Basket.f ({Fruit.a} + U2!)}, ∅⟩
def answer72 : Unifier (Fruits × Fruits × Fruits × Baskets × Baskets × Baskets) :=
  .bind fun U1! => ⟨∅, {Fruit.a}, ∅, U1!, {Basket.f {Fruit.a}}, U1!⟩
def answer73 : Unifier (Fruits × Fruits × Fruits × Baskets × Baskets × Baskets) :=
  .bind fun (U1!, U2!) => ⟨U1!, {Fruit.a}, ∅, U2!, {Basket.f ({Fruit.a} + U1!)}, U2!⟩
def answer74 : Unifier (Fruits × Fruits × Fruits × Baskets × Baskets × Baskets) :=
  .bind fun (U1!, U2!) => ⟨∅, {Fruit.a} + U2!, U2!, U1!, {Basket.f {Fruit.a}}, U1!⟩
def answer75 : Unifier (Fruits × Fruits × Fruits × Baskets × Baskets × Baskets) :=
  .bind fun (U1!, U2!, U3!) => ⟨U1!, {Fruit.a} + U3!, U3!, U2!, {Basket.f ({Fruit.a} + U1!)}, U2!⟩
def answer76 : Unifier (Fruits × Fruits × Fruits × Baskets × Baskets × Baskets) :=
  .bind fun (U1!, U2!) => ⟨∅, {Fruit.a}, ∅, U1! + U2!, U2! + {Basket.f {Fruit.a}}, U1!⟩
def answer77 : Unifier (Fruits × Fruits × Fruits × Baskets × Baskets × Baskets) :=
  .bind fun (U1!, U2!, U3!) => ⟨U1!, {Fruit.a}, ∅, U2! + U3!, U3! + {Basket.f ({Fruit.a} + U1!)}, U2!⟩
def answer78 : Unifier (Fruits × Fruits × Fruits × Baskets × Baskets × Baskets) :=
  .bind fun (U1!, U2!, U3!) => ⟨∅, {Fruit.a} + U2!, U2!, U1! + U3!, U3! + {Basket.f {Fruit.a}}, U1!⟩
def answer79 : Unifier (Fruits × Fruits × Fruits × Baskets × Baskets × Baskets) :=
  .bind fun (U1!, U2!, U3!, U4!) => ⟨U1!, {Fruit.a} + U3!, U3!, U2! + U4!, U4! + {Basket.f ({Fruit.a} + U1!)}, U2!⟩
def answer80 : Unifier (Fruits × Fruits × Fruits × Baskets × Baskets × Baskets) :=
  .bind fun () => ⟨∅, {Fruit.a}, ∅, ∅, ∅, {Basket.f {Fruit.a}}⟩
def answer81 : Unifier (Fruits × Fruits × Fruits × Baskets × Baskets × Baskets) :=
  .bind fun U1! => ⟨U1!, {Fruit.a}, ∅, ∅, ∅, {Basket.f ({Fruit.a} + U1!)}⟩
def answer82 : Unifier (Fruits × Fruits × Fruits × Baskets × Baskets × Baskets) :=
  .bind fun U1! => ⟨∅, {Fruit.a} + U1!, U1!, ∅, ∅, {Basket.f {Fruit.a}}⟩
def answer83 : Unifier (Fruits × Fruits × Fruits × Baskets × Baskets × Baskets) :=
  .bind fun (U1!, U2!) => ⟨U1!, {Fruit.a} + U2!, U2!, ∅, ∅, {Basket.f ({Fruit.a} + U1!)}⟩
def answer84 : Unifier (Fruits × Fruits × Fruits × Baskets × Baskets × Baskets) :=
  .bind fun U1! => ⟨∅, {Fruit.a}, ∅, U1!, U1!, {Basket.f {Fruit.a}}⟩
def answer85 : Unifier (Fruits × Fruits × Fruits × Baskets × Baskets × Baskets) :=
  .bind fun (U1!, U2!) => ⟨U1!, {Fruit.a}, ∅, U2!, U2!, {Basket.f ({Fruit.a} + U1!)}⟩
def answer86 : Unifier (Fruits × Fruits × Fruits × Baskets × Baskets × Baskets) :=
  .bind fun (U1!, U2!) => ⟨∅, {Fruit.a} + U2!, U2!, U1!, U1!, {Basket.f {Fruit.a}}⟩
def answer87 : Unifier (Fruits × Fruits × Fruits × Baskets × Baskets × Baskets) :=
  .bind fun (U1!, U2!, U3!) => ⟨U1!, {Fruit.a} + U3!, U3!, U2!, U2!, {Basket.f ({Fruit.a} + U1!)}⟩
def answer88 : Unifier (Fruits × Fruits × Fruits × Baskets × Baskets × Baskets) :=
  .bind fun U1! => ⟨∅, {Fruit.a}, ∅, U1!, ∅, U1! + {Basket.f {Fruit.a}}⟩
def answer89 : Unifier (Fruits × Fruits × Fruits × Baskets × Baskets × Baskets) :=
  .bind fun (U1!, U2!) => ⟨U2!, {Fruit.a}, ∅, U1!, ∅, U1! + {Basket.f ({Fruit.a} + U2!)}⟩
def answer90 : Unifier (Fruits × Fruits × Fruits × Baskets × Baskets × Baskets) :=
  .bind fun (U1!, U2!) => ⟨∅, {Fruit.a} + U2!, U2!, U1!, ∅, U1! + {Basket.f {Fruit.a}}⟩
def answer91 : Unifier (Fruits × Fruits × Fruits × Baskets × Baskets × Baskets) :=
  .bind fun (U1!, U2!, U3!) => ⟨U2!, {Fruit.a} + U3!, U3!, U1!, ∅, U1! + {Basket.f ({Fruit.a} + U2!)}⟩
def answer92 : Unifier (Fruits × Fruits × Fruits × Baskets × Baskets × Baskets) :=
  .bind fun (U1!, U2!) => ⟨∅, {Fruit.a}, ∅, U1! + U2!, U1!, U2! + {Basket.f {Fruit.a}}⟩
def answer93 : Unifier (Fruits × Fruits × Fruits × Baskets × Baskets × Baskets) :=
  .bind fun (U1!, U2!, U3!) => ⟨U1!, {Fruit.a}, ∅, U2! + U3!, U2!, U3! + {Basket.f ({Fruit.a} + U1!)}⟩
def answer94 : Unifier (Fruits × Fruits × Fruits × Baskets × Baskets × Baskets) :=
  .bind fun (U1!, U2!, U3!) => ⟨∅, {Fruit.a} + U2!, U2!, U1! + U3!, U1!, U3! + {Basket.f {Fruit.a}}⟩
def answer95 : Unifier (Fruits × Fruits × Fruits × Baskets × Baskets × Baskets) :=
  .bind fun (U1!, U2!, U3!, U4!) => ⟨U1!, {Fruit.a} + U3!, U3!, U2! + U4!, U2!, U4! + {Basket.f ({Fruit.a} + U1!)}⟩
def answer96 : Unifier (Fruits × Fruits × Fruits × Baskets × Baskets × Baskets) :=
  .bind fun U1! => ⟨∅, U1!, ∅, ∅, {Basket.f U1!}, ∅⟩
def answer97 : Unifier (Fruits × Fruits × Fruits × Baskets × Baskets × Baskets) :=
  .bind fun (U1!, U2!) => ⟨U2!, U1!, U2!, ∅, {Basket.f U1!}, ∅⟩
def answer98 : Unifier (Fruits × Fruits × Fruits × Baskets × Baskets × Baskets) :=
  .bind fun (U1!, U2!) => ⟨∅, U2!, ∅, U1!, U1! + {Basket.f U2!}, ∅⟩
def answer99 : Unifier (Fruits × Fruits × Fruits × Baskets × Baskets × Baskets) :=
  .bind fun (U1!, U2!, U3!) => ⟨U3!, U2!, U3!, U1!, U1! + {Basket.f U2!}, ∅⟩
def answer100 : Unifier (Fruits × Fruits × Fruits × Baskets × Baskets × Baskets) :=
  .bind fun (U1!, U2!) => ⟨∅, U1!, ∅, U2!, {Basket.f U1!}, U2!⟩
def answer101 : Unifier (Fruits × Fruits × Fruits × Baskets × Baskets × Baskets) :=
  .bind fun (U1!, U2!, U3!) => ⟨U2!, U1!, U2!, U3!, {Basket.f U1!}, U3!⟩
def answer102 : Unifier (Fruits × Fruits × Fruits × Baskets × Baskets × Baskets) :=
  .bind fun (U1!, U2!, U3!) => ⟨∅, U1!, ∅, U2! + U3!, U3! + {Basket.f U1!}, U2!⟩
def answer103 : Unifier (Fruits × Fruits × Fruits × Baskets × Baskets × Baskets) :=
  .bind fun (U1!, U2!, U3!, U4!) => ⟨U2!, U1!, U2!, U3! + U4!, U4! + {Basket.f U1!}, U3!⟩
def answer104 : Unifier (Fruits × Fruits × Fruits × Baskets × Baskets × Baskets) :=
  .bind fun U1! => ⟨∅, U1!, ∅, ∅, ∅, {Basket.f U1!}⟩
def answer105 : Unifier (Fruits × Fruits × Fruits × Baskets × Baskets × Baskets) :=
  .bind fun (U1!, U2!) => ⟨U2!, U1!, U2!, ∅, ∅, {Basket.f U1!}⟩
def answer106 : Unifier (Fruits × Fruits × Fruits × Baskets × Baskets × Baskets) :=
  .bind fun (U1!, U2!) => ⟨∅, U1!, ∅, U2!, U2!, {Basket.f U1!}⟩
def answer107 : Unifier (Fruits × Fruits × Fruits × Baskets × Baskets × Baskets) :=
  .bind fun (U1!, U2!, U3!) => ⟨U2!, U1!, U2!, U3!, U3!, {Basket.f U1!}⟩
def answer108 : Unifier (Fruits × Fruits × Fruits × Baskets × Baskets × Baskets) :=
  .bind fun (U1!, U2!) => ⟨∅, U2!, ∅, U1!, ∅, U1! + {Basket.f U2!}⟩
def answer109 : Unifier (Fruits × Fruits × Fruits × Baskets × Baskets × Baskets) :=
  .bind fun (U1!, U2!, U3!) => ⟨U3!, U2!, U3!, U1!, ∅, U1! + {Basket.f U2!}⟩
def answer110 : Unifier (Fruits × Fruits × Fruits × Baskets × Baskets × Baskets) :=
  .bind fun (U1!, U2!, U3!) => ⟨∅, U1!, ∅, U2! + U3!, U2!, U3! + {Basket.f U1!}⟩
def answer111 : Unifier (Fruits × Fruits × Fruits × Baskets × Baskets × Baskets) :=
  .bind fun (U1!, U2!, U3!, U4!) => ⟨U2!, U1!, U2!, U3! + U4!, U3!, U4! + {Basket.f U1!}⟩
def answers : UnifierSet (Fruits × Fruits × Fruits × Baskets × Baskets × Baskets) :=
  [answer0, answer1, answer2, answer3, answer4, answer5, answer6, answer7, answer8, answer9, answer10, answer11, answer12, answer13, answer14, answer15, answer16, answer17, answer18, answer19, answer20, answer21, answer22, answer23, answer24, answer25, answer26, answer27, answer28, answer29, answer30, answer31, answer32, answer33, answer34, answer35, answer36, answer37, answer38, answer39, answer40, answer41, answer42, answer43, answer44, answer45, answer46, answer47, answer48, answer49, answer50, answer51, answer52, answer53, answer54, answer55, answer56, answer57, answer58, answer59, answer60, answer61, answer62, answer63, answer64, answer65, answer66, answer67, answer68, answer69, answer70, answer71, answer72, answer73, answer74, answer75, answer76, answer77, answer78, answer79, answer80, answer81, answer82, answer83, answer84, answer85, answer86, answer87, answer88, answer89, answer90, answer91, answer92, answer93, answer94, answer95, answer96, answer97, answer98, answer99, answer100, answer101, answer102, answer103, answer104, answer105, answer106, answer107, answer108, answer109, answer110, answer111]

theorem complete : Unification.complete problem answers := by
  rw [← start_iff]
  -- ⊢ - | R? + {Basket.f ({Fruit.a} + X?)} + {Basket.f Y?} = S? + T? + {Basket.f ({Fruit.a} + W?)} | -
  checkpoint
  -- identify Basket.f Y? ~ Basket.f ({Fruit.a} + W?)
  refine identify (fun (_, Y?, _, _, _, _) => Basket.f Y?) (fun (_, _, W?, _, _, _) => Basket.f ({Fruit.a} + W?)) ?_ ?_
  · -- equal:
    -- ⊢ - | Basket.f Y? = Basket.f ({Fruit.a} + W?); R? + {Basket.f ({Fruit.a} + X?)} + {Basket.f Y?} = S? + T? + {Basket.f ({Fruit.a} + W?)} | -
    checkpoint
    -- decomp Basket.f Y? = Basket.f ({Fruit.a} + W?)
    refine decomp [fun (_, Y?, W?, _, _, _) => Y? = {Fruit.a} + W?]
        (fun (X?, Y?, W?, R?, S?, T?) h => by acu_decomp [problem, Basket.f.injEq]) ?_
    -- ⊢ - | Y? = {Fruit.a} + W?; R? + {Basket.f ({Fruit.a} + X?)} + {Basket.f Y?} = S? + T? + {Basket.f ({Fruit.a} + W?)} | -
    checkpoint
    -- elim Y? := {Fruit.a} + W?
    refine elim (fun (X?, W?, R?, S?, T?) => (X?, {Fruit.a} + W?, W?, R?, S?, T?))
        (fun (X?, Y?, W?, R?, S?, T?) h => ⟨(X?, W?, R?, S?, T?), by acu_elim [problem]⟩) ?_
    -- ⊢ Y? := {Fruit.a} + W? | R? + {Basket.f ({Fruit.a} + X?)} + {Basket.f ({Fruit.a} + W?)} = S? + T? + {Basket.f ({Fruit.a} + W?)} | -
    checkpoint
    -- solve R? + {Basket.f ({Fruit.a} + X?)} + {Basket.f ({Fruit.a} + W?)} = S? + T? + {Basket.f ({Fruit.a} + W?)}
    refine solve
        { V := fun (_, _, R?, S?, T?) => ![R?, S?, T?], rest := fun (X?, W?, _, _, _) => (X?, W?),
          glue := fun (X?, W?) V => (X?, W?, V 0, V 1, V 2) }
        (fun (X?, W?) => ![Basket.f ({Fruit.a} + X?), Basket.f ({Fruit.a} + W?)])
        { L := ![1, 0, 0], R := ![0, 1, 1], La := ![1, 1], Ra := ![0, 1], compatible := [(0, 1)] }
        { P := ![[![0, 1, 0], ![0, 0, 1]], [![0, 0, 0]]], B := ![![1, 1, 0], ![1, 0, 1]] }
        ⟨by decide, by decide, by decide,
          S2_of_list _ _ _ _ _ _ [[0], [1], [0, 1]] (by decide) (by acu_cliques), by acu_basis⟩
        (fun (X?, W?, R?, S?, T?) h => by (try simp only [unifiedBy, problem] at h); acu_side h)
        (fun (X?, W?, R?, S?, T?) h hD => by acu_distinct) ?_
    acu_branches
    · -- branch (0,1,0) (0,0,0)
      refine rename (fun (X?, W?, Z1, Z2) => ((X?, W?), ![Z1, Z2]))
          (fun ((X?, W?), Z) => (X?, W?, Z 0, Z 1))
          (fun ((X?, W?), Z) => Prod.ext rfl (funext fun i => by fin_cases i <;> rfl)) ?_
      -- ⊢ R? := Z1 + Z2, S? := Z1 + {Basket.f ({Fruit.a} + X?)}, T? := Z2, Y? := {Fruit.a} + W? | - | -
      checkpoint
      -- cover answer 79 with U1! := X?, U2! := Z2, U3! := W?, U4! := Z1
      exact cover answer79 (by simp [answers]) fun (X?, W?, Z1, Z2) _ _ => ⟨(X?, Z2, W?, Z1), by acu_cover⟩
    · -- branch (0,0,1) (0,0,0)
      refine rename (fun (X?, W?, Z1, Z2) => ((X?, W?), ![Z1, Z2]))
          (fun ((X?, W?), Z) => (X?, W?, Z 0, Z 1))
          (fun ((X?, W?), Z) => Prod.ext rfl (funext fun i => by fin_cases i <;> rfl)) ?_
      -- ⊢ R? := Z1 + Z2, S? := Z1, T? := Z2 + {Basket.f ({Fruit.a} + X?)}, Y? := {Fruit.a} + W? | - | -
      checkpoint
      -- cover answer 95 with U1! := X?, U2! := Z1, U3! := W?, U4! := Z2
      exact cover answer95 (by simp [answers]) fun (X?, W?, Z1, Z2) _ _ => ⟨(X?, Z1, W?, Z2), by acu_cover⟩
  · -- distinct:
    -- ⊢ - | R? + {Basket.f ({Fruit.a} + X?)} + {Basket.f Y?} = S? + T? + {Basket.f ({Fruit.a} + W?)} | Basket.f Y? ≠ Basket.f ({Fruit.a} + W?)
    checkpoint
    -- identify Basket.f ({Fruit.a} + X?) ~ Basket.f ({Fruit.a} + W?)
    refine identify (fun (X?, _, _, _, _, _) => Basket.f ({Fruit.a} + X?)) (fun (_, _, W?, _, _, _) => Basket.f ({Fruit.a} + W?)) ?_ ?_
    · -- equal:
      -- ⊢ - | Basket.f ({Fruit.a} + X?) = Basket.f ({Fruit.a} + W?); R? + {Basket.f ({Fruit.a} + X?)} + {Basket.f Y?} = S? + T? + {Basket.f ({Fruit.a} + W?)} | Basket.f Y? ≠ Basket.f ({Fruit.a} + W?)
      checkpoint
      -- decomp Basket.f ({Fruit.a} + X?) = Basket.f ({Fruit.a} + W?)
      refine decomp [fun (X?, _, W?, _, _, _) => {Fruit.a} + X? = {Fruit.a} + W?]
          (fun (X?, Y?, W?, R?, S?, T?) h => by acu_decomp [problem, Basket.f.injEq]) ?_
      -- ⊢ - | {Fruit.a} + X? = {Fruit.a} + W?; R? + {Basket.f ({Fruit.a} + X?)} + {Basket.f Y?} = S? + T? + {Basket.f ({Fruit.a} + W?)} | Basket.f Y? ≠ Basket.f ({Fruit.a} + W?)
      checkpoint
      -- solve {Fruit.a} + X? = {Fruit.a} + W?
      refine solve
          { V := fun (X?, _, W?, _, _, _) => ![X?, W?], rest := fun (_, Y?, _, R?, S?, T?) => (Y?, R?, S?, T?),
            glue := fun (Y?, R?, S?, T?) V => (V 0, Y?, V 1, R?, S?, T?) }
          (fun (_, _, _, _) => ![Fruit.a])
          { L := ![1, 0], R := ![0, 1], La := ![1], Ra := ![1] }
          { P := ![[![0, 0]]], B := ![![1, 1]] }
          ⟨by decide, by decide, by decide,
            S2_of_list _ _ _ _ _ _ [[0]] (by decide) (by acu_cliques), by acu_basis⟩
          (fun (X?, Y?, W?, R?, S?, T?) h => by (try simp only [unifiedBy, problem] at h); acu_side h)
          (fun (X?, Y?, W?, R?, S?, T?) h hD => by acu_distinct) ?_
      acu_branches
      -- branch (0,0)
      refine rename (fun (Y?, R?, S?, T?, Z1) => ((Y?, R?, S?, T?), ![Z1]))
          (fun ((Y?, R?, S?, T?), Z) => (Y?, R?, S?, T?, Z 0))
          (fun ((Y?, R?, S?, T?), Z) => Prod.ext rfl (funext fun i => by fin_cases i; rfl)) ?_
      -- ⊢ W? := Z1, X? := Z1 | R? + {Basket.f Y?} + {Basket.f ({Fruit.a} + Z1)} = S? + T? + {Basket.f ({Fruit.a} + Z1)} | Basket.f Y? ≠ Basket.f ({Fruit.a} + Z1)
      checkpoint
      -- solve R? + {Basket.f Y?} + {Basket.f ({Fruit.a} + Z1)} = S? + T? + {Basket.f ({Fruit.a} + Z1)}
      refine solve
          { V := fun (_, R?, S?, T?, _) => ![R?, S?, T?], rest := fun (Y?, _, _, _, Z1) => (Y?, Z1),
            glue := fun (Y?, Z1) V => (Y?, V 0, V 1, V 2, Z1) }
          (fun (Y?, Z1) => ![Basket.f Y?, Basket.f ({Fruit.a} + Z1)])
          { L := ![1, 0, 0], R := ![0, 1, 1], La := ![1, 1], Ra := ![0, 1] }
          { P := ![[![0, 1, 0], ![0, 0, 1]], [![0, 0, 0]]], B := ![![1, 1, 0], ![1, 0, 1]] }
          ⟨by decide, by decide, by decide,
            S2_of_list _ _ _ _ _ _ [[0], [1]] (by decide) (by acu_cliques), by acu_basis⟩
          (fun (Y?, R?, S?, T?, Z1) h => by (try simp only [unifiedBy, problem] at h); acu_side h)
          (fun (Y?, R?, S?, T?, Z1) h hD => by acu_distinct) ?_
      acu_branches
      · -- branch (0,1,0) (0,0,0)
        refine rename (fun (Y?, Z1, Z2, Z3) => ((Y?, Z1), ![Z2, Z3]))
            (fun ((Y?, Z1), Z) => (Y?, Z1, Z 0, Z 1))
            (fun ((Y?, Z1), Z) => Prod.ext rfl (funext fun i => by fin_cases i <;> rfl)) ?_
        -- ⊢ R? := Z2 + Z3, S? := Z2 + {Basket.f Y?}, T? := Z3, W? := Z1, X? := Z1 | - | Basket.f Y? ≠ Basket.f ({Fruit.a} + Z1)
        checkpoint
        -- cover answer 103 with U1! := Y?, U2! := Z1, U3! := Z3, U4! := Z2
        exact cover answer103 (by simp [answers]) fun (Y?, Z1, Z2, Z3) _ _ => ⟨(Y?, Z1, Z3, Z2), by acu_cover⟩
      · -- branch (0,0,1) (0,0,0)
        refine rename (fun (Y?, Z1, Z2, Z3) => ((Y?, Z1), ![Z2, Z3]))
            (fun ((Y?, Z1), Z) => (Y?, Z1, Z 0, Z 1))
            (fun ((Y?, Z1), Z) => Prod.ext rfl (funext fun i => by fin_cases i <;> rfl)) ?_
        -- ⊢ R? := Z2 + Z3, S? := Z2, T? := Z3 + {Basket.f Y?}, W? := Z1, X? := Z1 | - | Basket.f Y? ≠ Basket.f ({Fruit.a} + Z1)
        checkpoint
        -- cover answer 111 with U1! := Y?, U2! := Z1, U3! := Z2, U4! := Z3
        exact cover answer111 (by simp [answers]) fun (Y?, Z1, Z2, Z3) _ _ => ⟨(Y?, Z1, Z2, Z3), by acu_cover⟩
    · -- distinct:
      -- ⊢ - | R? + {Basket.f ({Fruit.a} + X?)} + {Basket.f Y?} = S? + T? + {Basket.f ({Fruit.a} + W?)} | Basket.f Y? ≠ Basket.f ({Fruit.a} + W?); Basket.f ({Fruit.a} + X?) ≠ Basket.f ({Fruit.a} + W?)
      checkpoint
      -- solve R? + {Basket.f ({Fruit.a} + X?)} + {Basket.f Y?} = S? + T? + {Basket.f ({Fruit.a} + W?)}
      refine solve
          { V := fun (_, _, _, R?, S?, T?) => ![R?, S?, T?], rest := fun (X?, Y?, W?, _, _, _) => (X?, Y?, W?),
            glue := fun (X?, Y?, W?) V => (X?, Y?, W?, V 0, V 1, V 2) }
          (fun (X?, Y?, W?) => ![Basket.f ({Fruit.a} + X?), Basket.f Y?, Basket.f ({Fruit.a} + W?)])
          { L := ![1, 0, 0], R := ![0, 1, 1], La := ![1, 1, 0], Ra := ![0, 0, 1], compatible := [(0, 1)] }
          { P := ![[![0, 1, 0], ![0, 0, 1]], [![0, 1, 0], ![0, 0, 1]], [![1, 0, 0]]], B := ![![1, 1, 0], ![1, 0, 1]] }
          ⟨by decide, by decide, by decide,
            S2_of_list _ _ _ _ _ _ [[0], [1], [2], [0, 1]] (by decide) (by acu_cliques), by acu_basis⟩
          (fun (X?, Y?, W?, R?, S?, T?) h => by (try simp only [unifiedBy, problem] at h); acu_side h)
          (fun (X?, Y?, W?, R?, S?, T?) h hD => by acu_distinct) ?_
      acu_branches
      · -- branch (0,1,0) (0,1,0) (1,0,0)
        refine rename (fun (X?, Y?, W?, Z1, Z2) => ((X?, Y?, W?), ![Z1, Z2]))
            (fun ((X?, Y?, W?), Z) => (X?, Y?, W?, Z 0, Z 1))
            (fun ((X?, Y?, W?), Z) => Prod.ext rfl (funext fun i => by fin_cases i <;> rfl)) ?_
        -- ⊢ R? := Z1 + Z2 + {Basket.f ({Fruit.a} + W?)}, S? := Z1 + {Basket.f Y?} + {Basket.f ({Fruit.a} + X?)}, T? := Z2 | - | Basket.f Y? ≠ Basket.f ({Fruit.a} + W?); Basket.f ({Fruit.a} + X?) ≠ Basket.f ({Fruit.a} + W?)
        checkpoint
        -- cover answer 15 with U1! := Y?, U2! := X?, U3! := Z2, U4! := W?, U5! := Z1
        exact cover answer15 (by simp [answers]) fun (X?, Y?, W?, Z1, Z2) _ _ => ⟨(Y?, X?, Z2, W?, Z1), by acu_cover⟩
      · -- branch (0,1,0) (0,0,1) (1,0,0)
        refine rename (fun (X?, Y?, W?, Z1, Z2) => ((X?, Y?, W?), ![Z1, Z2]))
            (fun ((X?, Y?, W?), Z) => (X?, Y?, W?, Z 0, Z 1))
            (fun ((X?, Y?, W?), Z) => Prod.ext rfl (funext fun i => by fin_cases i <;> rfl)) ?_
        -- ⊢ R? := Z1 + Z2 + {Basket.f ({Fruit.a} + W?)}, S? := Z1 + {Basket.f ({Fruit.a} + X?)}, T? := Z2 + {Basket.f Y?} | - | Basket.f Y? ≠ Basket.f ({Fruit.a} + W?); Basket.f ({Fruit.a} + X?) ≠ Basket.f ({Fruit.a} + W?)
        checkpoint
        -- cover answer 31 with U1! := Y?, U2! := X?, U3! := W?, U4! := Z1, U5! := Z2
        exact cover answer31 (by simp [answers]) fun (X?, Y?, W?, Z1, Z2) _ _ => ⟨(Y?, X?, W?, Z1, Z2), by acu_cover⟩
      · -- branch (0,0,1) (0,1,0) (1,0,0)
        refine rename (fun (X?, Y?, W?, Z1, Z2) => ((X?, Y?, W?), ![Z1, Z2]))
            (fun ((X?, Y?, W?), Z) => (X?, Y?, W?, Z 0, Z 1))
            (fun ((X?, Y?, W?), Z) => Prod.ext rfl (funext fun i => by fin_cases i <;> rfl)) ?_
        -- ⊢ R? := Z1 + Z2 + {Basket.f ({Fruit.a} + W?)}, S? := Z1 + {Basket.f Y?}, T? := Z2 + {Basket.f ({Fruit.a} + X?)} | - | Basket.f Y? ≠ Basket.f ({Fruit.a} + W?); Basket.f ({Fruit.a} + X?) ≠ Basket.f ({Fruit.a} + W?)
        checkpoint
        -- cover answer 47 with U1! := Y?, U2! := X?, U3! := W?, U4! := Z1, U5! := Z2
        exact cover answer47 (by simp [answers]) fun (X?, Y?, W?, Z1, Z2) _ _ => ⟨(Y?, X?, W?, Z1, Z2), by acu_cover⟩
      · -- branch (0,0,1) (0,0,1) (1,0,0)
        refine rename (fun (X?, Y?, W?, Z1, Z2) => ((X?, Y?, W?), ![Z1, Z2]))
            (fun ((X?, Y?, W?), Z) => (X?, Y?, W?, Z 0, Z 1))
            (fun ((X?, Y?, W?), Z) => Prod.ext rfl (funext fun i => by fin_cases i <;> rfl)) ?_
        -- ⊢ R? := Z1 + Z2 + {Basket.f ({Fruit.a} + W?)}, S? := Z1, T? := Z2 + {Basket.f Y?} + {Basket.f ({Fruit.a} + X?)} | - | Basket.f Y? ≠ Basket.f ({Fruit.a} + W?); Basket.f ({Fruit.a} + X?) ≠ Basket.f ({Fruit.a} + W?)
        checkpoint
        -- cover answer 63 with U1! := Y?, U2! := X?, U3! := Z1, U4! := W?, U5! := Z2
        exact cover answer63 (by simp [answers]) fun (X?, Y?, W?, Z1, Z2) _ _ => ⟨(Y?, X?, Z1, W?, Z2), by acu_cover⟩

end Pipeline.T7
