import Tiny.conPanna.Unification.Certification.Tactics

/-! A singleton against an incompatible one: P? + {wait(N?)} =? Q? + {idle}. -/

/- certify
{
  "namespace": "Pipeline.T2",
  "context": "Nat × ProcSet × ProcSet",
  "vars": [
    "N?",
    "P?",
    "Q?"
  ],
  "ops": {
    "<_,_,_>": "Conf.mk",
    "s": "({0} + 1)",
    "z": "0",
    "wait": "Mode.wait",
    "idle": "Mode.idle",
    "crit": "Mode.crit"
  }
}
-/

open Unification Certification

namespace Pipeline.T2

inductive Mode where
  | idle
  | wait (ticket : Nat)
  | crit (ticket : Nat)

abbrev ProcSet := ACU Mode

structure Conf where
  next : Nat
  serving : Nat
  procs : ProcSet

def problem : Problem ProcSet (Nat × ProcSet × ProcSet) :=
  .bind fun (N?, P?, Q?) => (P? + {Mode.wait N?}, Q? + {Mode.idle})

/-! ## Generated from t2_alien_clash.deriv by producer/tools/compile.py -/

def answer0 : Unifier (Nat × ProcSet × ProcSet) :=
  .bind fun U1! => .subst ⟨U1!, {Mode.idle}, {Mode.wait U1!}⟩
def answer1 : Unifier (Nat × ProcSet × ProcSet) :=
  .bind fun (U1!, U2!) => .subst ⟨U1!, {Mode.idle} + U2!, U2! + {Mode.wait U1!}⟩
def answers : UnifierSet (Nat × ProcSet × ProcSet) :=
  [answer0, answer1]

theorem complete : UnifierSet.Complete problem answers := by
  rw [← start_iff]
  -- ⊢ - | P? + {Mode.wait N?} = Q? + {Mode.idle} | -
  -- solve P? + {Mode.wait N?} = Q? + {Mode.idle}
  refine solve (V := fun (_, P?, Q?) => ![P?, Q?]) (rest := fun (N?, _, _) => N?)
      (glue := fun N? V => (N?, V 0, V 1)) (hglue := fun _ => rfl)
      (a := fun N? => ![Mode.wait N?, Mode.idle]) (L := ![1, 0]) (R := ![0, 1]) (La := ![1, 0]) (Ra := ![0, 1])
      (E' := fun (_, _, _) => True) (cp := fun _ _ => false)
      (P := ![[![0, 1]], [![1, 0]]]) (B := ![![1, 1]])
      (fun (N?, P?, Q?) h hD => ⟨by try simp only [State.start, Problem.unifies, problem] at h; acu_side h, trivial, by acu_distinct⟩)
      (by decide) (by decide) (by decide)
      (S2_of_list _ _ _ _ _ _ [[0], [1]] (by decide) (by acu_cliques)) (by acu_basis) ?_
  intro π hπ; simp [choices] at hπ; subst hπ
  -- branch (0,1) (1,0)
  refine rename (fun (N?, Z1) => (N?, ![Z1]))
      (fun (N?, Z) => (N?, Z 0))
      (fun (N?, Z) => Prod.ext rfl (funext fun i => by fin_cases i; rfl)) ?_
  -- ⊢ P? := {Mode.idle} + Z1, Q? := Z1 + {Mode.wait N?} | - | -
  -- cover answer 1 with U1! := N?, U2! := Z1
  exact cover answer1 (by simp [answers]) fun (N?, Z1) _ _ => ⟨(N?, Z1), by acu_cover⟩

end Pipeline.T2
