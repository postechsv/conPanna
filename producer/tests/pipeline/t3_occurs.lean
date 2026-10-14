import Tiny.conPanna.Unification.Certification.Tactics

/-! No unifiers: X? + {w(N?)} =? X? + {w(N? + 1)}. -/

/- certify
{
  "namespace": "Pipeline.T3",
  "context": "Bag × Bag × Nat × Nat",
  "vars": [
    "X?",
    "Y?",
    "N?",
    "M?"
  ],
  "ops": {
    "w": "Elem.w",
    "s": "({0} + 1)"
  }
}
-/

open Unification Certification

namespace Pipeline.T3

inductive Elem where
  | w (n : Nat)

abbrev Bag := ACU Elem

def problem : Problem Bag (Bag × Bag × Nat × Nat) :=
  .bind fun (X?, _, N?, _) => (X? + {Elem.w N?}, X? + {Elem.w (N? + 1)})

/-! ## Generated from t3_occurs.deriv by producer/tools/compile.py -/

def answers : UnifierSet (Bag × Bag × Nat × Nat) :=
  []

theorem complete : Unification.complete problem answers := by
  rw [← start_iff]
  -- ⊢ - | X? + {Elem.w N?} = X? + {Elem.w (N? + 1)} | -
  -- solve X? + {Elem.w N?} = X? + {Elem.w (N? + 1)}
  refine solve (V := fun (X?, _, _, _) => ![X?]) (rest := fun (_, Y?, N?, M?) => (Y?, N?, M?))
      (glue := fun (Y?, N?, M?) V => (V 0, Y?, N?, M?)) (hglue := fun _ => rfl)
      (a := fun (_, N?, _) => ![Elem.w N?, Elem.w (N? + 1)]) (L := ![1]) (R := ![1]) (La := ![1, 0]) (Ra := ![0, 1])
      (E' := fun (_, _, _, _) => True) (cp := fun _ _ => false)
      (P := ![[], []]) (B := ![![1]])
      (fun (X?, Y?, N?, M?) h hD => ⟨by try simp only [State.start, unifiedBy, problem] at h; acu_side h, trivial, by acu_distinct⟩)
      (by decide) (by decide) (by decide)
      (S2_of_list _ _ _ _ _ _ [[0], [1]] (by decide) (by acu_cliques)) (by acu_basis) ?_
  intro π hπ; simp [choices] at hπ

end Pipeline.T3
