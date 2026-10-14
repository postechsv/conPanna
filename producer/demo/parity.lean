import Tiny.conPanna.Unification.Certification.Tactics

/-!
No unifiers, by parity: at the element `a` the counts would satisfy 2x = 2y + 1.
The claim (model, problem) is written by the user; the compiler appends the
(empty) answers and the proof, from `parity.deriv`.
-/

/- certify
{
  "namespace": "Demo.Parity",
  "context": "Bag × Bag",
  "vars": ["X?", "Y?"],
  "ops": {"a": "Elem.a", "b": "Elem.b"}
}
-/

open Unification Certification

namespace Demo.Parity

/-! ## Claim -/

inductive Elem where
  | a
  | b

abbrev Bag := ACU Elem

def problem : Problem Bag (Bag × Bag) :=
  .bind fun (X?, Y?) => (X? + X?, Y? + Y? + {Elem.a})

/-! ## Generated from parity.deriv by producer/tools/compile.py -/

def answers : UnifierSet (Bag × Bag) :=
  []

theorem complete : UnifierSet.Complete problem answers := by
  rw [← start_iff]
  -- ⊢ - | X? + X? = Y? + Y? + {Elem.a} | -
  -- solve X? + X? = Y? + Y? + {Elem.a}
  refine solve (V := fun (X?, Y?) => ![X?, Y?]) (rest := fun (_, _) => ())
      (glue := fun _ V => (V 0, V 1)) (hglue := fun _ => rfl)
      (a := fun _ => ![Elem.a]) (L := ![2, 0]) (R := ![0, 2]) (La := ![0]) (Ra := ![1])
      (E' := fun (_, _) => True) (cp := fun _ _ => false)
      (P := ![[]]) (B := ![![1, 1]])
      (fun (X?, Y?) h hD => ⟨by try simp only [State.start, Problem.unifies, problem] at h; acu_side h, trivial, by acu_distinct⟩)
      (by decide) (by decide) (by decide)
      (S2_of_list _ _ _ _ _ _ [[0]] (by decide) (by acu_cliques)) (by acu_basis) ?_
  intro π hπ; simp [choices] at hπ

end Demo.Parity
