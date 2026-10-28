import conPanna.Unification.Certification.Tactics

/-!
Paper §6.1, mixed free and ACU. The claim (model, problem) is written by the user;
the compiler appends the answers and the proof, from `mixed.deriv`.
-/

/- certify
{
  "namespace": "Demo.Mixed",
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

namespace Demo.Mixed

/-! ## Claim -/

inductive Elem where
  | w (n : Nat)

abbrev Bag := ACU Elem

def problem : Problem Bag (Bag × Bag × Nat × Nat) :=
  .bind fun (X?, Y?, N?, M?) => (X? + {.w N?}, Y? + {.w M?})

/-! ## Generated from mixed.deriv by producer/tools/compile.py -/

def answer0 : Unifier (Bag × Bag × Nat × Nat) :=
  .bind fun (U1!, U2!) => ⟨{Elem.w U2!}, {Elem.w U1!}, U1!, U2!⟩
def answer1 : Unifier (Bag × Bag × Nat × Nat) :=
  .bind fun (U1!, U2!, U3!) => ⟨U3! + {Elem.w U2!}, U3! + {Elem.w U1!}, U1!, U2!⟩
def answer2 : Unifier (Bag × Bag × Nat × Nat) :=
  .bind fun U1! => ⟨∅, ∅, U1!, U1!⟩
def answer3 : Unifier (Bag × Bag × Nat × Nat) :=
  .bind fun (U1!, U2!) => ⟨U1!, U1!, U2!, U2!⟩
def answers : UnifierSet (Bag × Bag × Nat × Nat) :=
  [answer0, answer1, answer2, answer3]

theorem complete : Unification.complete problem answers := by
  rw [← start_iff]
  -- ⊢ - | X? + {Elem.w N?} = Y? + {Elem.w M?} | -
  checkpoint
  -- identify Elem.w N? ~ Elem.w M?
  refine identify (fun (_, _, N?, _) => Elem.w N?) (fun (_, _, _, M?) => Elem.w M?) ?_ ?_
  · -- equal:
    -- ⊢ - | Elem.w N? = Elem.w M?; X? + {Elem.w N?} = Y? + {Elem.w M?} | -
    checkpoint
    -- decomp Elem.w N? = Elem.w M?
    refine decomp [fun (_, _, N?, M?) => N? = M?]
        (fun (X?, Y?, N?, M?) h => by acu_decomp [problem, Elem.w.injEq]) ?_
    -- ⊢ - | N? = M?; X? + {Elem.w N?} = Y? + {Elem.w M?} | -
    checkpoint
    -- elim M? := N?
    refine elim (fun (X?, Y?, N?) => (X?, Y?, N?, N?))
        (fun (X?, Y?, N?, M?) h => ⟨(X?, Y?, N?), by acu_elim [problem]⟩) ?_
    -- ⊢ M? := N? | X? + {Elem.w N?} = Y? + {Elem.w N?} | -
    checkpoint
    -- solve X? + {Elem.w N?} = Y? + {Elem.w N?}
    refine solve
        { V := fun (X?, Y?, _) => ![X?, Y?], rest := fun (_, _, N?) => N?,
          glue := fun N? V => (V 0, V 1, N?) }
        (fun N? => ![Elem.w N?])
        { L := ![1, 0], R := ![0, 1], La := ![1], Ra := ![1] }
        { P := ![[![0, 0]]], B := ![![1, 1]] }
        ⟨by decide, by decide, by decide,
          S2_of_list _ _ _ _ _ _ [[0]] (by decide) (by acu_cliques), by acu_basis⟩
        (fun (X?, Y?, N?) h => by try simp only [unifiedBy, problem] at h; acu_side h)
        (fun (X?, Y?, N?) h hD => by acu_distinct) ?_
    acu_branches
    -- branch (0,0)
    refine rename (fun (N?, Z1) => (N?, ![Z1]))
        (fun (N?, Z) => (N?, Z 0))
        (fun (N?, Z) => Prod.ext rfl (funext fun i => by fin_cases i; rfl)) ?_
    -- ⊢ M? := N?, X? := Z1, Y? := Z1 | - | -
    checkpoint
    -- cover answer 3 with U1! := Z1, U2! := N?
    exact cover answer3 (by simp [answers]) fun (N?, Z1) _ _ => ⟨(Z1, N?), by acu_cover⟩
  · -- distinct:
    -- ⊢ - | X? + {Elem.w N?} = Y? + {Elem.w M?} | Elem.w N? ≠ Elem.w M?
    checkpoint
    -- solve X? + {Elem.w N?} = Y? + {Elem.w M?}
    refine solve
        { V := fun (X?, Y?, _, _) => ![X?, Y?], rest := fun (_, _, N?, M?) => (N?, M?),
          glue := fun (N?, M?) V => (V 0, V 1, N?, M?) }
        (fun (N?, M?) => ![Elem.w N?, Elem.w M?])
        { L := ![1, 0], R := ![0, 1], La := ![1, 0], Ra := ![0, 1] }
        { P := ![[![0, 1]], [![1, 0]]], B := ![![1, 1]] }
        ⟨by decide, by decide, by decide,
          S2_of_list _ _ _ _ _ _ [[0], [1]] (by decide) (by acu_cliques), by acu_basis⟩
        (fun (X?, Y?, N?, M?) h => by try simp only [unifiedBy, problem] at h; acu_side h)
        (fun (X?, Y?, N?, M?) h hD => by acu_distinct) ?_
    acu_branches
    -- branch (0,1) (1,0)
    refine rename (fun (N?, M?, Z1) => ((N?, M?), ![Z1]))
        (fun ((N?, M?), Z) => (N?, M?, Z 0))
        (fun ((N?, M?), Z) => Prod.ext rfl (funext fun i => by fin_cases i; rfl)) ?_
    -- ⊢ X? := Z1 + {Elem.w M?}, Y? := Z1 + {Elem.w N?} | - | Elem.w N? ≠ Elem.w M?
    checkpoint
    -- cover answer 1 with U1! := N?, U2! := M?, U3! := Z1
    exact cover answer1 (by simp [answers]) fun (N?, M?, Z1) _ _ => ⟨(N?, M?, Z1), by acu_cover⟩

end Demo.Mixed
