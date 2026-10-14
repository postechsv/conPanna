import Tiny.conPanna.Unification.Certification.Tactics

/-! A system: X? + {w(N?)} =? Y? + {w(M?)} and N? =? M?. -/

/- certify
{
  "namespace": "Pipeline.T4",
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

namespace Pipeline.T4

inductive Elem where
  | w (n : Nat)

abbrev Bag := ACU Elem

def problem : Problem (Bag × Nat) (Bag × Bag × Nat × Nat) :=
  .bind fun (X?, Y?, N?, M?) => ((X? + {Elem.w N?}, N?), (Y? + {Elem.w M?}, M?))

/-! ## Generated from t4_distinct.deriv by producer/tools/compile.py -/

def answer0 : Unifier (Bag × Bag × Nat × Nat) :=
  .bind fun U1! => .subst ⟨{Elem.w U1!}, {Elem.w U1!}, U1!, U1!⟩
def answer1 : Unifier (Bag × Bag × Nat × Nat) :=
  .bind fun (U1!, U2!) => .subst ⟨U2! + {Elem.w U1!}, U2! + {Elem.w U1!}, U1!, U1!⟩
def answer2 : Unifier (Bag × Bag × Nat × Nat) :=
  .bind fun U1! => .subst ⟨∅, ∅, U1!, U1!⟩
def answer3 : Unifier (Bag × Bag × Nat × Nat) :=
  .bind fun (U1!, U2!) => .subst ⟨U2!, U2!, U1!, U1!⟩
def answers : UnifierSet (Bag × Bag × Nat × Nat) :=
  [answer0, answer1, answer2, answer3]

theorem complete : UnifierSet.Complete problem answers := by
  rw [← start_iff]
  -- decomp of the tuple equation into the system
  refine decomp (fun (X?, Y?, N?, M?) => X? + {Elem.w N?} = Y? + {Elem.w M?} ∧ N? = M?)
      (fun (X?, Y?, N?, M?) h => by acu_free [problem]) ?_
  -- ⊢ - | X? + {Elem.w N?} = Y? + {Elem.w M?}; N? = M? | -
  -- identify Elem.w N? ~ Elem.w M?
  refine identify (fun (_, _, N?, _) => Elem.w N?) (fun (_, _, _, M?) => Elem.w M?) ?_ ?_
  · -- equal:
    -- ⊢ - | Elem.w N? = Elem.w M?; X? + {Elem.w N?} = Y? + {Elem.w M?}; N? = M? | -
    -- decomp Elem.w N? = Elem.w M?
    refine decomp (fun (X?, Y?, N?, M?) => N? = M? ∧ X? + {Elem.w N?} = Y? + {Elem.w M?} ∧ N? = M?)
        (fun (X?, Y?, N?, M?) h => by acu_free [problem]) ?_
    -- ⊢ - | N? = M?; X? + {Elem.w N?} = Y? + {Elem.w M?}; N? = M? | -
    -- elim M? := N?
    refine elim (fun (X?, Y?, N?) => (X?, Y?, N?, N?))
        (fun (X?, Y?, N?) => X? + {Elem.w N?} = Y? + {Elem.w N?} ∧ N? = N?)
        (fun (X?, Y?, N?, M?) h => ⟨(X?, Y?, N?), by acu_free [problem], by acu_free [problem]⟩) ?_
    -- ⊢ M? := N? | X? + {Elem.w N?} = Y? + {Elem.w N?}; N? = N? | -
    -- solve X? + {Elem.w N?} = Y? + {Elem.w N?}
    refine solve (V := fun (X?, Y?, _) => ![X?, Y?]) (rest := fun (_, _, N?) => N?)
        (glue := fun N? V => (V 0, V 1, N?)) (hglue := fun _ => rfl)
        (a := fun N? => ![Elem.w N?]) (L := ![1, 0]) (R := ![0, 1]) (La := ![1]) (Ra := ![1])
        (E' := fun (_, _, N?) => N? = N?) (cp := fun _ _ => false)
        (P := ![[![0, 0]]]) (B := ![![1, 1]])
        (fun (X?, Y?, N?) h hD => ⟨by try simp only [State.start, Problem.unifies, problem] at h; acu_side h.1, h.2, by acu_distinct⟩)
        (by decide) (by decide) (by decide)
        (S2_of_list _ _ _ _ _ _ [[0]] (by decide) (by acu_cliques)) (by acu_basis) ?_
    intro π hπ; simp [choices] at hπ; subst hπ
    -- branch (0,0)
    refine rename (fun (N?, Z1) => (N?, ![Z1]))
        (fun (N?, Z) => (N?, Z 0))
        (fun (N?, Z) => Prod.ext rfl (funext fun i => by fin_cases i; rfl)) ?_
    -- ⊢ M? := N?, X? := Z1, Y? := Z1 | N? = N? | -
    -- delete N? = N?
    refine decomp (fun (_, _) => True)
        (fun (N?, Z1) h => by acu_free [problem]) ?_
    -- ⊢ M? := N?, X? := Z1, Y? := Z1 | - | -
    -- cover answer 3 with U1! := N?, U2! := Z1
    exact cover answer3 (by simp [answers]) fun (N?, Z1) _ _ => ⟨(N?, Z1), by acu_cover⟩
  · -- distinct:
    -- ⊢ - | X? + {Elem.w N?} = Y? + {Elem.w M?}; N? = M? | Elem.w N? ≠ Elem.w M?
    -- solve X? + {Elem.w N?} = Y? + {Elem.w M?}
    refine solve (V := fun (X?, Y?, _, _) => ![X?, Y?]) (rest := fun (_, _, N?, M?) => (N?, M?))
        (glue := fun (N?, M?) V => (V 0, V 1, N?, M?)) (hglue := fun _ => rfl)
        (a := fun (N?, M?) => ![Elem.w N?, Elem.w M?]) (L := ![1, 0]) (R := ![0, 1]) (La := ![1, 0]) (Ra := ![0, 1])
        (E' := fun (_, _, N?, M?) => N? = M?) (cp := fun _ _ => false)
        (P := ![[![0, 1]], [![1, 0]]]) (B := ![![1, 1]])
        (fun (X?, Y?, N?, M?) h hD => ⟨by try simp only [State.start, Problem.unifies, problem] at h; acu_side h.1, h.2, by acu_distinct⟩)
        (by decide) (by decide) (by decide)
        (S2_of_list _ _ _ _ _ _ [[0], [1]] (by decide) (by acu_cliques)) (by acu_basis) ?_
    intro π hπ; simp [choices] at hπ; subst hπ
    -- branch (0,1) (1,0)
    refine rename (fun (N?, M?, Z1) => ((N?, M?), ![Z1]))
        (fun ((N?, M?), Z) => (N?, M?, Z 0))
        (fun ((N?, M?), Z) => Prod.ext rfl (funext fun i => by fin_cases i; rfl)) ?_
    -- ⊢ X? := Z1 + {Elem.w M?}, Y? := Z1 + {Elem.w N?} | N? = M? | Elem.w N? ≠ Elem.w M?
    -- elim M? := N?
    refine elim (fun (N?, Z1) => (N?, N?, Z1))
        (fun (_, _) => True)
        (fun (N?, M?, Z1) h => ⟨(N?, Z1), by acu_free [problem], by acu_free [problem]⟩) ?_
    -- ⊢ M? := N?, X? := Z1 + {Elem.w N?}, Y? := Z1 + {Elem.w N?} | - | Elem.w N? ≠ Elem.w N?
    -- distinct
    exact clash fun (N?, Z1) h hD => by acu_free [problem]

end Pipeline.T4
