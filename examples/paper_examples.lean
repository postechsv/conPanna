import conPanna.Unification.Certification.Calculus
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-!
The worked examples of the paper draft (§6), as Lean certificates.
Each step names the paper rule it applies. Original variables end in `?`, the answers'
own (existential) variables are `U1!`, `U2!`, ..., and SOLVE's fresh variables are `Z`. A judgment `⟨α ; E ; D⟩ ⊩ answers` is shown in comments.
-/

open Unification Certification

/-! ## §6.1 Mixed free and ACU: `X? + {w N?} = Y? + {w M?}` -/
namespace Mixed

inductive Elem where
  | w (n : Nat)

abbrev Bag := ACU Elem

-- Original variables (X?, Y?, N?, M?).
def problem : Problem Bag (Bag × Bag × Nat × Nat) :=
  .bind fun (X?, Y?, N?, M?) => (X? + {.w N?}, Y? + {.w M?})

-- Maude's four answers, verbatim up to naming.
def answer1 : Unifier (Bag × Bag × Nat × Nat) :=
  .bind fun (U1!, U2!) => ⟨{Elem.w U2!}, {Elem.w U1!}, U1!, U2!⟩
def answer2 : Unifier (Bag × Bag × Nat × Nat) :=
  .bind fun (U1!, U2!, U3!) => ⟨U3! + {Elem.w U2!}, U3! + {Elem.w U1!}, U1!, U2!⟩
def answer3 : Unifier (Bag × Bag × Nat × Nat) :=
  .bind fun U1! => ⟨∅, ∅, U1!, U1!⟩
def answer4 : Unifier (Bag × Bag × Nat × Nat) :=
  .bind fun (U1!, U2!) => ⟨U1!, U1!, U2!, U2!⟩
def answers : UnifierSet (Bag × Bag × Nat × Nat) := [answer1, answer2, answer3, answer4]

example : complete problem answers := by
  rw [← start_iff]
  -- ⟨id ; X? + {w N?} = Y? + {w M?} ; ∅⟩
  -- IDENTIFY the aliens w N? and w M?.
  refine identify (fun (_, _, N?, _) => Elem.w N?) (fun (_, _, _, M?) => Elem.w M?) ?eq ?ne
  case eq =>
    -- ⟨id ; X? + {w N?} = Y? + {w M?}, w N? = w M? ; ∅⟩
    -- DECOMP w N? = w M?: w is free, so N? = M?.
    refine decomp [fun (_, _, N?, M?) => N? = M?] (fun _ hw => ⟨Elem.w.inj hw, trivial⟩) ?_
    -- ⟨id ; N? = M?, X? + {w N?} = Y? + {w M?} ; ∅⟩
    -- ELIM M? := N?. The context becomes (X?, Y?, N?).
    refine elim (fun (X?, Y?, N?) => (X?, Y?, N?, N?))
      (fun (X?, Y?, N?, M?) hNM => ⟨(X?, Y?, N?), by subst hNM; rfl⟩) ?_
    -- ⟨M? ↦ N? ; X? + {w N?} = Y? + {w N?} ; ∅⟩
    -- SOLVE: one alien class; per element x + 1 = y + 1 at w N?, x = y elsewhere.
    --   P = {(0,0)} (the aliens cancel),  B = {(1,1)}.
    refine solve
      { V := fun (X?, Y?, _) => ![X?, Y?], rest := fun (_, _, N?) => N?,
        glue := fun N? V => (V 0, V 1, N?) }
      (fun N? => ![Elem.w N?])
      { L := ![1, 0], R := ![0, 1], La := ![1], Ra := ![1] }
      { P := fun _ => [![0, 0]], B := ![![1, 1]] }
      ⟨?S0, ?S1p, ?S1b, S2_single _ _ _ _ _ ?S2, ?S3⟩ ?heq ?hdistinct ?next
    case heq =>
      intro ⟨X?, Y?, N?⟩ h
      simpa [BagEq.Holds, side, sum, copies, List.ofFn_succ, ACU.plus_unit, ACU.unit_plus] using h
    case hdistinct => intro _ _ _ c c' hc _; exact absurd (Subsingleton.elim c c') hc
    case S0 => decide
    case S1p => decide
    case S1b => decide
    case S2 => intro c v _; exact ⟨![0, 0], by simp, fun i => by fin_cases i <;> simp⟩
    case S3 =>
      intro v h hv; refine ⟨0, fun i => ?_⟩
      simp [dot, List.ofFn_succ, Fin.exists_fin_two] at h hv; fin_cases i <;> simp <;> omega
    case next =>
      -- leaf ⟨X? ↦ Z1, Y? ↦ Z1, M? ↦ N? ; ∅ ; ∅⟩
      intro π hπ; simp [choices] at hπ; subst hπ
      -- COVER with answer 4: U1! := Z1, U2! := N?.
      exact cover answer4 (.tail _ (.tail _ (.tail _ (.head _)))) fun (N?, Z) _ _ =>
        ⟨(Z 0, N?), by simp [theta, sum, ACU.plus_unit, ACU.unit_plus]; rfl⟩
  case ne =>
    -- ⟨id ; X? + {w N?} = Y? + {w M?} ; w N? ≠ w M?⟩
    -- SOLVE: two alien classes a₁ = w N?, a₂ = w M?.
    --   at a₁: x + 1 = y, P = {(0,1)};  at a₂: x = y + 1, P = {(1,0)};  B = {(1,1)}.
    refine solve
      { V := fun (X?, Y?, _, _) => ![X?, Y?], rest := fun (_, _, N?, M?) => (N?, M?),
        glue := fun (N?, M?) V => (V 0, V 1, N?, M?) }
      (fun (N?, M?) => ![Elem.w N?, Elem.w M?])
      { L := ![1, 0], R := ![0, 1], La := ![1, 0], Ra := ![0, 1] }
      { P := ![[![0, 1]], [![1, 0]]], B := ![![1, 1]] }
      ⟨?S0, ?S1p, ?S1b, S2_single _ _ _ _ _ ?S2, ?S3⟩ ?heq ?hdistinct ?next
    case heq =>
      intro ⟨X?, Y?, N?, M?⟩ h
      simpa [BagEq.Holds, side, sum, copies, List.ofFn_succ, ACU.plus_unit, ACU.unit_plus] using h
    case hdistinct =>
      intro ⟨X?, Y?, N?, M?⟩ _ ⟨_, hNM⟩ c c' hc _
      fin_cases c <;> fin_cases c' <;> simp_all [BagEq.cp, eq_comm]
    case S0 => decide
    case S1p => decide
    case S1b => decide
    case S2 =>
      intro c v h; fin_cases c <;> simp [dot, List.ofFn_succ] at h
      · exact ⟨![0, 1], by simp, fun i => by fin_cases i <;> (simp; try omega)⟩
      · exact ⟨![1, 0], by simp, fun i => by fin_cases i <;> (simp; try omega)⟩
    case S3 =>
      intro v h hv; refine ⟨0, fun i => ?_⟩
      simp [dot, List.ofFn_succ, Fin.exists_fin_two] at h hv; fin_cases i <;> simp <;> omega
    case next =>
      -- leaf ⟨X? ↦ Z1 + {w M?}, Y? ↦ Z1 + {w N?} ; ∅ ; w N? ≠ w M?⟩
      intro π hπ; simp [choices] at hπ; subst hπ
      -- COVER with answer 2: U1! := N?, U2! := M?, U3! := Z1.
      exact cover answer2 (.tail _ (.head _)) fun ((N?, M?), Z) _ _ =>
        ⟨(N?, M?, Z 0), by simp [theta, sum, ACU.plus_unit, ACU.unit_plus]; ac_rfl⟩

end Mixed

/-! ## §6.2 Nonlinear: `X? + Y? = Z? + Z?` -/
namespace Nonlinear

variable {El : Type}

-- Original variables (X?, Y?, Z?).
def problem : Problem (ACU El) (ACU El × ACU El × ACU El) :=
  .bind fun (X?, Y?, Z?) => (X? + Y?, Z? + Z?)

-- Maude's most general answer: variables U1! U2! U3!, one per basis vector.
def answer8 : Unifier (ACU El × ACU El × ACU El) :=
  .bind fun (U1!, U2!, U3!) => ⟨U1! + U1! + U2!, U2! + U3! + U3!, U1! + U2! + U3!⟩

-- Maude's eight answers; the first seven are special cases of answer 8.
def answers : UnifierSet (ACU El × ACU El × ACU El) :=
  [ .bind fun () => ⟨∅, ∅, ∅⟩,
    .bind fun U1! => ⟨U1! + U1!, ∅, U1!⟩,
    .bind fun U1! => ⟨U1!, U1!, U1!⟩,
    .bind fun (U1!, U2!) => ⟨U1! + U2! + U2!, U1!, U1! + U2!⟩,
    .bind fun U1! => ⟨∅, U1! + U1!, U1!⟩,
    .bind fun (U1!, U2!) => ⟨U1! + U1!, U2! + U2!, U1! + U2!⟩,
    .bind fun (U1!, U2!) => ⟨U1!, U1! + U2! + U2!, U1! + U2!⟩,
    answer8 ]

-- The basis vectors, read off answer 8.
def basis : Fin 3 → Fin 3 → ℕ
  | 0 => ![2, 0, 1]
  | 1 => ![1, 1, 1]
  | 2 => ![0, 2, 1]

example : complete (problem (El := El)) answers := by
  rw [← start_iff]
  -- ⟨id ; X? + Y? = Z? + Z? ; ∅⟩
  -- SOLVE: no aliens; per element x + y = 2z.
  --   B = {(2,0,1), (1,1,1), (0,2,1)}, the multiplicities of U1! U2! U3! in answer 8;
  --   each basis vector gets a fresh Z.
  refine solve
    { V := fun (X?, Y?, Z?) => ![X?, Y?, Z?], rest := fun _ => (),
      glue := fun _ V => (V 0, V 1, V 2) }
    (fun _ => Fin.elim0)
    { L := ![1, 1, 0], R := ![0, 0, 2], La := Fin.elim0, Ra := Fin.elim0 }
    { P := Fin.elim0, B := basis }
    ⟨?S0, ?S1p, ?S1b, S2_single _ _ _ _ _ ?S2, ?S3⟩ ?heq ?hdistinct ?next
  case heq =>
    intro ⟨X?, Y?, Z?⟩ h
    have h : X? + Y? = Z? + Z? := h
    simp [BagEq.Holds, side, sum, copies, List.ofFn_succ, ACU.plus_unit, ACU.unit_plus]
    exact h
  case hdistinct => intro _ _ _ c; exact c.elim0
  case S0 => decide
  case S1p => intro c; exact c.elim0
  case S1b => intro j; fin_cases j <;> decide
  case S2 => intro c; exact c.elim0
  case S3 =>
    -- one omega call: every nonzero solution lies above a basis vector
    intro v h hv
    simp [dot, List.ofFn_succ, Fin.exists_fin_succ] at h hv
    by_cases c0 : 2 ≤ v 0 ∧ 1 ≤ v 2
    · exact ⟨0, fun i => by fin_cases i <;> simp [basis] <;> omega⟩
    by_cases c1 : 1 ≤ v 0 ∧ 1 ≤ v 1
    · exact ⟨1, fun i => by fin_cases i <;> simp [basis] <;> omega⟩
    · exact ⟨2, fun i => by fin_cases i <;> simp [basis] <;> omega⟩
  case next =>
    -- leaf ⟨X? ↦ Z1+Z1+Z2, Y? ↦ Z2+Z3+Z3, Z? ↦ Z1+Z2+Z3 ; ∅ ; ∅⟩
    intro π hπ; simp [choices] at hπ; subst hπ
    -- COVER with answer 8: U1! := Z1, U2! := Z2, U3! := Z3.
    exact cover answer8 (by simp [answers]) fun (_, Z) _ _ =>
      ⟨(Z 0, Z 1, Z 2), by
        obtain ⟨Z1, Z2, Z3, rfl⟩ : ∃ a b c, Z = ![a, b, c] :=
          ⟨Z 0, Z 1, Z 2, funext fun i => by fin_cases i <;> rfl⟩
        simp [State.subst, theta, sum, copies, basis, ACU.plus_unit, ACU.unit_plus]
        refine ⟨?_, ?_⟩ <;> ac_rfl⟩

end Nonlinear
