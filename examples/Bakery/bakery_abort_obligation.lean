import examples.Bakery.bakery_abort
import conPanna.Unification.Tactics.maudeCertifyComp

/-!
Bakery, abortable: the obligations of `abortable_preserves_inv`, printed by
`#obligations` and pasted verbatim. Completeness is certified by Maude
(`maude_certify_comp`); soundness by instantiating each unifier and checking the two
sides equal modulo ACU.
-/

namespace Bakery

open Expresso Unification Narrowing

-- the statements below are `#obligations`' output, pasted verbatim
set_option linter.style.longLine false
-- the soundness proofs share one script; with a single unifier, its `repeat'` is idle
set_option linter.unusedTactic false

theorem abortable_preserves_inv.obligation_1 :
    Unification.complete (Narrowing.mayFire abortR initialP)
      [Unification.Unifier.bind fun (x : ℕ × ℕ) => ((x.2, x.2, x.1, ∅), x.2, {Mode.wait x.1}),
        Unification.Unifier.bind fun (x : ProcSet × ℕ × ℕ) =>
          ((x.2.2, x.2.2, x.2.1, x.1), x.2.2, x.1 + {Mode.wait x.2.1})] := by
  maude_certify_comp

theorem abortable_preserves_inv.obligation_2 :
    Unification.sound (Narrowing.mayFire abortR initialP)
      [Unification.Unifier.bind fun (x : ℕ × ℕ) => ((x.2, x.2, x.1, ∅), x.2, {Mode.wait x.1}),
        Unification.Unifier.bind fun (x : ProcSet × ℕ × ℕ) =>
          ((x.2.2, x.2.2, x.2.1, x.1), x.2.2, x.1 + {Mode.wait x.2.1})] := by
  -- each unifier, instantiated, solves the problem
  simp only [sound, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  repeat' apply And.intro
  all_goals
    rintro γ ⟨x, rfl⟩
    simp only [unifiedBy, mayFire, abortR, initialP]
    try ac_rfl

theorem abortable_preserves_inv.obligation_3 :
    Unification.complete (Narrowing.mayFire abortR waitingP)
      [Unification.Unifier.bind fun (x : ℕ × ℕ × ℕ) => ((x.2.1, x.2.2, x.1, ∅), x.2.1, x.2.2, {Mode.wait x.1}),
        Unification.Unifier.bind fun (x : ProcSet × ℕ × ℕ × ℕ) =>
          ((x.2.2.1, x.2.2.2, x.2.1, x.1), x.2.2.1, x.2.2.2, x.1 + {Mode.wait x.2.1})] := by
  maude_certify_comp

theorem abortable_preserves_inv.obligation_4 :
    Unification.sound (Narrowing.mayFire abortR waitingP)
      [Unification.Unifier.bind fun (x : ℕ × ℕ × ℕ) => ((x.2.1, x.2.2, x.1, ∅), x.2.1, x.2.2, {Mode.wait x.1}),
        Unification.Unifier.bind fun (x : ProcSet × ℕ × ℕ × ℕ) =>
          ((x.2.2.1, x.2.2.2, x.2.1, x.1), x.2.2.1, x.2.2.2, x.1 + {Mode.wait x.2.1})] := by
  -- each unifier, instantiated, solves the problem
  simp only [sound, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  repeat' apply And.intro
  all_goals
    rintro γ ⟨x, rfl⟩
    simp only [unifiedBy, mayFire, abortR, waitingP]
    try ac_rfl

theorem abortable_preserves_inv.obligation_5 :
    Unification.complete (Narrowing.mayFire abortR criticalP)
      [Unification.Unifier.bind fun (x : ℕ × ℕ × ℕ) =>
          ((x.2.1, x.2.2, x.1, {Mode.crit x.2.2}), x.2.1, x.2.2, {Mode.wait x.1}),
        Unification.Unifier.bind fun (x : ℕ × ℕ × ℕ × ProcSet) =>
          ((x.2.1, x.2.2.1, x.1, x.2.2.2 + {Mode.crit x.2.2.1}), x.2.1, x.2.2.1, x.2.2.2 + {Mode.wait x.1})] := by
  maude_certify_comp

theorem abortable_preserves_inv.obligation_6 :
    Unification.sound (Narrowing.mayFire abortR criticalP)
      [Unification.Unifier.bind fun (x : ℕ × ℕ × ℕ) =>
          ((x.2.1, x.2.2, x.1, {Mode.crit x.2.2}), x.2.1, x.2.2, {Mode.wait x.1}),
        Unification.Unifier.bind fun (x : ℕ × ℕ × ℕ × ProcSet) =>
          ((x.2.1, x.2.2.1, x.1, x.2.2.2 + {Mode.crit x.2.2.1}), x.2.1, x.2.2.1, x.2.2.2 + {Mode.wait x.1})] := by
  -- each unifier, instantiated, solves the problem
  simp only [sound, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  repeat' apply And.intro
  all_goals
    rintro γ ⟨x, rfl⟩
    simp only [unifiedBy, mayFire, abortR, criticalP]
    try ac_rfl

theorem abortable_preserves_inv.obligation_7 :
    Unification.complete (Narrowing.mayFire skipR initialP)
      [Unification.Unifier.bind fun (x : ℕ × ProcSet) => ((x.1, x.1, x.2), x.1, x.2)] := by
  maude_certify_comp

theorem abortable_preserves_inv.obligation_8 :
    Unification.sound (Narrowing.mayFire skipR initialP)
      [Unification.Unifier.bind fun (x : ℕ × ProcSet) => ((x.1, x.1, x.2), x.1, x.2)] := by
  -- each unifier, instantiated, solves the problem
  simp only [sound, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  repeat' apply And.intro
  all_goals
    rintro γ ⟨x, rfl⟩
    simp only [unifiedBy, mayFire, skipR, initialP]
    try ac_rfl

theorem abortable_preserves_inv.obligation_9 :
    Unification.complete (Narrowing.mayFire skipR waitingP)
      [Unification.Unifier.bind fun (x : ℕ × ℕ × ProcSet) => ((x.1, x.2.1, x.2.2), x.1, x.2.1, x.2.2)] := by
  maude_certify_comp

theorem abortable_preserves_inv.obligation_10 :
    Unification.sound (Narrowing.mayFire skipR waitingP)
      [Unification.Unifier.bind fun (x : ℕ × ℕ × ProcSet) => ((x.1, x.2.1, x.2.2), x.1, x.2.1, x.2.2)] := by
  -- each unifier, instantiated, solves the problem
  simp only [sound, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  repeat' apply And.intro
  all_goals
    rintro γ ⟨x, rfl⟩
    simp only [unifiedBy, mayFire, skipR, waitingP]
    try ac_rfl

theorem abortable_preserves_inv.obligation_11 :
    Unification.complete (Narrowing.mayFire skipR criticalP)
      [Unification.Unifier.bind fun (x : ℕ × ℕ) => ((x.1, x.2, {Mode.crit x.2}), x.1, x.2, ∅),
        Unification.Unifier.bind fun (x : ℕ × ℕ × ProcSet) =>
          ((x.1, x.2.1, x.2.2 + {Mode.crit x.2.1}), x.1, x.2.1, x.2.2)] := by
  maude_certify_comp

theorem abortable_preserves_inv.obligation_12 :
    Unification.sound (Narrowing.mayFire skipR criticalP)
      [Unification.Unifier.bind fun (x : ℕ × ℕ) => ((x.1, x.2, {Mode.crit x.2}), x.1, x.2, ∅),
        Unification.Unifier.bind fun (x : ℕ × ℕ × ProcSet) =>
          ((x.1, x.2.1, x.2.2 + {Mode.crit x.2.1}), x.1, x.2.1, x.2.2)] := by
  -- each unifier, instantiated, solves the problem
  simp only [sound, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  repeat' apply And.intro
  all_goals
    rintro γ ⟨x, rfl⟩
    simp only [unifiedBy, mayFire, skipR, criticalP]
    try ac_rfl

end Bakery
