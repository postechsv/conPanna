import examples.Bakery.proof
import conPanna.Unification.Tactics.udfCertify

/-!
Bakery: the certification obligations of `bakery_preserves_inv` and
`abortable_preserves_inv`, as `#obligations` prints them. Completeness: the certificate
narrowing stored for the claim, replayed through the proved rules (`udf_certify`).
Soundness: each unifier, instantiated, solves the problem modulo ACU.
-/

set_option linter.style.longLine false
set_option linter.unusedSimpArgs false

open Expresso Unification Narrowing

theorem Bakery.bakery_preserves_inv.obligation_1 :
    Unification.complete (Narrowing.mayFire Bakery.wakeR Bakery.initialP)
      [Unification.Unifier.bind fun (x : Bakery.ProcSet × ℕ) => ((x.2, x.2, x.1), x.2, {Bakery.Mode.idle} + x.1)] := by
  udf_certify

theorem Bakery.bakery_preserves_inv.obligation_2 :
    Unification.sound (Narrowing.mayFire Bakery.wakeR Bakery.initialP)
      [Unification.Unifier.bind fun (x : Bakery.ProcSet × ℕ) => ((x.2, x.2, x.1), x.2, {Bakery.Mode.idle} + x.1)] := by
  -- each unifier, instantiated, solves the problem
  simp only [sound, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  repeat' apply And.intro
  all_goals
    rintro γ ⟨x, rfl⟩
    simp only [unifiedBy, Narrowing.mayFire, Bakery.wakeR, Bakery.initialP]
    try simp only [ACU.plus_unit, ACU.unit_plus, ACU.plus_comm, ACU.plus_left_comm,
      ACU.plus_assoc]

theorem Bakery.bakery_preserves_inv.obligation_3 :
    Unification.complete (Narrowing.mayFire Bakery.wakeR Bakery.waitingP)
      [Unification.Unifier.bind fun (x : Bakery.ProcSet × ℕ × ℕ) =>
          ((x.2.1, x.2.2, x.1), x.2.1, x.2.2, {Bakery.Mode.idle} + x.1)] := by
  udf_certify

theorem Bakery.bakery_preserves_inv.obligation_4 :
    Unification.sound (Narrowing.mayFire Bakery.wakeR Bakery.waitingP)
      [Unification.Unifier.bind fun (x : Bakery.ProcSet × ℕ × ℕ) =>
          ((x.2.1, x.2.2, x.1), x.2.1, x.2.2, {Bakery.Mode.idle} + x.1)] := by
  -- each unifier, instantiated, solves the problem
  simp only [sound, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  repeat' apply And.intro
  all_goals
    rintro γ ⟨x, rfl⟩
    simp only [unifiedBy, Narrowing.mayFire, Bakery.wakeR, Bakery.waitingP]
    try simp only [ACU.plus_unit, ACU.unit_plus, ACU.plus_comm, ACU.plus_left_comm,
      ACU.plus_assoc]

theorem Bakery.bakery_preserves_inv.obligation_5 :
    Unification.complete (Narrowing.mayFire Bakery.wakeR Bakery.criticalP)
      [Unification.Unifier.bind fun (x : ℕ × ℕ × Bakery.ProcSet) =>
          ((x.1, x.2.1, {Bakery.Mode.crit x.2.1} + x.2.2), x.1, x.2.1, {Bakery.Mode.idle} + x.2.2)] := by
  udf_certify

theorem Bakery.bakery_preserves_inv.obligation_6 :
    Unification.sound (Narrowing.mayFire Bakery.wakeR Bakery.criticalP)
      [Unification.Unifier.bind fun (x : ℕ × ℕ × Bakery.ProcSet) =>
          ((x.1, x.2.1, {Bakery.Mode.crit x.2.1} + x.2.2), x.1, x.2.1, {Bakery.Mode.idle} + x.2.2)] := by
  -- each unifier, instantiated, solves the problem
  simp only [sound, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  repeat' apply And.intro
  all_goals
    rintro γ ⟨x, rfl⟩
    simp only [unifiedBy, Narrowing.mayFire, Bakery.wakeR, Bakery.criticalP]
    try simp only [ACU.plus_unit, ACU.unit_plus, ACU.plus_comm, ACU.plus_left_comm,
      ACU.plus_assoc]

theorem Bakery.bakery_preserves_inv.obligation_7 :
    Unification.complete (Narrowing.mayFire Bakery.enterR Bakery.initialP)
      [Unification.Unifier.bind fun (x : Bakery.ProcSet × ℕ) =>
          ((x.2, x.2, x.1), x.2, {Bakery.Mode.wait x.2} + x.1)] := by
  udf_certify

theorem Bakery.bakery_preserves_inv.obligation_8 :
    Unification.sound (Narrowing.mayFire Bakery.enterR Bakery.initialP)
      [Unification.Unifier.bind fun (x : Bakery.ProcSet × ℕ) =>
          ((x.2, x.2, x.1), x.2, {Bakery.Mode.wait x.2} + x.1)] := by
  -- each unifier, instantiated, solves the problem
  simp only [sound, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  repeat' apply And.intro
  all_goals
    rintro γ ⟨x, rfl⟩
    simp only [unifiedBy, Narrowing.mayFire, Bakery.enterR, Bakery.initialP]
    try simp only [ACU.plus_unit, ACU.unit_plus, ACU.plus_comm, ACU.plus_left_comm,
      ACU.plus_assoc]

theorem Bakery.bakery_preserves_inv.obligation_9 :
    Unification.complete (Narrowing.mayFire Bakery.enterR Bakery.waitingP)
      [Unification.Unifier.bind fun (x : Bakery.ProcSet × ℕ × ℕ) =>
          ((x.2.1, x.2.2, x.1), x.2.1, x.2.2, {Bakery.Mode.wait x.2.2} + x.1)] := by
  udf_certify

theorem Bakery.bakery_preserves_inv.obligation_10 :
    Unification.sound (Narrowing.mayFire Bakery.enterR Bakery.waitingP)
      [Unification.Unifier.bind fun (x : Bakery.ProcSet × ℕ × ℕ) =>
          ((x.2.1, x.2.2, x.1), x.2.1, x.2.2, {Bakery.Mode.wait x.2.2} + x.1)] := by
  -- each unifier, instantiated, solves the problem
  simp only [sound, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  repeat' apply And.intro
  all_goals
    rintro γ ⟨x, rfl⟩
    simp only [unifiedBy, Narrowing.mayFire, Bakery.enterR, Bakery.waitingP]
    try simp only [ACU.plus_unit, ACU.unit_plus, ACU.plus_comm, ACU.plus_left_comm,
      ACU.plus_assoc]

theorem Bakery.bakery_preserves_inv.obligation_11 :
    Unification.complete (Narrowing.mayFire Bakery.enterR Bakery.criticalP)
      [Unification.Unifier.bind fun (x : ℕ × ℕ × Bakery.ProcSet) =>
          ((x.1, x.2.1, {Bakery.Mode.crit x.2.1} + x.2.2), x.1, x.2.1, {Bakery.Mode.wait x.2.1} + x.2.2)] := by
  udf_certify

theorem Bakery.bakery_preserves_inv.obligation_12 :
    Unification.sound (Narrowing.mayFire Bakery.enterR Bakery.criticalP)
      [Unification.Unifier.bind fun (x : ℕ × ℕ × Bakery.ProcSet) =>
          ((x.1, x.2.1, {Bakery.Mode.crit x.2.1} + x.2.2), x.1, x.2.1, {Bakery.Mode.wait x.2.1} + x.2.2)] := by
  -- each unifier, instantiated, solves the problem
  simp only [sound, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  repeat' apply And.intro
  all_goals
    rintro γ ⟨x, rfl⟩
    simp only [unifiedBy, Narrowing.mayFire, Bakery.enterR, Bakery.criticalP]
    try simp only [ACU.plus_unit, ACU.unit_plus, ACU.plus_comm, ACU.plus_left_comm,
      ACU.plus_assoc]

theorem Bakery.bakery_preserves_inv.obligation_13 :
    Unification.complete (Narrowing.mayFire Bakery.exitR Bakery.initialP)
      [Unification.Unifier.bind fun (x : Bakery.ProcSet × ℕ) =>
          ((x.2, x.2, x.1), x.2, {Bakery.Mode.crit x.2} + x.1)] := by
  udf_certify

theorem Bakery.bakery_preserves_inv.obligation_14 :
    Unification.sound (Narrowing.mayFire Bakery.exitR Bakery.initialP)
      [Unification.Unifier.bind fun (x : Bakery.ProcSet × ℕ) =>
          ((x.2, x.2, x.1), x.2, {Bakery.Mode.crit x.2} + x.1)] := by
  -- each unifier, instantiated, solves the problem
  simp only [sound, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  repeat' apply And.intro
  all_goals
    rintro γ ⟨x, rfl⟩
    simp only [unifiedBy, Narrowing.mayFire, Bakery.exitR, Bakery.initialP]
    try simp only [ACU.plus_unit, ACU.unit_plus, ACU.plus_comm, ACU.plus_left_comm,
      ACU.plus_assoc]

theorem Bakery.bakery_preserves_inv.obligation_15 :
    Unification.complete (Narrowing.mayFire Bakery.exitR Bakery.waitingP)
      [Unification.Unifier.bind fun (x : Bakery.ProcSet × ℕ × ℕ) =>
          ((x.2.1, x.2.2, x.1), x.2.1, x.2.2, {Bakery.Mode.crit x.2.2} + x.1)] := by
  udf_certify

theorem Bakery.bakery_preserves_inv.obligation_16 :
    Unification.sound (Narrowing.mayFire Bakery.exitR Bakery.waitingP)
      [Unification.Unifier.bind fun (x : Bakery.ProcSet × ℕ × ℕ) =>
          ((x.2.1, x.2.2, x.1), x.2.1, x.2.2, {Bakery.Mode.crit x.2.2} + x.1)] := by
  -- each unifier, instantiated, solves the problem
  simp only [sound, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  repeat' apply And.intro
  all_goals
    rintro γ ⟨x, rfl⟩
    simp only [unifiedBy, Narrowing.mayFire, Bakery.exitR, Bakery.waitingP]
    try simp only [ACU.plus_unit, ACU.unit_plus, ACU.plus_comm, ACU.plus_left_comm,
      ACU.plus_assoc]

theorem Bakery.bakery_preserves_inv.obligation_17 :
    Unification.complete (Narrowing.mayFire Bakery.exitR Bakery.criticalP)
      [Unification.Unifier.bind fun (x : ℕ × ℕ × Bakery.ProcSet) => ((x.1, x.2.1, x.2.2), x.1, x.2.1, x.2.2)] := by
  udf_certify

theorem Bakery.bakery_preserves_inv.obligation_18 :
    Unification.sound (Narrowing.mayFire Bakery.exitR Bakery.criticalP)
      [Unification.Unifier.bind fun (x : ℕ × ℕ × Bakery.ProcSet) => ((x.1, x.2.1, x.2.2), x.1, x.2.1, x.2.2)] := by
  -- each unifier, instantiated, solves the problem
  simp only [sound, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  repeat' apply And.intro
  all_goals
    rintro γ ⟨x, rfl⟩
    simp only [unifiedBy, Narrowing.mayFire, Bakery.exitR, Bakery.criticalP]
    try simp only [ACU.plus_unit, ACU.unit_plus, ACU.plus_comm, ACU.plus_left_comm,
      ACU.plus_assoc]

theorem Bakery.abortable_preserves_inv.obligation_1 :
    Unification.complete (Narrowing.mayFire Bakery.abortR Bakery.initialP)
      [Unification.Unifier.bind fun (x : Bakery.ProcSet × ℕ × ℕ) =>
          ((x.2.2, x.2.2, x.2.1, x.1), x.2.2, {Bakery.Mode.wait x.2.1} + x.1)] := by
  udf_certify

theorem Bakery.abortable_preserves_inv.obligation_2 :
    Unification.sound (Narrowing.mayFire Bakery.abortR Bakery.initialP)
      [Unification.Unifier.bind fun (x : Bakery.ProcSet × ℕ × ℕ) =>
          ((x.2.2, x.2.2, x.2.1, x.1), x.2.2, {Bakery.Mode.wait x.2.1} + x.1)] := by
  -- each unifier, instantiated, solves the problem
  simp only [sound, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  repeat' apply And.intro
  all_goals
    rintro γ ⟨x, rfl⟩
    simp only [unifiedBy, Narrowing.mayFire, Bakery.abortR, Bakery.initialP]
    try simp only [ACU.plus_unit, ACU.unit_plus, ACU.plus_comm, ACU.plus_left_comm,
      ACU.plus_assoc]

theorem Bakery.abortable_preserves_inv.obligation_3 :
    Unification.complete (Narrowing.mayFire Bakery.abortR Bakery.waitingP)
      [Unification.Unifier.bind fun (x : Bakery.ProcSet × ℕ × ℕ × ℕ) =>
          ((x.2.2.1, x.2.2.2, x.2.1, x.1), x.2.2.1, x.2.2.2, {Bakery.Mode.wait x.2.1} + x.1)] := by
  udf_certify

theorem Bakery.abortable_preserves_inv.obligation_4 :
    Unification.sound (Narrowing.mayFire Bakery.abortR Bakery.waitingP)
      [Unification.Unifier.bind fun (x : Bakery.ProcSet × ℕ × ℕ × ℕ) =>
          ((x.2.2.1, x.2.2.2, x.2.1, x.1), x.2.2.1, x.2.2.2, {Bakery.Mode.wait x.2.1} + x.1)] := by
  -- each unifier, instantiated, solves the problem
  simp only [sound, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  repeat' apply And.intro
  all_goals
    rintro γ ⟨x, rfl⟩
    simp only [unifiedBy, Narrowing.mayFire, Bakery.abortR, Bakery.waitingP]
    try simp only [ACU.plus_unit, ACU.unit_plus, ACU.plus_comm, ACU.plus_left_comm,
      ACU.plus_assoc]

theorem Bakery.abortable_preserves_inv.obligation_5 :
    Unification.complete (Narrowing.mayFire Bakery.abortR Bakery.criticalP)
      [Unification.Unifier.bind fun (x : ℕ × ℕ × ℕ × Bakery.ProcSet) =>
          ((x.2.1, x.2.2.1, x.1, {Bakery.Mode.crit x.2.2.1} + x.2.2.2), x.2.1, x.2.2.1,
            {Bakery.Mode.wait x.1} + x.2.2.2)] := by
  udf_certify

theorem Bakery.abortable_preserves_inv.obligation_6 :
    Unification.sound (Narrowing.mayFire Bakery.abortR Bakery.criticalP)
      [Unification.Unifier.bind fun (x : ℕ × ℕ × ℕ × Bakery.ProcSet) =>
          ((x.2.1, x.2.2.1, x.1, {Bakery.Mode.crit x.2.2.1} + x.2.2.2), x.2.1, x.2.2.1,
            {Bakery.Mode.wait x.1} + x.2.2.2)] := by
  -- each unifier, instantiated, solves the problem
  simp only [sound, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  repeat' apply And.intro
  all_goals
    rintro γ ⟨x, rfl⟩
    simp only [unifiedBy, Narrowing.mayFire, Bakery.abortR, Bakery.criticalP]
    try simp only [ACU.plus_unit, ACU.unit_plus, ACU.plus_comm, ACU.plus_left_comm,
      ACU.plus_assoc]

theorem Bakery.abortable_preserves_inv.obligation_7 :
    Unification.complete (Narrowing.mayFire Bakery.skipR Bakery.initialP)
      [Unification.Unifier.bind fun (x : ℕ × Bakery.ProcSet) => ((x.1, x.1, x.2), x.1, x.2)] := by
  udf_certify

theorem Bakery.abortable_preserves_inv.obligation_8 :
    Unification.sound (Narrowing.mayFire Bakery.skipR Bakery.initialP)
      [Unification.Unifier.bind fun (x : ℕ × Bakery.ProcSet) => ((x.1, x.1, x.2), x.1, x.2)] := by
  -- each unifier, instantiated, solves the problem
  simp only [sound, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  repeat' apply And.intro
  all_goals
    rintro γ ⟨x, rfl⟩
    simp only [unifiedBy, Narrowing.mayFire, Bakery.skipR, Bakery.initialP]
    try simp only [ACU.plus_unit, ACU.unit_plus, ACU.plus_comm, ACU.plus_left_comm,
      ACU.plus_assoc]

theorem Bakery.abortable_preserves_inv.obligation_9 :
    Unification.complete (Narrowing.mayFire Bakery.skipR Bakery.waitingP)
      [Unification.Unifier.bind fun (x : ℕ × ℕ × Bakery.ProcSet) => ((x.1, x.2.1, x.2.2), x.1, x.2.1, x.2.2)] := by
  udf_certify

theorem Bakery.abortable_preserves_inv.obligation_10 :
    Unification.sound (Narrowing.mayFire Bakery.skipR Bakery.waitingP)
      [Unification.Unifier.bind fun (x : ℕ × ℕ × Bakery.ProcSet) => ((x.1, x.2.1, x.2.2), x.1, x.2.1, x.2.2)] := by
  -- each unifier, instantiated, solves the problem
  simp only [sound, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  repeat' apply And.intro
  all_goals
    rintro γ ⟨x, rfl⟩
    simp only [unifiedBy, Narrowing.mayFire, Bakery.skipR, Bakery.waitingP]
    try simp only [ACU.plus_unit, ACU.unit_plus, ACU.plus_comm, ACU.plus_left_comm,
      ACU.plus_assoc]

theorem Bakery.abortable_preserves_inv.obligation_11 :
    Unification.complete (Narrowing.mayFire Bakery.skipR Bakery.criticalP)
      [Unification.Unifier.bind fun (x : ℕ × ℕ × Bakery.ProcSet) =>
          ((x.1, x.2.1, {Bakery.Mode.crit x.2.1} + x.2.2), x.1, x.2.1, x.2.2)] := by
  udf_certify

theorem Bakery.abortable_preserves_inv.obligation_12 :
    Unification.sound (Narrowing.mayFire Bakery.skipR Bakery.criticalP)
      [Unification.Unifier.bind fun (x : ℕ × ℕ × Bakery.ProcSet) =>
          ((x.1, x.2.1, {Bakery.Mode.crit x.2.1} + x.2.2), x.1, x.2.1, x.2.2)] := by
  -- each unifier, instantiated, solves the problem
  simp only [sound, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  repeat' apply And.intro
  all_goals
    rintro γ ⟨x, rfl⟩
    simp only [unifiedBy, Narrowing.mayFire, Bakery.skipR, Bakery.criticalP]
    try simp only [ACU.plus_unit, ACU.unit_plus, ACU.plus_comm, ACU.plus_left_comm,
      ACU.plus_assoc]
