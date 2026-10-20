import examples.TwoPC.draft.TwoPC
import conPanna.Unification.Tactics.maudeCertifyComp

/-!
Two-phase commit: the obligations of `twoPC_inv`, printed by `#obligations` and pasted
verbatim. Completeness is certified by Maude (`maude_certify_comp`); soundness by
instantiating each unifier and checking the two sides equal modulo ACU.
-/

namespace TwoPC

open Expresso Unification Narrowing

-- the statements below are `#obligations`' output, pasted verbatim
set_option linter.style.longLine false

theorem twoPC_inv.obligation_1 :
    complete (mayFire voteYes collP)
      [Unifier.bind fun (x : ℕ × ℕ × Oids × Oids × Oid) =>
          ((x.1, x.2.2.2.2,
              {Item.coord { id := x.2.1, phase := CState.collecting, parts := x.2.2.1, wait := x.2.2.2.1 }}),
            x.2.1, x.2.2.1, x.2.2.2.1, {Item.part { id := x.1, state := PState.working }}),
        Unifier.bind fun (x : ℕ × ℕ × Oids × Oids × Items × Oid) =>
          ((x.1, x.2.2.2.2.2,
              x.2.2.2.2.1 +
                {Item.coord { id := x.2.1, phase := CState.collecting, parts := x.2.2.1, wait := x.2.2.2.1 }}),
            x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1 + {Item.part { id := x.1, state := PState.working }})] := by
  maude_certify_comp

theorem twoPC_inv.obligation_2 :
    sound (mayFire voteYes collP)
      [Unifier.bind fun (x : ℕ × ℕ × Oids × Oids × Oid) =>
          ((x.1, x.2.2.2.2,
              {Item.coord { id := x.2.1, phase := CState.collecting, parts := x.2.2.1, wait := x.2.2.2.1 }}),
            x.2.1, x.2.2.1, x.2.2.2.1, {Item.part { id := x.1, state := PState.working }}),
        Unifier.bind fun (x : ℕ × ℕ × Oids × Oids × Items × Oid) =>
          ((x.1, x.2.2.2.2.2,
              x.2.2.2.2.1 +
                {Item.coord { id := x.2.1, phase := CState.collecting, parts := x.2.2.1, wait := x.2.2.2.1 }}),
            x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1 + {Item.part { id := x.1, state := PState.working }})] := by
  simp only [sound, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  repeat' apply And.intro
  all_goals
    rintro γ ⟨x, rfl⟩
    simp only [unifiedBy, mayFire, voteYes, collP]
    try ac_rfl

theorem twoPC_inv.obligation_3 :
    complete (mayFire voteYes commP)
      [Unifier.bind fun (x : ℕ × ℕ × Oids × Oids × Oid) =>
          ((x.1, x.2.2.2.2,
              {Item.coord { id := x.2.1, phase := CState.committing, parts := x.2.2.1, wait := x.2.2.2.1 }}),
            x.2.1, x.2.2.1, x.2.2.2.1, {Item.part { id := x.1, state := PState.working }}),
        Unifier.bind fun (x : ℕ × ℕ × Oids × Oids × Items × Oid) =>
          ((x.1, x.2.2.2.2.2,
              x.2.2.2.2.1 +
                {Item.coord { id := x.2.1, phase := CState.committing, parts := x.2.2.1, wait := x.2.2.2.1 }}),
            x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1 + {Item.part { id := x.1, state := PState.working }})] := by
  maude_certify_comp

theorem twoPC_inv.obligation_4 :
    sound (mayFire voteYes commP)
      [Unifier.bind fun (x : ℕ × ℕ × Oids × Oids × Oid) =>
          ((x.1, x.2.2.2.2,
              {Item.coord { id := x.2.1, phase := CState.committing, parts := x.2.2.1, wait := x.2.2.2.1 }}),
            x.2.1, x.2.2.1, x.2.2.2.1, {Item.part { id := x.1, state := PState.working }}),
        Unifier.bind fun (x : ℕ × ℕ × Oids × Oids × Items × Oid) =>
          ((x.1, x.2.2.2.2.2,
              x.2.2.2.2.1 +
                {Item.coord { id := x.2.1, phase := CState.committing, parts := x.2.2.1, wait := x.2.2.2.1 }}),
            x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1 + {Item.part { id := x.1, state := PState.working }})] := by
  simp only [sound, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  repeat' apply And.intro
  all_goals
    rintro γ ⟨x, rfl⟩
    simp only [unifiedBy, mayFire, voteYes, commP]
    try ac_rfl

theorem twoPC_inv.obligation_5 :
    complete (mayFire voteYes abrtP)
      [Unifier.bind fun (x : ℕ × ℕ × Oids × Oids × Oid) =>
          ((x.1, x.2.2.2.2,
              {Item.coord { id := x.2.1, phase := CState.aborting, parts := x.2.2.1, wait := x.2.2.2.1 }}),
            x.2.1, x.2.2.1, x.2.2.2.1, {Item.part { id := x.1, state := PState.working }}),
        Unifier.bind fun (x : ℕ × ℕ × Oids × Oids × Items × Oid) =>
          ((x.1, x.2.2.2.2.2,
              x.2.2.2.2.1 +
                {Item.coord { id := x.2.1, phase := CState.aborting, parts := x.2.2.1, wait := x.2.2.2.1 }}),
            x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1 + {Item.part { id := x.1, state := PState.working }})] := by
  maude_certify_comp

theorem twoPC_inv.obligation_6 :
    sound (mayFire voteYes abrtP)
      [Unifier.bind fun (x : ℕ × ℕ × Oids × Oids × Oid) =>
          ((x.1, x.2.2.2.2,
              {Item.coord { id := x.2.1, phase := CState.aborting, parts := x.2.2.1, wait := x.2.2.2.1 }}),
            x.2.1, x.2.2.1, x.2.2.2.1, {Item.part { id := x.1, state := PState.working }}),
        Unifier.bind fun (x : ℕ × ℕ × Oids × Oids × Items × Oid) =>
          ((x.1, x.2.2.2.2.2,
              x.2.2.2.2.1 +
                {Item.coord { id := x.2.1, phase := CState.aborting, parts := x.2.2.1, wait := x.2.2.2.1 }}),
            x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1 + {Item.part { id := x.1, state := PState.working }})] := by
  simp only [sound, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  repeat' apply And.intro
  all_goals
    rintro γ ⟨x, rfl⟩
    simp only [unifiedBy, mayFire, voteYes, abrtP]
    try ac_rfl

theorem twoPC_inv.obligation_7 :
    complete (mayFire voteNo collP)
      [Unifier.bind fun (x : ℕ × ℕ × Oids × Oids × Oid) =>
          ((x.1, x.2.2.2.2,
              {Item.coord { id := x.2.1, phase := CState.collecting, parts := x.2.2.1, wait := x.2.2.2.1 }}),
            x.2.1, x.2.2.1, x.2.2.2.1, {Item.part { id := x.1, state := PState.working }}),
        Unifier.bind fun (x : ℕ × ℕ × Oids × Oids × Items × Oid) =>
          ((x.1, x.2.2.2.2.2,
              x.2.2.2.2.1 +
                {Item.coord { id := x.2.1, phase := CState.collecting, parts := x.2.2.1, wait := x.2.2.2.1 }}),
            x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1 + {Item.part { id := x.1, state := PState.working }})] := by
  maude_certify_comp

theorem twoPC_inv.obligation_8 :
    sound (mayFire voteNo collP)
      [Unifier.bind fun (x : ℕ × ℕ × Oids × Oids × Oid) =>
          ((x.1, x.2.2.2.2,
              {Item.coord { id := x.2.1, phase := CState.collecting, parts := x.2.2.1, wait := x.2.2.2.1 }}),
            x.2.1, x.2.2.1, x.2.2.2.1, {Item.part { id := x.1, state := PState.working }}),
        Unifier.bind fun (x : ℕ × ℕ × Oids × Oids × Items × Oid) =>
          ((x.1, x.2.2.2.2.2,
              x.2.2.2.2.1 +
                {Item.coord { id := x.2.1, phase := CState.collecting, parts := x.2.2.1, wait := x.2.2.2.1 }}),
            x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1 + {Item.part { id := x.1, state := PState.working }})] := by
  simp only [sound, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  repeat' apply And.intro
  all_goals
    rintro γ ⟨x, rfl⟩
    simp only [unifiedBy, mayFire, voteNo, collP]
    try ac_rfl

theorem twoPC_inv.obligation_9 :
    complete (mayFire voteNo commP)
      [Unifier.bind fun (x : ℕ × ℕ × Oids × Oids × Oid) =>
          ((x.1, x.2.2.2.2,
              {Item.coord { id := x.2.1, phase := CState.committing, parts := x.2.2.1, wait := x.2.2.2.1 }}),
            x.2.1, x.2.2.1, x.2.2.2.1, {Item.part { id := x.1, state := PState.working }}),
        Unifier.bind fun (x : ℕ × ℕ × Oids × Oids × Items × Oid) =>
          ((x.1, x.2.2.2.2.2,
              x.2.2.2.2.1 +
                {Item.coord { id := x.2.1, phase := CState.committing, parts := x.2.2.1, wait := x.2.2.2.1 }}),
            x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1 + {Item.part { id := x.1, state := PState.working }})] := by
  maude_certify_comp

theorem twoPC_inv.obligation_10 :
    sound (mayFire voteNo commP)
      [Unifier.bind fun (x : ℕ × ℕ × Oids × Oids × Oid) =>
          ((x.1, x.2.2.2.2,
              {Item.coord { id := x.2.1, phase := CState.committing, parts := x.2.2.1, wait := x.2.2.2.1 }}),
            x.2.1, x.2.2.1, x.2.2.2.1, {Item.part { id := x.1, state := PState.working }}),
        Unifier.bind fun (x : ℕ × ℕ × Oids × Oids × Items × Oid) =>
          ((x.1, x.2.2.2.2.2,
              x.2.2.2.2.1 +
                {Item.coord { id := x.2.1, phase := CState.committing, parts := x.2.2.1, wait := x.2.2.2.1 }}),
            x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1 + {Item.part { id := x.1, state := PState.working }})] := by
  simp only [sound, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  repeat' apply And.intro
  all_goals
    rintro γ ⟨x, rfl⟩
    simp only [unifiedBy, mayFire, voteNo, commP]
    try ac_rfl

theorem twoPC_inv.obligation_11 :
    complete (mayFire voteNo abrtP)
      [Unifier.bind fun (x : ℕ × ℕ × Oids × Oids × Oid) =>
          ((x.1, x.2.2.2.2,
              {Item.coord { id := x.2.1, phase := CState.aborting, parts := x.2.2.1, wait := x.2.2.2.1 }}),
            x.2.1, x.2.2.1, x.2.2.2.1, {Item.part { id := x.1, state := PState.working }}),
        Unifier.bind fun (x : ℕ × ℕ × Oids × Oids × Items × Oid) =>
          ((x.1, x.2.2.2.2.2,
              x.2.2.2.2.1 +
                {Item.coord { id := x.2.1, phase := CState.aborting, parts := x.2.2.1, wait := x.2.2.2.1 }}),
            x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1 + {Item.part { id := x.1, state := PState.working }})] := by
  maude_certify_comp

theorem twoPC_inv.obligation_12 :
    sound (mayFire voteNo abrtP)
      [Unifier.bind fun (x : ℕ × ℕ × Oids × Oids × Oid) =>
          ((x.1, x.2.2.2.2,
              {Item.coord { id := x.2.1, phase := CState.aborting, parts := x.2.2.1, wait := x.2.2.2.1 }}),
            x.2.1, x.2.2.1, x.2.2.2.1, {Item.part { id := x.1, state := PState.working }}),
        Unifier.bind fun (x : ℕ × ℕ × Oids × Oids × Items × Oid) =>
          ((x.1, x.2.2.2.2.2,
              x.2.2.2.2.1 +
                {Item.coord { id := x.2.1, phase := CState.aborting, parts := x.2.2.1, wait := x.2.2.2.1 }}),
            x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1 + {Item.part { id := x.1, state := PState.working }})] := by
  simp only [sound, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  repeat' apply And.intro
  all_goals
    rintro γ ⟨x, rfl⟩
    simp only [unifiedBy, mayFire, voteNo, abrtP]
    try ac_rfl

theorem twoPC_inv.obligation_13 :
    complete (mayFire recvYes collP)
      [Unifier.bind fun (x : ℕ × Oids × ℕ × ℕ × Oids × Oids) =>
          ((x.1, x.2.1, x.2.2.1, ∅,
              {Item.coord { id := x.2.2.2.1, phase := CState.collecting, parts := x.2.2.2.2.1, wait := x.2.2.2.2.2 }}),
            x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2,
            {Item.coord { id := x.1, phase := CState.collecting, parts := x.2.1, wait := {x.2.2.1} }} +
              {Item.msg (Msg.vote true x.2.2.1 x.1)}),
        Unifier.bind fun (x : ℕ × Oids × ℕ × Oids × ℕ × Oids × Oids) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {Item.coord
                  { id := x.2.2.2.2.1, phase := CState.collecting, parts := x.2.2.2.2.2.1, wait := x.2.2.2.2.2.2 }}),
            x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2,
            {Item.coord { id := x.1, phase := CState.collecting, parts := x.2.1, wait := {x.2.2.1} + x.2.2.2.1 }} +
              {Item.msg (Msg.vote true x.2.2.1 x.1)}),
        Unifier.bind fun (x : ℕ × Oids × ℕ × ℕ × Oids × Oids × Items) =>
          ((x.1, x.2.1, x.2.2.1, ∅,
              x.2.2.2.2.2.2 +
                {Item.coord
                    { id := x.2.2.2.1, phase := CState.collecting, parts := x.2.2.2.2.1, wait := x.2.2.2.2.2.1 }}),
            x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
            x.2.2.2.2.2.2 + {Item.coord { id := x.1, phase := CState.collecting, parts := x.2.1, wait := {x.2.2.1} }} +
              {Item.msg (Msg.vote true x.2.2.1 x.1)}),
        Unifier.bind fun (x : ℕ × Oids × ℕ × Oids × ℕ × Oids × Oids × Items) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              x.2.2.2.2.2.2.2 +
                {Item.coord
                    { id := x.2.2.2.2.1, phase := CState.collecting, parts := x.2.2.2.2.2.1,
                      wait := x.2.2.2.2.2.2.1 }}),
            x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
            x.2.2.2.2.2.2.2 +
                {Item.coord { id := x.1, phase := CState.collecting, parts := x.2.1, wait := {x.2.2.1} + x.2.2.2.1 }} +
              {Item.msg (Msg.vote true x.2.2.1 x.1)}),
        Unifier.bind fun (x : ℕ × ℕ × Oids) =>
          ((x.2.1, x.2.2, x.1, ∅, ∅), x.2.1, x.2.2, {x.1}, {Item.msg (Msg.vote true x.1 x.2.1)}),
        Unifier.bind fun (x : ℕ × Oids × ℕ × Oids) =>
          ((x.2.2.1, x.2.2.2, x.1, x.2.1, ∅), x.2.2.1, x.2.2.2, {x.1} + x.2.1, {Item.msg (Msg.vote true x.1 x.2.2.1)}),
        Unifier.bind fun (x : Items × ℕ × ℕ × Oids) =>
          ((x.2.2.1, x.2.2.2, x.2.1, ∅, x.1), x.2.2.1, x.2.2.2, {x.2.1},
            x.1 + {Item.msg (Msg.vote true x.2.1 x.2.2.1)}),
        Unifier.bind fun (x : Items × ℕ × Oids × ℕ × Oids) =>
          ((x.2.2.2.1, x.2.2.2.2, x.2.1, x.2.2.1, x.1), x.2.2.2.1, x.2.2.2.2, {x.2.1} + x.2.2.1,
            x.1 + {Item.msg (Msg.vote true x.2.1 x.2.2.2.1)})] := by
  maude_certify_comp

theorem twoPC_inv.obligation_14 :
    sound (mayFire recvYes collP)
      [Unifier.bind fun (x : ℕ × Oids × ℕ × ℕ × Oids × Oids) =>
          ((x.1, x.2.1, x.2.2.1, ∅,
              {Item.coord { id := x.2.2.2.1, phase := CState.collecting, parts := x.2.2.2.2.1, wait := x.2.2.2.2.2 }}),
            x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2,
            {Item.coord { id := x.1, phase := CState.collecting, parts := x.2.1, wait := {x.2.2.1} }} +
              {Item.msg (Msg.vote true x.2.2.1 x.1)}),
        Unifier.bind fun (x : ℕ × Oids × ℕ × Oids × ℕ × Oids × Oids) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {Item.coord
                  { id := x.2.2.2.2.1, phase := CState.collecting, parts := x.2.2.2.2.2.1, wait := x.2.2.2.2.2.2 }}),
            x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2,
            {Item.coord { id := x.1, phase := CState.collecting, parts := x.2.1, wait := {x.2.2.1} + x.2.2.2.1 }} +
              {Item.msg (Msg.vote true x.2.2.1 x.1)}),
        Unifier.bind fun (x : ℕ × Oids × ℕ × ℕ × Oids × Oids × Items) =>
          ((x.1, x.2.1, x.2.2.1, ∅,
              x.2.2.2.2.2.2 +
                {Item.coord
                    { id := x.2.2.2.1, phase := CState.collecting, parts := x.2.2.2.2.1, wait := x.2.2.2.2.2.1 }}),
            x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
            x.2.2.2.2.2.2 + {Item.coord { id := x.1, phase := CState.collecting, parts := x.2.1, wait := {x.2.2.1} }} +
              {Item.msg (Msg.vote true x.2.2.1 x.1)}),
        Unifier.bind fun (x : ℕ × Oids × ℕ × Oids × ℕ × Oids × Oids × Items) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              x.2.2.2.2.2.2.2 +
                {Item.coord
                    { id := x.2.2.2.2.1, phase := CState.collecting, parts := x.2.2.2.2.2.1,
                      wait := x.2.2.2.2.2.2.1 }}),
            x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
            x.2.2.2.2.2.2.2 +
                {Item.coord { id := x.1, phase := CState.collecting, parts := x.2.1, wait := {x.2.2.1} + x.2.2.2.1 }} +
              {Item.msg (Msg.vote true x.2.2.1 x.1)}),
        Unifier.bind fun (x : ℕ × ℕ × Oids) =>
          ((x.2.1, x.2.2, x.1, ∅, ∅), x.2.1, x.2.2, {x.1}, {Item.msg (Msg.vote true x.1 x.2.1)}),
        Unifier.bind fun (x : ℕ × Oids × ℕ × Oids) =>
          ((x.2.2.1, x.2.2.2, x.1, x.2.1, ∅), x.2.2.1, x.2.2.2, {x.1} + x.2.1, {Item.msg (Msg.vote true x.1 x.2.2.1)}),
        Unifier.bind fun (x : Items × ℕ × ℕ × Oids) =>
          ((x.2.2.1, x.2.2.2, x.2.1, ∅, x.1), x.2.2.1, x.2.2.2, {x.2.1},
            x.1 + {Item.msg (Msg.vote true x.2.1 x.2.2.1)}),
        Unifier.bind fun (x : Items × ℕ × Oids × ℕ × Oids) =>
          ((x.2.2.2.1, x.2.2.2.2, x.2.1, x.2.2.1, x.1), x.2.2.2.1, x.2.2.2.2, {x.2.1} + x.2.2.1,
            x.1 + {Item.msg (Msg.vote true x.2.1 x.2.2.2.1)})] := by
  simp only [sound, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  repeat' apply And.intro
  all_goals
    rintro γ ⟨x, rfl⟩
    simp only [unifiedBy, mayFire, recvYes, collP]
    try ac_rfl

theorem twoPC_inv.obligation_15 :
    complete (mayFire recvYes commP)
      [Unifier.bind fun (x : ℕ × Oids × ℕ × ℕ × Oids × Oids) =>
          ((x.1, x.2.1, x.2.2.1, ∅,
              {Item.coord { id := x.2.2.2.1, phase := CState.committing, parts := x.2.2.2.2.1, wait := x.2.2.2.2.2 }}),
            x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2,
            {Item.coord { id := x.1, phase := CState.collecting, parts := x.2.1, wait := {x.2.2.1} }} +
              {Item.msg (Msg.vote true x.2.2.1 x.1)}),
        Unifier.bind fun (x : ℕ × Oids × ℕ × Oids × ℕ × Oids × Oids) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {Item.coord
                  { id := x.2.2.2.2.1, phase := CState.committing, parts := x.2.2.2.2.2.1, wait := x.2.2.2.2.2.2 }}),
            x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2,
            {Item.coord { id := x.1, phase := CState.collecting, parts := x.2.1, wait := {x.2.2.1} + x.2.2.2.1 }} +
              {Item.msg (Msg.vote true x.2.2.1 x.1)}),
        Unifier.bind fun (x : ℕ × Oids × ℕ × ℕ × Oids × Oids × Items) =>
          ((x.1, x.2.1, x.2.2.1, ∅,
              x.2.2.2.2.2.2 +
                {Item.coord
                    { id := x.2.2.2.1, phase := CState.committing, parts := x.2.2.2.2.1, wait := x.2.2.2.2.2.1 }}),
            x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
            x.2.2.2.2.2.2 + {Item.coord { id := x.1, phase := CState.collecting, parts := x.2.1, wait := {x.2.2.1} }} +
              {Item.msg (Msg.vote true x.2.2.1 x.1)}),
        Unifier.bind fun (x : ℕ × Oids × ℕ × Oids × ℕ × Oids × Oids × Items) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              x.2.2.2.2.2.2.2 +
                {Item.coord
                    { id := x.2.2.2.2.1, phase := CState.committing, parts := x.2.2.2.2.2.1,
                      wait := x.2.2.2.2.2.2.1 }}),
            x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
            x.2.2.2.2.2.2.2 +
                {Item.coord { id := x.1, phase := CState.collecting, parts := x.2.1, wait := {x.2.2.1} + x.2.2.2.1 }} +
              {Item.msg (Msg.vote true x.2.2.1 x.1)})] := by
  maude_certify_comp

theorem twoPC_inv.obligation_16 :
    sound (mayFire recvYes commP)
      [Unifier.bind fun (x : ℕ × Oids × ℕ × ℕ × Oids × Oids) =>
          ((x.1, x.2.1, x.2.2.1, ∅,
              {Item.coord { id := x.2.2.2.1, phase := CState.committing, parts := x.2.2.2.2.1, wait := x.2.2.2.2.2 }}),
            x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2,
            {Item.coord { id := x.1, phase := CState.collecting, parts := x.2.1, wait := {x.2.2.1} }} +
              {Item.msg (Msg.vote true x.2.2.1 x.1)}),
        Unifier.bind fun (x : ℕ × Oids × ℕ × Oids × ℕ × Oids × Oids) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {Item.coord
                  { id := x.2.2.2.2.1, phase := CState.committing, parts := x.2.2.2.2.2.1, wait := x.2.2.2.2.2.2 }}),
            x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2,
            {Item.coord { id := x.1, phase := CState.collecting, parts := x.2.1, wait := {x.2.2.1} + x.2.2.2.1 }} +
              {Item.msg (Msg.vote true x.2.2.1 x.1)}),
        Unifier.bind fun (x : ℕ × Oids × ℕ × ℕ × Oids × Oids × Items) =>
          ((x.1, x.2.1, x.2.2.1, ∅,
              x.2.2.2.2.2.2 +
                {Item.coord
                    { id := x.2.2.2.1, phase := CState.committing, parts := x.2.2.2.2.1, wait := x.2.2.2.2.2.1 }}),
            x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
            x.2.2.2.2.2.2 + {Item.coord { id := x.1, phase := CState.collecting, parts := x.2.1, wait := {x.2.2.1} }} +
              {Item.msg (Msg.vote true x.2.2.1 x.1)}),
        Unifier.bind fun (x : ℕ × Oids × ℕ × Oids × ℕ × Oids × Oids × Items) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              x.2.2.2.2.2.2.2 +
                {Item.coord
                    { id := x.2.2.2.2.1, phase := CState.committing, parts := x.2.2.2.2.2.1,
                      wait := x.2.2.2.2.2.2.1 }}),
            x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
            x.2.2.2.2.2.2.2 +
                {Item.coord { id := x.1, phase := CState.collecting, parts := x.2.1, wait := {x.2.2.1} + x.2.2.2.1 }} +
              {Item.msg (Msg.vote true x.2.2.1 x.1)})] := by
  simp only [sound, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  repeat' apply And.intro
  all_goals
    rintro γ ⟨x, rfl⟩
    simp only [unifiedBy, mayFire, recvYes, commP]
    try ac_rfl

theorem twoPC_inv.obligation_17 :
    complete (mayFire recvYes abrtP)
      [Unifier.bind fun (x : ℕ × Oids × ℕ × ℕ × Oids × Oids) =>
          ((x.1, x.2.1, x.2.2.1, ∅,
              {Item.coord { id := x.2.2.2.1, phase := CState.aborting, parts := x.2.2.2.2.1, wait := x.2.2.2.2.2 }}),
            x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2,
            {Item.coord { id := x.1, phase := CState.collecting, parts := x.2.1, wait := {x.2.2.1} }} +
              {Item.msg (Msg.vote true x.2.2.1 x.1)}),
        Unifier.bind fun (x : ℕ × Oids × ℕ × Oids × ℕ × Oids × Oids) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {Item.coord
                  { id := x.2.2.2.2.1, phase := CState.aborting, parts := x.2.2.2.2.2.1, wait := x.2.2.2.2.2.2 }}),
            x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2,
            {Item.coord { id := x.1, phase := CState.collecting, parts := x.2.1, wait := {x.2.2.1} + x.2.2.2.1 }} +
              {Item.msg (Msg.vote true x.2.2.1 x.1)}),
        Unifier.bind fun (x : ℕ × Oids × ℕ × ℕ × Oids × Oids × Items) =>
          ((x.1, x.2.1, x.2.2.1, ∅,
              x.2.2.2.2.2.2 +
                {Item.coord
                    { id := x.2.2.2.1, phase := CState.aborting, parts := x.2.2.2.2.1, wait := x.2.2.2.2.2.1 }}),
            x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
            x.2.2.2.2.2.2 + {Item.coord { id := x.1, phase := CState.collecting, parts := x.2.1, wait := {x.2.2.1} }} +
              {Item.msg (Msg.vote true x.2.2.1 x.1)}),
        Unifier.bind fun (x : ℕ × Oids × ℕ × Oids × ℕ × Oids × Oids × Items) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              x.2.2.2.2.2.2.2 +
                {Item.coord
                    { id := x.2.2.2.2.1, phase := CState.aborting, parts := x.2.2.2.2.2.1, wait := x.2.2.2.2.2.2.1 }}),
            x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
            x.2.2.2.2.2.2.2 +
                {Item.coord { id := x.1, phase := CState.collecting, parts := x.2.1, wait := {x.2.2.1} + x.2.2.2.1 }} +
              {Item.msg (Msg.vote true x.2.2.1 x.1)})] := by
  maude_certify_comp

theorem twoPC_inv.obligation_18 :
    sound (mayFire recvYes abrtP)
      [Unifier.bind fun (x : ℕ × Oids × ℕ × ℕ × Oids × Oids) =>
          ((x.1, x.2.1, x.2.2.1, ∅,
              {Item.coord { id := x.2.2.2.1, phase := CState.aborting, parts := x.2.2.2.2.1, wait := x.2.2.2.2.2 }}),
            x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2,
            {Item.coord { id := x.1, phase := CState.collecting, parts := x.2.1, wait := {x.2.2.1} }} +
              {Item.msg (Msg.vote true x.2.2.1 x.1)}),
        Unifier.bind fun (x : ℕ × Oids × ℕ × Oids × ℕ × Oids × Oids) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {Item.coord
                  { id := x.2.2.2.2.1, phase := CState.aborting, parts := x.2.2.2.2.2.1, wait := x.2.2.2.2.2.2 }}),
            x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2,
            {Item.coord { id := x.1, phase := CState.collecting, parts := x.2.1, wait := {x.2.2.1} + x.2.2.2.1 }} +
              {Item.msg (Msg.vote true x.2.2.1 x.1)}),
        Unifier.bind fun (x : ℕ × Oids × ℕ × ℕ × Oids × Oids × Items) =>
          ((x.1, x.2.1, x.2.2.1, ∅,
              x.2.2.2.2.2.2 +
                {Item.coord
                    { id := x.2.2.2.1, phase := CState.aborting, parts := x.2.2.2.2.1, wait := x.2.2.2.2.2.1 }}),
            x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
            x.2.2.2.2.2.2 + {Item.coord { id := x.1, phase := CState.collecting, parts := x.2.1, wait := {x.2.2.1} }} +
              {Item.msg (Msg.vote true x.2.2.1 x.1)}),
        Unifier.bind fun (x : ℕ × Oids × ℕ × Oids × ℕ × Oids × Oids × Items) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              x.2.2.2.2.2.2.2 +
                {Item.coord
                    { id := x.2.2.2.2.1, phase := CState.aborting, parts := x.2.2.2.2.2.1, wait := x.2.2.2.2.2.2.1 }}),
            x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
            x.2.2.2.2.2.2.2 +
                {Item.coord { id := x.1, phase := CState.collecting, parts := x.2.1, wait := {x.2.2.1} + x.2.2.2.1 }} +
              {Item.msg (Msg.vote true x.2.2.1 x.1)})] := by
  simp only [sound, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  repeat' apply And.intro
  all_goals
    rintro γ ⟨x, rfl⟩
    simp only [unifiedBy, mayFire, recvYes, abrtP]
    try ac_rfl

theorem twoPC_inv.obligation_19 :
    complete (mayFire decideCommit collP)
      [Unifier.bind fun (x : ℕ × Oids × ℕ × Oids × Oids) =>
          ((x.1, x.2.1,
              {Item.coord { id := x.2.2.1, phase := CState.collecting, parts := x.2.2.2.1, wait := x.2.2.2.2 }}),
            x.2.2.1, x.2.2.2.1, x.2.2.2.2,
            {Item.coord { id := x.1, phase := CState.collecting, parts := x.2.1, wait := ∅ }}),
        Unifier.bind fun (x : ℕ × Oids × ℕ × Oids × Oids × Items) =>
          ((x.1, x.2.1,
              x.2.2.2.2.2 +
                {Item.coord { id := x.2.2.1, phase := CState.collecting, parts := x.2.2.2.1, wait := x.2.2.2.2.1 }}),
            x.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
            x.2.2.2.2.2 + {Item.coord { id := x.1, phase := CState.collecting, parts := x.2.1, wait := ∅ }}),
        Unifier.bind fun (x : ℕ × Oids) => ((x.1, x.2, ∅), x.1, x.2, ∅, ∅),
        Unifier.bind fun (x : Items × ℕ × Oids) => ((x.2.1, x.2.2, x.1), x.2.1, x.2.2, ∅, x.1)] := by
  maude_certify_comp

theorem twoPC_inv.obligation_20 :
    sound (mayFire decideCommit collP)
      [Unifier.bind fun (x : ℕ × Oids × ℕ × Oids × Oids) =>
          ((x.1, x.2.1,
              {Item.coord { id := x.2.2.1, phase := CState.collecting, parts := x.2.2.2.1, wait := x.2.2.2.2 }}),
            x.2.2.1, x.2.2.2.1, x.2.2.2.2,
            {Item.coord { id := x.1, phase := CState.collecting, parts := x.2.1, wait := ∅ }}),
        Unifier.bind fun (x : ℕ × Oids × ℕ × Oids × Oids × Items) =>
          ((x.1, x.2.1,
              x.2.2.2.2.2 +
                {Item.coord { id := x.2.2.1, phase := CState.collecting, parts := x.2.2.2.1, wait := x.2.2.2.2.1 }}),
            x.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
            x.2.2.2.2.2 + {Item.coord { id := x.1, phase := CState.collecting, parts := x.2.1, wait := ∅ }}),
        Unifier.bind fun (x : ℕ × Oids) => ((x.1, x.2, ∅), x.1, x.2, ∅, ∅),
        Unifier.bind fun (x : Items × ℕ × Oids) => ((x.2.1, x.2.2, x.1), x.2.1, x.2.2, ∅, x.1)] := by
  simp only [sound, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  repeat' apply And.intro
  all_goals
    rintro γ ⟨x, rfl⟩
    simp only [unifiedBy, mayFire, decideCommit, collP]
    try ac_rfl

theorem twoPC_inv.obligation_21 :
    complete (mayFire decideCommit commP)
      [Unifier.bind fun (x : ℕ × Oids × ℕ × Oids × Oids) =>
          ((x.1, x.2.1,
              {Item.coord { id := x.2.2.1, phase := CState.committing, parts := x.2.2.2.1, wait := x.2.2.2.2 }}),
            x.2.2.1, x.2.2.2.1, x.2.2.2.2,
            {Item.coord { id := x.1, phase := CState.collecting, parts := x.2.1, wait := ∅ }}),
        Unifier.bind fun (x : ℕ × Oids × ℕ × Oids × Oids × Items) =>
          ((x.1, x.2.1,
              x.2.2.2.2.2 +
                {Item.coord { id := x.2.2.1, phase := CState.committing, parts := x.2.2.2.1, wait := x.2.2.2.2.1 }}),
            x.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
            x.2.2.2.2.2 + {Item.coord { id := x.1, phase := CState.collecting, parts := x.2.1, wait := ∅ }})] := by
  maude_certify_comp

theorem twoPC_inv.obligation_22 :
    sound (mayFire decideCommit commP)
      [Unifier.bind fun (x : ℕ × Oids × ℕ × Oids × Oids) =>
          ((x.1, x.2.1,
              {Item.coord { id := x.2.2.1, phase := CState.committing, parts := x.2.2.2.1, wait := x.2.2.2.2 }}),
            x.2.2.1, x.2.2.2.1, x.2.2.2.2,
            {Item.coord { id := x.1, phase := CState.collecting, parts := x.2.1, wait := ∅ }}),
        Unifier.bind fun (x : ℕ × Oids × ℕ × Oids × Oids × Items) =>
          ((x.1, x.2.1,
              x.2.2.2.2.2 +
                {Item.coord { id := x.2.2.1, phase := CState.committing, parts := x.2.2.2.1, wait := x.2.2.2.2.1 }}),
            x.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
            x.2.2.2.2.2 + {Item.coord { id := x.1, phase := CState.collecting, parts := x.2.1, wait := ∅ }})] := by
  simp only [sound, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  repeat' apply And.intro
  all_goals
    rintro γ ⟨x, rfl⟩
    simp only [unifiedBy, mayFire, decideCommit, commP]
    try ac_rfl

theorem twoPC_inv.obligation_23 :
    complete (mayFire decideCommit abrtP)
      [Unifier.bind fun (x : ℕ × Oids × ℕ × Oids × Oids) =>
          ((x.1, x.2.1,
              {Item.coord { id := x.2.2.1, phase := CState.aborting, parts := x.2.2.2.1, wait := x.2.2.2.2 }}),
            x.2.2.1, x.2.2.2.1, x.2.2.2.2,
            {Item.coord { id := x.1, phase := CState.collecting, parts := x.2.1, wait := ∅ }}),
        Unifier.bind fun (x : ℕ × Oids × ℕ × Oids × Oids × Items) =>
          ((x.1, x.2.1,
              x.2.2.2.2.2 +
                {Item.coord { id := x.2.2.1, phase := CState.aborting, parts := x.2.2.2.1, wait := x.2.2.2.2.1 }}),
            x.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
            x.2.2.2.2.2 + {Item.coord { id := x.1, phase := CState.collecting, parts := x.2.1, wait := ∅ }})] := by
  maude_certify_comp

theorem twoPC_inv.obligation_24 :
    sound (mayFire decideCommit abrtP)
      [Unifier.bind fun (x : ℕ × Oids × ℕ × Oids × Oids) =>
          ((x.1, x.2.1,
              {Item.coord { id := x.2.2.1, phase := CState.aborting, parts := x.2.2.2.1, wait := x.2.2.2.2 }}),
            x.2.2.1, x.2.2.2.1, x.2.2.2.2,
            {Item.coord { id := x.1, phase := CState.collecting, parts := x.2.1, wait := ∅ }}),
        Unifier.bind fun (x : ℕ × Oids × ℕ × Oids × Oids × Items) =>
          ((x.1, x.2.1,
              x.2.2.2.2.2 +
                {Item.coord { id := x.2.2.1, phase := CState.aborting, parts := x.2.2.2.1, wait := x.2.2.2.2.1 }}),
            x.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
            x.2.2.2.2.2 + {Item.coord { id := x.1, phase := CState.collecting, parts := x.2.1, wait := ∅ }})] := by
  simp only [sound, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  repeat' apply And.intro
  all_goals
    rintro γ ⟨x, rfl⟩
    simp only [unifiedBy, mayFire, decideCommit, abrtP]
    try ac_rfl

theorem twoPC_inv.obligation_25 :
    complete (mayFire recvNo collP)
      [Unifier.bind fun (x : ℕ × Oids × Oids × ℕ × ℕ × Oids × Oids) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {Item.coord
                  { id := x.2.2.2.2.1, phase := CState.collecting, parts := x.2.2.2.2.2.1, wait := x.2.2.2.2.2.2 }}),
            x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2,
            {Item.coord { id := x.1, phase := CState.collecting, parts := x.2.1, wait := x.2.2.1 }} +
              {Item.msg (Msg.vote false x.2.2.2.1 x.1)}),
        Unifier.bind fun (x : ℕ × Oids × Oids × ℕ × ℕ × Oids × Oids × Items) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              x.2.2.2.2.2.2.2 +
                {Item.coord
                    { id := x.2.2.2.2.1, phase := CState.collecting, parts := x.2.2.2.2.2.1,
                      wait := x.2.2.2.2.2.2.1 }}),
            x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
            x.2.2.2.2.2.2.2 + {Item.coord { id := x.1, phase := CState.collecting, parts := x.2.1, wait := x.2.2.1 }} +
              {Item.msg (Msg.vote false x.2.2.2.1 x.1)}),
        Unifier.bind fun (x : ℕ × ℕ × Oids × Oids) =>
          ((x.2.1, x.2.2.1, x.2.2.2, x.1, ∅), x.2.1, x.2.2.1, x.2.2.2, {Item.msg (Msg.vote false x.1 x.2.1)}),
        Unifier.bind fun (x : Items × ℕ × ℕ × Oids × Oids) =>
          ((x.2.2.1, x.2.2.2.1, x.2.2.2.2, x.2.1, x.1), x.2.2.1, x.2.2.2.1, x.2.2.2.2,
            x.1 + {Item.msg (Msg.vote false x.2.1 x.2.2.1)})] := by
  maude_certify_comp

theorem twoPC_inv.obligation_26 :
    sound (mayFire recvNo collP)
      [Unifier.bind fun (x : ℕ × Oids × Oids × ℕ × ℕ × Oids × Oids) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {Item.coord
                  { id := x.2.2.2.2.1, phase := CState.collecting, parts := x.2.2.2.2.2.1, wait := x.2.2.2.2.2.2 }}),
            x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2,
            {Item.coord { id := x.1, phase := CState.collecting, parts := x.2.1, wait := x.2.2.1 }} +
              {Item.msg (Msg.vote false x.2.2.2.1 x.1)}),
        Unifier.bind fun (x : ℕ × Oids × Oids × ℕ × ℕ × Oids × Oids × Items) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              x.2.2.2.2.2.2.2 +
                {Item.coord
                    { id := x.2.2.2.2.1, phase := CState.collecting, parts := x.2.2.2.2.2.1,
                      wait := x.2.2.2.2.2.2.1 }}),
            x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
            x.2.2.2.2.2.2.2 + {Item.coord { id := x.1, phase := CState.collecting, parts := x.2.1, wait := x.2.2.1 }} +
              {Item.msg (Msg.vote false x.2.2.2.1 x.1)}),
        Unifier.bind fun (x : ℕ × ℕ × Oids × Oids) =>
          ((x.2.1, x.2.2.1, x.2.2.2, x.1, ∅), x.2.1, x.2.2.1, x.2.2.2, {Item.msg (Msg.vote false x.1 x.2.1)}),
        Unifier.bind fun (x : Items × ℕ × ℕ × Oids × Oids) =>
          ((x.2.2.1, x.2.2.2.1, x.2.2.2.2, x.2.1, x.1), x.2.2.1, x.2.2.2.1, x.2.2.2.2,
            x.1 + {Item.msg (Msg.vote false x.2.1 x.2.2.1)})] := by
  simp only [sound, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  repeat' apply And.intro
  all_goals
    rintro γ ⟨x, rfl⟩
    simp only [unifiedBy, mayFire, recvNo, collP]
    try ac_rfl

theorem twoPC_inv.obligation_27 :
    complete (mayFire recvNo commP)
      [Unifier.bind fun (x : ℕ × Oids × Oids × ℕ × ℕ × Oids × Oids) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {Item.coord
                  { id := x.2.2.2.2.1, phase := CState.committing, parts := x.2.2.2.2.2.1, wait := x.2.2.2.2.2.2 }}),
            x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2,
            {Item.coord { id := x.1, phase := CState.collecting, parts := x.2.1, wait := x.2.2.1 }} +
              {Item.msg (Msg.vote false x.2.2.2.1 x.1)}),
        Unifier.bind fun (x : ℕ × Oids × Oids × ℕ × ℕ × Oids × Oids × Items) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              x.2.2.2.2.2.2.2 +
                {Item.coord
                    { id := x.2.2.2.2.1, phase := CState.committing, parts := x.2.2.2.2.2.1,
                      wait := x.2.2.2.2.2.2.1 }}),
            x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
            x.2.2.2.2.2.2.2 + {Item.coord { id := x.1, phase := CState.collecting, parts := x.2.1, wait := x.2.2.1 }} +
              {Item.msg (Msg.vote false x.2.2.2.1 x.1)})] := by
  maude_certify_comp

theorem twoPC_inv.obligation_28 :
    sound (mayFire recvNo commP)
      [Unifier.bind fun (x : ℕ × Oids × Oids × ℕ × ℕ × Oids × Oids) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {Item.coord
                  { id := x.2.2.2.2.1, phase := CState.committing, parts := x.2.2.2.2.2.1, wait := x.2.2.2.2.2.2 }}),
            x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2,
            {Item.coord { id := x.1, phase := CState.collecting, parts := x.2.1, wait := x.2.2.1 }} +
              {Item.msg (Msg.vote false x.2.2.2.1 x.1)}),
        Unifier.bind fun (x : ℕ × Oids × Oids × ℕ × ℕ × Oids × Oids × Items) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              x.2.2.2.2.2.2.2 +
                {Item.coord
                    { id := x.2.2.2.2.1, phase := CState.committing, parts := x.2.2.2.2.2.1,
                      wait := x.2.2.2.2.2.2.1 }}),
            x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
            x.2.2.2.2.2.2.2 + {Item.coord { id := x.1, phase := CState.collecting, parts := x.2.1, wait := x.2.2.1 }} +
              {Item.msg (Msg.vote false x.2.2.2.1 x.1)})] := by
  simp only [sound, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  repeat' apply And.intro
  all_goals
    rintro γ ⟨x, rfl⟩
    simp only [unifiedBy, mayFire, recvNo, commP]
    try ac_rfl

theorem twoPC_inv.obligation_29 :
    complete (mayFire recvNo abrtP)
      [Unifier.bind fun (x : ℕ × Oids × Oids × ℕ × ℕ × Oids × Oids) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {Item.coord
                  { id := x.2.2.2.2.1, phase := CState.aborting, parts := x.2.2.2.2.2.1, wait := x.2.2.2.2.2.2 }}),
            x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2,
            {Item.coord { id := x.1, phase := CState.collecting, parts := x.2.1, wait := x.2.2.1 }} +
              {Item.msg (Msg.vote false x.2.2.2.1 x.1)}),
        Unifier.bind fun (x : ℕ × Oids × Oids × ℕ × ℕ × Oids × Oids × Items) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              x.2.2.2.2.2.2.2 +
                {Item.coord
                    { id := x.2.2.2.2.1, phase := CState.aborting, parts := x.2.2.2.2.2.1, wait := x.2.2.2.2.2.2.1 }}),
            x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
            x.2.2.2.2.2.2.2 + {Item.coord { id := x.1, phase := CState.collecting, parts := x.2.1, wait := x.2.2.1 }} +
              {Item.msg (Msg.vote false x.2.2.2.1 x.1)})] := by
  maude_certify_comp

theorem twoPC_inv.obligation_30 :
    sound (mayFire recvNo abrtP)
      [Unifier.bind fun (x : ℕ × Oids × Oids × ℕ × ℕ × Oids × Oids) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {Item.coord
                  { id := x.2.2.2.2.1, phase := CState.aborting, parts := x.2.2.2.2.2.1, wait := x.2.2.2.2.2.2 }}),
            x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2,
            {Item.coord { id := x.1, phase := CState.collecting, parts := x.2.1, wait := x.2.2.1 }} +
              {Item.msg (Msg.vote false x.2.2.2.1 x.1)}),
        Unifier.bind fun (x : ℕ × Oids × Oids × ℕ × ℕ × Oids × Oids × Items) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              x.2.2.2.2.2.2.2 +
                {Item.coord
                    { id := x.2.2.2.2.1, phase := CState.aborting, parts := x.2.2.2.2.2.1, wait := x.2.2.2.2.2.2.1 }}),
            x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
            x.2.2.2.2.2.2.2 + {Item.coord { id := x.1, phase := CState.collecting, parts := x.2.1, wait := x.2.2.1 }} +
              {Item.msg (Msg.vote false x.2.2.2.1 x.1)})] := by
  simp only [sound, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  repeat' apply And.intro
  all_goals
    rintro γ ⟨x, rfl⟩
    simp only [unifiedBy, mayFire, recvNo, abrtP]
    try ac_rfl

theorem twoPC_inv.obligation_31 :
    complete (mayFire timeout collP)
      [Unifier.bind fun (x : ℕ × Oids × Oids × ℕ × Oids × Oids) =>
          ((x.1, x.2.1, x.2.2.1,
              {Item.coord { id := x.2.2.2.1, phase := CState.collecting, parts := x.2.2.2.2.1, wait := x.2.2.2.2.2 }}),
            x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2,
            {Item.coord { id := x.1, phase := CState.collecting, parts := x.2.1, wait := x.2.2.1 }}),
        Unifier.bind fun (x : ℕ × Oids × Oids × ℕ × Oids × Oids × Items) =>
          ((x.1, x.2.1, x.2.2.1,
              x.2.2.2.2.2.2 +
                {Item.coord
                    { id := x.2.2.2.1, phase := CState.collecting, parts := x.2.2.2.2.1, wait := x.2.2.2.2.2.1 }}),
            x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
            x.2.2.2.2.2.2 + {Item.coord { id := x.1, phase := CState.collecting, parts := x.2.1, wait := x.2.2.1 }}),
        Unifier.bind fun (x : ℕ × Oids × Oids) => ((x.1, x.2.1, x.2.2, ∅), x.1, x.2.1, x.2.2, ∅),
        Unifier.bind fun (x : Items × ℕ × Oids × Oids) =>
          ((x.2.1, x.2.2.1, x.2.2.2, x.1), x.2.1, x.2.2.1, x.2.2.2, x.1)] := by
  maude_certify_comp

theorem twoPC_inv.obligation_32 :
    sound (mayFire timeout collP)
      [Unifier.bind fun (x : ℕ × Oids × Oids × ℕ × Oids × Oids) =>
          ((x.1, x.2.1, x.2.2.1,
              {Item.coord { id := x.2.2.2.1, phase := CState.collecting, parts := x.2.2.2.2.1, wait := x.2.2.2.2.2 }}),
            x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2,
            {Item.coord { id := x.1, phase := CState.collecting, parts := x.2.1, wait := x.2.2.1 }}),
        Unifier.bind fun (x : ℕ × Oids × Oids × ℕ × Oids × Oids × Items) =>
          ((x.1, x.2.1, x.2.2.1,
              x.2.2.2.2.2.2 +
                {Item.coord
                    { id := x.2.2.2.1, phase := CState.collecting, parts := x.2.2.2.2.1, wait := x.2.2.2.2.2.1 }}),
            x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
            x.2.2.2.2.2.2 + {Item.coord { id := x.1, phase := CState.collecting, parts := x.2.1, wait := x.2.2.1 }}),
        Unifier.bind fun (x : ℕ × Oids × Oids) => ((x.1, x.2.1, x.2.2, ∅), x.1, x.2.1, x.2.2, ∅),
        Unifier.bind fun (x : Items × ℕ × Oids × Oids) =>
          ((x.2.1, x.2.2.1, x.2.2.2, x.1), x.2.1, x.2.2.1, x.2.2.2, x.1)] := by
  simp only [sound, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  repeat' apply And.intro
  all_goals
    rintro γ ⟨x, rfl⟩
    simp only [unifiedBy, mayFire, timeout, collP]
    try ac_rfl

theorem twoPC_inv.obligation_33 :
    complete (mayFire timeout commP)
      [Unifier.bind fun (x : ℕ × Oids × Oids × ℕ × Oids × Oids) =>
          ((x.1, x.2.1, x.2.2.1,
              {Item.coord { id := x.2.2.2.1, phase := CState.committing, parts := x.2.2.2.2.1, wait := x.2.2.2.2.2 }}),
            x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2,
            {Item.coord { id := x.1, phase := CState.collecting, parts := x.2.1, wait := x.2.2.1 }}),
        Unifier.bind fun (x : ℕ × Oids × Oids × ℕ × Oids × Oids × Items) =>
          ((x.1, x.2.1, x.2.2.1,
              x.2.2.2.2.2.2 +
                {Item.coord
                    { id := x.2.2.2.1, phase := CState.committing, parts := x.2.2.2.2.1, wait := x.2.2.2.2.2.1 }}),
            x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
            x.2.2.2.2.2.2 +
              {Item.coord { id := x.1, phase := CState.collecting, parts := x.2.1, wait := x.2.2.1 }})] := by
  maude_certify_comp

theorem twoPC_inv.obligation_34 :
    sound (mayFire timeout commP)
      [Unifier.bind fun (x : ℕ × Oids × Oids × ℕ × Oids × Oids) =>
          ((x.1, x.2.1, x.2.2.1,
              {Item.coord { id := x.2.2.2.1, phase := CState.committing, parts := x.2.2.2.2.1, wait := x.2.2.2.2.2 }}),
            x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2,
            {Item.coord { id := x.1, phase := CState.collecting, parts := x.2.1, wait := x.2.2.1 }}),
        Unifier.bind fun (x : ℕ × Oids × Oids × ℕ × Oids × Oids × Items) =>
          ((x.1, x.2.1, x.2.2.1,
              x.2.2.2.2.2.2 +
                {Item.coord
                    { id := x.2.2.2.1, phase := CState.committing, parts := x.2.2.2.2.1, wait := x.2.2.2.2.2.1 }}),
            x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
            x.2.2.2.2.2.2 +
              {Item.coord { id := x.1, phase := CState.collecting, parts := x.2.1, wait := x.2.2.1 }})] := by
  simp only [sound, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  repeat' apply And.intro
  all_goals
    rintro γ ⟨x, rfl⟩
    simp only [unifiedBy, mayFire, timeout, commP]
    try ac_rfl

theorem twoPC_inv.obligation_35 :
    complete (mayFire timeout abrtP)
      [Unifier.bind fun (x : ℕ × Oids × Oids × ℕ × Oids × Oids) =>
          ((x.1, x.2.1, x.2.2.1,
              {Item.coord { id := x.2.2.2.1, phase := CState.aborting, parts := x.2.2.2.2.1, wait := x.2.2.2.2.2 }}),
            x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2,
            {Item.coord { id := x.1, phase := CState.collecting, parts := x.2.1, wait := x.2.2.1 }}),
        Unifier.bind fun (x : ℕ × Oids × Oids × ℕ × Oids × Oids × Items) =>
          ((x.1, x.2.1, x.2.2.1,
              x.2.2.2.2.2.2 +
                {Item.coord
                    { id := x.2.2.2.1, phase := CState.aborting, parts := x.2.2.2.2.1, wait := x.2.2.2.2.2.1 }}),
            x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
            x.2.2.2.2.2.2 +
              {Item.coord { id := x.1, phase := CState.collecting, parts := x.2.1, wait := x.2.2.1 }})] := by
  maude_certify_comp

theorem twoPC_inv.obligation_36 :
    sound (mayFire timeout abrtP)
      [Unifier.bind fun (x : ℕ × Oids × Oids × ℕ × Oids × Oids) =>
          ((x.1, x.2.1, x.2.2.1,
              {Item.coord { id := x.2.2.2.1, phase := CState.aborting, parts := x.2.2.2.2.1, wait := x.2.2.2.2.2 }}),
            x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2,
            {Item.coord { id := x.1, phase := CState.collecting, parts := x.2.1, wait := x.2.2.1 }}),
        Unifier.bind fun (x : ℕ × Oids × Oids × ℕ × Oids × Oids × Items) =>
          ((x.1, x.2.1, x.2.2.1,
              x.2.2.2.2.2.2 +
                {Item.coord
                    { id := x.2.2.2.1, phase := CState.aborting, parts := x.2.2.2.2.1, wait := x.2.2.2.2.2.1 }}),
            x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
            x.2.2.2.2.2.2 +
              {Item.coord { id := x.1, phase := CState.collecting, parts := x.2.1, wait := x.2.2.1 }})] := by
  simp only [sound, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  repeat' apply And.intro
  all_goals
    rintro γ ⟨x, rfl⟩
    simp only [unifiedBy, mayFire, timeout, abrtP]
    try ac_rfl

theorem twoPC_inv.obligation_37 :
    complete (mayFire deliverCommit collP)
      [Unifier.bind fun (x : ℕ × ℕ × PState × ℕ × Oids × Oids) =>
          ((x.1, x.2.1, ∅, x.2.2.1,
              {Item.coord { id := x.2.2.2.1, phase := CState.collecting, parts := x.2.2.2.2.1, wait := x.2.2.2.2.2 }}),
            x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2,
            {Item.msg (Msg.decision true x.1 {x.2.1})} + {Item.part { id := x.2.1, state := x.2.2.1 }}),
        Unifier.bind fun (x : ℕ × ℕ × Oids × PState × ℕ × Oids × Oids) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {Item.coord
                  { id := x.2.2.2.2.1, phase := CState.collecting, parts := x.2.2.2.2.2.1, wait := x.2.2.2.2.2.2 }}),
            x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2,
            {Item.msg (Msg.decision true x.1 ({x.2.1} + x.2.2.1))} + {Item.part { id := x.2.1, state := x.2.2.2.1 }}),
        Unifier.bind fun (x : ℕ × ℕ × PState × ℕ × Oids × Oids × Items) =>
          ((x.1, x.2.1, ∅, x.2.2.1,
              x.2.2.2.2.2.2 +
                {Item.coord
                    { id := x.2.2.2.1, phase := CState.collecting, parts := x.2.2.2.2.1, wait := x.2.2.2.2.2.1 }}),
            x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
            x.2.2.2.2.2.2 + {Item.msg (Msg.decision true x.1 {x.2.1})} + {Item.part { id := x.2.1, state := x.2.2.1 }}),
        Unifier.bind fun (x : ℕ × ℕ × Oids × PState × ℕ × Oids × Oids × Items) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              x.2.2.2.2.2.2.2 +
                {Item.coord
                    { id := x.2.2.2.2.1, phase := CState.collecting, parts := x.2.2.2.2.2.1,
                      wait := x.2.2.2.2.2.2.1 }}),
            x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
            x.2.2.2.2.2.2.2 + {Item.msg (Msg.decision true x.1 ({x.2.1} + x.2.2.1))} +
              {Item.part { id := x.2.1, state := x.2.2.2.1 }})] := by
  maude_certify_comp

theorem twoPC_inv.obligation_38 :
    sound (mayFire deliverCommit collP)
      [Unifier.bind fun (x : ℕ × ℕ × PState × ℕ × Oids × Oids) =>
          ((x.1, x.2.1, ∅, x.2.2.1,
              {Item.coord { id := x.2.2.2.1, phase := CState.collecting, parts := x.2.2.2.2.1, wait := x.2.2.2.2.2 }}),
            x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2,
            {Item.msg (Msg.decision true x.1 {x.2.1})} + {Item.part { id := x.2.1, state := x.2.2.1 }}),
        Unifier.bind fun (x : ℕ × ℕ × Oids × PState × ℕ × Oids × Oids) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {Item.coord
                  { id := x.2.2.2.2.1, phase := CState.collecting, parts := x.2.2.2.2.2.1, wait := x.2.2.2.2.2.2 }}),
            x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2,
            {Item.msg (Msg.decision true x.1 ({x.2.1} + x.2.2.1))} + {Item.part { id := x.2.1, state := x.2.2.2.1 }}),
        Unifier.bind fun (x : ℕ × ℕ × PState × ℕ × Oids × Oids × Items) =>
          ((x.1, x.2.1, ∅, x.2.2.1,
              x.2.2.2.2.2.2 +
                {Item.coord
                    { id := x.2.2.2.1, phase := CState.collecting, parts := x.2.2.2.2.1, wait := x.2.2.2.2.2.1 }}),
            x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
            x.2.2.2.2.2.2 + {Item.msg (Msg.decision true x.1 {x.2.1})} + {Item.part { id := x.2.1, state := x.2.2.1 }}),
        Unifier.bind fun (x : ℕ × ℕ × Oids × PState × ℕ × Oids × Oids × Items) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              x.2.2.2.2.2.2.2 +
                {Item.coord
                    { id := x.2.2.2.2.1, phase := CState.collecting, parts := x.2.2.2.2.2.1,
                      wait := x.2.2.2.2.2.2.1 }}),
            x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
            x.2.2.2.2.2.2.2 + {Item.msg (Msg.decision true x.1 ({x.2.1} + x.2.2.1))} +
              {Item.part { id := x.2.1, state := x.2.2.2.1 }})] := by
  simp only [sound, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  repeat' apply And.intro
  all_goals
    rintro γ ⟨x, rfl⟩
    simp only [unifiedBy, mayFire, deliverCommit, collP]
    try ac_rfl

theorem twoPC_inv.obligation_39 :
    complete (mayFire deliverCommit commP)
      [Unifier.bind fun (x : ℕ × ℕ × PState × ℕ × Oids × Oids) =>
          ((x.1, x.2.1, ∅, x.2.2.1,
              {Item.coord { id := x.2.2.2.1, phase := CState.committing, parts := x.2.2.2.2.1, wait := x.2.2.2.2.2 }}),
            x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2,
            {Item.msg (Msg.decision true x.1 {x.2.1})} + {Item.part { id := x.2.1, state := x.2.2.1 }}),
        Unifier.bind fun (x : ℕ × ℕ × Oids × PState × ℕ × Oids × Oids) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {Item.coord
                  { id := x.2.2.2.2.1, phase := CState.committing, parts := x.2.2.2.2.2.1, wait := x.2.2.2.2.2.2 }}),
            x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2,
            {Item.msg (Msg.decision true x.1 ({x.2.1} + x.2.2.1))} + {Item.part { id := x.2.1, state := x.2.2.2.1 }}),
        Unifier.bind fun (x : ℕ × ℕ × PState × ℕ × Oids × Oids × Items) =>
          ((x.1, x.2.1, ∅, x.2.2.1,
              x.2.2.2.2.2.2 +
                {Item.coord
                    { id := x.2.2.2.1, phase := CState.committing, parts := x.2.2.2.2.1, wait := x.2.2.2.2.2.1 }}),
            x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
            x.2.2.2.2.2.2 + {Item.msg (Msg.decision true x.1 {x.2.1})} + {Item.part { id := x.2.1, state := x.2.2.1 }}),
        Unifier.bind fun (x : ℕ × ℕ × Oids × PState × ℕ × Oids × Oids × Items) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              x.2.2.2.2.2.2.2 +
                {Item.coord
                    { id := x.2.2.2.2.1, phase := CState.committing, parts := x.2.2.2.2.2.1,
                      wait := x.2.2.2.2.2.2.1 }}),
            x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
            x.2.2.2.2.2.2.2 + {Item.msg (Msg.decision true x.1 ({x.2.1} + x.2.2.1))} +
              {Item.part { id := x.2.1, state := x.2.2.2.1 }})] := by
  maude_certify_comp

theorem twoPC_inv.obligation_40 :
    sound (mayFire deliverCommit commP)
      [Unifier.bind fun (x : ℕ × ℕ × PState × ℕ × Oids × Oids) =>
          ((x.1, x.2.1, ∅, x.2.2.1,
              {Item.coord { id := x.2.2.2.1, phase := CState.committing, parts := x.2.2.2.2.1, wait := x.2.2.2.2.2 }}),
            x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2,
            {Item.msg (Msg.decision true x.1 {x.2.1})} + {Item.part { id := x.2.1, state := x.2.2.1 }}),
        Unifier.bind fun (x : ℕ × ℕ × Oids × PState × ℕ × Oids × Oids) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {Item.coord
                  { id := x.2.2.2.2.1, phase := CState.committing, parts := x.2.2.2.2.2.1, wait := x.2.2.2.2.2.2 }}),
            x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2,
            {Item.msg (Msg.decision true x.1 ({x.2.1} + x.2.2.1))} + {Item.part { id := x.2.1, state := x.2.2.2.1 }}),
        Unifier.bind fun (x : ℕ × ℕ × PState × ℕ × Oids × Oids × Items) =>
          ((x.1, x.2.1, ∅, x.2.2.1,
              x.2.2.2.2.2.2 +
                {Item.coord
                    { id := x.2.2.2.1, phase := CState.committing, parts := x.2.2.2.2.1, wait := x.2.2.2.2.2.1 }}),
            x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
            x.2.2.2.2.2.2 + {Item.msg (Msg.decision true x.1 {x.2.1})} + {Item.part { id := x.2.1, state := x.2.2.1 }}),
        Unifier.bind fun (x : ℕ × ℕ × Oids × PState × ℕ × Oids × Oids × Items) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              x.2.2.2.2.2.2.2 +
                {Item.coord
                    { id := x.2.2.2.2.1, phase := CState.committing, parts := x.2.2.2.2.2.1,
                      wait := x.2.2.2.2.2.2.1 }}),
            x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
            x.2.2.2.2.2.2.2 + {Item.msg (Msg.decision true x.1 ({x.2.1} + x.2.2.1))} +
              {Item.part { id := x.2.1, state := x.2.2.2.1 }})] := by
  simp only [sound, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  repeat' apply And.intro
  all_goals
    rintro γ ⟨x, rfl⟩
    simp only [unifiedBy, mayFire, deliverCommit, commP]
    try ac_rfl

theorem twoPC_inv.obligation_41 :
    complete (mayFire deliverCommit abrtP)
      [Unifier.bind fun (x : ℕ × ℕ × PState × ℕ × Oids × Oids) =>
          ((x.1, x.2.1, ∅, x.2.2.1,
              {Item.coord { id := x.2.2.2.1, phase := CState.aborting, parts := x.2.2.2.2.1, wait := x.2.2.2.2.2 }}),
            x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2,
            {Item.msg (Msg.decision true x.1 {x.2.1})} + {Item.part { id := x.2.1, state := x.2.2.1 }}),
        Unifier.bind fun (x : ℕ × ℕ × Oids × PState × ℕ × Oids × Oids) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {Item.coord
                  { id := x.2.2.2.2.1, phase := CState.aborting, parts := x.2.2.2.2.2.1, wait := x.2.2.2.2.2.2 }}),
            x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2,
            {Item.msg (Msg.decision true x.1 ({x.2.1} + x.2.2.1))} + {Item.part { id := x.2.1, state := x.2.2.2.1 }}),
        Unifier.bind fun (x : ℕ × ℕ × PState × ℕ × Oids × Oids × Items) =>
          ((x.1, x.2.1, ∅, x.2.2.1,
              x.2.2.2.2.2.2 +
                {Item.coord
                    { id := x.2.2.2.1, phase := CState.aborting, parts := x.2.2.2.2.1, wait := x.2.2.2.2.2.1 }}),
            x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
            x.2.2.2.2.2.2 + {Item.msg (Msg.decision true x.1 {x.2.1})} + {Item.part { id := x.2.1, state := x.2.2.1 }}),
        Unifier.bind fun (x : ℕ × ℕ × Oids × PState × ℕ × Oids × Oids × Items) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              x.2.2.2.2.2.2.2 +
                {Item.coord
                    { id := x.2.2.2.2.1, phase := CState.aborting, parts := x.2.2.2.2.2.1, wait := x.2.2.2.2.2.2.1 }}),
            x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
            x.2.2.2.2.2.2.2 + {Item.msg (Msg.decision true x.1 ({x.2.1} + x.2.2.1))} +
              {Item.part { id := x.2.1, state := x.2.2.2.1 }})] := by
  maude_certify_comp

theorem twoPC_inv.obligation_42 :
    sound (mayFire deliverCommit abrtP)
      [Unifier.bind fun (x : ℕ × ℕ × PState × ℕ × Oids × Oids) =>
          ((x.1, x.2.1, ∅, x.2.2.1,
              {Item.coord { id := x.2.2.2.1, phase := CState.aborting, parts := x.2.2.2.2.1, wait := x.2.2.2.2.2 }}),
            x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2,
            {Item.msg (Msg.decision true x.1 {x.2.1})} + {Item.part { id := x.2.1, state := x.2.2.1 }}),
        Unifier.bind fun (x : ℕ × ℕ × Oids × PState × ℕ × Oids × Oids) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {Item.coord
                  { id := x.2.2.2.2.1, phase := CState.aborting, parts := x.2.2.2.2.2.1, wait := x.2.2.2.2.2.2 }}),
            x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2,
            {Item.msg (Msg.decision true x.1 ({x.2.1} + x.2.2.1))} + {Item.part { id := x.2.1, state := x.2.2.2.1 }}),
        Unifier.bind fun (x : ℕ × ℕ × PState × ℕ × Oids × Oids × Items) =>
          ((x.1, x.2.1, ∅, x.2.2.1,
              x.2.2.2.2.2.2 +
                {Item.coord
                    { id := x.2.2.2.1, phase := CState.aborting, parts := x.2.2.2.2.1, wait := x.2.2.2.2.2.1 }}),
            x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
            x.2.2.2.2.2.2 + {Item.msg (Msg.decision true x.1 {x.2.1})} + {Item.part { id := x.2.1, state := x.2.2.1 }}),
        Unifier.bind fun (x : ℕ × ℕ × Oids × PState × ℕ × Oids × Oids × Items) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              x.2.2.2.2.2.2.2 +
                {Item.coord
                    { id := x.2.2.2.2.1, phase := CState.aborting, parts := x.2.2.2.2.2.1, wait := x.2.2.2.2.2.2.1 }}),
            x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
            x.2.2.2.2.2.2.2 + {Item.msg (Msg.decision true x.1 ({x.2.1} + x.2.2.1))} +
              {Item.part { id := x.2.1, state := x.2.2.2.1 }})] := by
  simp only [sound, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  repeat' apply And.intro
  all_goals
    rintro γ ⟨x, rfl⟩
    simp only [unifiedBy, mayFire, deliverCommit, abrtP]
    try ac_rfl

theorem twoPC_inv.obligation_43 :
    complete (mayFire deliverAbort collP)
      [Unifier.bind fun (x : ℕ × ℕ × PState × ℕ × Oids × Oids) =>
          ((x.1, x.2.1, ∅, x.2.2.1,
              {Item.coord { id := x.2.2.2.1, phase := CState.collecting, parts := x.2.2.2.2.1, wait := x.2.2.2.2.2 }}),
            x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2,
            {Item.msg (Msg.decision false x.1 {x.2.1})} + {Item.part { id := x.2.1, state := x.2.2.1 }}),
        Unifier.bind fun (x : ℕ × ℕ × Oids × PState × ℕ × Oids × Oids) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {Item.coord
                  { id := x.2.2.2.2.1, phase := CState.collecting, parts := x.2.2.2.2.2.1, wait := x.2.2.2.2.2.2 }}),
            x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2,
            {Item.msg (Msg.decision false x.1 ({x.2.1} + x.2.2.1))} + {Item.part { id := x.2.1, state := x.2.2.2.1 }}),
        Unifier.bind fun (x : ℕ × ℕ × PState × ℕ × Oids × Oids × Items) =>
          ((x.1, x.2.1, ∅, x.2.2.1,
              x.2.2.2.2.2.2 +
                {Item.coord
                    { id := x.2.2.2.1, phase := CState.collecting, parts := x.2.2.2.2.1, wait := x.2.2.2.2.2.1 }}),
            x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
            x.2.2.2.2.2.2 + {Item.msg (Msg.decision false x.1 {x.2.1})} +
              {Item.part { id := x.2.1, state := x.2.2.1 }}),
        Unifier.bind fun (x : ℕ × ℕ × Oids × PState × ℕ × Oids × Oids × Items) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              x.2.2.2.2.2.2.2 +
                {Item.coord
                    { id := x.2.2.2.2.1, phase := CState.collecting, parts := x.2.2.2.2.2.1,
                      wait := x.2.2.2.2.2.2.1 }}),
            x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
            x.2.2.2.2.2.2.2 + {Item.msg (Msg.decision false x.1 ({x.2.1} + x.2.2.1))} +
              {Item.part { id := x.2.1, state := x.2.2.2.1 }})] := by
  maude_certify_comp

theorem twoPC_inv.obligation_44 :
    sound (mayFire deliverAbort collP)
      [Unifier.bind fun (x : ℕ × ℕ × PState × ℕ × Oids × Oids) =>
          ((x.1, x.2.1, ∅, x.2.2.1,
              {Item.coord { id := x.2.2.2.1, phase := CState.collecting, parts := x.2.2.2.2.1, wait := x.2.2.2.2.2 }}),
            x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2,
            {Item.msg (Msg.decision false x.1 {x.2.1})} + {Item.part { id := x.2.1, state := x.2.2.1 }}),
        Unifier.bind fun (x : ℕ × ℕ × Oids × PState × ℕ × Oids × Oids) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {Item.coord
                  { id := x.2.2.2.2.1, phase := CState.collecting, parts := x.2.2.2.2.2.1, wait := x.2.2.2.2.2.2 }}),
            x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2,
            {Item.msg (Msg.decision false x.1 ({x.2.1} + x.2.2.1))} + {Item.part { id := x.2.1, state := x.2.2.2.1 }}),
        Unifier.bind fun (x : ℕ × ℕ × PState × ℕ × Oids × Oids × Items) =>
          ((x.1, x.2.1, ∅, x.2.2.1,
              x.2.2.2.2.2.2 +
                {Item.coord
                    { id := x.2.2.2.1, phase := CState.collecting, parts := x.2.2.2.2.1, wait := x.2.2.2.2.2.1 }}),
            x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
            x.2.2.2.2.2.2 + {Item.msg (Msg.decision false x.1 {x.2.1})} +
              {Item.part { id := x.2.1, state := x.2.2.1 }}),
        Unifier.bind fun (x : ℕ × ℕ × Oids × PState × ℕ × Oids × Oids × Items) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              x.2.2.2.2.2.2.2 +
                {Item.coord
                    { id := x.2.2.2.2.1, phase := CState.collecting, parts := x.2.2.2.2.2.1,
                      wait := x.2.2.2.2.2.2.1 }}),
            x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
            x.2.2.2.2.2.2.2 + {Item.msg (Msg.decision false x.1 ({x.2.1} + x.2.2.1))} +
              {Item.part { id := x.2.1, state := x.2.2.2.1 }})] := by
  simp only [sound, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  repeat' apply And.intro
  all_goals
    rintro γ ⟨x, rfl⟩
    simp only [unifiedBy, mayFire, deliverAbort, collP]
    try ac_rfl

theorem twoPC_inv.obligation_45 :
    complete (mayFire deliverAbort commP)
      [Unifier.bind fun (x : ℕ × ℕ × PState × ℕ × Oids × Oids) =>
          ((x.1, x.2.1, ∅, x.2.2.1,
              {Item.coord { id := x.2.2.2.1, phase := CState.committing, parts := x.2.2.2.2.1, wait := x.2.2.2.2.2 }}),
            x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2,
            {Item.msg (Msg.decision false x.1 {x.2.1})} + {Item.part { id := x.2.1, state := x.2.2.1 }}),
        Unifier.bind fun (x : ℕ × ℕ × Oids × PState × ℕ × Oids × Oids) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {Item.coord
                  { id := x.2.2.2.2.1, phase := CState.committing, parts := x.2.2.2.2.2.1, wait := x.2.2.2.2.2.2 }}),
            x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2,
            {Item.msg (Msg.decision false x.1 ({x.2.1} + x.2.2.1))} + {Item.part { id := x.2.1, state := x.2.2.2.1 }}),
        Unifier.bind fun (x : ℕ × ℕ × PState × ℕ × Oids × Oids × Items) =>
          ((x.1, x.2.1, ∅, x.2.2.1,
              x.2.2.2.2.2.2 +
                {Item.coord
                    { id := x.2.2.2.1, phase := CState.committing, parts := x.2.2.2.2.1, wait := x.2.2.2.2.2.1 }}),
            x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
            x.2.2.2.2.2.2 + {Item.msg (Msg.decision false x.1 {x.2.1})} +
              {Item.part { id := x.2.1, state := x.2.2.1 }}),
        Unifier.bind fun (x : ℕ × ℕ × Oids × PState × ℕ × Oids × Oids × Items) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              x.2.2.2.2.2.2.2 +
                {Item.coord
                    { id := x.2.2.2.2.1, phase := CState.committing, parts := x.2.2.2.2.2.1,
                      wait := x.2.2.2.2.2.2.1 }}),
            x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
            x.2.2.2.2.2.2.2 + {Item.msg (Msg.decision false x.1 ({x.2.1} + x.2.2.1))} +
              {Item.part { id := x.2.1, state := x.2.2.2.1 }})] := by
  maude_certify_comp

theorem twoPC_inv.obligation_46 :
    sound (mayFire deliverAbort commP)
      [Unifier.bind fun (x : ℕ × ℕ × PState × ℕ × Oids × Oids) =>
          ((x.1, x.2.1, ∅, x.2.2.1,
              {Item.coord { id := x.2.2.2.1, phase := CState.committing, parts := x.2.2.2.2.1, wait := x.2.2.2.2.2 }}),
            x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2,
            {Item.msg (Msg.decision false x.1 {x.2.1})} + {Item.part { id := x.2.1, state := x.2.2.1 }}),
        Unifier.bind fun (x : ℕ × ℕ × Oids × PState × ℕ × Oids × Oids) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {Item.coord
                  { id := x.2.2.2.2.1, phase := CState.committing, parts := x.2.2.2.2.2.1, wait := x.2.2.2.2.2.2 }}),
            x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2,
            {Item.msg (Msg.decision false x.1 ({x.2.1} + x.2.2.1))} + {Item.part { id := x.2.1, state := x.2.2.2.1 }}),
        Unifier.bind fun (x : ℕ × ℕ × PState × ℕ × Oids × Oids × Items) =>
          ((x.1, x.2.1, ∅, x.2.2.1,
              x.2.2.2.2.2.2 +
                {Item.coord
                    { id := x.2.2.2.1, phase := CState.committing, parts := x.2.2.2.2.1, wait := x.2.2.2.2.2.1 }}),
            x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
            x.2.2.2.2.2.2 + {Item.msg (Msg.decision false x.1 {x.2.1})} +
              {Item.part { id := x.2.1, state := x.2.2.1 }}),
        Unifier.bind fun (x : ℕ × ℕ × Oids × PState × ℕ × Oids × Oids × Items) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              x.2.2.2.2.2.2.2 +
                {Item.coord
                    { id := x.2.2.2.2.1, phase := CState.committing, parts := x.2.2.2.2.2.1,
                      wait := x.2.2.2.2.2.2.1 }}),
            x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
            x.2.2.2.2.2.2.2 + {Item.msg (Msg.decision false x.1 ({x.2.1} + x.2.2.1))} +
              {Item.part { id := x.2.1, state := x.2.2.2.1 }})] := by
  simp only [sound, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  repeat' apply And.intro
  all_goals
    rintro γ ⟨x, rfl⟩
    simp only [unifiedBy, mayFire, deliverAbort, commP]
    try ac_rfl

theorem twoPC_inv.obligation_47 :
    complete (mayFire deliverAbort abrtP)
      [Unifier.bind fun (x : ℕ × ℕ × PState × ℕ × Oids × Oids) =>
          ((x.1, x.2.1, ∅, x.2.2.1,
              {Item.coord { id := x.2.2.2.1, phase := CState.aborting, parts := x.2.2.2.2.1, wait := x.2.2.2.2.2 }}),
            x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2,
            {Item.msg (Msg.decision false x.1 {x.2.1})} + {Item.part { id := x.2.1, state := x.2.2.1 }}),
        Unifier.bind fun (x : ℕ × ℕ × Oids × PState × ℕ × Oids × Oids) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {Item.coord
                  { id := x.2.2.2.2.1, phase := CState.aborting, parts := x.2.2.2.2.2.1, wait := x.2.2.2.2.2.2 }}),
            x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2,
            {Item.msg (Msg.decision false x.1 ({x.2.1} + x.2.2.1))} + {Item.part { id := x.2.1, state := x.2.2.2.1 }}),
        Unifier.bind fun (x : ℕ × ℕ × PState × ℕ × Oids × Oids × Items) =>
          ((x.1, x.2.1, ∅, x.2.2.1,
              x.2.2.2.2.2.2 +
                {Item.coord
                    { id := x.2.2.2.1, phase := CState.aborting, parts := x.2.2.2.2.1, wait := x.2.2.2.2.2.1 }}),
            x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
            x.2.2.2.2.2.2 + {Item.msg (Msg.decision false x.1 {x.2.1})} +
              {Item.part { id := x.2.1, state := x.2.2.1 }}),
        Unifier.bind fun (x : ℕ × ℕ × Oids × PState × ℕ × Oids × Oids × Items) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              x.2.2.2.2.2.2.2 +
                {Item.coord
                    { id := x.2.2.2.2.1, phase := CState.aborting, parts := x.2.2.2.2.2.1, wait := x.2.2.2.2.2.2.1 }}),
            x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
            x.2.2.2.2.2.2.2 + {Item.msg (Msg.decision false x.1 ({x.2.1} + x.2.2.1))} +
              {Item.part { id := x.2.1, state := x.2.2.2.1 }})] := by
  maude_certify_comp

theorem twoPC_inv.obligation_48 :
    sound (mayFire deliverAbort abrtP)
      [Unifier.bind fun (x : ℕ × ℕ × PState × ℕ × Oids × Oids) =>
          ((x.1, x.2.1, ∅, x.2.2.1,
              {Item.coord { id := x.2.2.2.1, phase := CState.aborting, parts := x.2.2.2.2.1, wait := x.2.2.2.2.2 }}),
            x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2,
            {Item.msg (Msg.decision false x.1 {x.2.1})} + {Item.part { id := x.2.1, state := x.2.2.1 }}),
        Unifier.bind fun (x : ℕ × ℕ × Oids × PState × ℕ × Oids × Oids) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {Item.coord
                  { id := x.2.2.2.2.1, phase := CState.aborting, parts := x.2.2.2.2.2.1, wait := x.2.2.2.2.2.2 }}),
            x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2,
            {Item.msg (Msg.decision false x.1 ({x.2.1} + x.2.2.1))} + {Item.part { id := x.2.1, state := x.2.2.2.1 }}),
        Unifier.bind fun (x : ℕ × ℕ × PState × ℕ × Oids × Oids × Items) =>
          ((x.1, x.2.1, ∅, x.2.2.1,
              x.2.2.2.2.2.2 +
                {Item.coord
                    { id := x.2.2.2.1, phase := CState.aborting, parts := x.2.2.2.2.1, wait := x.2.2.2.2.2.1 }}),
            x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
            x.2.2.2.2.2.2 + {Item.msg (Msg.decision false x.1 {x.2.1})} +
              {Item.part { id := x.2.1, state := x.2.2.1 }}),
        Unifier.bind fun (x : ℕ × ℕ × Oids × PState × ℕ × Oids × Oids × Items) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              x.2.2.2.2.2.2.2 +
                {Item.coord
                    { id := x.2.2.2.2.1, phase := CState.aborting, parts := x.2.2.2.2.2.1, wait := x.2.2.2.2.2.2.1 }}),
            x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
            x.2.2.2.2.2.2.2 + {Item.msg (Msg.decision false x.1 ({x.2.1} + x.2.2.1))} +
              {Item.part { id := x.2.1, state := x.2.2.2.1 }})] := by
  simp only [sound, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  repeat' apply And.intro
  all_goals
    rintro γ ⟨x, rfl⟩
    simp only [unifiedBy, mayFire, deliverAbort, abrtP]
    try ac_rfl

theorem twoPC_inv.obligation_49 :
    complete (mayFire lossVote collP)
      [Unifier.bind fun (x : Bool × ℕ × ℕ × ℕ × Oids × Oids) =>
          ((x.1, x.2.1, x.2.2.1,
              {Item.coord { id := x.2.2.2.1, phase := CState.collecting, parts := x.2.2.2.2.1, wait := x.2.2.2.2.2 }}),
            x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2, {Item.msg (Msg.vote x.1 x.2.1 x.2.2.1)}),
        Unifier.bind fun (x : Bool × ℕ × ℕ × ℕ × Oids × Oids × Items) =>
          ((x.1, x.2.1, x.2.2.1,
              x.2.2.2.2.2.2 +
                {Item.coord
                    { id := x.2.2.2.1, phase := CState.collecting, parts := x.2.2.2.2.1, wait := x.2.2.2.2.2.1 }}),
            x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2 + {Item.msg (Msg.vote x.1 x.2.1 x.2.2.1)})] := by
  maude_certify_comp

theorem twoPC_inv.obligation_50 :
    sound (mayFire lossVote collP)
      [Unifier.bind fun (x : Bool × ℕ × ℕ × ℕ × Oids × Oids) =>
          ((x.1, x.2.1, x.2.2.1,
              {Item.coord { id := x.2.2.2.1, phase := CState.collecting, parts := x.2.2.2.2.1, wait := x.2.2.2.2.2 }}),
            x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2, {Item.msg (Msg.vote x.1 x.2.1 x.2.2.1)}),
        Unifier.bind fun (x : Bool × ℕ × ℕ × ℕ × Oids × Oids × Items) =>
          ((x.1, x.2.1, x.2.2.1,
              x.2.2.2.2.2.2 +
                {Item.coord
                    { id := x.2.2.2.1, phase := CState.collecting, parts := x.2.2.2.2.1, wait := x.2.2.2.2.2.1 }}),
            x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2 + {Item.msg (Msg.vote x.1 x.2.1 x.2.2.1)})] := by
  simp only [sound, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  repeat' apply And.intro
  all_goals
    rintro γ ⟨x, rfl⟩
    simp only [unifiedBy, mayFire, lossVote, collP]
    try ac_rfl

theorem twoPC_inv.obligation_51 :
    complete (mayFire lossVote commP)
      [Unifier.bind fun (x : Bool × ℕ × ℕ × ℕ × Oids × Oids) =>
          ((x.1, x.2.1, x.2.2.1,
              {Item.coord { id := x.2.2.2.1, phase := CState.committing, parts := x.2.2.2.2.1, wait := x.2.2.2.2.2 }}),
            x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2, {Item.msg (Msg.vote x.1 x.2.1 x.2.2.1)}),
        Unifier.bind fun (x : Bool × ℕ × ℕ × ℕ × Oids × Oids × Items) =>
          ((x.1, x.2.1, x.2.2.1,
              x.2.2.2.2.2.2 +
                {Item.coord
                    { id := x.2.2.2.1, phase := CState.committing, parts := x.2.2.2.2.1, wait := x.2.2.2.2.2.1 }}),
            x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2 + {Item.msg (Msg.vote x.1 x.2.1 x.2.2.1)})] := by
  maude_certify_comp

theorem twoPC_inv.obligation_52 :
    sound (mayFire lossVote commP)
      [Unifier.bind fun (x : Bool × ℕ × ℕ × ℕ × Oids × Oids) =>
          ((x.1, x.2.1, x.2.2.1,
              {Item.coord { id := x.2.2.2.1, phase := CState.committing, parts := x.2.2.2.2.1, wait := x.2.2.2.2.2 }}),
            x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2, {Item.msg (Msg.vote x.1 x.2.1 x.2.2.1)}),
        Unifier.bind fun (x : Bool × ℕ × ℕ × ℕ × Oids × Oids × Items) =>
          ((x.1, x.2.1, x.2.2.1,
              x.2.2.2.2.2.2 +
                {Item.coord
                    { id := x.2.2.2.1, phase := CState.committing, parts := x.2.2.2.2.1, wait := x.2.2.2.2.2.1 }}),
            x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2 + {Item.msg (Msg.vote x.1 x.2.1 x.2.2.1)})] := by
  simp only [sound, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  repeat' apply And.intro
  all_goals
    rintro γ ⟨x, rfl⟩
    simp only [unifiedBy, mayFire, lossVote, commP]
    try ac_rfl

theorem twoPC_inv.obligation_53 :
    complete (mayFire lossVote abrtP)
      [Unifier.bind fun (x : Bool × ℕ × ℕ × ℕ × Oids × Oids) =>
          ((x.1, x.2.1, x.2.2.1,
              {Item.coord { id := x.2.2.2.1, phase := CState.aborting, parts := x.2.2.2.2.1, wait := x.2.2.2.2.2 }}),
            x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2, {Item.msg (Msg.vote x.1 x.2.1 x.2.2.1)}),
        Unifier.bind fun (x : Bool × ℕ × ℕ × ℕ × Oids × Oids × Items) =>
          ((x.1, x.2.1, x.2.2.1,
              x.2.2.2.2.2.2 +
                {Item.coord
                    { id := x.2.2.2.1, phase := CState.aborting, parts := x.2.2.2.2.1, wait := x.2.2.2.2.2.1 }}),
            x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2 + {Item.msg (Msg.vote x.1 x.2.1 x.2.2.1)})] := by
  maude_certify_comp

theorem twoPC_inv.obligation_54 :
    sound (mayFire lossVote abrtP)
      [Unifier.bind fun (x : Bool × ℕ × ℕ × ℕ × Oids × Oids) =>
          ((x.1, x.2.1, x.2.2.1,
              {Item.coord { id := x.2.2.2.1, phase := CState.aborting, parts := x.2.2.2.2.1, wait := x.2.2.2.2.2 }}),
            x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2, {Item.msg (Msg.vote x.1 x.2.1 x.2.2.1)}),
        Unifier.bind fun (x : Bool × ℕ × ℕ × ℕ × Oids × Oids × Items) =>
          ((x.1, x.2.1, x.2.2.1,
              x.2.2.2.2.2.2 +
                {Item.coord
                    { id := x.2.2.2.1, phase := CState.aborting, parts := x.2.2.2.2.1, wait := x.2.2.2.2.2.1 }}),
            x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2 + {Item.msg (Msg.vote x.1 x.2.1 x.2.2.1)})] := by
  simp only [sound, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  repeat' apply And.intro
  all_goals
    rintro γ ⟨x, rfl⟩
    simp only [unifiedBy, mayFire, lossVote, abrtP]
    try ac_rfl

end TwoPC
