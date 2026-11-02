import examples.German.proof
import conPanna.Unification.Tactics.udfCertify

/-!
German's protocol: the certification obligations of the per-rule invariance proofs (`*_inv`), as `#obligations` prints them.
Completeness: the certificate narrowing stored for the claim, replayed through the proved
rules (`udf_certify`). Soundness: each unifier, instantiated, solves the problem modulo ACU.
-/

set_option linter.style.longLine false
set_option linter.unusedSimpArgs false

open Expresso Unification Narrowing

theorem German.sendReqS_inv.obligation_1 :
    Unification.complete (Narrowing.mayFire German.sendReqS German.freeP)
      [Unification.Unifier.bind
          fun (x : ℕ × German.Gnt × German.Ack × German.Cmd × ℕ × German.Oids × German.Oids × German.Items) =>
          ((x.1, x.2.1, x.2.2.1,
              {German.Item.dir
                    { cmd := x.2.2.2.1, ptr := x.2.2.2.2.1, exGntd := false, shr := x.2.2.2.2.2.1,
                      inv := x.2.2.2.2.2.2.1 }} +
                x.2.2.2.2.2.2.2),
            x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
            {German.Item.cache
                  { id := x.1, state := German.CacheState.invalid, ch1 := German.Req.noReq, ch2 := x.2.1,
                    ch3 := x.2.2.1 }} +
              x.2.2.2.2.2.2.2)] := by
  udf_certify

theorem German.sendReqS_inv.obligation_2 :
    Unification.sound (Narrowing.mayFire German.sendReqS German.freeP)
      [Unification.Unifier.bind
          fun (x : ℕ × German.Gnt × German.Ack × German.Cmd × ℕ × German.Oids × German.Oids × German.Items) =>
          ((x.1, x.2.1, x.2.2.1,
              {German.Item.dir
                    { cmd := x.2.2.2.1, ptr := x.2.2.2.2.1, exGntd := false, shr := x.2.2.2.2.2.1,
                      inv := x.2.2.2.2.2.2.1 }} +
                x.2.2.2.2.2.2.2),
            x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
            {German.Item.cache
                  { id := x.1, state := German.CacheState.invalid, ch1 := German.Req.noReq, ch2 := x.2.1,
                    ch3 := x.2.2.1 }} +
              x.2.2.2.2.2.2.2)] := by
  -- each unifier, instantiated, solves the problem
  simp only [sound, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  repeat' apply And.intro
  all_goals
    rintro γ ⟨x, rfl⟩
    simp only [unifiedBy, Narrowing.mayFire, German.sendReqS, German.freeP]
  all_goals first
    | rfl
    | ac_rfl
    | simp only [ACU.plus_unit, ACU.unit_plus, ACU.plus_comm, ACU.plus_left_comm, ACU.plus_assoc]

theorem German.sendReqS_inv.obligation_3 :
    Unification.complete (Narrowing.mayFire German.sendReqS German.ownE)
      [Unification.Unifier.bind
          fun (x : ℕ × German.Gnt × German.Ack × ℕ × German.Req × German.Cmd × ℕ × German.Oids × German.Items) =>
          ((x.1, x.2.1, x.2.2.1,
              {German.Item.cache
                      { id := x.2.2.2.1, state := German.CacheState.exclusive, ch1 := x.2.2.2.2.1,
                        ch2 := German.Gnt.noGnt, ch3 := German.Ack.noAck }} +
                  {German.Item.dir
                      { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.1},
                        inv := x.2.2.2.2.2.2.2.1 }} +
                x.2.2.2.2.2.2.2.2),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
            {German.Item.cache
                  { id := x.1, state := German.CacheState.invalid, ch1 := German.Req.noReq, ch2 := x.2.1,
                    ch3 := x.2.2.1 }} +
              x.2.2.2.2.2.2.2.2)] := by
  udf_certify

theorem German.sendReqS_inv.obligation_4 :
    Unification.sound (Narrowing.mayFire German.sendReqS German.ownE)
      [Unification.Unifier.bind
          fun (x : ℕ × German.Gnt × German.Ack × ℕ × German.Req × German.Cmd × ℕ × German.Oids × German.Items) =>
          ((x.1, x.2.1, x.2.2.1,
              {German.Item.cache
                      { id := x.2.2.2.1, state := German.CacheState.exclusive, ch1 := x.2.2.2.2.1,
                        ch2 := German.Gnt.noGnt, ch3 := German.Ack.noAck }} +
                  {German.Item.dir
                      { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.1},
                        inv := x.2.2.2.2.2.2.2.1 }} +
                x.2.2.2.2.2.2.2.2),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
            {German.Item.cache
                  { id := x.1, state := German.CacheState.invalid, ch1 := German.Req.noReq, ch2 := x.2.1,
                    ch3 := x.2.2.1 }} +
              x.2.2.2.2.2.2.2.2)] := by
  -- each unifier, instantiated, solves the problem
  simp only [sound, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  repeat' apply And.intro
  all_goals
    rintro γ ⟨x, rfl⟩
    simp only [unifiedBy, Narrowing.mayFire, German.sendReqS, German.ownE]
  all_goals first
    | rfl
    | ac_rfl
    | simp only [ACU.plus_unit, ACU.unit_plus, ACU.plus_comm, ACU.plus_left_comm, ACU.plus_assoc]

theorem German.sendReqS_inv.obligation_5 :
    Unification.complete (Narrowing.mayFire German.sendReqS German.ownG)
      [Unification.Unifier.bind
          fun (x : ℕ × German.Gnt × German.Ack × ℕ × German.Req × German.Cmd × ℕ × German.Oids × German.Items) =>
          ((x.1, x.2.1, x.2.2.1,
              {German.Item.cache
                      { id := x.2.2.2.1, state := German.CacheState.invalid, ch1 := x.2.2.2.2.1, ch2 := German.Gnt.gntE,
                        ch3 := German.Ack.noAck }} +
                  {German.Item.dir
                      { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.1},
                        inv := x.2.2.2.2.2.2.2.1 }} +
                x.2.2.2.2.2.2.2.2),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
            {German.Item.cache
                  { id := x.1, state := German.CacheState.invalid, ch1 := German.Req.noReq, ch2 := x.2.1,
                    ch3 := x.2.2.1 }} +
              x.2.2.2.2.2.2.2.2),
        Unification.Unifier.bind fun (x : German.Items × ℕ × German.Cmd × ℕ × German.Oids) =>
          ((x.2.1, German.Gnt.gntE, German.Ack.noAck,
              {German.Item.dir { cmd := x.2.2.1, ptr := x.2.2.2.1, exGntd := true, shr := {x.2.1}, inv := x.2.2.2.2 }} +
                x.1),
            x.2.2.1, x.2.2.2.1, x.2.2.2.2, x.2.1, German.Req.noReq, x.1)] := by
  udf_certify

theorem German.sendReqS_inv.obligation_6 :
    Unification.sound (Narrowing.mayFire German.sendReqS German.ownG)
      [Unification.Unifier.bind
          fun (x : ℕ × German.Gnt × German.Ack × ℕ × German.Req × German.Cmd × ℕ × German.Oids × German.Items) =>
          ((x.1, x.2.1, x.2.2.1,
              {German.Item.cache
                      { id := x.2.2.2.1, state := German.CacheState.invalid, ch1 := x.2.2.2.2.1, ch2 := German.Gnt.gntE,
                        ch3 := German.Ack.noAck }} +
                  {German.Item.dir
                      { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.1},
                        inv := x.2.2.2.2.2.2.2.1 }} +
                x.2.2.2.2.2.2.2.2),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
            {German.Item.cache
                  { id := x.1, state := German.CacheState.invalid, ch1 := German.Req.noReq, ch2 := x.2.1,
                    ch3 := x.2.2.1 }} +
              x.2.2.2.2.2.2.2.2),
        Unification.Unifier.bind fun (x : German.Items × ℕ × German.Cmd × ℕ × German.Oids) =>
          ((x.2.1, German.Gnt.gntE, German.Ack.noAck,
              {German.Item.dir { cmd := x.2.2.1, ptr := x.2.2.2.1, exGntd := true, shr := {x.2.1}, inv := x.2.2.2.2 }} +
                x.1),
            x.2.2.1, x.2.2.2.1, x.2.2.2.2, x.2.1, German.Req.noReq, x.1)] := by
  -- each unifier, instantiated, solves the problem
  simp only [sound, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  repeat' apply And.intro
  all_goals
    rintro γ ⟨x, rfl⟩
    simp only [unifiedBy, Narrowing.mayFire, German.sendReqS, German.ownG]
  all_goals first
    | rfl
    | ac_rfl
    | simp only [ACU.plus_unit, ACU.unit_plus, ACU.plus_comm, ACU.plus_left_comm, ACU.plus_assoc]

theorem German.sendReqS_inv.obligation_7 :
    Unification.complete (Narrowing.mayFire German.sendReqS German.ownInv)
      [Unification.Unifier.bind
          fun (x : ℕ × German.Gnt × German.Ack × ℕ × German.Req × German.Cmd × ℕ × German.Items) =>
          ((x.1, x.2.1, x.2.2.1,
              {German.Item.cache
                      { id := x.2.2.2.1, state := German.CacheState.exclusive, ch1 := x.2.2.2.2.1,
                        ch2 := German.Gnt.inv, ch3 := German.Ack.noAck }} +
                  {German.Item.dir
                      { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.1}, inv := ∅ }} +
                x.2.2.2.2.2.2.2),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
            {German.Item.cache
                  { id := x.1, state := German.CacheState.invalid, ch1 := German.Req.noReq, ch2 := x.2.1,
                    ch3 := x.2.2.1 }} +
              x.2.2.2.2.2.2.2)] := by
  udf_certify

theorem German.sendReqS_inv.obligation_8 :
    Unification.sound (Narrowing.mayFire German.sendReqS German.ownInv)
      [Unification.Unifier.bind
          fun (x : ℕ × German.Gnt × German.Ack × ℕ × German.Req × German.Cmd × ℕ × German.Items) =>
          ((x.1, x.2.1, x.2.2.1,
              {German.Item.cache
                      { id := x.2.2.2.1, state := German.CacheState.exclusive, ch1 := x.2.2.2.2.1,
                        ch2 := German.Gnt.inv, ch3 := German.Ack.noAck }} +
                  {German.Item.dir
                      { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.1}, inv := ∅ }} +
                x.2.2.2.2.2.2.2),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
            {German.Item.cache
                  { id := x.1, state := German.CacheState.invalid, ch1 := German.Req.noReq, ch2 := x.2.1,
                    ch3 := x.2.2.1 }} +
              x.2.2.2.2.2.2.2)] := by
  -- each unifier, instantiated, solves the problem
  simp only [sound, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  repeat' apply And.intro
  all_goals
    rintro γ ⟨x, rfl⟩
    simp only [unifiedBy, Narrowing.mayFire, German.sendReqS, German.ownInv]
  all_goals first
    | rfl
    | ac_rfl
    | simp only [ACU.plus_unit, ACU.unit_plus, ACU.plus_comm, ACU.plus_left_comm, ACU.plus_assoc]

theorem German.sendReqS_inv.obligation_9 :
    Unification.complete (Narrowing.mayFire German.sendReqS German.ownAck)
      [Unification.Unifier.bind
          fun (x : ℕ × German.Gnt × German.Ack × ℕ × German.Req × German.Cmd × ℕ × German.Items) =>
          ((x.1, x.2.1, x.2.2.1,
              {German.Item.cache
                      { id := x.2.2.2.1, state := German.CacheState.invalid, ch1 := x.2.2.2.2.1,
                        ch2 := German.Gnt.noGnt, ch3 := German.Ack.invAck }} +
                  {German.Item.dir
                      { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.1}, inv := ∅ }} +
                x.2.2.2.2.2.2.2),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
            {German.Item.cache
                  { id := x.1, state := German.CacheState.invalid, ch1 := German.Req.noReq, ch2 := x.2.1,
                    ch3 := x.2.2.1 }} +
              x.2.2.2.2.2.2.2),
        Unification.Unifier.bind fun (x : German.Items × ℕ × German.Cmd × ℕ) =>
          ((x.2.1, German.Gnt.noGnt, German.Ack.invAck,
              {German.Item.dir { cmd := x.2.2.1, ptr := x.2.2.2, exGntd := true, shr := {x.2.1}, inv := ∅ }} + x.1),
            x.2.2.1, x.2.2.2, x.2.1, German.Req.noReq, x.1)] := by
  udf_certify

theorem German.sendReqS_inv.obligation_10 :
    Unification.sound (Narrowing.mayFire German.sendReqS German.ownAck)
      [Unification.Unifier.bind
          fun (x : ℕ × German.Gnt × German.Ack × ℕ × German.Req × German.Cmd × ℕ × German.Items) =>
          ((x.1, x.2.1, x.2.2.1,
              {German.Item.cache
                      { id := x.2.2.2.1, state := German.CacheState.invalid, ch1 := x.2.2.2.2.1,
                        ch2 := German.Gnt.noGnt, ch3 := German.Ack.invAck }} +
                  {German.Item.dir
                      { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.1}, inv := ∅ }} +
                x.2.2.2.2.2.2.2),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
            {German.Item.cache
                  { id := x.1, state := German.CacheState.invalid, ch1 := German.Req.noReq, ch2 := x.2.1,
                    ch3 := x.2.2.1 }} +
              x.2.2.2.2.2.2.2),
        Unification.Unifier.bind fun (x : German.Items × ℕ × German.Cmd × ℕ) =>
          ((x.2.1, German.Gnt.noGnt, German.Ack.invAck,
              {German.Item.dir { cmd := x.2.2.1, ptr := x.2.2.2, exGntd := true, shr := {x.2.1}, inv := ∅ }} + x.1),
            x.2.2.1, x.2.2.2, x.2.1, German.Req.noReq, x.1)] := by
  -- each unifier, instantiated, solves the problem
  simp only [sound, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  repeat' apply And.intro
  all_goals
    rintro γ ⟨x, rfl⟩
    simp only [unifiedBy, Narrowing.mayFire, German.sendReqS, German.ownAck]
  all_goals first
    | rfl
    | ac_rfl
    | simp only [ACU.plus_unit, ACU.unit_plus, ACU.plus_comm, ACU.plus_left_comm, ACU.plus_assoc]

theorem German.sendReqEI_inv.obligation_1 :
    Unification.complete (Narrowing.mayFire German.sendReqEI German.freeP)
      [Unification.Unifier.bind
          fun (x : ℕ × German.Gnt × German.Ack × German.Cmd × ℕ × German.Oids × German.Oids × German.Items) =>
          ((x.1, x.2.1, x.2.2.1,
              {German.Item.dir
                    { cmd := x.2.2.2.1, ptr := x.2.2.2.2.1, exGntd := false, shr := x.2.2.2.2.2.1,
                      inv := x.2.2.2.2.2.2.1 }} +
                x.2.2.2.2.2.2.2),
            x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
            {German.Item.cache
                  { id := x.1, state := German.CacheState.invalid, ch1 := German.Req.noReq, ch2 := x.2.1,
                    ch3 := x.2.2.1 }} +
              x.2.2.2.2.2.2.2)] := by
  udf_certify

theorem German.sendReqEI_inv.obligation_2 :
    Unification.sound (Narrowing.mayFire German.sendReqEI German.freeP)
      [Unification.Unifier.bind
          fun (x : ℕ × German.Gnt × German.Ack × German.Cmd × ℕ × German.Oids × German.Oids × German.Items) =>
          ((x.1, x.2.1, x.2.2.1,
              {German.Item.dir
                    { cmd := x.2.2.2.1, ptr := x.2.2.2.2.1, exGntd := false, shr := x.2.2.2.2.2.1,
                      inv := x.2.2.2.2.2.2.1 }} +
                x.2.2.2.2.2.2.2),
            x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
            {German.Item.cache
                  { id := x.1, state := German.CacheState.invalid, ch1 := German.Req.noReq, ch2 := x.2.1,
                    ch3 := x.2.2.1 }} +
              x.2.2.2.2.2.2.2)] := by
  -- each unifier, instantiated, solves the problem
  simp only [sound, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  repeat' apply And.intro
  all_goals
    rintro γ ⟨x, rfl⟩
    simp only [unifiedBy, Narrowing.mayFire, German.sendReqEI, German.freeP]
  all_goals first
    | rfl
    | ac_rfl
    | simp only [ACU.plus_unit, ACU.unit_plus, ACU.plus_comm, ACU.plus_left_comm, ACU.plus_assoc]

theorem German.sendReqEI_inv.obligation_3 :
    Unification.complete (Narrowing.mayFire German.sendReqEI German.ownE)
      [Unification.Unifier.bind
          fun (x : ℕ × German.Gnt × German.Ack × ℕ × German.Req × German.Cmd × ℕ × German.Oids × German.Items) =>
          ((x.1, x.2.1, x.2.2.1,
              {German.Item.cache
                      { id := x.2.2.2.1, state := German.CacheState.exclusive, ch1 := x.2.2.2.2.1,
                        ch2 := German.Gnt.noGnt, ch3 := German.Ack.noAck }} +
                  {German.Item.dir
                      { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.1},
                        inv := x.2.2.2.2.2.2.2.1 }} +
                x.2.2.2.2.2.2.2.2),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
            {German.Item.cache
                  { id := x.1, state := German.CacheState.invalid, ch1 := German.Req.noReq, ch2 := x.2.1,
                    ch3 := x.2.2.1 }} +
              x.2.2.2.2.2.2.2.2)] := by
  udf_certify

theorem German.sendReqEI_inv.obligation_4 :
    Unification.sound (Narrowing.mayFire German.sendReqEI German.ownE)
      [Unification.Unifier.bind
          fun (x : ℕ × German.Gnt × German.Ack × ℕ × German.Req × German.Cmd × ℕ × German.Oids × German.Items) =>
          ((x.1, x.2.1, x.2.2.1,
              {German.Item.cache
                      { id := x.2.2.2.1, state := German.CacheState.exclusive, ch1 := x.2.2.2.2.1,
                        ch2 := German.Gnt.noGnt, ch3 := German.Ack.noAck }} +
                  {German.Item.dir
                      { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.1},
                        inv := x.2.2.2.2.2.2.2.1 }} +
                x.2.2.2.2.2.2.2.2),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
            {German.Item.cache
                  { id := x.1, state := German.CacheState.invalid, ch1 := German.Req.noReq, ch2 := x.2.1,
                    ch3 := x.2.2.1 }} +
              x.2.2.2.2.2.2.2.2)] := by
  -- each unifier, instantiated, solves the problem
  simp only [sound, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  repeat' apply And.intro
  all_goals
    rintro γ ⟨x, rfl⟩
    simp only [unifiedBy, Narrowing.mayFire, German.sendReqEI, German.ownE]
  all_goals first
    | rfl
    | ac_rfl
    | simp only [ACU.plus_unit, ACU.unit_plus, ACU.plus_comm, ACU.plus_left_comm, ACU.plus_assoc]

theorem German.sendReqEI_inv.obligation_5 :
    Unification.complete (Narrowing.mayFire German.sendReqEI German.ownG)
      [Unification.Unifier.bind
          fun (x : ℕ × German.Gnt × German.Ack × ℕ × German.Req × German.Cmd × ℕ × German.Oids × German.Items) =>
          ((x.1, x.2.1, x.2.2.1,
              {German.Item.cache
                      { id := x.2.2.2.1, state := German.CacheState.invalid, ch1 := x.2.2.2.2.1, ch2 := German.Gnt.gntE,
                        ch3 := German.Ack.noAck }} +
                  {German.Item.dir
                      { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.1},
                        inv := x.2.2.2.2.2.2.2.1 }} +
                x.2.2.2.2.2.2.2.2),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
            {German.Item.cache
                  { id := x.1, state := German.CacheState.invalid, ch1 := German.Req.noReq, ch2 := x.2.1,
                    ch3 := x.2.2.1 }} +
              x.2.2.2.2.2.2.2.2),
        Unification.Unifier.bind fun (x : German.Items × ℕ × German.Cmd × ℕ × German.Oids) =>
          ((x.2.1, German.Gnt.gntE, German.Ack.noAck,
              {German.Item.dir { cmd := x.2.2.1, ptr := x.2.2.2.1, exGntd := true, shr := {x.2.1}, inv := x.2.2.2.2 }} +
                x.1),
            x.2.2.1, x.2.2.2.1, x.2.2.2.2, x.2.1, German.Req.noReq, x.1)] := by
  udf_certify

theorem German.sendReqEI_inv.obligation_6 :
    Unification.sound (Narrowing.mayFire German.sendReqEI German.ownG)
      [Unification.Unifier.bind
          fun (x : ℕ × German.Gnt × German.Ack × ℕ × German.Req × German.Cmd × ℕ × German.Oids × German.Items) =>
          ((x.1, x.2.1, x.2.2.1,
              {German.Item.cache
                      { id := x.2.2.2.1, state := German.CacheState.invalid, ch1 := x.2.2.2.2.1, ch2 := German.Gnt.gntE,
                        ch3 := German.Ack.noAck }} +
                  {German.Item.dir
                      { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.1},
                        inv := x.2.2.2.2.2.2.2.1 }} +
                x.2.2.2.2.2.2.2.2),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
            {German.Item.cache
                  { id := x.1, state := German.CacheState.invalid, ch1 := German.Req.noReq, ch2 := x.2.1,
                    ch3 := x.2.2.1 }} +
              x.2.2.2.2.2.2.2.2),
        Unification.Unifier.bind fun (x : German.Items × ℕ × German.Cmd × ℕ × German.Oids) =>
          ((x.2.1, German.Gnt.gntE, German.Ack.noAck,
              {German.Item.dir { cmd := x.2.2.1, ptr := x.2.2.2.1, exGntd := true, shr := {x.2.1}, inv := x.2.2.2.2 }} +
                x.1),
            x.2.2.1, x.2.2.2.1, x.2.2.2.2, x.2.1, German.Req.noReq, x.1)] := by
  -- each unifier, instantiated, solves the problem
  simp only [sound, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  repeat' apply And.intro
  all_goals
    rintro γ ⟨x, rfl⟩
    simp only [unifiedBy, Narrowing.mayFire, German.sendReqEI, German.ownG]
  all_goals first
    | rfl
    | ac_rfl
    | simp only [ACU.plus_unit, ACU.unit_plus, ACU.plus_comm, ACU.plus_left_comm, ACU.plus_assoc]

theorem German.sendReqEI_inv.obligation_7 :
    Unification.complete (Narrowing.mayFire German.sendReqEI German.ownInv)
      [Unification.Unifier.bind
          fun (x : ℕ × German.Gnt × German.Ack × ℕ × German.Req × German.Cmd × ℕ × German.Items) =>
          ((x.1, x.2.1, x.2.2.1,
              {German.Item.cache
                      { id := x.2.2.2.1, state := German.CacheState.exclusive, ch1 := x.2.2.2.2.1,
                        ch2 := German.Gnt.inv, ch3 := German.Ack.noAck }} +
                  {German.Item.dir
                      { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.1}, inv := ∅ }} +
                x.2.2.2.2.2.2.2),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
            {German.Item.cache
                  { id := x.1, state := German.CacheState.invalid, ch1 := German.Req.noReq, ch2 := x.2.1,
                    ch3 := x.2.2.1 }} +
              x.2.2.2.2.2.2.2)] := by
  udf_certify

theorem German.sendReqEI_inv.obligation_8 :
    Unification.sound (Narrowing.mayFire German.sendReqEI German.ownInv)
      [Unification.Unifier.bind
          fun (x : ℕ × German.Gnt × German.Ack × ℕ × German.Req × German.Cmd × ℕ × German.Items) =>
          ((x.1, x.2.1, x.2.2.1,
              {German.Item.cache
                      { id := x.2.2.2.1, state := German.CacheState.exclusive, ch1 := x.2.2.2.2.1,
                        ch2 := German.Gnt.inv, ch3 := German.Ack.noAck }} +
                  {German.Item.dir
                      { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.1}, inv := ∅ }} +
                x.2.2.2.2.2.2.2),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
            {German.Item.cache
                  { id := x.1, state := German.CacheState.invalid, ch1 := German.Req.noReq, ch2 := x.2.1,
                    ch3 := x.2.2.1 }} +
              x.2.2.2.2.2.2.2)] := by
  -- each unifier, instantiated, solves the problem
  simp only [sound, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  repeat' apply And.intro
  all_goals
    rintro γ ⟨x, rfl⟩
    simp only [unifiedBy, Narrowing.mayFire, German.sendReqEI, German.ownInv]
  all_goals first
    | rfl
    | ac_rfl
    | simp only [ACU.plus_unit, ACU.unit_plus, ACU.plus_comm, ACU.plus_left_comm, ACU.plus_assoc]

theorem German.sendReqEI_inv.obligation_9 :
    Unification.complete (Narrowing.mayFire German.sendReqEI German.ownAck)
      [Unification.Unifier.bind
          fun (x : ℕ × German.Gnt × German.Ack × ℕ × German.Req × German.Cmd × ℕ × German.Items) =>
          ((x.1, x.2.1, x.2.2.1,
              {German.Item.cache
                      { id := x.2.2.2.1, state := German.CacheState.invalid, ch1 := x.2.2.2.2.1,
                        ch2 := German.Gnt.noGnt, ch3 := German.Ack.invAck }} +
                  {German.Item.dir
                      { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.1}, inv := ∅ }} +
                x.2.2.2.2.2.2.2),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
            {German.Item.cache
                  { id := x.1, state := German.CacheState.invalid, ch1 := German.Req.noReq, ch2 := x.2.1,
                    ch3 := x.2.2.1 }} +
              x.2.2.2.2.2.2.2),
        Unification.Unifier.bind fun (x : German.Items × ℕ × German.Cmd × ℕ) =>
          ((x.2.1, German.Gnt.noGnt, German.Ack.invAck,
              {German.Item.dir { cmd := x.2.2.1, ptr := x.2.2.2, exGntd := true, shr := {x.2.1}, inv := ∅ }} + x.1),
            x.2.2.1, x.2.2.2, x.2.1, German.Req.noReq, x.1)] := by
  udf_certify

theorem German.sendReqEI_inv.obligation_10 :
    Unification.sound (Narrowing.mayFire German.sendReqEI German.ownAck)
      [Unification.Unifier.bind
          fun (x : ℕ × German.Gnt × German.Ack × ℕ × German.Req × German.Cmd × ℕ × German.Items) =>
          ((x.1, x.2.1, x.2.2.1,
              {German.Item.cache
                      { id := x.2.2.2.1, state := German.CacheState.invalid, ch1 := x.2.2.2.2.1,
                        ch2 := German.Gnt.noGnt, ch3 := German.Ack.invAck }} +
                  {German.Item.dir
                      { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.1}, inv := ∅ }} +
                x.2.2.2.2.2.2.2),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
            {German.Item.cache
                  { id := x.1, state := German.CacheState.invalid, ch1 := German.Req.noReq, ch2 := x.2.1,
                    ch3 := x.2.2.1 }} +
              x.2.2.2.2.2.2.2),
        Unification.Unifier.bind fun (x : German.Items × ℕ × German.Cmd × ℕ) =>
          ((x.2.1, German.Gnt.noGnt, German.Ack.invAck,
              {German.Item.dir { cmd := x.2.2.1, ptr := x.2.2.2, exGntd := true, shr := {x.2.1}, inv := ∅ }} + x.1),
            x.2.2.1, x.2.2.2, x.2.1, German.Req.noReq, x.1)] := by
  -- each unifier, instantiated, solves the problem
  simp only [sound, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  repeat' apply And.intro
  all_goals
    rintro γ ⟨x, rfl⟩
    simp only [unifiedBy, Narrowing.mayFire, German.sendReqEI, German.ownAck]
  all_goals first
    | rfl
    | ac_rfl
    | simp only [ACU.plus_unit, ACU.unit_plus, ACU.plus_comm, ACU.plus_left_comm, ACU.plus_assoc]

theorem German.sendReqES_inv.obligation_1 :
    Unification.complete (Narrowing.mayFire German.sendReqES German.freeP)
      [Unification.Unifier.bind
          fun (x : ℕ × German.Gnt × German.Ack × German.Cmd × ℕ × German.Oids × German.Oids × German.Items) =>
          ((x.1, x.2.1, x.2.2.1,
              {German.Item.dir
                    { cmd := x.2.2.2.1, ptr := x.2.2.2.2.1, exGntd := false, shr := x.2.2.2.2.2.1,
                      inv := x.2.2.2.2.2.2.1 }} +
                x.2.2.2.2.2.2.2),
            x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
            {German.Item.cache
                  { id := x.1, state := German.CacheState.shared, ch1 := German.Req.noReq, ch2 := x.2.1,
                    ch3 := x.2.2.1 }} +
              x.2.2.2.2.2.2.2)] := by
  udf_certify

theorem German.sendReqES_inv.obligation_2 :
    Unification.sound (Narrowing.mayFire German.sendReqES German.freeP)
      [Unification.Unifier.bind
          fun (x : ℕ × German.Gnt × German.Ack × German.Cmd × ℕ × German.Oids × German.Oids × German.Items) =>
          ((x.1, x.2.1, x.2.2.1,
              {German.Item.dir
                    { cmd := x.2.2.2.1, ptr := x.2.2.2.2.1, exGntd := false, shr := x.2.2.2.2.2.1,
                      inv := x.2.2.2.2.2.2.1 }} +
                x.2.2.2.2.2.2.2),
            x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
            {German.Item.cache
                  { id := x.1, state := German.CacheState.shared, ch1 := German.Req.noReq, ch2 := x.2.1,
                    ch3 := x.2.2.1 }} +
              x.2.2.2.2.2.2.2)] := by
  -- each unifier, instantiated, solves the problem
  simp only [sound, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  repeat' apply And.intro
  all_goals
    rintro γ ⟨x, rfl⟩
    simp only [unifiedBy, Narrowing.mayFire, German.sendReqES, German.freeP]
  all_goals first
    | rfl
    | ac_rfl
    | simp only [ACU.plus_unit, ACU.unit_plus, ACU.plus_comm, ACU.plus_left_comm, ACU.plus_assoc]

theorem German.sendReqES_inv.obligation_3 :
    Unification.complete (Narrowing.mayFire German.sendReqES German.ownE)
      [Unification.Unifier.bind
          fun (x : ℕ × German.Gnt × German.Ack × ℕ × German.Req × German.Cmd × ℕ × German.Oids × German.Items) =>
          ((x.1, x.2.1, x.2.2.1,
              {German.Item.cache
                      { id := x.2.2.2.1, state := German.CacheState.exclusive, ch1 := x.2.2.2.2.1,
                        ch2 := German.Gnt.noGnt, ch3 := German.Ack.noAck }} +
                  {German.Item.dir
                      { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.1},
                        inv := x.2.2.2.2.2.2.2.1 }} +
                x.2.2.2.2.2.2.2.2),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
            {German.Item.cache
                  { id := x.1, state := German.CacheState.shared, ch1 := German.Req.noReq, ch2 := x.2.1,
                    ch3 := x.2.2.1 }} +
              x.2.2.2.2.2.2.2.2)] := by
  udf_certify

theorem German.sendReqES_inv.obligation_4 :
    Unification.sound (Narrowing.mayFire German.sendReqES German.ownE)
      [Unification.Unifier.bind
          fun (x : ℕ × German.Gnt × German.Ack × ℕ × German.Req × German.Cmd × ℕ × German.Oids × German.Items) =>
          ((x.1, x.2.1, x.2.2.1,
              {German.Item.cache
                      { id := x.2.2.2.1, state := German.CacheState.exclusive, ch1 := x.2.2.2.2.1,
                        ch2 := German.Gnt.noGnt, ch3 := German.Ack.noAck }} +
                  {German.Item.dir
                      { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.1},
                        inv := x.2.2.2.2.2.2.2.1 }} +
                x.2.2.2.2.2.2.2.2),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
            {German.Item.cache
                  { id := x.1, state := German.CacheState.shared, ch1 := German.Req.noReq, ch2 := x.2.1,
                    ch3 := x.2.2.1 }} +
              x.2.2.2.2.2.2.2.2)] := by
  -- each unifier, instantiated, solves the problem
  simp only [sound, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  repeat' apply And.intro
  all_goals
    rintro γ ⟨x, rfl⟩
    simp only [unifiedBy, Narrowing.mayFire, German.sendReqES, German.ownE]
  all_goals first
    | rfl
    | ac_rfl
    | simp only [ACU.plus_unit, ACU.unit_plus, ACU.plus_comm, ACU.plus_left_comm, ACU.plus_assoc]

theorem German.sendReqES_inv.obligation_5 :
    Unification.complete (Narrowing.mayFire German.sendReqES German.ownG)
      [Unification.Unifier.bind
          fun (x : ℕ × German.Gnt × German.Ack × ℕ × German.Req × German.Cmd × ℕ × German.Oids × German.Items) =>
          ((x.1, x.2.1, x.2.2.1,
              {German.Item.cache
                      { id := x.2.2.2.1, state := German.CacheState.invalid, ch1 := x.2.2.2.2.1, ch2 := German.Gnt.gntE,
                        ch3 := German.Ack.noAck }} +
                  {German.Item.dir
                      { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.1},
                        inv := x.2.2.2.2.2.2.2.1 }} +
                x.2.2.2.2.2.2.2.2),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
            {German.Item.cache
                  { id := x.1, state := German.CacheState.shared, ch1 := German.Req.noReq, ch2 := x.2.1,
                    ch3 := x.2.2.1 }} +
              x.2.2.2.2.2.2.2.2)] := by
  udf_certify

theorem German.sendReqES_inv.obligation_6 :
    Unification.sound (Narrowing.mayFire German.sendReqES German.ownG)
      [Unification.Unifier.bind
          fun (x : ℕ × German.Gnt × German.Ack × ℕ × German.Req × German.Cmd × ℕ × German.Oids × German.Items) =>
          ((x.1, x.2.1, x.2.2.1,
              {German.Item.cache
                      { id := x.2.2.2.1, state := German.CacheState.invalid, ch1 := x.2.2.2.2.1, ch2 := German.Gnt.gntE,
                        ch3 := German.Ack.noAck }} +
                  {German.Item.dir
                      { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.1},
                        inv := x.2.2.2.2.2.2.2.1 }} +
                x.2.2.2.2.2.2.2.2),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
            {German.Item.cache
                  { id := x.1, state := German.CacheState.shared, ch1 := German.Req.noReq, ch2 := x.2.1,
                    ch3 := x.2.2.1 }} +
              x.2.2.2.2.2.2.2.2)] := by
  -- each unifier, instantiated, solves the problem
  simp only [sound, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  repeat' apply And.intro
  all_goals
    rintro γ ⟨x, rfl⟩
    simp only [unifiedBy, Narrowing.mayFire, German.sendReqES, German.ownG]
  all_goals first
    | rfl
    | ac_rfl
    | simp only [ACU.plus_unit, ACU.unit_plus, ACU.plus_comm, ACU.plus_left_comm, ACU.plus_assoc]

theorem German.sendReqES_inv.obligation_7 :
    Unification.complete (Narrowing.mayFire German.sendReqES German.ownInv)
      [Unification.Unifier.bind
          fun (x : ℕ × German.Gnt × German.Ack × ℕ × German.Req × German.Cmd × ℕ × German.Items) =>
          ((x.1, x.2.1, x.2.2.1,
              {German.Item.cache
                      { id := x.2.2.2.1, state := German.CacheState.exclusive, ch1 := x.2.2.2.2.1,
                        ch2 := German.Gnt.inv, ch3 := German.Ack.noAck }} +
                  {German.Item.dir
                      { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.1}, inv := ∅ }} +
                x.2.2.2.2.2.2.2),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
            {German.Item.cache
                  { id := x.1, state := German.CacheState.shared, ch1 := German.Req.noReq, ch2 := x.2.1,
                    ch3 := x.2.2.1 }} +
              x.2.2.2.2.2.2.2)] := by
  udf_certify

theorem German.sendReqES_inv.obligation_8 :
    Unification.sound (Narrowing.mayFire German.sendReqES German.ownInv)
      [Unification.Unifier.bind
          fun (x : ℕ × German.Gnt × German.Ack × ℕ × German.Req × German.Cmd × ℕ × German.Items) =>
          ((x.1, x.2.1, x.2.2.1,
              {German.Item.cache
                      { id := x.2.2.2.1, state := German.CacheState.exclusive, ch1 := x.2.2.2.2.1,
                        ch2 := German.Gnt.inv, ch3 := German.Ack.noAck }} +
                  {German.Item.dir
                      { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.1}, inv := ∅ }} +
                x.2.2.2.2.2.2.2),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
            {German.Item.cache
                  { id := x.1, state := German.CacheState.shared, ch1 := German.Req.noReq, ch2 := x.2.1,
                    ch3 := x.2.2.1 }} +
              x.2.2.2.2.2.2.2)] := by
  -- each unifier, instantiated, solves the problem
  simp only [sound, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  repeat' apply And.intro
  all_goals
    rintro γ ⟨x, rfl⟩
    simp only [unifiedBy, Narrowing.mayFire, German.sendReqES, German.ownInv]
  all_goals first
    | rfl
    | ac_rfl
    | simp only [ACU.plus_unit, ACU.unit_plus, ACU.plus_comm, ACU.plus_left_comm, ACU.plus_assoc]

theorem German.sendReqES_inv.obligation_9 :
    Unification.complete (Narrowing.mayFire German.sendReqES German.ownAck)
      [Unification.Unifier.bind
          fun (x : ℕ × German.Gnt × German.Ack × ℕ × German.Req × German.Cmd × ℕ × German.Items) =>
          ((x.1, x.2.1, x.2.2.1,
              {German.Item.cache
                      { id := x.2.2.2.1, state := German.CacheState.invalid, ch1 := x.2.2.2.2.1,
                        ch2 := German.Gnt.noGnt, ch3 := German.Ack.invAck }} +
                  {German.Item.dir
                      { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.1}, inv := ∅ }} +
                x.2.2.2.2.2.2.2),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
            {German.Item.cache
                  { id := x.1, state := German.CacheState.shared, ch1 := German.Req.noReq, ch2 := x.2.1,
                    ch3 := x.2.2.1 }} +
              x.2.2.2.2.2.2.2)] := by
  udf_certify

theorem German.sendReqES_inv.obligation_10 :
    Unification.sound (Narrowing.mayFire German.sendReqES German.ownAck)
      [Unification.Unifier.bind
          fun (x : ℕ × German.Gnt × German.Ack × ℕ × German.Req × German.Cmd × ℕ × German.Items) =>
          ((x.1, x.2.1, x.2.2.1,
              {German.Item.cache
                      { id := x.2.2.2.1, state := German.CacheState.invalid, ch1 := x.2.2.2.2.1,
                        ch2 := German.Gnt.noGnt, ch3 := German.Ack.invAck }} +
                  {German.Item.dir
                      { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.1}, inv := ∅ }} +
                x.2.2.2.2.2.2.2),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
            {German.Item.cache
                  { id := x.1, state := German.CacheState.shared, ch1 := German.Req.noReq, ch2 := x.2.1,
                    ch3 := x.2.2.1 }} +
              x.2.2.2.2.2.2.2)] := by
  -- each unifier, instantiated, solves the problem
  simp only [sound, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  repeat' apply And.intro
  all_goals
    rintro γ ⟨x, rfl⟩
    simp only [unifiedBy, Narrowing.mayFire, German.sendReqES, German.ownAck]
  all_goals first
    | rfl
    | ac_rfl
    | simp only [ACU.plus_unit, ACU.unit_plus, ACU.plus_comm, ACU.plus_left_comm, ACU.plus_assoc]

theorem German.recvReqS_inv.obligation_1 :
    Unification.complete (Narrowing.mayFire German.recvReqS German.freeP)
      [Unification.Unifier.bind
          fun
            (x :
              ℕ ×
                ℕ ×
                  German.Oids ×
                    German.Oids ×
                      German.Items ×
                        German.CacheState ×
                          German.Gnt × German.Ack × ℕ × Bool × German.Oids × German.Oids × German.Cmd) =>
          ((x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.1, x.1,
              x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1,
              {German.Item.dir
                    { cmd := x.2.2.2.2.2.2.2.2.2.2.2.2, ptr := x.2.1, exGntd := false, shr := x.2.2.1,
                      inv := x.2.2.2.1 }} +
                x.2.2.2.2.1),
            x.2.2.2.2.2.2.2.2.2.2.2.2, x.2.1, x.2.2.1, x.2.2.2.1,
            {German.Item.cache
                    { id := x.1, state := x.2.2.2.2.2.1, ch1 := German.Req.reqS, ch2 := x.2.2.2.2.2.2.1,
                      ch3 := x.2.2.2.2.2.2.2.1 }} +
                {German.Item.dir
                    { cmd := German.Cmd.idle, ptr := x.2.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.2.1,
                      shr := x.2.2.2.2.2.2.2.2.2.2.1, inv := x.2.2.2.2.2.2.2.2.2.2.2.1 }} +
              x.2.2.2.2.1),
        Unification.Unifier.bind
          fun (x : German.Items × ℕ × German.CacheState × German.Gnt × German.Ack × ℕ × German.Oids × German.Oids) =>
          ((x.2.2.2.2.2.1, false, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.1),
            German.Cmd.idle, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2,
            {German.Item.cache
                  { id := x.2.1, state := x.2.2.1, ch1 := German.Req.reqS, ch2 := x.2.2.2.1, ch3 := x.2.2.2.2.1 }} +
              x.1)] := by
  udf_certify

theorem German.recvReqS_inv.obligation_2 :
    Unification.sound (Narrowing.mayFire German.recvReqS German.freeP)
      [Unification.Unifier.bind
          fun
            (x :
              ℕ ×
                ℕ ×
                  German.Oids ×
                    German.Oids ×
                      German.Items ×
                        German.CacheState ×
                          German.Gnt × German.Ack × ℕ × Bool × German.Oids × German.Oids × German.Cmd) =>
          ((x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.1, x.1,
              x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1,
              {German.Item.dir
                    { cmd := x.2.2.2.2.2.2.2.2.2.2.2.2, ptr := x.2.1, exGntd := false, shr := x.2.2.1,
                      inv := x.2.2.2.1 }} +
                x.2.2.2.2.1),
            x.2.2.2.2.2.2.2.2.2.2.2.2, x.2.1, x.2.2.1, x.2.2.2.1,
            {German.Item.cache
                    { id := x.1, state := x.2.2.2.2.2.1, ch1 := German.Req.reqS, ch2 := x.2.2.2.2.2.2.1,
                      ch3 := x.2.2.2.2.2.2.2.1 }} +
                {German.Item.dir
                    { cmd := German.Cmd.idle, ptr := x.2.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.2.1,
                      shr := x.2.2.2.2.2.2.2.2.2.2.1, inv := x.2.2.2.2.2.2.2.2.2.2.2.1 }} +
              x.2.2.2.2.1),
        Unification.Unifier.bind
          fun (x : German.Items × ℕ × German.CacheState × German.Gnt × German.Ack × ℕ × German.Oids × German.Oids) =>
          ((x.2.2.2.2.2.1, false, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.1),
            German.Cmd.idle, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2,
            {German.Item.cache
                  { id := x.2.1, state := x.2.2.1, ch1 := German.Req.reqS, ch2 := x.2.2.2.1, ch3 := x.2.2.2.2.1 }} +
              x.1)] := by
  -- each unifier, instantiated, solves the problem
  simp only [sound, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  repeat' apply And.intro
  all_goals
    rintro γ ⟨x, rfl⟩
    simp only [unifiedBy, Narrowing.mayFire, German.recvReqS, German.freeP]
  all_goals first
    | rfl
    | ac_rfl
    | simp only [ACU.plus_unit, ACU.unit_plus, ACU.plus_comm, ACU.plus_left_comm, ACU.plus_assoc]

theorem German.recvReqS_inv.obligation_3 :
    Unification.complete (Narrowing.mayFire German.recvReqS German.ownE)
      [Unification.Unifier.bind
          fun
            (x :
              ℕ ×
                German.Req ×
                  German.Cmd ×
                    ℕ ×
                      German.Oids ×
                        German.Items ×
                          German.CacheState × German.Gnt × German.Ack × ℕ × Bool × German.Oids × German.Oids × ℕ) =>
          ((x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2.1, x.1,
              x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1,
              {German.Item.cache
                      { id := x.2.2.2.2.2.2.2.2.2.2.2.2.2, state := German.CacheState.exclusive, ch1 := x.2.1,
                        ch2 := German.Gnt.noGnt, ch3 := German.Ack.noAck }} +
                  {German.Item.dir
                      { cmd := x.2.2.1, ptr := x.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.2.2.2.2.2},
                        inv := x.2.2.2.2.1 }} +
                x.2.2.2.2.2.1),
            x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2.2, x.2.1,
            {German.Item.cache
                    { id := x.1, state := x.2.2.2.2.2.2.1, ch1 := German.Req.reqS, ch2 := x.2.2.2.2.2.2.2.1,
                      ch3 := x.2.2.2.2.2.2.2.2.1 }} +
                {German.Item.dir
                    { cmd := German.Cmd.idle, ptr := x.2.2.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.2.2.1,
                      shr := x.2.2.2.2.2.2.2.2.2.2.2.1, inv := x.2.2.2.2.2.2.2.2.2.2.2.2.1 }} +
              x.2.2.2.2.2.1),
        Unification.Unifier.bind
          fun (x : ℕ × Bool × German.Oids × German.Oids × ℕ × German.Cmd × ℕ × German.Oids × German.Items) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, German.CacheState.exclusive, German.Gnt.noGnt,
              German.Ack.noAck,
              {German.Item.dir
                    { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.1},
                      inv := x.2.2.2.2.2.2.2.1 }} +
                x.2.2.2.2.2.2.2.2),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.1, German.Req.reqS,
            {German.Item.dir
                  { cmd := German.Cmd.idle, ptr := x.1, exGntd := x.2.1, shr := x.2.2.1, inv := x.2.2.2.1 }} +
              x.2.2.2.2.2.2.2.2),
        Unification.Unifier.bind
          fun (x : ℕ × German.CacheState × German.Gnt × German.Ack × ℕ × German.Req × ℕ × German.Oids × German.Items) =>
          ((x.2.2.2.2.2.2.1, true, {x.2.2.2.2.1}, x.2.2.2.2.2.2.2.1, x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {German.Item.cache
                    { id := x.2.2.2.2.1, state := German.CacheState.exclusive, ch1 := x.2.2.2.2.2.1,
                      ch2 := German.Gnt.noGnt, ch3 := German.Ack.noAck }} +
                x.2.2.2.2.2.2.2.2),
            German.Cmd.idle, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
            {German.Item.cache
                  { id := x.1, state := x.2.1, ch1 := German.Req.reqS, ch2 := x.2.2.1, ch3 := x.2.2.2.1 }} +
              x.2.2.2.2.2.2.2.2),
        Unification.Unifier.bind fun (x : German.Items × ℕ × ℕ × German.Oids) =>
          ((x.2.2.1, true, {x.2.1}, x.2.2.2, x.2.1, German.CacheState.exclusive, German.Gnt.noGnt, German.Ack.noAck,
              x.1),
            German.Cmd.idle, x.2.2.1, x.2.2.2, x.2.1, German.Req.reqS, x.1)] := by
  udf_certify

theorem German.recvReqS_inv.obligation_4 :
    Unification.sound (Narrowing.mayFire German.recvReqS German.ownE)
      [Unification.Unifier.bind
          fun
            (x :
              ℕ ×
                German.Req ×
                  German.Cmd ×
                    ℕ ×
                      German.Oids ×
                        German.Items ×
                          German.CacheState × German.Gnt × German.Ack × ℕ × Bool × German.Oids × German.Oids × ℕ) =>
          ((x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2.1, x.1,
              x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1,
              {German.Item.cache
                      { id := x.2.2.2.2.2.2.2.2.2.2.2.2.2, state := German.CacheState.exclusive, ch1 := x.2.1,
                        ch2 := German.Gnt.noGnt, ch3 := German.Ack.noAck }} +
                  {German.Item.dir
                      { cmd := x.2.2.1, ptr := x.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.2.2.2.2.2},
                        inv := x.2.2.2.2.1 }} +
                x.2.2.2.2.2.1),
            x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2.2, x.2.1,
            {German.Item.cache
                    { id := x.1, state := x.2.2.2.2.2.2.1, ch1 := German.Req.reqS, ch2 := x.2.2.2.2.2.2.2.1,
                      ch3 := x.2.2.2.2.2.2.2.2.1 }} +
                {German.Item.dir
                    { cmd := German.Cmd.idle, ptr := x.2.2.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.2.2.1,
                      shr := x.2.2.2.2.2.2.2.2.2.2.2.1, inv := x.2.2.2.2.2.2.2.2.2.2.2.2.1 }} +
              x.2.2.2.2.2.1),
        Unification.Unifier.bind
          fun (x : ℕ × Bool × German.Oids × German.Oids × ℕ × German.Cmd × ℕ × German.Oids × German.Items) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, German.CacheState.exclusive, German.Gnt.noGnt,
              German.Ack.noAck,
              {German.Item.dir
                    { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.1},
                      inv := x.2.2.2.2.2.2.2.1 }} +
                x.2.2.2.2.2.2.2.2),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.1, German.Req.reqS,
            {German.Item.dir
                  { cmd := German.Cmd.idle, ptr := x.1, exGntd := x.2.1, shr := x.2.2.1, inv := x.2.2.2.1 }} +
              x.2.2.2.2.2.2.2.2),
        Unification.Unifier.bind
          fun (x : ℕ × German.CacheState × German.Gnt × German.Ack × ℕ × German.Req × ℕ × German.Oids × German.Items) =>
          ((x.2.2.2.2.2.2.1, true, {x.2.2.2.2.1}, x.2.2.2.2.2.2.2.1, x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {German.Item.cache
                    { id := x.2.2.2.2.1, state := German.CacheState.exclusive, ch1 := x.2.2.2.2.2.1,
                      ch2 := German.Gnt.noGnt, ch3 := German.Ack.noAck }} +
                x.2.2.2.2.2.2.2.2),
            German.Cmd.idle, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
            {German.Item.cache
                  { id := x.1, state := x.2.1, ch1 := German.Req.reqS, ch2 := x.2.2.1, ch3 := x.2.2.2.1 }} +
              x.2.2.2.2.2.2.2.2),
        Unification.Unifier.bind fun (x : German.Items × ℕ × ℕ × German.Oids) =>
          ((x.2.2.1, true, {x.2.1}, x.2.2.2, x.2.1, German.CacheState.exclusive, German.Gnt.noGnt, German.Ack.noAck,
              x.1),
            German.Cmd.idle, x.2.2.1, x.2.2.2, x.2.1, German.Req.reqS, x.1)] := by
  -- each unifier, instantiated, solves the problem
  simp only [sound, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  repeat' apply And.intro
  all_goals
    rintro γ ⟨x, rfl⟩
    simp only [unifiedBy, Narrowing.mayFire, German.recvReqS, German.ownE]
  all_goals first
    | rfl
    | ac_rfl
    | simp only [ACU.plus_unit, ACU.unit_plus, ACU.plus_comm, ACU.plus_left_comm, ACU.plus_assoc]

theorem German.recvReqS_inv.obligation_5 :
    Unification.complete (Narrowing.mayFire German.recvReqS German.ownG)
      [Unification.Unifier.bind
          fun
            (x :
              ℕ ×
                German.Req ×
                  German.Cmd ×
                    ℕ ×
                      German.Oids ×
                        German.Items ×
                          German.CacheState × German.Gnt × German.Ack × ℕ × Bool × German.Oids × German.Oids × ℕ) =>
          ((x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2.1, x.1,
              x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1,
              {German.Item.cache
                      { id := x.2.2.2.2.2.2.2.2.2.2.2.2.2, state := German.CacheState.invalid, ch1 := x.2.1,
                        ch2 := German.Gnt.gntE, ch3 := German.Ack.noAck }} +
                  {German.Item.dir
                      { cmd := x.2.2.1, ptr := x.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.2.2.2.2.2},
                        inv := x.2.2.2.2.1 }} +
                x.2.2.2.2.2.1),
            x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2.2, x.2.1,
            {German.Item.cache
                    { id := x.1, state := x.2.2.2.2.2.2.1, ch1 := German.Req.reqS, ch2 := x.2.2.2.2.2.2.2.1,
                      ch3 := x.2.2.2.2.2.2.2.2.1 }} +
                {German.Item.dir
                    { cmd := German.Cmd.idle, ptr := x.2.2.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.2.2.1,
                      shr := x.2.2.2.2.2.2.2.2.2.2.2.1, inv := x.2.2.2.2.2.2.2.2.2.2.2.2.1 }} +
              x.2.2.2.2.2.1),
        Unification.Unifier.bind
          fun (x : ℕ × Bool × German.Oids × German.Oids × ℕ × German.Cmd × ℕ × German.Oids × German.Items) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, German.CacheState.invalid, German.Gnt.gntE, German.Ack.noAck,
              {German.Item.dir
                    { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.1},
                      inv := x.2.2.2.2.2.2.2.1 }} +
                x.2.2.2.2.2.2.2.2),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.1, German.Req.reqS,
            {German.Item.dir
                  { cmd := German.Cmd.idle, ptr := x.1, exGntd := x.2.1, shr := x.2.2.1, inv := x.2.2.2.1 }} +
              x.2.2.2.2.2.2.2.2),
        Unification.Unifier.bind
          fun (x : ℕ × German.CacheState × German.Gnt × German.Ack × ℕ × German.Req × ℕ × German.Oids × German.Items) =>
          ((x.2.2.2.2.2.2.1, true, {x.2.2.2.2.1}, x.2.2.2.2.2.2.2.1, x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {German.Item.cache
                    { id := x.2.2.2.2.1, state := German.CacheState.invalid, ch1 := x.2.2.2.2.2.1,
                      ch2 := German.Gnt.gntE, ch3 := German.Ack.noAck }} +
                x.2.2.2.2.2.2.2.2),
            German.Cmd.idle, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
            {German.Item.cache
                  { id := x.1, state := x.2.1, ch1 := German.Req.reqS, ch2 := x.2.2.1, ch3 := x.2.2.2.1 }} +
              x.2.2.2.2.2.2.2.2),
        Unification.Unifier.bind fun (x : German.Items × ℕ × ℕ × German.Oids) =>
          ((x.2.2.1, true, {x.2.1}, x.2.2.2, x.2.1, German.CacheState.invalid, German.Gnt.gntE, German.Ack.noAck, x.1),
            German.Cmd.idle, x.2.2.1, x.2.2.2, x.2.1, German.Req.reqS, x.1)] := by
  udf_certify

theorem German.recvReqS_inv.obligation_6 :
    Unification.sound (Narrowing.mayFire German.recvReqS German.ownG)
      [Unification.Unifier.bind
          fun
            (x :
              ℕ ×
                German.Req ×
                  German.Cmd ×
                    ℕ ×
                      German.Oids ×
                        German.Items ×
                          German.CacheState × German.Gnt × German.Ack × ℕ × Bool × German.Oids × German.Oids × ℕ) =>
          ((x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2.1, x.1,
              x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1,
              {German.Item.cache
                      { id := x.2.2.2.2.2.2.2.2.2.2.2.2.2, state := German.CacheState.invalid, ch1 := x.2.1,
                        ch2 := German.Gnt.gntE, ch3 := German.Ack.noAck }} +
                  {German.Item.dir
                      { cmd := x.2.2.1, ptr := x.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.2.2.2.2.2},
                        inv := x.2.2.2.2.1 }} +
                x.2.2.2.2.2.1),
            x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2.2, x.2.1,
            {German.Item.cache
                    { id := x.1, state := x.2.2.2.2.2.2.1, ch1 := German.Req.reqS, ch2 := x.2.2.2.2.2.2.2.1,
                      ch3 := x.2.2.2.2.2.2.2.2.1 }} +
                {German.Item.dir
                    { cmd := German.Cmd.idle, ptr := x.2.2.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.2.2.1,
                      shr := x.2.2.2.2.2.2.2.2.2.2.2.1, inv := x.2.2.2.2.2.2.2.2.2.2.2.2.1 }} +
              x.2.2.2.2.2.1),
        Unification.Unifier.bind
          fun (x : ℕ × Bool × German.Oids × German.Oids × ℕ × German.Cmd × ℕ × German.Oids × German.Items) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, German.CacheState.invalid, German.Gnt.gntE, German.Ack.noAck,
              {German.Item.dir
                    { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.1},
                      inv := x.2.2.2.2.2.2.2.1 }} +
                x.2.2.2.2.2.2.2.2),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.1, German.Req.reqS,
            {German.Item.dir
                  { cmd := German.Cmd.idle, ptr := x.1, exGntd := x.2.1, shr := x.2.2.1, inv := x.2.2.2.1 }} +
              x.2.2.2.2.2.2.2.2),
        Unification.Unifier.bind
          fun (x : ℕ × German.CacheState × German.Gnt × German.Ack × ℕ × German.Req × ℕ × German.Oids × German.Items) =>
          ((x.2.2.2.2.2.2.1, true, {x.2.2.2.2.1}, x.2.2.2.2.2.2.2.1, x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {German.Item.cache
                    { id := x.2.2.2.2.1, state := German.CacheState.invalid, ch1 := x.2.2.2.2.2.1,
                      ch2 := German.Gnt.gntE, ch3 := German.Ack.noAck }} +
                x.2.2.2.2.2.2.2.2),
            German.Cmd.idle, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
            {German.Item.cache
                  { id := x.1, state := x.2.1, ch1 := German.Req.reqS, ch2 := x.2.2.1, ch3 := x.2.2.2.1 }} +
              x.2.2.2.2.2.2.2.2),
        Unification.Unifier.bind fun (x : German.Items × ℕ × ℕ × German.Oids) =>
          ((x.2.2.1, true, {x.2.1}, x.2.2.2, x.2.1, German.CacheState.invalid, German.Gnt.gntE, German.Ack.noAck, x.1),
            German.Cmd.idle, x.2.2.1, x.2.2.2, x.2.1, German.Req.reqS, x.1)] := by
  -- each unifier, instantiated, solves the problem
  simp only [sound, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  repeat' apply And.intro
  all_goals
    rintro γ ⟨x, rfl⟩
    simp only [unifiedBy, Narrowing.mayFire, German.recvReqS, German.ownG]
  all_goals first
    | rfl
    | ac_rfl
    | simp only [ACU.plus_unit, ACU.unit_plus, ACU.plus_comm, ACU.plus_left_comm, ACU.plus_assoc]

theorem German.recvReqS_inv.obligation_7 :
    Unification.complete (Narrowing.mayFire German.recvReqS German.ownInv)
      [Unification.Unifier.bind
          fun
            (x :
              ℕ ×
                German.Req ×
                  German.Cmd ×
                    ℕ ×
                      German.Items ×
                        German.CacheState × German.Gnt × German.Ack × ℕ × Bool × German.Oids × German.Oids × ℕ) =>
          ((x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.1, x.1,
              x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1,
              {German.Item.cache
                      { id := x.2.2.2.2.2.2.2.2.2.2.2.2, state := German.CacheState.exclusive, ch1 := x.2.1,
                        ch2 := German.Gnt.inv, ch3 := German.Ack.noAck }} +
                  {German.Item.dir
                      { cmd := x.2.2.1, ptr := x.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.2.2.2.2},
                        inv := ∅ }} +
                x.2.2.2.2.1),
            x.2.2.1, x.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2, x.2.1,
            {German.Item.cache
                    { id := x.1, state := x.2.2.2.2.2.1, ch1 := German.Req.reqS, ch2 := x.2.2.2.2.2.2.1,
                      ch3 := x.2.2.2.2.2.2.2.1 }} +
                {German.Item.dir
                    { cmd := German.Cmd.idle, ptr := x.2.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.2.1,
                      shr := x.2.2.2.2.2.2.2.2.2.2.1, inv := x.2.2.2.2.2.2.2.2.2.2.2.1 }} +
              x.2.2.2.2.1),
        Unification.Unifier.bind fun (x : ℕ × Bool × German.Oids × German.Oids × ℕ × German.Cmd × ℕ × German.Items) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, German.CacheState.exclusive, German.Gnt.inv, German.Ack.noAck,
              {German.Item.dir
                    { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.1}, inv := ∅ }} +
                x.2.2.2.2.2.2.2),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.1, German.Req.reqS,
            {German.Item.dir
                  { cmd := German.Cmd.idle, ptr := x.1, exGntd := x.2.1, shr := x.2.2.1, inv := x.2.2.2.1 }} +
              x.2.2.2.2.2.2.2),
        Unification.Unifier.bind
          fun (x : ℕ × German.CacheState × German.Gnt × German.Ack × ℕ × German.Req × ℕ × German.Items) =>
          ((x.2.2.2.2.2.2.1, true, {x.2.2.2.2.1}, ∅, x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {German.Item.cache
                    { id := x.2.2.2.2.1, state := German.CacheState.exclusive, ch1 := x.2.2.2.2.2.1,
                      ch2 := German.Gnt.inv, ch3 := German.Ack.noAck }} +
                x.2.2.2.2.2.2.2),
            German.Cmd.idle, x.2.2.2.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
            {German.Item.cache
                  { id := x.1, state := x.2.1, ch1 := German.Req.reqS, ch2 := x.2.2.1, ch3 := x.2.2.2.1 }} +
              x.2.2.2.2.2.2.2),
        Unification.Unifier.bind fun (x : German.Items × ℕ × ℕ) =>
          ((x.2.2, true, {x.2.1}, ∅, x.2.1, German.CacheState.exclusive, German.Gnt.inv, German.Ack.noAck, x.1),
            German.Cmd.idle, x.2.2, x.2.1, German.Req.reqS, x.1)] := by
  udf_certify

theorem German.recvReqS_inv.obligation_8 :
    Unification.sound (Narrowing.mayFire German.recvReqS German.ownInv)
      [Unification.Unifier.bind
          fun
            (x :
              ℕ ×
                German.Req ×
                  German.Cmd ×
                    ℕ ×
                      German.Items ×
                        German.CacheState × German.Gnt × German.Ack × ℕ × Bool × German.Oids × German.Oids × ℕ) =>
          ((x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.1, x.1,
              x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1,
              {German.Item.cache
                      { id := x.2.2.2.2.2.2.2.2.2.2.2.2, state := German.CacheState.exclusive, ch1 := x.2.1,
                        ch2 := German.Gnt.inv, ch3 := German.Ack.noAck }} +
                  {German.Item.dir
                      { cmd := x.2.2.1, ptr := x.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.2.2.2.2},
                        inv := ∅ }} +
                x.2.2.2.2.1),
            x.2.2.1, x.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2, x.2.1,
            {German.Item.cache
                    { id := x.1, state := x.2.2.2.2.2.1, ch1 := German.Req.reqS, ch2 := x.2.2.2.2.2.2.1,
                      ch3 := x.2.2.2.2.2.2.2.1 }} +
                {German.Item.dir
                    { cmd := German.Cmd.idle, ptr := x.2.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.2.1,
                      shr := x.2.2.2.2.2.2.2.2.2.2.1, inv := x.2.2.2.2.2.2.2.2.2.2.2.1 }} +
              x.2.2.2.2.1),
        Unification.Unifier.bind fun (x : ℕ × Bool × German.Oids × German.Oids × ℕ × German.Cmd × ℕ × German.Items) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, German.CacheState.exclusive, German.Gnt.inv, German.Ack.noAck,
              {German.Item.dir
                    { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.1}, inv := ∅ }} +
                x.2.2.2.2.2.2.2),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.1, German.Req.reqS,
            {German.Item.dir
                  { cmd := German.Cmd.idle, ptr := x.1, exGntd := x.2.1, shr := x.2.2.1, inv := x.2.2.2.1 }} +
              x.2.2.2.2.2.2.2),
        Unification.Unifier.bind
          fun (x : ℕ × German.CacheState × German.Gnt × German.Ack × ℕ × German.Req × ℕ × German.Items) =>
          ((x.2.2.2.2.2.2.1, true, {x.2.2.2.2.1}, ∅, x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {German.Item.cache
                    { id := x.2.2.2.2.1, state := German.CacheState.exclusive, ch1 := x.2.2.2.2.2.1,
                      ch2 := German.Gnt.inv, ch3 := German.Ack.noAck }} +
                x.2.2.2.2.2.2.2),
            German.Cmd.idle, x.2.2.2.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
            {German.Item.cache
                  { id := x.1, state := x.2.1, ch1 := German.Req.reqS, ch2 := x.2.2.1, ch3 := x.2.2.2.1 }} +
              x.2.2.2.2.2.2.2),
        Unification.Unifier.bind fun (x : German.Items × ℕ × ℕ) =>
          ((x.2.2, true, {x.2.1}, ∅, x.2.1, German.CacheState.exclusive, German.Gnt.inv, German.Ack.noAck, x.1),
            German.Cmd.idle, x.2.2, x.2.1, German.Req.reqS, x.1)] := by
  -- each unifier, instantiated, solves the problem
  simp only [sound, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  repeat' apply And.intro
  all_goals
    rintro γ ⟨x, rfl⟩
    simp only [unifiedBy, Narrowing.mayFire, German.recvReqS, German.ownInv]
  all_goals first
    | rfl
    | ac_rfl
    | simp only [ACU.plus_unit, ACU.unit_plus, ACU.plus_comm, ACU.plus_left_comm, ACU.plus_assoc]

theorem German.recvReqS_inv.obligation_9 :
    Unification.complete (Narrowing.mayFire German.recvReqS German.ownAck)
      [Unification.Unifier.bind
          fun
            (x :
              ℕ ×
                German.Req ×
                  German.Cmd ×
                    ℕ ×
                      German.Items ×
                        German.CacheState × German.Gnt × German.Ack × ℕ × Bool × German.Oids × German.Oids × ℕ) =>
          ((x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.1, x.1,
              x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1,
              {German.Item.cache
                      { id := x.2.2.2.2.2.2.2.2.2.2.2.2, state := German.CacheState.invalid, ch1 := x.2.1,
                        ch2 := German.Gnt.noGnt, ch3 := German.Ack.invAck }} +
                  {German.Item.dir
                      { cmd := x.2.2.1, ptr := x.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.2.2.2.2},
                        inv := ∅ }} +
                x.2.2.2.2.1),
            x.2.2.1, x.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2, x.2.1,
            {German.Item.cache
                    { id := x.1, state := x.2.2.2.2.2.1, ch1 := German.Req.reqS, ch2 := x.2.2.2.2.2.2.1,
                      ch3 := x.2.2.2.2.2.2.2.1 }} +
                {German.Item.dir
                    { cmd := German.Cmd.idle, ptr := x.2.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.2.1,
                      shr := x.2.2.2.2.2.2.2.2.2.2.1, inv := x.2.2.2.2.2.2.2.2.2.2.2.1 }} +
              x.2.2.2.2.1),
        Unification.Unifier.bind fun (x : ℕ × Bool × German.Oids × German.Oids × ℕ × German.Cmd × ℕ × German.Items) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, German.CacheState.invalid, German.Gnt.noGnt, German.Ack.invAck,
              {German.Item.dir
                    { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.1}, inv := ∅ }} +
                x.2.2.2.2.2.2.2),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.1, German.Req.reqS,
            {German.Item.dir
                  { cmd := German.Cmd.idle, ptr := x.1, exGntd := x.2.1, shr := x.2.2.1, inv := x.2.2.2.1 }} +
              x.2.2.2.2.2.2.2),
        Unification.Unifier.bind
          fun (x : ℕ × German.CacheState × German.Gnt × German.Ack × ℕ × German.Req × ℕ × German.Items) =>
          ((x.2.2.2.2.2.2.1, true, {x.2.2.2.2.1}, ∅, x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {German.Item.cache
                    { id := x.2.2.2.2.1, state := German.CacheState.invalid, ch1 := x.2.2.2.2.2.1,
                      ch2 := German.Gnt.noGnt, ch3 := German.Ack.invAck }} +
                x.2.2.2.2.2.2.2),
            German.Cmd.idle, x.2.2.2.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
            {German.Item.cache
                  { id := x.1, state := x.2.1, ch1 := German.Req.reqS, ch2 := x.2.2.1, ch3 := x.2.2.2.1 }} +
              x.2.2.2.2.2.2.2),
        Unification.Unifier.bind fun (x : German.Items × ℕ × ℕ) =>
          ((x.2.2, true, {x.2.1}, ∅, x.2.1, German.CacheState.invalid, German.Gnt.noGnt, German.Ack.invAck, x.1),
            German.Cmd.idle, x.2.2, x.2.1, German.Req.reqS, x.1)] := by
  udf_certify

theorem German.recvReqS_inv.obligation_10 :
    Unification.sound (Narrowing.mayFire German.recvReqS German.ownAck)
      [Unification.Unifier.bind
          fun
            (x :
              ℕ ×
                German.Req ×
                  German.Cmd ×
                    ℕ ×
                      German.Items ×
                        German.CacheState × German.Gnt × German.Ack × ℕ × Bool × German.Oids × German.Oids × ℕ) =>
          ((x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.1, x.1,
              x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1,
              {German.Item.cache
                      { id := x.2.2.2.2.2.2.2.2.2.2.2.2, state := German.CacheState.invalid, ch1 := x.2.1,
                        ch2 := German.Gnt.noGnt, ch3 := German.Ack.invAck }} +
                  {German.Item.dir
                      { cmd := x.2.2.1, ptr := x.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.2.2.2.2},
                        inv := ∅ }} +
                x.2.2.2.2.1),
            x.2.2.1, x.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2, x.2.1,
            {German.Item.cache
                    { id := x.1, state := x.2.2.2.2.2.1, ch1 := German.Req.reqS, ch2 := x.2.2.2.2.2.2.1,
                      ch3 := x.2.2.2.2.2.2.2.1 }} +
                {German.Item.dir
                    { cmd := German.Cmd.idle, ptr := x.2.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.2.1,
                      shr := x.2.2.2.2.2.2.2.2.2.2.1, inv := x.2.2.2.2.2.2.2.2.2.2.2.1 }} +
              x.2.2.2.2.1),
        Unification.Unifier.bind fun (x : ℕ × Bool × German.Oids × German.Oids × ℕ × German.Cmd × ℕ × German.Items) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, German.CacheState.invalid, German.Gnt.noGnt, German.Ack.invAck,
              {German.Item.dir
                    { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.1}, inv := ∅ }} +
                x.2.2.2.2.2.2.2),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.1, German.Req.reqS,
            {German.Item.dir
                  { cmd := German.Cmd.idle, ptr := x.1, exGntd := x.2.1, shr := x.2.2.1, inv := x.2.2.2.1 }} +
              x.2.2.2.2.2.2.2),
        Unification.Unifier.bind
          fun (x : ℕ × German.CacheState × German.Gnt × German.Ack × ℕ × German.Req × ℕ × German.Items) =>
          ((x.2.2.2.2.2.2.1, true, {x.2.2.2.2.1}, ∅, x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {German.Item.cache
                    { id := x.2.2.2.2.1, state := German.CacheState.invalid, ch1 := x.2.2.2.2.2.1,
                      ch2 := German.Gnt.noGnt, ch3 := German.Ack.invAck }} +
                x.2.2.2.2.2.2.2),
            German.Cmd.idle, x.2.2.2.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
            {German.Item.cache
                  { id := x.1, state := x.2.1, ch1 := German.Req.reqS, ch2 := x.2.2.1, ch3 := x.2.2.2.1 }} +
              x.2.2.2.2.2.2.2),
        Unification.Unifier.bind fun (x : German.Items × ℕ × ℕ) =>
          ((x.2.2, true, {x.2.1}, ∅, x.2.1, German.CacheState.invalid, German.Gnt.noGnt, German.Ack.invAck, x.1),
            German.Cmd.idle, x.2.2, x.2.1, German.Req.reqS, x.1)] := by
  -- each unifier, instantiated, solves the problem
  simp only [sound, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  repeat' apply And.intro
  all_goals
    rintro γ ⟨x, rfl⟩
    simp only [unifiedBy, Narrowing.mayFire, German.recvReqS, German.ownAck]
  all_goals first
    | rfl
    | ac_rfl
    | simp only [ACU.plus_unit, ACU.unit_plus, ACU.plus_comm, ACU.plus_left_comm, ACU.plus_assoc]

theorem German.recvReqE_inv.obligation_1 :
    Unification.complete (Narrowing.mayFire German.recvReqE German.freeP)
      [Unification.Unifier.bind
          fun
            (x :
              ℕ ×
                ℕ ×
                  German.Oids ×
                    German.Oids ×
                      German.Items ×
                        German.CacheState ×
                          German.Gnt × German.Ack × ℕ × Bool × German.Oids × German.Oids × German.Cmd) =>
          ((x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.1, x.1,
              x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1,
              {German.Item.dir
                    { cmd := x.2.2.2.2.2.2.2.2.2.2.2.2, ptr := x.2.1, exGntd := false, shr := x.2.2.1,
                      inv := x.2.2.2.1 }} +
                x.2.2.2.2.1),
            x.2.2.2.2.2.2.2.2.2.2.2.2, x.2.1, x.2.2.1, x.2.2.2.1,
            {German.Item.cache
                    { id := x.1, state := x.2.2.2.2.2.1, ch1 := German.Req.reqE, ch2 := x.2.2.2.2.2.2.1,
                      ch3 := x.2.2.2.2.2.2.2.1 }} +
                {German.Item.dir
                    { cmd := German.Cmd.idle, ptr := x.2.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.2.1,
                      shr := x.2.2.2.2.2.2.2.2.2.2.1, inv := x.2.2.2.2.2.2.2.2.2.2.2.1 }} +
              x.2.2.2.2.1),
        Unification.Unifier.bind
          fun (x : German.Items × ℕ × German.CacheState × German.Gnt × German.Ack × ℕ × German.Oids × German.Oids) =>
          ((x.2.2.2.2.2.1, false, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.1),
            German.Cmd.idle, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2,
            {German.Item.cache
                  { id := x.2.1, state := x.2.2.1, ch1 := German.Req.reqE, ch2 := x.2.2.2.1, ch3 := x.2.2.2.2.1 }} +
              x.1)] := by
  udf_certify

theorem German.recvReqE_inv.obligation_2 :
    Unification.sound (Narrowing.mayFire German.recvReqE German.freeP)
      [Unification.Unifier.bind
          fun
            (x :
              ℕ ×
                ℕ ×
                  German.Oids ×
                    German.Oids ×
                      German.Items ×
                        German.CacheState ×
                          German.Gnt × German.Ack × ℕ × Bool × German.Oids × German.Oids × German.Cmd) =>
          ((x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.1, x.1,
              x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1,
              {German.Item.dir
                    { cmd := x.2.2.2.2.2.2.2.2.2.2.2.2, ptr := x.2.1, exGntd := false, shr := x.2.2.1,
                      inv := x.2.2.2.1 }} +
                x.2.2.2.2.1),
            x.2.2.2.2.2.2.2.2.2.2.2.2, x.2.1, x.2.2.1, x.2.2.2.1,
            {German.Item.cache
                    { id := x.1, state := x.2.2.2.2.2.1, ch1 := German.Req.reqE, ch2 := x.2.2.2.2.2.2.1,
                      ch3 := x.2.2.2.2.2.2.2.1 }} +
                {German.Item.dir
                    { cmd := German.Cmd.idle, ptr := x.2.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.2.1,
                      shr := x.2.2.2.2.2.2.2.2.2.2.1, inv := x.2.2.2.2.2.2.2.2.2.2.2.1 }} +
              x.2.2.2.2.1),
        Unification.Unifier.bind
          fun (x : German.Items × ℕ × German.CacheState × German.Gnt × German.Ack × ℕ × German.Oids × German.Oids) =>
          ((x.2.2.2.2.2.1, false, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.1),
            German.Cmd.idle, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2,
            {German.Item.cache
                  { id := x.2.1, state := x.2.2.1, ch1 := German.Req.reqE, ch2 := x.2.2.2.1, ch3 := x.2.2.2.2.1 }} +
              x.1)] := by
  -- each unifier, instantiated, solves the problem
  simp only [sound, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  repeat' apply And.intro
  all_goals
    rintro γ ⟨x, rfl⟩
    simp only [unifiedBy, Narrowing.mayFire, German.recvReqE, German.freeP]
  all_goals first
    | rfl
    | ac_rfl
    | simp only [ACU.plus_unit, ACU.unit_plus, ACU.plus_comm, ACU.plus_left_comm, ACU.plus_assoc]

theorem German.recvReqE_inv.obligation_3 :
    Unification.complete (Narrowing.mayFire German.recvReqE German.ownE)
      [Unification.Unifier.bind
          fun
            (x :
              ℕ ×
                German.Req ×
                  German.Cmd ×
                    ℕ ×
                      German.Oids ×
                        German.Items ×
                          German.CacheState × German.Gnt × German.Ack × ℕ × Bool × German.Oids × German.Oids × ℕ) =>
          ((x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2.1, x.1,
              x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1,
              {German.Item.cache
                      { id := x.2.2.2.2.2.2.2.2.2.2.2.2.2, state := German.CacheState.exclusive, ch1 := x.2.1,
                        ch2 := German.Gnt.noGnt, ch3 := German.Ack.noAck }} +
                  {German.Item.dir
                      { cmd := x.2.2.1, ptr := x.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.2.2.2.2.2},
                        inv := x.2.2.2.2.1 }} +
                x.2.2.2.2.2.1),
            x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2.2, x.2.1,
            {German.Item.cache
                    { id := x.1, state := x.2.2.2.2.2.2.1, ch1 := German.Req.reqE, ch2 := x.2.2.2.2.2.2.2.1,
                      ch3 := x.2.2.2.2.2.2.2.2.1 }} +
                {German.Item.dir
                    { cmd := German.Cmd.idle, ptr := x.2.2.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.2.2.1,
                      shr := x.2.2.2.2.2.2.2.2.2.2.2.1, inv := x.2.2.2.2.2.2.2.2.2.2.2.2.1 }} +
              x.2.2.2.2.2.1),
        Unification.Unifier.bind
          fun (x : ℕ × Bool × German.Oids × German.Oids × ℕ × German.Cmd × ℕ × German.Oids × German.Items) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, German.CacheState.exclusive, German.Gnt.noGnt,
              German.Ack.noAck,
              {German.Item.dir
                    { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.1},
                      inv := x.2.2.2.2.2.2.2.1 }} +
                x.2.2.2.2.2.2.2.2),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.1, German.Req.reqE,
            {German.Item.dir
                  { cmd := German.Cmd.idle, ptr := x.1, exGntd := x.2.1, shr := x.2.2.1, inv := x.2.2.2.1 }} +
              x.2.2.2.2.2.2.2.2),
        Unification.Unifier.bind
          fun (x : ℕ × German.CacheState × German.Gnt × German.Ack × ℕ × German.Req × ℕ × German.Oids × German.Items) =>
          ((x.2.2.2.2.2.2.1, true, {x.2.2.2.2.1}, x.2.2.2.2.2.2.2.1, x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {German.Item.cache
                    { id := x.2.2.2.2.1, state := German.CacheState.exclusive, ch1 := x.2.2.2.2.2.1,
                      ch2 := German.Gnt.noGnt, ch3 := German.Ack.noAck }} +
                x.2.2.2.2.2.2.2.2),
            German.Cmd.idle, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
            {German.Item.cache
                  { id := x.1, state := x.2.1, ch1 := German.Req.reqE, ch2 := x.2.2.1, ch3 := x.2.2.2.1 }} +
              x.2.2.2.2.2.2.2.2),
        Unification.Unifier.bind fun (x : German.Items × ℕ × ℕ × German.Oids) =>
          ((x.2.2.1, true, {x.2.1}, x.2.2.2, x.2.1, German.CacheState.exclusive, German.Gnt.noGnt, German.Ack.noAck,
              x.1),
            German.Cmd.idle, x.2.2.1, x.2.2.2, x.2.1, German.Req.reqE, x.1)] := by
  udf_certify

theorem German.recvReqE_inv.obligation_4 :
    Unification.sound (Narrowing.mayFire German.recvReqE German.ownE)
      [Unification.Unifier.bind
          fun
            (x :
              ℕ ×
                German.Req ×
                  German.Cmd ×
                    ℕ ×
                      German.Oids ×
                        German.Items ×
                          German.CacheState × German.Gnt × German.Ack × ℕ × Bool × German.Oids × German.Oids × ℕ) =>
          ((x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2.1, x.1,
              x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1,
              {German.Item.cache
                      { id := x.2.2.2.2.2.2.2.2.2.2.2.2.2, state := German.CacheState.exclusive, ch1 := x.2.1,
                        ch2 := German.Gnt.noGnt, ch3 := German.Ack.noAck }} +
                  {German.Item.dir
                      { cmd := x.2.2.1, ptr := x.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.2.2.2.2.2},
                        inv := x.2.2.2.2.1 }} +
                x.2.2.2.2.2.1),
            x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2.2, x.2.1,
            {German.Item.cache
                    { id := x.1, state := x.2.2.2.2.2.2.1, ch1 := German.Req.reqE, ch2 := x.2.2.2.2.2.2.2.1,
                      ch3 := x.2.2.2.2.2.2.2.2.1 }} +
                {German.Item.dir
                    { cmd := German.Cmd.idle, ptr := x.2.2.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.2.2.1,
                      shr := x.2.2.2.2.2.2.2.2.2.2.2.1, inv := x.2.2.2.2.2.2.2.2.2.2.2.2.1 }} +
              x.2.2.2.2.2.1),
        Unification.Unifier.bind
          fun (x : ℕ × Bool × German.Oids × German.Oids × ℕ × German.Cmd × ℕ × German.Oids × German.Items) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, German.CacheState.exclusive, German.Gnt.noGnt,
              German.Ack.noAck,
              {German.Item.dir
                    { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.1},
                      inv := x.2.2.2.2.2.2.2.1 }} +
                x.2.2.2.2.2.2.2.2),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.1, German.Req.reqE,
            {German.Item.dir
                  { cmd := German.Cmd.idle, ptr := x.1, exGntd := x.2.1, shr := x.2.2.1, inv := x.2.2.2.1 }} +
              x.2.2.2.2.2.2.2.2),
        Unification.Unifier.bind
          fun (x : ℕ × German.CacheState × German.Gnt × German.Ack × ℕ × German.Req × ℕ × German.Oids × German.Items) =>
          ((x.2.2.2.2.2.2.1, true, {x.2.2.2.2.1}, x.2.2.2.2.2.2.2.1, x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {German.Item.cache
                    { id := x.2.2.2.2.1, state := German.CacheState.exclusive, ch1 := x.2.2.2.2.2.1,
                      ch2 := German.Gnt.noGnt, ch3 := German.Ack.noAck }} +
                x.2.2.2.2.2.2.2.2),
            German.Cmd.idle, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
            {German.Item.cache
                  { id := x.1, state := x.2.1, ch1 := German.Req.reqE, ch2 := x.2.2.1, ch3 := x.2.2.2.1 }} +
              x.2.2.2.2.2.2.2.2),
        Unification.Unifier.bind fun (x : German.Items × ℕ × ℕ × German.Oids) =>
          ((x.2.2.1, true, {x.2.1}, x.2.2.2, x.2.1, German.CacheState.exclusive, German.Gnt.noGnt, German.Ack.noAck,
              x.1),
            German.Cmd.idle, x.2.2.1, x.2.2.2, x.2.1, German.Req.reqE, x.1)] := by
  -- each unifier, instantiated, solves the problem
  simp only [sound, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  repeat' apply And.intro
  all_goals
    rintro γ ⟨x, rfl⟩
    simp only [unifiedBy, Narrowing.mayFire, German.recvReqE, German.ownE]
  all_goals first
    | rfl
    | ac_rfl
    | simp only [ACU.plus_unit, ACU.unit_plus, ACU.plus_comm, ACU.plus_left_comm, ACU.plus_assoc]

theorem German.recvReqE_inv.obligation_5 :
    Unification.complete (Narrowing.mayFire German.recvReqE German.ownG)
      [Unification.Unifier.bind
          fun
            (x :
              ℕ ×
                German.Req ×
                  German.Cmd ×
                    ℕ ×
                      German.Oids ×
                        German.Items ×
                          German.CacheState × German.Gnt × German.Ack × ℕ × Bool × German.Oids × German.Oids × ℕ) =>
          ((x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2.1, x.1,
              x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1,
              {German.Item.cache
                      { id := x.2.2.2.2.2.2.2.2.2.2.2.2.2, state := German.CacheState.invalid, ch1 := x.2.1,
                        ch2 := German.Gnt.gntE, ch3 := German.Ack.noAck }} +
                  {German.Item.dir
                      { cmd := x.2.2.1, ptr := x.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.2.2.2.2.2},
                        inv := x.2.2.2.2.1 }} +
                x.2.2.2.2.2.1),
            x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2.2, x.2.1,
            {German.Item.cache
                    { id := x.1, state := x.2.2.2.2.2.2.1, ch1 := German.Req.reqE, ch2 := x.2.2.2.2.2.2.2.1,
                      ch3 := x.2.2.2.2.2.2.2.2.1 }} +
                {German.Item.dir
                    { cmd := German.Cmd.idle, ptr := x.2.2.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.2.2.1,
                      shr := x.2.2.2.2.2.2.2.2.2.2.2.1, inv := x.2.2.2.2.2.2.2.2.2.2.2.2.1 }} +
              x.2.2.2.2.2.1),
        Unification.Unifier.bind
          fun (x : ℕ × Bool × German.Oids × German.Oids × ℕ × German.Cmd × ℕ × German.Oids × German.Items) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, German.CacheState.invalid, German.Gnt.gntE, German.Ack.noAck,
              {German.Item.dir
                    { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.1},
                      inv := x.2.2.2.2.2.2.2.1 }} +
                x.2.2.2.2.2.2.2.2),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.1, German.Req.reqE,
            {German.Item.dir
                  { cmd := German.Cmd.idle, ptr := x.1, exGntd := x.2.1, shr := x.2.2.1, inv := x.2.2.2.1 }} +
              x.2.2.2.2.2.2.2.2),
        Unification.Unifier.bind
          fun (x : ℕ × German.CacheState × German.Gnt × German.Ack × ℕ × German.Req × ℕ × German.Oids × German.Items) =>
          ((x.2.2.2.2.2.2.1, true, {x.2.2.2.2.1}, x.2.2.2.2.2.2.2.1, x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {German.Item.cache
                    { id := x.2.2.2.2.1, state := German.CacheState.invalid, ch1 := x.2.2.2.2.2.1,
                      ch2 := German.Gnt.gntE, ch3 := German.Ack.noAck }} +
                x.2.2.2.2.2.2.2.2),
            German.Cmd.idle, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
            {German.Item.cache
                  { id := x.1, state := x.2.1, ch1 := German.Req.reqE, ch2 := x.2.2.1, ch3 := x.2.2.2.1 }} +
              x.2.2.2.2.2.2.2.2),
        Unification.Unifier.bind fun (x : German.Items × ℕ × ℕ × German.Oids) =>
          ((x.2.2.1, true, {x.2.1}, x.2.2.2, x.2.1, German.CacheState.invalid, German.Gnt.gntE, German.Ack.noAck, x.1),
            German.Cmd.idle, x.2.2.1, x.2.2.2, x.2.1, German.Req.reqE, x.1)] := by
  udf_certify

theorem German.recvReqE_inv.obligation_6 :
    Unification.sound (Narrowing.mayFire German.recvReqE German.ownG)
      [Unification.Unifier.bind
          fun
            (x :
              ℕ ×
                German.Req ×
                  German.Cmd ×
                    ℕ ×
                      German.Oids ×
                        German.Items ×
                          German.CacheState × German.Gnt × German.Ack × ℕ × Bool × German.Oids × German.Oids × ℕ) =>
          ((x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2.1, x.1,
              x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1,
              {German.Item.cache
                      { id := x.2.2.2.2.2.2.2.2.2.2.2.2.2, state := German.CacheState.invalid, ch1 := x.2.1,
                        ch2 := German.Gnt.gntE, ch3 := German.Ack.noAck }} +
                  {German.Item.dir
                      { cmd := x.2.2.1, ptr := x.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.2.2.2.2.2},
                        inv := x.2.2.2.2.1 }} +
                x.2.2.2.2.2.1),
            x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2.2, x.2.1,
            {German.Item.cache
                    { id := x.1, state := x.2.2.2.2.2.2.1, ch1 := German.Req.reqE, ch2 := x.2.2.2.2.2.2.2.1,
                      ch3 := x.2.2.2.2.2.2.2.2.1 }} +
                {German.Item.dir
                    { cmd := German.Cmd.idle, ptr := x.2.2.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.2.2.1,
                      shr := x.2.2.2.2.2.2.2.2.2.2.2.1, inv := x.2.2.2.2.2.2.2.2.2.2.2.2.1 }} +
              x.2.2.2.2.2.1),
        Unification.Unifier.bind
          fun (x : ℕ × Bool × German.Oids × German.Oids × ℕ × German.Cmd × ℕ × German.Oids × German.Items) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, German.CacheState.invalid, German.Gnt.gntE, German.Ack.noAck,
              {German.Item.dir
                    { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.1},
                      inv := x.2.2.2.2.2.2.2.1 }} +
                x.2.2.2.2.2.2.2.2),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.1, German.Req.reqE,
            {German.Item.dir
                  { cmd := German.Cmd.idle, ptr := x.1, exGntd := x.2.1, shr := x.2.2.1, inv := x.2.2.2.1 }} +
              x.2.2.2.2.2.2.2.2),
        Unification.Unifier.bind
          fun (x : ℕ × German.CacheState × German.Gnt × German.Ack × ℕ × German.Req × ℕ × German.Oids × German.Items) =>
          ((x.2.2.2.2.2.2.1, true, {x.2.2.2.2.1}, x.2.2.2.2.2.2.2.1, x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {German.Item.cache
                    { id := x.2.2.2.2.1, state := German.CacheState.invalid, ch1 := x.2.2.2.2.2.1,
                      ch2 := German.Gnt.gntE, ch3 := German.Ack.noAck }} +
                x.2.2.2.2.2.2.2.2),
            German.Cmd.idle, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
            {German.Item.cache
                  { id := x.1, state := x.2.1, ch1 := German.Req.reqE, ch2 := x.2.2.1, ch3 := x.2.2.2.1 }} +
              x.2.2.2.2.2.2.2.2),
        Unification.Unifier.bind fun (x : German.Items × ℕ × ℕ × German.Oids) =>
          ((x.2.2.1, true, {x.2.1}, x.2.2.2, x.2.1, German.CacheState.invalid, German.Gnt.gntE, German.Ack.noAck, x.1),
            German.Cmd.idle, x.2.2.1, x.2.2.2, x.2.1, German.Req.reqE, x.1)] := by
  -- each unifier, instantiated, solves the problem
  simp only [sound, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  repeat' apply And.intro
  all_goals
    rintro γ ⟨x, rfl⟩
    simp only [unifiedBy, Narrowing.mayFire, German.recvReqE, German.ownG]
  all_goals first
    | rfl
    | ac_rfl
    | simp only [ACU.plus_unit, ACU.unit_plus, ACU.plus_comm, ACU.plus_left_comm, ACU.plus_assoc]

theorem German.recvReqE_inv.obligation_7 :
    Unification.complete (Narrowing.mayFire German.recvReqE German.ownInv)
      [Unification.Unifier.bind
          fun
            (x :
              ℕ ×
                German.Req ×
                  German.Cmd ×
                    ℕ ×
                      German.Items ×
                        German.CacheState × German.Gnt × German.Ack × ℕ × Bool × German.Oids × German.Oids × ℕ) =>
          ((x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.1, x.1,
              x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1,
              {German.Item.cache
                      { id := x.2.2.2.2.2.2.2.2.2.2.2.2, state := German.CacheState.exclusive, ch1 := x.2.1,
                        ch2 := German.Gnt.inv, ch3 := German.Ack.noAck }} +
                  {German.Item.dir
                      { cmd := x.2.2.1, ptr := x.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.2.2.2.2},
                        inv := ∅ }} +
                x.2.2.2.2.1),
            x.2.2.1, x.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2, x.2.1,
            {German.Item.cache
                    { id := x.1, state := x.2.2.2.2.2.1, ch1 := German.Req.reqE, ch2 := x.2.2.2.2.2.2.1,
                      ch3 := x.2.2.2.2.2.2.2.1 }} +
                {German.Item.dir
                    { cmd := German.Cmd.idle, ptr := x.2.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.2.1,
                      shr := x.2.2.2.2.2.2.2.2.2.2.1, inv := x.2.2.2.2.2.2.2.2.2.2.2.1 }} +
              x.2.2.2.2.1),
        Unification.Unifier.bind fun (x : ℕ × Bool × German.Oids × German.Oids × ℕ × German.Cmd × ℕ × German.Items) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, German.CacheState.exclusive, German.Gnt.inv, German.Ack.noAck,
              {German.Item.dir
                    { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.1}, inv := ∅ }} +
                x.2.2.2.2.2.2.2),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.1, German.Req.reqE,
            {German.Item.dir
                  { cmd := German.Cmd.idle, ptr := x.1, exGntd := x.2.1, shr := x.2.2.1, inv := x.2.2.2.1 }} +
              x.2.2.2.2.2.2.2),
        Unification.Unifier.bind
          fun (x : ℕ × German.CacheState × German.Gnt × German.Ack × ℕ × German.Req × ℕ × German.Items) =>
          ((x.2.2.2.2.2.2.1, true, {x.2.2.2.2.1}, ∅, x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {German.Item.cache
                    { id := x.2.2.2.2.1, state := German.CacheState.exclusive, ch1 := x.2.2.2.2.2.1,
                      ch2 := German.Gnt.inv, ch3 := German.Ack.noAck }} +
                x.2.2.2.2.2.2.2),
            German.Cmd.idle, x.2.2.2.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
            {German.Item.cache
                  { id := x.1, state := x.2.1, ch1 := German.Req.reqE, ch2 := x.2.2.1, ch3 := x.2.2.2.1 }} +
              x.2.2.2.2.2.2.2),
        Unification.Unifier.bind fun (x : German.Items × ℕ × ℕ) =>
          ((x.2.2, true, {x.2.1}, ∅, x.2.1, German.CacheState.exclusive, German.Gnt.inv, German.Ack.noAck, x.1),
            German.Cmd.idle, x.2.2, x.2.1, German.Req.reqE, x.1)] := by
  udf_certify

theorem German.recvReqE_inv.obligation_8 :
    Unification.sound (Narrowing.mayFire German.recvReqE German.ownInv)
      [Unification.Unifier.bind
          fun
            (x :
              ℕ ×
                German.Req ×
                  German.Cmd ×
                    ℕ ×
                      German.Items ×
                        German.CacheState × German.Gnt × German.Ack × ℕ × Bool × German.Oids × German.Oids × ℕ) =>
          ((x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.1, x.1,
              x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1,
              {German.Item.cache
                      { id := x.2.2.2.2.2.2.2.2.2.2.2.2, state := German.CacheState.exclusive, ch1 := x.2.1,
                        ch2 := German.Gnt.inv, ch3 := German.Ack.noAck }} +
                  {German.Item.dir
                      { cmd := x.2.2.1, ptr := x.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.2.2.2.2},
                        inv := ∅ }} +
                x.2.2.2.2.1),
            x.2.2.1, x.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2, x.2.1,
            {German.Item.cache
                    { id := x.1, state := x.2.2.2.2.2.1, ch1 := German.Req.reqE, ch2 := x.2.2.2.2.2.2.1,
                      ch3 := x.2.2.2.2.2.2.2.1 }} +
                {German.Item.dir
                    { cmd := German.Cmd.idle, ptr := x.2.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.2.1,
                      shr := x.2.2.2.2.2.2.2.2.2.2.1, inv := x.2.2.2.2.2.2.2.2.2.2.2.1 }} +
              x.2.2.2.2.1),
        Unification.Unifier.bind fun (x : ℕ × Bool × German.Oids × German.Oids × ℕ × German.Cmd × ℕ × German.Items) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, German.CacheState.exclusive, German.Gnt.inv, German.Ack.noAck,
              {German.Item.dir
                    { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.1}, inv := ∅ }} +
                x.2.2.2.2.2.2.2),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.1, German.Req.reqE,
            {German.Item.dir
                  { cmd := German.Cmd.idle, ptr := x.1, exGntd := x.2.1, shr := x.2.2.1, inv := x.2.2.2.1 }} +
              x.2.2.2.2.2.2.2),
        Unification.Unifier.bind
          fun (x : ℕ × German.CacheState × German.Gnt × German.Ack × ℕ × German.Req × ℕ × German.Items) =>
          ((x.2.2.2.2.2.2.1, true, {x.2.2.2.2.1}, ∅, x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {German.Item.cache
                    { id := x.2.2.2.2.1, state := German.CacheState.exclusive, ch1 := x.2.2.2.2.2.1,
                      ch2 := German.Gnt.inv, ch3 := German.Ack.noAck }} +
                x.2.2.2.2.2.2.2),
            German.Cmd.idle, x.2.2.2.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
            {German.Item.cache
                  { id := x.1, state := x.2.1, ch1 := German.Req.reqE, ch2 := x.2.2.1, ch3 := x.2.2.2.1 }} +
              x.2.2.2.2.2.2.2),
        Unification.Unifier.bind fun (x : German.Items × ℕ × ℕ) =>
          ((x.2.2, true, {x.2.1}, ∅, x.2.1, German.CacheState.exclusive, German.Gnt.inv, German.Ack.noAck, x.1),
            German.Cmd.idle, x.2.2, x.2.1, German.Req.reqE, x.1)] := by
  -- each unifier, instantiated, solves the problem
  simp only [sound, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  repeat' apply And.intro
  all_goals
    rintro γ ⟨x, rfl⟩
    simp only [unifiedBy, Narrowing.mayFire, German.recvReqE, German.ownInv]
  all_goals first
    | rfl
    | ac_rfl
    | simp only [ACU.plus_unit, ACU.unit_plus, ACU.plus_comm, ACU.plus_left_comm, ACU.plus_assoc]

theorem German.recvReqE_inv.obligation_9 :
    Unification.complete (Narrowing.mayFire German.recvReqE German.ownAck)
      [Unification.Unifier.bind
          fun
            (x :
              ℕ ×
                German.Req ×
                  German.Cmd ×
                    ℕ ×
                      German.Items ×
                        German.CacheState × German.Gnt × German.Ack × ℕ × Bool × German.Oids × German.Oids × ℕ) =>
          ((x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.1, x.1,
              x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1,
              {German.Item.cache
                      { id := x.2.2.2.2.2.2.2.2.2.2.2.2, state := German.CacheState.invalid, ch1 := x.2.1,
                        ch2 := German.Gnt.noGnt, ch3 := German.Ack.invAck }} +
                  {German.Item.dir
                      { cmd := x.2.2.1, ptr := x.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.2.2.2.2},
                        inv := ∅ }} +
                x.2.2.2.2.1),
            x.2.2.1, x.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2, x.2.1,
            {German.Item.cache
                    { id := x.1, state := x.2.2.2.2.2.1, ch1 := German.Req.reqE, ch2 := x.2.2.2.2.2.2.1,
                      ch3 := x.2.2.2.2.2.2.2.1 }} +
                {German.Item.dir
                    { cmd := German.Cmd.idle, ptr := x.2.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.2.1,
                      shr := x.2.2.2.2.2.2.2.2.2.2.1, inv := x.2.2.2.2.2.2.2.2.2.2.2.1 }} +
              x.2.2.2.2.1),
        Unification.Unifier.bind fun (x : ℕ × Bool × German.Oids × German.Oids × ℕ × German.Cmd × ℕ × German.Items) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, German.CacheState.invalid, German.Gnt.noGnt, German.Ack.invAck,
              {German.Item.dir
                    { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.1}, inv := ∅ }} +
                x.2.2.2.2.2.2.2),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.1, German.Req.reqE,
            {German.Item.dir
                  { cmd := German.Cmd.idle, ptr := x.1, exGntd := x.2.1, shr := x.2.2.1, inv := x.2.2.2.1 }} +
              x.2.2.2.2.2.2.2),
        Unification.Unifier.bind
          fun (x : ℕ × German.CacheState × German.Gnt × German.Ack × ℕ × German.Req × ℕ × German.Items) =>
          ((x.2.2.2.2.2.2.1, true, {x.2.2.2.2.1}, ∅, x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {German.Item.cache
                    { id := x.2.2.2.2.1, state := German.CacheState.invalid, ch1 := x.2.2.2.2.2.1,
                      ch2 := German.Gnt.noGnt, ch3 := German.Ack.invAck }} +
                x.2.2.2.2.2.2.2),
            German.Cmd.idle, x.2.2.2.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
            {German.Item.cache
                  { id := x.1, state := x.2.1, ch1 := German.Req.reqE, ch2 := x.2.2.1, ch3 := x.2.2.2.1 }} +
              x.2.2.2.2.2.2.2),
        Unification.Unifier.bind fun (x : German.Items × ℕ × ℕ) =>
          ((x.2.2, true, {x.2.1}, ∅, x.2.1, German.CacheState.invalid, German.Gnt.noGnt, German.Ack.invAck, x.1),
            German.Cmd.idle, x.2.2, x.2.1, German.Req.reqE, x.1)] := by
  udf_certify

theorem German.recvReqE_inv.obligation_10 :
    Unification.sound (Narrowing.mayFire German.recvReqE German.ownAck)
      [Unification.Unifier.bind
          fun
            (x :
              ℕ ×
                German.Req ×
                  German.Cmd ×
                    ℕ ×
                      German.Items ×
                        German.CacheState × German.Gnt × German.Ack × ℕ × Bool × German.Oids × German.Oids × ℕ) =>
          ((x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.1, x.1,
              x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1,
              {German.Item.cache
                      { id := x.2.2.2.2.2.2.2.2.2.2.2.2, state := German.CacheState.invalid, ch1 := x.2.1,
                        ch2 := German.Gnt.noGnt, ch3 := German.Ack.invAck }} +
                  {German.Item.dir
                      { cmd := x.2.2.1, ptr := x.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.2.2.2.2},
                        inv := ∅ }} +
                x.2.2.2.2.1),
            x.2.2.1, x.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2, x.2.1,
            {German.Item.cache
                    { id := x.1, state := x.2.2.2.2.2.1, ch1 := German.Req.reqE, ch2 := x.2.2.2.2.2.2.1,
                      ch3 := x.2.2.2.2.2.2.2.1 }} +
                {German.Item.dir
                    { cmd := German.Cmd.idle, ptr := x.2.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.2.1,
                      shr := x.2.2.2.2.2.2.2.2.2.2.1, inv := x.2.2.2.2.2.2.2.2.2.2.2.1 }} +
              x.2.2.2.2.1),
        Unification.Unifier.bind fun (x : ℕ × Bool × German.Oids × German.Oids × ℕ × German.Cmd × ℕ × German.Items) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, German.CacheState.invalid, German.Gnt.noGnt, German.Ack.invAck,
              {German.Item.dir
                    { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.1}, inv := ∅ }} +
                x.2.2.2.2.2.2.2),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.1, German.Req.reqE,
            {German.Item.dir
                  { cmd := German.Cmd.idle, ptr := x.1, exGntd := x.2.1, shr := x.2.2.1, inv := x.2.2.2.1 }} +
              x.2.2.2.2.2.2.2),
        Unification.Unifier.bind
          fun (x : ℕ × German.CacheState × German.Gnt × German.Ack × ℕ × German.Req × ℕ × German.Items) =>
          ((x.2.2.2.2.2.2.1, true, {x.2.2.2.2.1}, ∅, x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {German.Item.cache
                    { id := x.2.2.2.2.1, state := German.CacheState.invalid, ch1 := x.2.2.2.2.2.1,
                      ch2 := German.Gnt.noGnt, ch3 := German.Ack.invAck }} +
                x.2.2.2.2.2.2.2),
            German.Cmd.idle, x.2.2.2.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
            {German.Item.cache
                  { id := x.1, state := x.2.1, ch1 := German.Req.reqE, ch2 := x.2.2.1, ch3 := x.2.2.2.1 }} +
              x.2.2.2.2.2.2.2),
        Unification.Unifier.bind fun (x : German.Items × ℕ × ℕ) =>
          ((x.2.2, true, {x.2.1}, ∅, x.2.1, German.CacheState.invalid, German.Gnt.noGnt, German.Ack.invAck, x.1),
            German.Cmd.idle, x.2.2, x.2.1, German.Req.reqE, x.1)] := by
  -- each unifier, instantiated, solves the problem
  simp only [sound, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  repeat' apply And.intro
  all_goals
    rintro γ ⟨x, rfl⟩
    simp only [unifiedBy, Narrowing.mayFire, German.recvReqE, German.ownAck]
  all_goals first
    | rfl
    | ac_rfl
    | simp only [ACU.plus_unit, ACU.unit_plus, ACU.plus_comm, ACU.plus_left_comm, ACU.plus_assoc]

theorem German.sendInvE_inv.obligation_1 :
    Unification.complete (Narrowing.mayFire German.sendInvE German.freeP)
      [Unification.Unifier.bind
          fun
            (x :
              ℕ ×
                ℕ ×
                  German.Oids ×
                    German.Oids ×
                      German.Items ×
                        German.CacheState ×
                          German.Req × German.Ack × ℕ × Bool × German.Oids × German.Oids × German.Cmd) =>
          ((x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.1, x.2.2.2.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1,
              {German.Item.dir
                    { cmd := x.2.2.2.2.2.2.2.2.2.2.2.2, ptr := x.2.1, exGntd := false, shr := x.2.2.1,
                      inv := x.2.2.2.1 }} +
                x.2.2.2.2.1),
            x.2.2.2.2.2.2.2.2.2.2.2.2, x.2.1, x.2.2.1, x.2.2.2.1,
            {German.Item.cache
                    { id := x.1, state := x.2.2.2.2.2.1, ch1 := x.2.2.2.2.2.2.1, ch2 := German.Gnt.noGnt,
                      ch3 := x.2.2.2.2.2.2.2.1 }} +
                {German.Item.dir
                    { cmd := German.Cmd.cmdE, ptr := x.2.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.2.1,
                      shr := x.2.2.2.2.2.2.2.2.2.2.1, inv := {x.1} + x.2.2.2.2.2.2.2.2.2.2.2.1 }} +
              x.2.2.2.2.1),
        Unification.Unifier.bind
          fun (x : German.Items × ℕ × German.CacheState × German.Req × German.Ack × German.Oids × ℕ × German.Oids) =>
          ((x.2.2.2.2.2.2.1, false, x.2.2.2.2.2.2.2, x.2.1, x.2.2.2.2.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.1),
            German.Cmd.cmdE, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2, {x.2.1} + x.2.2.2.2.2.1,
            {German.Item.cache
                  { id := x.2.1, state := x.2.2.1, ch1 := x.2.2.2.1, ch2 := German.Gnt.noGnt, ch3 := x.2.2.2.2.1 }} +
              x.1)] := by
  udf_certify

theorem German.sendInvE_inv.obligation_2 :
    Unification.sound (Narrowing.mayFire German.sendInvE German.freeP)
      [Unification.Unifier.bind
          fun
            (x :
              ℕ ×
                ℕ ×
                  German.Oids ×
                    German.Oids ×
                      German.Items ×
                        German.CacheState ×
                          German.Req × German.Ack × ℕ × Bool × German.Oids × German.Oids × German.Cmd) =>
          ((x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.1, x.2.2.2.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1,
              {German.Item.dir
                    { cmd := x.2.2.2.2.2.2.2.2.2.2.2.2, ptr := x.2.1, exGntd := false, shr := x.2.2.1,
                      inv := x.2.2.2.1 }} +
                x.2.2.2.2.1),
            x.2.2.2.2.2.2.2.2.2.2.2.2, x.2.1, x.2.2.1, x.2.2.2.1,
            {German.Item.cache
                    { id := x.1, state := x.2.2.2.2.2.1, ch1 := x.2.2.2.2.2.2.1, ch2 := German.Gnt.noGnt,
                      ch3 := x.2.2.2.2.2.2.2.1 }} +
                {German.Item.dir
                    { cmd := German.Cmd.cmdE, ptr := x.2.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.2.1,
                      shr := x.2.2.2.2.2.2.2.2.2.2.1, inv := {x.1} + x.2.2.2.2.2.2.2.2.2.2.2.1 }} +
              x.2.2.2.2.1),
        Unification.Unifier.bind
          fun (x : German.Items × ℕ × German.CacheState × German.Req × German.Ack × German.Oids × ℕ × German.Oids) =>
          ((x.2.2.2.2.2.2.1, false, x.2.2.2.2.2.2.2, x.2.1, x.2.2.2.2.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.1),
            German.Cmd.cmdE, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2, {x.2.1} + x.2.2.2.2.2.1,
            {German.Item.cache
                  { id := x.2.1, state := x.2.2.1, ch1 := x.2.2.2.1, ch2 := German.Gnt.noGnt, ch3 := x.2.2.2.2.1 }} +
              x.1)] := by
  -- each unifier, instantiated, solves the problem
  simp only [sound, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  repeat' apply And.intro
  all_goals
    rintro γ ⟨x, rfl⟩
    simp only [unifiedBy, Narrowing.mayFire, German.sendInvE, German.freeP]
  all_goals first
    | rfl
    | ac_rfl
    | simp only [ACU.plus_unit, ACU.unit_plus, ACU.plus_comm, ACU.plus_left_comm, ACU.plus_assoc]

theorem German.sendInvE_inv.obligation_3 :
    Unification.complete (Narrowing.mayFire German.sendInvE German.ownE)
      [Unification.Unifier.bind
          fun
            (x :
              ℕ ×
                German.Req ×
                  German.Cmd ×
                    ℕ ×
                      German.Oids ×
                        German.Items ×
                          German.CacheState × German.Req × German.Ack × ℕ × Bool × German.Oids × German.Oids × ℕ) =>
          ((x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.1, x.1, x.2.2.2.2.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1,
              {German.Item.cache
                      { id := x.2.2.2.2.2.2.2.2.2.2.2.2.2, state := German.CacheState.exclusive, ch1 := x.2.1,
                        ch2 := German.Gnt.noGnt, ch3 := German.Ack.noAck }} +
                  {German.Item.dir
                      { cmd := x.2.2.1, ptr := x.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.2.2.2.2.2},
                        inv := x.2.2.2.2.1 }} +
                x.2.2.2.2.2.1),
            x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2.2, x.2.1,
            {German.Item.cache
                    { id := x.1, state := x.2.2.2.2.2.2.1, ch1 := x.2.2.2.2.2.2.2.1, ch2 := German.Gnt.noGnt,
                      ch3 := x.2.2.2.2.2.2.2.2.1 }} +
                {German.Item.dir
                    { cmd := German.Cmd.cmdE, ptr := x.2.2.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.2.2.1,
                      shr := x.2.2.2.2.2.2.2.2.2.2.2.1, inv := {x.1} + x.2.2.2.2.2.2.2.2.2.2.2.2.1 }} +
              x.2.2.2.2.2.1),
        Unification.Unifier.bind
          fun
            (x : ℕ × German.Items × Bool × German.Oids × German.Oids × ℕ × German.Req × German.Cmd × ℕ × German.Oids) =>
          ((x.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.1, German.CacheState.exclusive, x.2.2.2.2.2.2.1,
              German.Ack.noAck,
              {German.Item.dir
                    { cmd := x.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.2.1},
                      inv := x.2.2.2.2.2.2.2.2.2 }} +
                x.2.1),
            x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
            {German.Item.dir
                  { cmd := German.Cmd.cmdE, ptr := x.1, exGntd := x.2.2.1, shr := x.2.2.2.1,
                    inv := x.2.2.2.2.1 + {x.2.2.2.2.2.1} }} +
              x.2.1),
        Unification.Unifier.bind
          fun (x : ℕ × German.CacheState × German.Req × German.Ack × German.Oids × ℕ × German.Req × ℕ × German.Items) =>
          ((x.2.2.2.2.2.2.2.1, true, {x.2.2.2.2.2.1}, x.1, x.2.2.2.2.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {German.Item.cache
                    { id := x.2.2.2.2.2.1, state := German.CacheState.exclusive, ch1 := x.2.2.2.2.2.2.1,
                      ch2 := German.Gnt.noGnt, ch3 := German.Ack.noAck }} +
                x.2.2.2.2.2.2.2.2),
            German.Cmd.cmdE, x.2.2.2.2.2.2.2.1, {x.1} + x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
            {German.Item.cache
                  { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := German.Gnt.noGnt, ch3 := x.2.2.2.1 }} +
              x.2.2.2.2.2.2.2.2),
        Unification.Unifier.bind fun (x : German.Oids × German.Items × ℕ × German.Req × ℕ) =>
          ((x.2.2.2.2, true, {x.2.2.1}, x.2.2.1, x.1, German.CacheState.exclusive, x.2.2.2.1, German.Ack.noAck, x.2.1),
            German.Cmd.cmdE, x.2.2.2.2, x.1 + {x.2.2.1}, x.2.2.1, x.2.2.2.1, x.2.1)] := by
  udf_certify

theorem German.sendInvE_inv.obligation_4 :
    Unification.sound (Narrowing.mayFire German.sendInvE German.ownE)
      [Unification.Unifier.bind
          fun
            (x :
              ℕ ×
                German.Req ×
                  German.Cmd ×
                    ℕ ×
                      German.Oids ×
                        German.Items ×
                          German.CacheState × German.Req × German.Ack × ℕ × Bool × German.Oids × German.Oids × ℕ) =>
          ((x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.1, x.1, x.2.2.2.2.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1,
              {German.Item.cache
                      { id := x.2.2.2.2.2.2.2.2.2.2.2.2.2, state := German.CacheState.exclusive, ch1 := x.2.1,
                        ch2 := German.Gnt.noGnt, ch3 := German.Ack.noAck }} +
                  {German.Item.dir
                      { cmd := x.2.2.1, ptr := x.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.2.2.2.2.2},
                        inv := x.2.2.2.2.1 }} +
                x.2.2.2.2.2.1),
            x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2.2, x.2.1,
            {German.Item.cache
                    { id := x.1, state := x.2.2.2.2.2.2.1, ch1 := x.2.2.2.2.2.2.2.1, ch2 := German.Gnt.noGnt,
                      ch3 := x.2.2.2.2.2.2.2.2.1 }} +
                {German.Item.dir
                    { cmd := German.Cmd.cmdE, ptr := x.2.2.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.2.2.1,
                      shr := x.2.2.2.2.2.2.2.2.2.2.2.1, inv := {x.1} + x.2.2.2.2.2.2.2.2.2.2.2.2.1 }} +
              x.2.2.2.2.2.1),
        Unification.Unifier.bind
          fun
            (x : ℕ × German.Items × Bool × German.Oids × German.Oids × ℕ × German.Req × German.Cmd × ℕ × German.Oids) =>
          ((x.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.1, German.CacheState.exclusive, x.2.2.2.2.2.2.1,
              German.Ack.noAck,
              {German.Item.dir
                    { cmd := x.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.2.1},
                      inv := x.2.2.2.2.2.2.2.2.2 }} +
                x.2.1),
            x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
            {German.Item.dir
                  { cmd := German.Cmd.cmdE, ptr := x.1, exGntd := x.2.2.1, shr := x.2.2.2.1,
                    inv := x.2.2.2.2.1 + {x.2.2.2.2.2.1} }} +
              x.2.1),
        Unification.Unifier.bind
          fun (x : ℕ × German.CacheState × German.Req × German.Ack × German.Oids × ℕ × German.Req × ℕ × German.Items) =>
          ((x.2.2.2.2.2.2.2.1, true, {x.2.2.2.2.2.1}, x.1, x.2.2.2.2.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {German.Item.cache
                    { id := x.2.2.2.2.2.1, state := German.CacheState.exclusive, ch1 := x.2.2.2.2.2.2.1,
                      ch2 := German.Gnt.noGnt, ch3 := German.Ack.noAck }} +
                x.2.2.2.2.2.2.2.2),
            German.Cmd.cmdE, x.2.2.2.2.2.2.2.1, {x.1} + x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
            {German.Item.cache
                  { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := German.Gnt.noGnt, ch3 := x.2.2.2.1 }} +
              x.2.2.2.2.2.2.2.2),
        Unification.Unifier.bind fun (x : German.Oids × German.Items × ℕ × German.Req × ℕ) =>
          ((x.2.2.2.2, true, {x.2.2.1}, x.2.2.1, x.1, German.CacheState.exclusive, x.2.2.2.1, German.Ack.noAck, x.2.1),
            German.Cmd.cmdE, x.2.2.2.2, x.1 + {x.2.2.1}, x.2.2.1, x.2.2.2.1, x.2.1)] := by
  -- each unifier, instantiated, solves the problem
  simp only [sound, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  repeat' apply And.intro
  all_goals
    rintro γ ⟨x, rfl⟩
    simp only [unifiedBy, Narrowing.mayFire, German.sendInvE, German.ownE]
  all_goals first
    | rfl
    | ac_rfl
    | simp only [ACU.plus_unit, ACU.unit_plus, ACU.plus_comm, ACU.plus_left_comm, ACU.plus_assoc]

theorem German.sendInvE_inv.obligation_5 :
    Unification.complete (Narrowing.mayFire German.sendInvE German.ownG)
      [Unification.Unifier.bind
          fun
            (x :
              ℕ ×
                German.Req ×
                  German.Cmd ×
                    ℕ ×
                      German.Oids ×
                        German.Items ×
                          German.CacheState × German.Req × German.Ack × ℕ × Bool × German.Oids × German.Oids × ℕ) =>
          ((x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.1, x.1, x.2.2.2.2.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1,
              {German.Item.cache
                      { id := x.2.2.2.2.2.2.2.2.2.2.2.2.2, state := German.CacheState.invalid, ch1 := x.2.1,
                        ch2 := German.Gnt.gntE, ch3 := German.Ack.noAck }} +
                  {German.Item.dir
                      { cmd := x.2.2.1, ptr := x.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.2.2.2.2.2},
                        inv := x.2.2.2.2.1 }} +
                x.2.2.2.2.2.1),
            x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2.2, x.2.1,
            {German.Item.cache
                    { id := x.1, state := x.2.2.2.2.2.2.1, ch1 := x.2.2.2.2.2.2.2.1, ch2 := German.Gnt.noGnt,
                      ch3 := x.2.2.2.2.2.2.2.2.1 }} +
                {German.Item.dir
                    { cmd := German.Cmd.cmdE, ptr := x.2.2.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.2.2.1,
                      shr := x.2.2.2.2.2.2.2.2.2.2.2.1, inv := {x.1} + x.2.2.2.2.2.2.2.2.2.2.2.2.1 }} +
              x.2.2.2.2.2.1),
        Unification.Unifier.bind
          fun (x : ℕ × German.CacheState × German.Req × German.Ack × German.Oids × ℕ × German.Req × ℕ × German.Items) =>
          ((x.2.2.2.2.2.2.2.1, true, {x.2.2.2.2.2.1}, x.1, x.2.2.2.2.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {German.Item.cache
                    { id := x.2.2.2.2.2.1, state := German.CacheState.invalid, ch1 := x.2.2.2.2.2.2.1,
                      ch2 := German.Gnt.gntE, ch3 := German.Ack.noAck }} +
                x.2.2.2.2.2.2.2.2),
            German.Cmd.cmdE, x.2.2.2.2.2.2.2.1, {x.1} + x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
            {German.Item.cache
                  { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := German.Gnt.noGnt, ch3 := x.2.2.2.1 }} +
              x.2.2.2.2.2.2.2.2)] := by
  udf_certify

theorem German.sendInvE_inv.obligation_6 :
    Unification.sound (Narrowing.mayFire German.sendInvE German.ownG)
      [Unification.Unifier.bind
          fun
            (x :
              ℕ ×
                German.Req ×
                  German.Cmd ×
                    ℕ ×
                      German.Oids ×
                        German.Items ×
                          German.CacheState × German.Req × German.Ack × ℕ × Bool × German.Oids × German.Oids × ℕ) =>
          ((x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.1, x.1, x.2.2.2.2.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1,
              {German.Item.cache
                      { id := x.2.2.2.2.2.2.2.2.2.2.2.2.2, state := German.CacheState.invalid, ch1 := x.2.1,
                        ch2 := German.Gnt.gntE, ch3 := German.Ack.noAck }} +
                  {German.Item.dir
                      { cmd := x.2.2.1, ptr := x.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.2.2.2.2.2},
                        inv := x.2.2.2.2.1 }} +
                x.2.2.2.2.2.1),
            x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2.2, x.2.1,
            {German.Item.cache
                    { id := x.1, state := x.2.2.2.2.2.2.1, ch1 := x.2.2.2.2.2.2.2.1, ch2 := German.Gnt.noGnt,
                      ch3 := x.2.2.2.2.2.2.2.2.1 }} +
                {German.Item.dir
                    { cmd := German.Cmd.cmdE, ptr := x.2.2.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.2.2.1,
                      shr := x.2.2.2.2.2.2.2.2.2.2.2.1, inv := {x.1} + x.2.2.2.2.2.2.2.2.2.2.2.2.1 }} +
              x.2.2.2.2.2.1),
        Unification.Unifier.bind
          fun (x : ℕ × German.CacheState × German.Req × German.Ack × German.Oids × ℕ × German.Req × ℕ × German.Items) =>
          ((x.2.2.2.2.2.2.2.1, true, {x.2.2.2.2.2.1}, x.1, x.2.2.2.2.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {German.Item.cache
                    { id := x.2.2.2.2.2.1, state := German.CacheState.invalid, ch1 := x.2.2.2.2.2.2.1,
                      ch2 := German.Gnt.gntE, ch3 := German.Ack.noAck }} +
                x.2.2.2.2.2.2.2.2),
            German.Cmd.cmdE, x.2.2.2.2.2.2.2.1, {x.1} + x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
            {German.Item.cache
                  { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := German.Gnt.noGnt, ch3 := x.2.2.2.1 }} +
              x.2.2.2.2.2.2.2.2)] := by
  -- each unifier, instantiated, solves the problem
  simp only [sound, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  repeat' apply And.intro
  all_goals
    rintro γ ⟨x, rfl⟩
    simp only [unifiedBy, Narrowing.mayFire, German.sendInvE, German.ownG]
  all_goals first
    | rfl
    | ac_rfl
    | simp only [ACU.plus_unit, ACU.unit_plus, ACU.plus_comm, ACU.plus_left_comm, ACU.plus_assoc]

theorem German.sendInvE_inv.obligation_7 :
    Unification.complete (Narrowing.mayFire German.sendInvE German.ownInv)
      [Unification.Unifier.bind
          fun
            (x :
              ℕ ×
                German.Req ×
                  German.Cmd ×
                    ℕ ×
                      German.Items ×
                        German.CacheState × German.Req × German.Ack × ℕ × Bool × German.Oids × German.Oids × ℕ) =>
          ((x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.1, x.2.2.2.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1,
              {German.Item.cache
                      { id := x.2.2.2.2.2.2.2.2.2.2.2.2, state := German.CacheState.exclusive, ch1 := x.2.1,
                        ch2 := German.Gnt.inv, ch3 := German.Ack.noAck }} +
                  {German.Item.dir
                      { cmd := x.2.2.1, ptr := x.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.2.2.2.2},
                        inv := ∅ }} +
                x.2.2.2.2.1),
            x.2.2.1, x.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2, x.2.1,
            {German.Item.cache
                    { id := x.1, state := x.2.2.2.2.2.1, ch1 := x.2.2.2.2.2.2.1, ch2 := German.Gnt.noGnt,
                      ch3 := x.2.2.2.2.2.2.2.1 }} +
                {German.Item.dir
                    { cmd := German.Cmd.cmdE, ptr := x.2.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.2.1,
                      shr := x.2.2.2.2.2.2.2.2.2.2.1, inv := {x.1} + x.2.2.2.2.2.2.2.2.2.2.2.1 }} +
              x.2.2.2.2.1)] := by
  udf_certify

theorem German.sendInvE_inv.obligation_8 :
    Unification.sound (Narrowing.mayFire German.sendInvE German.ownInv)
      [Unification.Unifier.bind
          fun
            (x :
              ℕ ×
                German.Req ×
                  German.Cmd ×
                    ℕ ×
                      German.Items ×
                        German.CacheState × German.Req × German.Ack × ℕ × Bool × German.Oids × German.Oids × ℕ) =>
          ((x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.1, x.2.2.2.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1,
              {German.Item.cache
                      { id := x.2.2.2.2.2.2.2.2.2.2.2.2, state := German.CacheState.exclusive, ch1 := x.2.1,
                        ch2 := German.Gnt.inv, ch3 := German.Ack.noAck }} +
                  {German.Item.dir
                      { cmd := x.2.2.1, ptr := x.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.2.2.2.2},
                        inv := ∅ }} +
                x.2.2.2.2.1),
            x.2.2.1, x.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2, x.2.1,
            {German.Item.cache
                    { id := x.1, state := x.2.2.2.2.2.1, ch1 := x.2.2.2.2.2.2.1, ch2 := German.Gnt.noGnt,
                      ch3 := x.2.2.2.2.2.2.2.1 }} +
                {German.Item.dir
                    { cmd := German.Cmd.cmdE, ptr := x.2.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.2.1,
                      shr := x.2.2.2.2.2.2.2.2.2.2.1, inv := {x.1} + x.2.2.2.2.2.2.2.2.2.2.2.1 }} +
              x.2.2.2.2.1)] := by
  -- each unifier, instantiated, solves the problem
  simp only [sound, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  repeat' apply And.intro
  all_goals
    rintro γ ⟨x, rfl⟩
    simp only [unifiedBy, Narrowing.mayFire, German.sendInvE, German.ownInv]
  all_goals first
    | rfl
    | ac_rfl
    | simp only [ACU.plus_unit, ACU.unit_plus, ACU.plus_comm, ACU.plus_left_comm, ACU.plus_assoc]

theorem German.sendInvE_inv.obligation_9 :
    Unification.complete (Narrowing.mayFire German.sendInvE German.ownAck)
      [Unification.Unifier.bind
          fun
            (x :
              ℕ ×
                German.Req ×
                  German.Cmd ×
                    ℕ ×
                      German.Items ×
                        German.CacheState × German.Req × German.Ack × ℕ × Bool × German.Oids × German.Oids × ℕ) =>
          ((x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.1, x.2.2.2.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1,
              {German.Item.cache
                      { id := x.2.2.2.2.2.2.2.2.2.2.2.2, state := German.CacheState.invalid, ch1 := x.2.1,
                        ch2 := German.Gnt.noGnt, ch3 := German.Ack.invAck }} +
                  {German.Item.dir
                      { cmd := x.2.2.1, ptr := x.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.2.2.2.2},
                        inv := ∅ }} +
                x.2.2.2.2.1),
            x.2.2.1, x.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2, x.2.1,
            {German.Item.cache
                    { id := x.1, state := x.2.2.2.2.2.1, ch1 := x.2.2.2.2.2.2.1, ch2 := German.Gnt.noGnt,
                      ch3 := x.2.2.2.2.2.2.2.1 }} +
                {German.Item.dir
                    { cmd := German.Cmd.cmdE, ptr := x.2.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.2.1,
                      shr := x.2.2.2.2.2.2.2.2.2.2.1, inv := {x.1} + x.2.2.2.2.2.2.2.2.2.2.2.1 }} +
              x.2.2.2.2.1),
        Unification.Unifier.bind
          fun (x : ℕ × Bool × German.Oids × German.Oids × ℕ × German.Req × German.Cmd × ℕ × German.Items) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.2.1, x.2.2.2.1, German.CacheState.invalid, x.2.2.2.2.2.1, German.Ack.invAck,
              {German.Item.dir
                    { cmd := x.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.1},
                      inv := ∅ }} +
                x.2.2.2.2.2.2.2.2),
            x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
            {German.Item.dir
                  { cmd := German.Cmd.cmdE, ptr := x.1, exGntd := x.2.1, shr := x.2.2.1,
                    inv := x.2.2.2.1 + {x.2.2.2.2.1} }} +
              x.2.2.2.2.2.2.2.2)] := by
  udf_certify

theorem German.sendInvE_inv.obligation_10 :
    Unification.sound (Narrowing.mayFire German.sendInvE German.ownAck)
      [Unification.Unifier.bind
          fun
            (x :
              ℕ ×
                German.Req ×
                  German.Cmd ×
                    ℕ ×
                      German.Items ×
                        German.CacheState × German.Req × German.Ack × ℕ × Bool × German.Oids × German.Oids × ℕ) =>
          ((x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.1, x.2.2.2.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1,
              {German.Item.cache
                      { id := x.2.2.2.2.2.2.2.2.2.2.2.2, state := German.CacheState.invalid, ch1 := x.2.1,
                        ch2 := German.Gnt.noGnt, ch3 := German.Ack.invAck }} +
                  {German.Item.dir
                      { cmd := x.2.2.1, ptr := x.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.2.2.2.2},
                        inv := ∅ }} +
                x.2.2.2.2.1),
            x.2.2.1, x.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2, x.2.1,
            {German.Item.cache
                    { id := x.1, state := x.2.2.2.2.2.1, ch1 := x.2.2.2.2.2.2.1, ch2 := German.Gnt.noGnt,
                      ch3 := x.2.2.2.2.2.2.2.1 }} +
                {German.Item.dir
                    { cmd := German.Cmd.cmdE, ptr := x.2.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.2.1,
                      shr := x.2.2.2.2.2.2.2.2.2.2.1, inv := {x.1} + x.2.2.2.2.2.2.2.2.2.2.2.1 }} +
              x.2.2.2.2.1),
        Unification.Unifier.bind
          fun (x : ℕ × Bool × German.Oids × German.Oids × ℕ × German.Req × German.Cmd × ℕ × German.Items) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.2.1, x.2.2.2.1, German.CacheState.invalid, x.2.2.2.2.2.1, German.Ack.invAck,
              {German.Item.dir
                    { cmd := x.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.1},
                      inv := ∅ }} +
                x.2.2.2.2.2.2.2.2),
            x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
            {German.Item.dir
                  { cmd := German.Cmd.cmdE, ptr := x.1, exGntd := x.2.1, shr := x.2.2.1,
                    inv := x.2.2.2.1 + {x.2.2.2.2.1} }} +
              x.2.2.2.2.2.2.2.2)] := by
  -- each unifier, instantiated, solves the problem
  simp only [sound, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  repeat' apply And.intro
  all_goals
    rintro γ ⟨x, rfl⟩
    simp only [unifiedBy, Narrowing.mayFire, German.sendInvE, German.ownAck]
  all_goals first
    | rfl
    | ac_rfl
    | simp only [ACU.plus_unit, ACU.unit_plus, ACU.plus_comm, ACU.plus_left_comm, ACU.plus_assoc]

theorem German.sendInvS_inv.obligation_1 :
    Unification.complete (Narrowing.mayFire German.sendInvS German.freeP)
      [Unification.Unifier.bind
          fun
            (x :
              ℕ ×
                German.Oids ×
                  German.Oids ×
                    German.Items ×
                      German.CacheState × German.Req × German.Ack × ℕ × German.Oids × German.Oids × German.Cmd × ℕ) =>
          ((x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1, x.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
              x.2.2.2.2.2.2.1,
              {German.Item.dir
                    { cmd := x.2.2.2.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.2.2.2, exGntd := false, shr := x.2.1,
                      inv := x.2.2.1 }} +
                x.2.2.2.1),
            x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2, x.2.1, x.2.2.1,
            {German.Item.cache
                    { id := x.1, state := x.2.2.2.2.1, ch1 := x.2.2.2.2.2.1, ch2 := German.Gnt.noGnt,
                      ch3 := x.2.2.2.2.2.2.1 }} +
                {German.Item.dir
                    { cmd := German.Cmd.cmdS, ptr := x.2.2.2.2.2.2.2.1, exGntd := true, shr := x.2.2.2.2.2.2.2.2.1,
                      inv := {x.1} + x.2.2.2.2.2.2.2.2.2.1 }} +
              x.2.2.2.1)] := by
  udf_certify

theorem German.sendInvS_inv.obligation_2 :
    Unification.sound (Narrowing.mayFire German.sendInvS German.freeP)
      [Unification.Unifier.bind
          fun
            (x :
              ℕ ×
                German.Oids ×
                  German.Oids ×
                    German.Items ×
                      German.CacheState × German.Req × German.Ack × ℕ × German.Oids × German.Oids × German.Cmd × ℕ) =>
          ((x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1, x.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
              x.2.2.2.2.2.2.1,
              {German.Item.dir
                    { cmd := x.2.2.2.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.2.2.2, exGntd := false, shr := x.2.1,
                      inv := x.2.2.1 }} +
                x.2.2.2.1),
            x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2, x.2.1, x.2.2.1,
            {German.Item.cache
                    { id := x.1, state := x.2.2.2.2.1, ch1 := x.2.2.2.2.2.1, ch2 := German.Gnt.noGnt,
                      ch3 := x.2.2.2.2.2.2.1 }} +
                {German.Item.dir
                    { cmd := German.Cmd.cmdS, ptr := x.2.2.2.2.2.2.2.1, exGntd := true, shr := x.2.2.2.2.2.2.2.2.1,
                      inv := {x.1} + x.2.2.2.2.2.2.2.2.2.1 }} +
              x.2.2.2.1)] := by
  -- each unifier, instantiated, solves the problem
  simp only [sound, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  repeat' apply And.intro
  all_goals
    rintro γ ⟨x, rfl⟩
    simp only [unifiedBy, Narrowing.mayFire, German.sendInvS, German.freeP]
  all_goals first
    | rfl
    | ac_rfl
    | simp only [ACU.plus_unit, ACU.unit_plus, ACU.plus_comm, ACU.plus_left_comm, ACU.plus_assoc]

theorem German.sendInvS_inv.obligation_3 :
    Unification.complete (Narrowing.mayFire German.sendInvS German.ownE)
      [Unification.Unifier.bind
          fun
            (x :
              ℕ ×
                German.Cmd ×
                  ℕ ×
                    German.Oids ×
                      German.Items ×
                        German.CacheState × German.Req × German.Ack × ℕ × German.Oids × German.Oids × ℕ × German.Req) =>
          ((x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.2.1,
              {German.Item.cache
                      { id := x.2.2.2.2.2.2.2.2.2.2.2.1, state := German.CacheState.exclusive,
                        ch1 := x.2.2.2.2.2.2.2.2.2.2.2.2, ch2 := German.Gnt.noGnt, ch3 := German.Ack.noAck }} +
                  {German.Item.dir
                      { cmd := x.2.1, ptr := x.2.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.2.2.2.1},
                        inv := x.2.2.2.1 }} +
                x.2.2.2.2.1),
            x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2,
            {German.Item.cache
                    { id := x.1, state := x.2.2.2.2.2.1, ch1 := x.2.2.2.2.2.2.1, ch2 := German.Gnt.noGnt,
                      ch3 := x.2.2.2.2.2.2.2.1 }} +
                {German.Item.dir
                    { cmd := German.Cmd.cmdS, ptr := x.2.2.2.2.2.2.2.2.1, exGntd := true, shr := x.2.2.2.2.2.2.2.2.2.1,
                      inv := {x.1} + x.2.2.2.2.2.2.2.2.2.2.1 }} +
              x.2.2.2.2.1),
        Unification.Unifier.bind
          fun (x : ℕ × German.Oids × German.Oids × ℕ × German.Req × German.Cmd × ℕ × German.Oids × German.Items) =>
          ((x.1, x.2.1, x.2.2.2.1, x.2.2.1, German.CacheState.exclusive, x.2.2.2.2.1, German.Ack.noAck,
              {German.Item.dir
                    { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.1},
                      inv := x.2.2.2.2.2.2.2.1 }} +
                x.2.2.2.2.2.2.2.2),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
            {German.Item.dir
                  { cmd := German.Cmd.cmdS, ptr := x.1, exGntd := true, shr := x.2.1, inv := x.2.2.1 + {x.2.2.2.1} }} +
              x.2.2.2.2.2.2.2.2),
        Unification.Unifier.bind
          fun (x : ℕ × German.CacheState × German.Req × German.Ack × German.Oids × ℕ × German.Req × ℕ × German.Items) =>
          ((x.2.2.2.2.2.2.2.1, {x.2.2.2.2.2.1}, x.1, x.2.2.2.2.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {German.Item.cache
                    { id := x.2.2.2.2.2.1, state := German.CacheState.exclusive, ch1 := x.2.2.2.2.2.2.1,
                      ch2 := German.Gnt.noGnt, ch3 := German.Ack.noAck }} +
                x.2.2.2.2.2.2.2.2),
            German.Cmd.cmdS, x.2.2.2.2.2.2.2.1, {x.1} + x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
            {German.Item.cache
                  { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := German.Gnt.noGnt, ch3 := x.2.2.2.1 }} +
              x.2.2.2.2.2.2.2.2),
        Unification.Unifier.bind fun (x : German.Oids × German.Items × ℕ × German.Req × ℕ) =>
          ((x.2.2.2.2, {x.2.2.1}, x.2.2.1, x.1, German.CacheState.exclusive, x.2.2.2.1, German.Ack.noAck, x.2.1),
            German.Cmd.cmdS, x.2.2.2.2, x.1 + {x.2.2.1}, x.2.2.1, x.2.2.2.1, x.2.1)] := by
  udf_certify

theorem German.sendInvS_inv.obligation_4 :
    Unification.sound (Narrowing.mayFire German.sendInvS German.ownE)
      [Unification.Unifier.bind
          fun
            (x :
              ℕ ×
                German.Cmd ×
                  ℕ ×
                    German.Oids ×
                      German.Items ×
                        German.CacheState × German.Req × German.Ack × ℕ × German.Oids × German.Oids × ℕ × German.Req) =>
          ((x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.2.1,
              {German.Item.cache
                      { id := x.2.2.2.2.2.2.2.2.2.2.2.1, state := German.CacheState.exclusive,
                        ch1 := x.2.2.2.2.2.2.2.2.2.2.2.2, ch2 := German.Gnt.noGnt, ch3 := German.Ack.noAck }} +
                  {German.Item.dir
                      { cmd := x.2.1, ptr := x.2.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.2.2.2.1},
                        inv := x.2.2.2.1 }} +
                x.2.2.2.2.1),
            x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2,
            {German.Item.cache
                    { id := x.1, state := x.2.2.2.2.2.1, ch1 := x.2.2.2.2.2.2.1, ch2 := German.Gnt.noGnt,
                      ch3 := x.2.2.2.2.2.2.2.1 }} +
                {German.Item.dir
                    { cmd := German.Cmd.cmdS, ptr := x.2.2.2.2.2.2.2.2.1, exGntd := true, shr := x.2.2.2.2.2.2.2.2.2.1,
                      inv := {x.1} + x.2.2.2.2.2.2.2.2.2.2.1 }} +
              x.2.2.2.2.1),
        Unification.Unifier.bind
          fun (x : ℕ × German.Oids × German.Oids × ℕ × German.Req × German.Cmd × ℕ × German.Oids × German.Items) =>
          ((x.1, x.2.1, x.2.2.2.1, x.2.2.1, German.CacheState.exclusive, x.2.2.2.2.1, German.Ack.noAck,
              {German.Item.dir
                    { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.1},
                      inv := x.2.2.2.2.2.2.2.1 }} +
                x.2.2.2.2.2.2.2.2),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
            {German.Item.dir
                  { cmd := German.Cmd.cmdS, ptr := x.1, exGntd := true, shr := x.2.1, inv := x.2.2.1 + {x.2.2.2.1} }} +
              x.2.2.2.2.2.2.2.2),
        Unification.Unifier.bind
          fun (x : ℕ × German.CacheState × German.Req × German.Ack × German.Oids × ℕ × German.Req × ℕ × German.Items) =>
          ((x.2.2.2.2.2.2.2.1, {x.2.2.2.2.2.1}, x.1, x.2.2.2.2.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {German.Item.cache
                    { id := x.2.2.2.2.2.1, state := German.CacheState.exclusive, ch1 := x.2.2.2.2.2.2.1,
                      ch2 := German.Gnt.noGnt, ch3 := German.Ack.noAck }} +
                x.2.2.2.2.2.2.2.2),
            German.Cmd.cmdS, x.2.2.2.2.2.2.2.1, {x.1} + x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
            {German.Item.cache
                  { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := German.Gnt.noGnt, ch3 := x.2.2.2.1 }} +
              x.2.2.2.2.2.2.2.2),
        Unification.Unifier.bind fun (x : German.Oids × German.Items × ℕ × German.Req × ℕ) =>
          ((x.2.2.2.2, {x.2.2.1}, x.2.2.1, x.1, German.CacheState.exclusive, x.2.2.2.1, German.Ack.noAck, x.2.1),
            German.Cmd.cmdS, x.2.2.2.2, x.1 + {x.2.2.1}, x.2.2.1, x.2.2.2.1, x.2.1)] := by
  -- each unifier, instantiated, solves the problem
  simp only [sound, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  repeat' apply And.intro
  all_goals
    rintro γ ⟨x, rfl⟩
    simp only [unifiedBy, Narrowing.mayFire, German.sendInvS, German.ownE]
  all_goals first
    | rfl
    | ac_rfl
    | simp only [ACU.plus_unit, ACU.unit_plus, ACU.plus_comm, ACU.plus_left_comm, ACU.plus_assoc]

theorem German.sendInvS_inv.obligation_5 :
    Unification.complete (Narrowing.mayFire German.sendInvS German.ownG)
      [Unification.Unifier.bind
          fun
            (x :
              ℕ ×
                German.Cmd ×
                  ℕ ×
                    German.Oids ×
                      German.Items ×
                        German.CacheState × German.Req × German.Ack × ℕ × German.Oids × German.Oids × ℕ × German.Req) =>
          ((x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.2.1,
              {German.Item.cache
                      { id := x.2.2.2.2.2.2.2.2.2.2.2.1, state := German.CacheState.invalid,
                        ch1 := x.2.2.2.2.2.2.2.2.2.2.2.2, ch2 := German.Gnt.gntE, ch3 := German.Ack.noAck }} +
                  {German.Item.dir
                      { cmd := x.2.1, ptr := x.2.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.2.2.2.1},
                        inv := x.2.2.2.1 }} +
                x.2.2.2.2.1),
            x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2,
            {German.Item.cache
                    { id := x.1, state := x.2.2.2.2.2.1, ch1 := x.2.2.2.2.2.2.1, ch2 := German.Gnt.noGnt,
                      ch3 := x.2.2.2.2.2.2.2.1 }} +
                {German.Item.dir
                    { cmd := German.Cmd.cmdS, ptr := x.2.2.2.2.2.2.2.2.1, exGntd := true, shr := x.2.2.2.2.2.2.2.2.2.1,
                      inv := {x.1} + x.2.2.2.2.2.2.2.2.2.2.1 }} +
              x.2.2.2.2.1),
        Unification.Unifier.bind
          fun (x : ℕ × German.CacheState × German.Req × German.Ack × German.Oids × ℕ × German.Req × ℕ × German.Items) =>
          ((x.2.2.2.2.2.2.2.1, {x.2.2.2.2.2.1}, x.1, x.2.2.2.2.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {German.Item.cache
                    { id := x.2.2.2.2.2.1, state := German.CacheState.invalid, ch1 := x.2.2.2.2.2.2.1,
                      ch2 := German.Gnt.gntE, ch3 := German.Ack.noAck }} +
                x.2.2.2.2.2.2.2.2),
            German.Cmd.cmdS, x.2.2.2.2.2.2.2.1, {x.1} + x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
            {German.Item.cache
                  { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := German.Gnt.noGnt, ch3 := x.2.2.2.1 }} +
              x.2.2.2.2.2.2.2.2)] := by
  udf_certify

theorem German.sendInvS_inv.obligation_6 :
    Unification.sound (Narrowing.mayFire German.sendInvS German.ownG)
      [Unification.Unifier.bind
          fun
            (x :
              ℕ ×
                German.Cmd ×
                  ℕ ×
                    German.Oids ×
                      German.Items ×
                        German.CacheState × German.Req × German.Ack × ℕ × German.Oids × German.Oids × ℕ × German.Req) =>
          ((x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.2.1,
              {German.Item.cache
                      { id := x.2.2.2.2.2.2.2.2.2.2.2.1, state := German.CacheState.invalid,
                        ch1 := x.2.2.2.2.2.2.2.2.2.2.2.2, ch2 := German.Gnt.gntE, ch3 := German.Ack.noAck }} +
                  {German.Item.dir
                      { cmd := x.2.1, ptr := x.2.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.2.2.2.1},
                        inv := x.2.2.2.1 }} +
                x.2.2.2.2.1),
            x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2,
            {German.Item.cache
                    { id := x.1, state := x.2.2.2.2.2.1, ch1 := x.2.2.2.2.2.2.1, ch2 := German.Gnt.noGnt,
                      ch3 := x.2.2.2.2.2.2.2.1 }} +
                {German.Item.dir
                    { cmd := German.Cmd.cmdS, ptr := x.2.2.2.2.2.2.2.2.1, exGntd := true, shr := x.2.2.2.2.2.2.2.2.2.1,
                      inv := {x.1} + x.2.2.2.2.2.2.2.2.2.2.1 }} +
              x.2.2.2.2.1),
        Unification.Unifier.bind
          fun (x : ℕ × German.CacheState × German.Req × German.Ack × German.Oids × ℕ × German.Req × ℕ × German.Items) =>
          ((x.2.2.2.2.2.2.2.1, {x.2.2.2.2.2.1}, x.1, x.2.2.2.2.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {German.Item.cache
                    { id := x.2.2.2.2.2.1, state := German.CacheState.invalid, ch1 := x.2.2.2.2.2.2.1,
                      ch2 := German.Gnt.gntE, ch3 := German.Ack.noAck }} +
                x.2.2.2.2.2.2.2.2),
            German.Cmd.cmdS, x.2.2.2.2.2.2.2.1, {x.1} + x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
            {German.Item.cache
                  { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := German.Gnt.noGnt, ch3 := x.2.2.2.1 }} +
              x.2.2.2.2.2.2.2.2)] := by
  -- each unifier, instantiated, solves the problem
  simp only [sound, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  repeat' apply And.intro
  all_goals
    rintro γ ⟨x, rfl⟩
    simp only [unifiedBy, Narrowing.mayFire, German.sendInvS, German.ownG]
  all_goals first
    | rfl
    | ac_rfl
    | simp only [ACU.plus_unit, ACU.unit_plus, ACU.plus_comm, ACU.plus_left_comm, ACU.plus_assoc]

theorem German.sendInvS_inv.obligation_7 :
    Unification.complete (Narrowing.mayFire German.sendInvS German.ownInv)
      [Unification.Unifier.bind
          fun
            (x :
              ℕ ×
                German.Cmd ×
                  ℕ ×
                    German.Items ×
                      German.CacheState × German.Req × German.Ack × ℕ × German.Oids × German.Oids × ℕ × German.Req) =>
          ((x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1, x.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
              x.2.2.2.2.2.2.1,
              {German.Item.cache
                      { id := x.2.2.2.2.2.2.2.2.2.2.1, state := German.CacheState.exclusive,
                        ch1 := x.2.2.2.2.2.2.2.2.2.2.2, ch2 := German.Gnt.inv, ch3 := German.Ack.noAck }} +
                  {German.Item.dir
                      { cmd := x.2.1, ptr := x.2.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.2.2.1}, inv := ∅ }} +
                x.2.2.2.1),
            x.2.1, x.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2,
            {German.Item.cache
                    { id := x.1, state := x.2.2.2.2.1, ch1 := x.2.2.2.2.2.1, ch2 := German.Gnt.noGnt,
                      ch3 := x.2.2.2.2.2.2.1 }} +
                {German.Item.dir
                    { cmd := German.Cmd.cmdS, ptr := x.2.2.2.2.2.2.2.1, exGntd := true, shr := x.2.2.2.2.2.2.2.2.1,
                      inv := {x.1} + x.2.2.2.2.2.2.2.2.2.1 }} +
              x.2.2.2.1)] := by
  udf_certify

theorem German.sendInvS_inv.obligation_8 :
    Unification.sound (Narrowing.mayFire German.sendInvS German.ownInv)
      [Unification.Unifier.bind
          fun
            (x :
              ℕ ×
                German.Cmd ×
                  ℕ ×
                    German.Items ×
                      German.CacheState × German.Req × German.Ack × ℕ × German.Oids × German.Oids × ℕ × German.Req) =>
          ((x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1, x.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
              x.2.2.2.2.2.2.1,
              {German.Item.cache
                      { id := x.2.2.2.2.2.2.2.2.2.2.1, state := German.CacheState.exclusive,
                        ch1 := x.2.2.2.2.2.2.2.2.2.2.2, ch2 := German.Gnt.inv, ch3 := German.Ack.noAck }} +
                  {German.Item.dir
                      { cmd := x.2.1, ptr := x.2.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.2.2.1}, inv := ∅ }} +
                x.2.2.2.1),
            x.2.1, x.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2,
            {German.Item.cache
                    { id := x.1, state := x.2.2.2.2.1, ch1 := x.2.2.2.2.2.1, ch2 := German.Gnt.noGnt,
                      ch3 := x.2.2.2.2.2.2.1 }} +
                {German.Item.dir
                    { cmd := German.Cmd.cmdS, ptr := x.2.2.2.2.2.2.2.1, exGntd := true, shr := x.2.2.2.2.2.2.2.2.1,
                      inv := {x.1} + x.2.2.2.2.2.2.2.2.2.1 }} +
              x.2.2.2.1)] := by
  -- each unifier, instantiated, solves the problem
  simp only [sound, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  repeat' apply And.intro
  all_goals
    rintro γ ⟨x, rfl⟩
    simp only [unifiedBy, Narrowing.mayFire, German.sendInvS, German.ownInv]
  all_goals first
    | rfl
    | ac_rfl
    | simp only [ACU.plus_unit, ACU.unit_plus, ACU.plus_comm, ACU.plus_left_comm, ACU.plus_assoc]

theorem German.sendInvS_inv.obligation_9 :
    Unification.complete (Narrowing.mayFire German.sendInvS German.ownAck)
      [Unification.Unifier.bind
          fun
            (x :
              ℕ ×
                German.Cmd ×
                  ℕ ×
                    German.Items ×
                      German.CacheState × German.Req × German.Ack × ℕ × German.Oids × German.Oids × ℕ × German.Req) =>
          ((x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1, x.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
              x.2.2.2.2.2.2.1,
              {German.Item.cache
                      { id := x.2.2.2.2.2.2.2.2.2.2.1, state := German.CacheState.invalid,
                        ch1 := x.2.2.2.2.2.2.2.2.2.2.2, ch2 := German.Gnt.noGnt, ch3 := German.Ack.invAck }} +
                  {German.Item.dir
                      { cmd := x.2.1, ptr := x.2.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.2.2.1}, inv := ∅ }} +
                x.2.2.2.1),
            x.2.1, x.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2,
            {German.Item.cache
                    { id := x.1, state := x.2.2.2.2.1, ch1 := x.2.2.2.2.2.1, ch2 := German.Gnt.noGnt,
                      ch3 := x.2.2.2.2.2.2.1 }} +
                {German.Item.dir
                    { cmd := German.Cmd.cmdS, ptr := x.2.2.2.2.2.2.2.1, exGntd := true, shr := x.2.2.2.2.2.2.2.2.1,
                      inv := {x.1} + x.2.2.2.2.2.2.2.2.2.1 }} +
              x.2.2.2.1),
        Unification.Unifier.bind
          fun (x : ℕ × German.Oids × German.Oids × ℕ × German.Req × German.Cmd × ℕ × German.Items) =>
          ((x.1, x.2.1, x.2.2.2.1, x.2.2.1, German.CacheState.invalid, x.2.2.2.2.1, German.Ack.invAck,
              {German.Item.dir
                    { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.1}, inv := ∅ }} +
                x.2.2.2.2.2.2.2),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
            {German.Item.dir
                  { cmd := German.Cmd.cmdS, ptr := x.1, exGntd := true, shr := x.2.1, inv := x.2.2.1 + {x.2.2.2.1} }} +
              x.2.2.2.2.2.2.2)] := by
  udf_certify

theorem German.sendInvS_inv.obligation_10 :
    Unification.sound (Narrowing.mayFire German.sendInvS German.ownAck)
      [Unification.Unifier.bind
          fun
            (x :
              ℕ ×
                German.Cmd ×
                  ℕ ×
                    German.Items ×
                      German.CacheState × German.Req × German.Ack × ℕ × German.Oids × German.Oids × ℕ × German.Req) =>
          ((x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1, x.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
              x.2.2.2.2.2.2.1,
              {German.Item.cache
                      { id := x.2.2.2.2.2.2.2.2.2.2.1, state := German.CacheState.invalid,
                        ch1 := x.2.2.2.2.2.2.2.2.2.2.2, ch2 := German.Gnt.noGnt, ch3 := German.Ack.invAck }} +
                  {German.Item.dir
                      { cmd := x.2.1, ptr := x.2.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.2.2.1}, inv := ∅ }} +
                x.2.2.2.1),
            x.2.1, x.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2,
            {German.Item.cache
                    { id := x.1, state := x.2.2.2.2.1, ch1 := x.2.2.2.2.2.1, ch2 := German.Gnt.noGnt,
                      ch3 := x.2.2.2.2.2.2.1 }} +
                {German.Item.dir
                    { cmd := German.Cmd.cmdS, ptr := x.2.2.2.2.2.2.2.1, exGntd := true, shr := x.2.2.2.2.2.2.2.2.1,
                      inv := {x.1} + x.2.2.2.2.2.2.2.2.2.1 }} +
              x.2.2.2.1),
        Unification.Unifier.bind
          fun (x : ℕ × German.Oids × German.Oids × ℕ × German.Req × German.Cmd × ℕ × German.Items) =>
          ((x.1, x.2.1, x.2.2.2.1, x.2.2.1, German.CacheState.invalid, x.2.2.2.2.1, German.Ack.invAck,
              {German.Item.dir
                    { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.1}, inv := ∅ }} +
                x.2.2.2.2.2.2.2),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
            {German.Item.dir
                  { cmd := German.Cmd.cmdS, ptr := x.1, exGntd := true, shr := x.2.1, inv := x.2.2.1 + {x.2.2.2.1} }} +
              x.2.2.2.2.2.2.2)] := by
  -- each unifier, instantiated, solves the problem
  simp only [sound, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  repeat' apply And.intro
  all_goals
    rintro γ ⟨x, rfl⟩
    simp only [unifiedBy, Narrowing.mayFire, German.sendInvS, German.ownAck]
  all_goals first
    | rfl
    | ac_rfl
    | simp only [ACU.plus_unit, ACU.unit_plus, ACU.plus_comm, ACU.plus_left_comm, ACU.plus_assoc]

theorem German.sendInvAck_inv.obligation_1 :
    Unification.complete (Narrowing.mayFire German.sendInvAck German.freeP)
      [Unification.Unifier.bind
          fun (x : ℕ × German.CacheState × German.Req × German.Cmd × ℕ × German.Oids × German.Oids × German.Items) =>
          ((x.1, x.2.1, x.2.2.1,
              {German.Item.dir
                    { cmd := x.2.2.2.1, ptr := x.2.2.2.2.1, exGntd := false, shr := x.2.2.2.2.2.1,
                      inv := x.2.2.2.2.2.2.1 }} +
                x.2.2.2.2.2.2.2),
            x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
            {German.Item.cache
                  { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := German.Gnt.inv, ch3 := German.Ack.noAck }} +
              x.2.2.2.2.2.2.2)] := by
  udf_certify

theorem German.sendInvAck_inv.obligation_2 :
    Unification.sound (Narrowing.mayFire German.sendInvAck German.freeP)
      [Unification.Unifier.bind
          fun (x : ℕ × German.CacheState × German.Req × German.Cmd × ℕ × German.Oids × German.Oids × German.Items) =>
          ((x.1, x.2.1, x.2.2.1,
              {German.Item.dir
                    { cmd := x.2.2.2.1, ptr := x.2.2.2.2.1, exGntd := false, shr := x.2.2.2.2.2.1,
                      inv := x.2.2.2.2.2.2.1 }} +
                x.2.2.2.2.2.2.2),
            x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
            {German.Item.cache
                  { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := German.Gnt.inv, ch3 := German.Ack.noAck }} +
              x.2.2.2.2.2.2.2)] := by
  -- each unifier, instantiated, solves the problem
  simp only [sound, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  repeat' apply And.intro
  all_goals
    rintro γ ⟨x, rfl⟩
    simp only [unifiedBy, Narrowing.mayFire, German.sendInvAck, German.freeP]
  all_goals first
    | rfl
    | ac_rfl
    | simp only [ACU.plus_unit, ACU.unit_plus, ACU.plus_comm, ACU.plus_left_comm, ACU.plus_assoc]

theorem German.sendInvAck_inv.obligation_3 :
    Unification.complete (Narrowing.mayFire German.sendInvAck German.ownE)
      [Unification.Unifier.bind
          fun (x : ℕ × German.CacheState × German.Req × ℕ × German.Req × German.Cmd × ℕ × German.Oids × German.Items) =>
          ((x.1, x.2.1, x.2.2.1,
              {German.Item.cache
                      { id := x.2.2.2.1, state := German.CacheState.exclusive, ch1 := x.2.2.2.2.1,
                        ch2 := German.Gnt.noGnt, ch3 := German.Ack.noAck }} +
                  {German.Item.dir
                      { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.1},
                        inv := x.2.2.2.2.2.2.2.1 }} +
                x.2.2.2.2.2.2.2.2),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
            {German.Item.cache
                  { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := German.Gnt.inv, ch3 := German.Ack.noAck }} +
              x.2.2.2.2.2.2.2.2)] := by
  udf_certify

theorem German.sendInvAck_inv.obligation_4 :
    Unification.sound (Narrowing.mayFire German.sendInvAck German.ownE)
      [Unification.Unifier.bind
          fun (x : ℕ × German.CacheState × German.Req × ℕ × German.Req × German.Cmd × ℕ × German.Oids × German.Items) =>
          ((x.1, x.2.1, x.2.2.1,
              {German.Item.cache
                      { id := x.2.2.2.1, state := German.CacheState.exclusive, ch1 := x.2.2.2.2.1,
                        ch2 := German.Gnt.noGnt, ch3 := German.Ack.noAck }} +
                  {German.Item.dir
                      { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.1},
                        inv := x.2.2.2.2.2.2.2.1 }} +
                x.2.2.2.2.2.2.2.2),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
            {German.Item.cache
                  { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := German.Gnt.inv, ch3 := German.Ack.noAck }} +
              x.2.2.2.2.2.2.2.2)] := by
  -- each unifier, instantiated, solves the problem
  simp only [sound, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  repeat' apply And.intro
  all_goals
    rintro γ ⟨x, rfl⟩
    simp only [unifiedBy, Narrowing.mayFire, German.sendInvAck, German.ownE]
  all_goals first
    | rfl
    | ac_rfl
    | simp only [ACU.plus_unit, ACU.unit_plus, ACU.plus_comm, ACU.plus_left_comm, ACU.plus_assoc]

theorem German.sendInvAck_inv.obligation_5 :
    Unification.complete (Narrowing.mayFire German.sendInvAck German.ownG)
      [Unification.Unifier.bind
          fun (x : ℕ × German.CacheState × German.Req × ℕ × German.Req × German.Cmd × ℕ × German.Oids × German.Items) =>
          ((x.1, x.2.1, x.2.2.1,
              {German.Item.cache
                      { id := x.2.2.2.1, state := German.CacheState.invalid, ch1 := x.2.2.2.2.1, ch2 := German.Gnt.gntE,
                        ch3 := German.Ack.noAck }} +
                  {German.Item.dir
                      { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.1},
                        inv := x.2.2.2.2.2.2.2.1 }} +
                x.2.2.2.2.2.2.2.2),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
            {German.Item.cache
                  { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := German.Gnt.inv, ch3 := German.Ack.noAck }} +
              x.2.2.2.2.2.2.2.2)] := by
  udf_certify

theorem German.sendInvAck_inv.obligation_6 :
    Unification.sound (Narrowing.mayFire German.sendInvAck German.ownG)
      [Unification.Unifier.bind
          fun (x : ℕ × German.CacheState × German.Req × ℕ × German.Req × German.Cmd × ℕ × German.Oids × German.Items) =>
          ((x.1, x.2.1, x.2.2.1,
              {German.Item.cache
                      { id := x.2.2.2.1, state := German.CacheState.invalid, ch1 := x.2.2.2.2.1, ch2 := German.Gnt.gntE,
                        ch3 := German.Ack.noAck }} +
                  {German.Item.dir
                      { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.1},
                        inv := x.2.2.2.2.2.2.2.1 }} +
                x.2.2.2.2.2.2.2.2),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
            {German.Item.cache
                  { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := German.Gnt.inv, ch3 := German.Ack.noAck }} +
              x.2.2.2.2.2.2.2.2)] := by
  -- each unifier, instantiated, solves the problem
  simp only [sound, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  repeat' apply And.intro
  all_goals
    rintro γ ⟨x, rfl⟩
    simp only [unifiedBy, Narrowing.mayFire, German.sendInvAck, German.ownG]
  all_goals first
    | rfl
    | ac_rfl
    | simp only [ACU.plus_unit, ACU.unit_plus, ACU.plus_comm, ACU.plus_left_comm, ACU.plus_assoc]

theorem German.sendInvAck_inv.obligation_7 :
    Unification.complete (Narrowing.mayFire German.sendInvAck German.ownInv)
      [Unification.Unifier.bind
          fun (x : ℕ × German.CacheState × German.Req × ℕ × German.Req × German.Cmd × ℕ × German.Items) =>
          ((x.1, x.2.1, x.2.2.1,
              {German.Item.cache
                      { id := x.2.2.2.1, state := German.CacheState.exclusive, ch1 := x.2.2.2.2.1,
                        ch2 := German.Gnt.inv, ch3 := German.Ack.noAck }} +
                  {German.Item.dir
                      { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.1}, inv := ∅ }} +
                x.2.2.2.2.2.2.2),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
            {German.Item.cache
                  { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := German.Gnt.inv, ch3 := German.Ack.noAck }} +
              x.2.2.2.2.2.2.2),
        Unification.Unifier.bind fun (x : German.Items × ℕ × German.Req × German.Cmd × ℕ) =>
          ((x.2.1, German.CacheState.exclusive, x.2.2.1,
              {German.Item.dir { cmd := x.2.2.2.1, ptr := x.2.2.2.2, exGntd := true, shr := {x.2.1}, inv := ∅ }} + x.1),
            x.2.2.2.1, x.2.2.2.2, x.2.1, x.2.2.1, x.1)] := by
  udf_certify

theorem German.sendInvAck_inv.obligation_8 :
    Unification.sound (Narrowing.mayFire German.sendInvAck German.ownInv)
      [Unification.Unifier.bind
          fun (x : ℕ × German.CacheState × German.Req × ℕ × German.Req × German.Cmd × ℕ × German.Items) =>
          ((x.1, x.2.1, x.2.2.1,
              {German.Item.cache
                      { id := x.2.2.2.1, state := German.CacheState.exclusive, ch1 := x.2.2.2.2.1,
                        ch2 := German.Gnt.inv, ch3 := German.Ack.noAck }} +
                  {German.Item.dir
                      { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.1}, inv := ∅ }} +
                x.2.2.2.2.2.2.2),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
            {German.Item.cache
                  { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := German.Gnt.inv, ch3 := German.Ack.noAck }} +
              x.2.2.2.2.2.2.2),
        Unification.Unifier.bind fun (x : German.Items × ℕ × German.Req × German.Cmd × ℕ) =>
          ((x.2.1, German.CacheState.exclusive, x.2.2.1,
              {German.Item.dir { cmd := x.2.2.2.1, ptr := x.2.2.2.2, exGntd := true, shr := {x.2.1}, inv := ∅ }} + x.1),
            x.2.2.2.1, x.2.2.2.2, x.2.1, x.2.2.1, x.1)] := by
  -- each unifier, instantiated, solves the problem
  simp only [sound, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  repeat' apply And.intro
  all_goals
    rintro γ ⟨x, rfl⟩
    simp only [unifiedBy, Narrowing.mayFire, German.sendInvAck, German.ownInv]
  all_goals first
    | rfl
    | ac_rfl
    | simp only [ACU.plus_unit, ACU.unit_plus, ACU.plus_comm, ACU.plus_left_comm, ACU.plus_assoc]

theorem German.sendInvAck_inv.obligation_9 :
    Unification.complete (Narrowing.mayFire German.sendInvAck German.ownAck)
      [Unification.Unifier.bind
          fun (x : ℕ × German.CacheState × German.Req × ℕ × German.Req × German.Cmd × ℕ × German.Items) =>
          ((x.1, x.2.1, x.2.2.1,
              {German.Item.cache
                      { id := x.2.2.2.1, state := German.CacheState.invalid, ch1 := x.2.2.2.2.1,
                        ch2 := German.Gnt.noGnt, ch3 := German.Ack.invAck }} +
                  {German.Item.dir
                      { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.1}, inv := ∅ }} +
                x.2.2.2.2.2.2.2),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
            {German.Item.cache
                  { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := German.Gnt.inv, ch3 := German.Ack.noAck }} +
              x.2.2.2.2.2.2.2)] := by
  udf_certify

theorem German.sendInvAck_inv.obligation_10 :
    Unification.sound (Narrowing.mayFire German.sendInvAck German.ownAck)
      [Unification.Unifier.bind
          fun (x : ℕ × German.CacheState × German.Req × ℕ × German.Req × German.Cmd × ℕ × German.Items) =>
          ((x.1, x.2.1, x.2.2.1,
              {German.Item.cache
                      { id := x.2.2.2.1, state := German.CacheState.invalid, ch1 := x.2.2.2.2.1,
                        ch2 := German.Gnt.noGnt, ch3 := German.Ack.invAck }} +
                  {German.Item.dir
                      { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.1}, inv := ∅ }} +
                x.2.2.2.2.2.2.2),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
            {German.Item.cache
                  { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := German.Gnt.inv, ch3 := German.Ack.noAck }} +
              x.2.2.2.2.2.2.2)] := by
  -- each unifier, instantiated, solves the problem
  simp only [sound, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  repeat' apply And.intro
  all_goals
    rintro γ ⟨x, rfl⟩
    simp only [unifiedBy, Narrowing.mayFire, German.sendInvAck, German.ownAck]
  all_goals first
    | rfl
    | ac_rfl
    | simp only [ACU.plus_unit, ACU.unit_plus, ACU.plus_comm, ACU.plus_left_comm, ACU.plus_assoc]

theorem German.recvInvAckS_inv.obligation_1 :
    Unification.complete (Narrowing.mayFire German.recvInvAckS German.freeP)
      [Unification.Unifier.bind
          fun
            (x :
              ℕ ×
                German.Cmd ×
                  ℕ ×
                    German.Oids ×
                      German.Oids ×
                        German.Items ×
                          German.CacheState ×
                            German.Req × German.Gnt × German.Cmd × ℕ × Bool × German.Oids × German.Oids) =>
          ((x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.1, x.1, x.2.2.2.2.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.2.2.2.2.2.2.2, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1,
              {German.Item.dir
                    { cmd := x.2.1, ptr := x.2.2.1, exGntd := false, shr := x.2.2.2.1, inv := x.2.2.2.2.1 }} +
                x.2.2.2.2.2.1),
            x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
            {German.Item.cache
                    { id := x.1, state := x.2.2.2.2.2.2.1, ch1 := x.2.2.2.2.2.2.2.1, ch2 := x.2.2.2.2.2.2.2.2.1,
                      ch3 := German.Ack.invAck }} +
                {German.Item.dir
                    { cmd := x.2.2.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.2.2.2.1,
                      shr := {x.1} + x.2.2.2.2.2.2.2.2.2.2.2.2.1, inv := x.2.2.2.2.2.2.2.2.2.2.2.2.2 }} +
              x.2.2.2.2.2.1),
        Unification.Unifier.bind
          fun
            (x :
              German.Items ×
                ℕ × German.CacheState × German.Req × German.Gnt × German.Oids × German.Cmd × ℕ × German.Oids) =>
          ((x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, false, x.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2, x.2.2.1, x.2.2.2.1,
              x.2.2.2.2.1, x.1),
            x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, {x.2.1} + x.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2,
            {German.Item.cache
                  { id := x.2.1, state := x.2.2.1, ch1 := x.2.2.2.1, ch2 := x.2.2.2.2.1, ch3 := German.Ack.invAck }} +
              x.1)] := by
  udf_certify

theorem German.recvInvAckS_inv.obligation_2 :
    Unification.sound (Narrowing.mayFire German.recvInvAckS German.freeP)
      [Unification.Unifier.bind
          fun
            (x :
              ℕ ×
                German.Cmd ×
                  ℕ ×
                    German.Oids ×
                      German.Oids ×
                        German.Items ×
                          German.CacheState ×
                            German.Req × German.Gnt × German.Cmd × ℕ × Bool × German.Oids × German.Oids) =>
          ((x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.1, x.1, x.2.2.2.2.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.2.2.2.2.2.2.2, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1,
              {German.Item.dir
                    { cmd := x.2.1, ptr := x.2.2.1, exGntd := false, shr := x.2.2.2.1, inv := x.2.2.2.2.1 }} +
                x.2.2.2.2.2.1),
            x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
            {German.Item.cache
                    { id := x.1, state := x.2.2.2.2.2.2.1, ch1 := x.2.2.2.2.2.2.2.1, ch2 := x.2.2.2.2.2.2.2.2.1,
                      ch3 := German.Ack.invAck }} +
                {German.Item.dir
                    { cmd := x.2.2.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.2.2.2.1,
                      shr := {x.1} + x.2.2.2.2.2.2.2.2.2.2.2.2.1, inv := x.2.2.2.2.2.2.2.2.2.2.2.2.2 }} +
              x.2.2.2.2.2.1),
        Unification.Unifier.bind
          fun
            (x :
              German.Items ×
                ℕ × German.CacheState × German.Req × German.Gnt × German.Oids × German.Cmd × ℕ × German.Oids) =>
          ((x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, false, x.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2, x.2.2.1, x.2.2.2.1,
              x.2.2.2.2.1, x.1),
            x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, {x.2.1} + x.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2,
            {German.Item.cache
                  { id := x.2.1, state := x.2.2.1, ch1 := x.2.2.2.1, ch2 := x.2.2.2.2.1, ch3 := German.Ack.invAck }} +
              x.1)] := by
  -- each unifier, instantiated, solves the problem
  simp only [sound, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  repeat' apply And.intro
  all_goals
    rintro γ ⟨x, rfl⟩
    simp only [unifiedBy, Narrowing.mayFire, German.recvInvAckS, German.freeP]
  all_goals first
    | rfl
    | ac_rfl
    | simp only [ACU.plus_unit, ACU.unit_plus, ACU.plus_comm, ACU.plus_left_comm, ACU.plus_assoc]

theorem German.recvInvAckS_inv.obligation_3 :
    Unification.complete (Narrowing.mayFire German.recvInvAckS German.ownE)
      [Unification.Unifier.bind
          fun
            (x :
              ℕ ×
                ℕ ×
                  German.Req ×
                    German.Cmd ×
                      ℕ ×
                        German.Oids ×
                          German.Items ×
                            German.CacheState ×
                              German.Req × German.Gnt × German.Cmd × ℕ × Bool × German.Oids × German.Oids) =>
          ((x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2.1, x.1,
              x.2.2.2.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2.2.2, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.2.2.2.1,
              {German.Item.cache
                      { id := x.2.1, state := German.CacheState.exclusive, ch1 := x.2.2.1, ch2 := German.Gnt.noGnt,
                        ch3 := German.Ack.noAck }} +
                  {German.Item.dir
                      { cmd := x.2.2.2.1, ptr := x.2.2.2.2.1, exGntd := true, shr := {x.2.1}, inv := x.2.2.2.2.2.1 }} +
                x.2.2.2.2.2.2.1),
            x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.1, x.2.2.1,
            {German.Item.cache
                    { id := x.1, state := x.2.2.2.2.2.2.2.1, ch1 := x.2.2.2.2.2.2.2.2.1, ch2 := x.2.2.2.2.2.2.2.2.2.1,
                      ch3 := German.Ack.invAck }} +
                {German.Item.dir
                    { cmd := x.2.2.2.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.2.2.2.1,
                      exGntd := x.2.2.2.2.2.2.2.2.2.2.2.2.1, shr := {x.1} + x.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
                      inv := x.2.2.2.2.2.2.2.2.2.2.2.2.2.2 }} +
              x.2.2.2.2.2.2.1),
        Unification.Unifier.bind
          fun
            (x :
              German.CacheState ×
                German.Req × German.Gnt × ℕ × German.Req × German.Cmd × ℕ × German.Oids × German.Items) =>
          ((x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, true, x.2.2.2.1, ∅, x.2.2.2.2.2.2.2.1, x.1, x.2.1, x.2.2.1,
              {German.Item.cache
                    { id := x.2.2.2.1, state := German.CacheState.exclusive, ch1 := x.2.2.2.2.1,
                      ch2 := German.Gnt.noGnt, ch3 := German.Ack.noAck }} +
                x.2.2.2.2.2.2.2.2),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
            {German.Item.cache
                  { id := x.2.2.2.1, state := x.1, ch1 := x.2.1, ch2 := x.2.2.1, ch3 := German.Ack.invAck }} +
              x.2.2.2.2.2.2.2.2)] := by
  udf_certify

theorem German.recvInvAckS_inv.obligation_4 :
    Unification.sound (Narrowing.mayFire German.recvInvAckS German.ownE)
      [Unification.Unifier.bind
          fun
            (x :
              ℕ ×
                ℕ ×
                  German.Req ×
                    German.Cmd ×
                      ℕ ×
                        German.Oids ×
                          German.Items ×
                            German.CacheState ×
                              German.Req × German.Gnt × German.Cmd × ℕ × Bool × German.Oids × German.Oids) =>
          ((x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2.1, x.1,
              x.2.2.2.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2.2.2, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.2.2.2.1,
              {German.Item.cache
                      { id := x.2.1, state := German.CacheState.exclusive, ch1 := x.2.2.1, ch2 := German.Gnt.noGnt,
                        ch3 := German.Ack.noAck }} +
                  {German.Item.dir
                      { cmd := x.2.2.2.1, ptr := x.2.2.2.2.1, exGntd := true, shr := {x.2.1}, inv := x.2.2.2.2.2.1 }} +
                x.2.2.2.2.2.2.1),
            x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.1, x.2.2.1,
            {German.Item.cache
                    { id := x.1, state := x.2.2.2.2.2.2.2.1, ch1 := x.2.2.2.2.2.2.2.2.1, ch2 := x.2.2.2.2.2.2.2.2.2.1,
                      ch3 := German.Ack.invAck }} +
                {German.Item.dir
                    { cmd := x.2.2.2.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.2.2.2.1,
                      exGntd := x.2.2.2.2.2.2.2.2.2.2.2.2.1, shr := {x.1} + x.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
                      inv := x.2.2.2.2.2.2.2.2.2.2.2.2.2.2 }} +
              x.2.2.2.2.2.2.1),
        Unification.Unifier.bind
          fun
            (x :
              German.CacheState ×
                German.Req × German.Gnt × ℕ × German.Req × German.Cmd × ℕ × German.Oids × German.Items) =>
          ((x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, true, x.2.2.2.1, ∅, x.2.2.2.2.2.2.2.1, x.1, x.2.1, x.2.2.1,
              {German.Item.cache
                    { id := x.2.2.2.1, state := German.CacheState.exclusive, ch1 := x.2.2.2.2.1,
                      ch2 := German.Gnt.noGnt, ch3 := German.Ack.noAck }} +
                x.2.2.2.2.2.2.2.2),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
            {German.Item.cache
                  { id := x.2.2.2.1, state := x.1, ch1 := x.2.1, ch2 := x.2.2.1, ch3 := German.Ack.invAck }} +
              x.2.2.2.2.2.2.2.2)] := by
  -- each unifier, instantiated, solves the problem
  simp only [sound, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  repeat' apply And.intro
  all_goals
    rintro γ ⟨x, rfl⟩
    simp only [unifiedBy, Narrowing.mayFire, German.recvInvAckS, German.ownE]
  all_goals first
    | rfl
    | ac_rfl
    | simp only [ACU.plus_unit, ACU.unit_plus, ACU.plus_comm, ACU.plus_left_comm, ACU.plus_assoc]

theorem German.recvInvAckS_inv.obligation_5 :
    Unification.complete (Narrowing.mayFire German.recvInvAckS German.ownG)
      [Unification.Unifier.bind
          fun
            (x :
              ℕ ×
                ℕ ×
                  German.Req ×
                    German.Cmd ×
                      ℕ ×
                        German.Oids ×
                          German.Items ×
                            German.CacheState ×
                              German.Req × German.Gnt × German.Cmd × ℕ × Bool × German.Oids × German.Oids) =>
          ((x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2.1, x.1,
              x.2.2.2.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2.2.2, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.2.2.2.1,
              {German.Item.cache
                      { id := x.2.1, state := German.CacheState.invalid, ch1 := x.2.2.1, ch2 := German.Gnt.gntE,
                        ch3 := German.Ack.noAck }} +
                  {German.Item.dir
                      { cmd := x.2.2.2.1, ptr := x.2.2.2.2.1, exGntd := true, shr := {x.2.1}, inv := x.2.2.2.2.2.1 }} +
                x.2.2.2.2.2.2.1),
            x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.1, x.2.2.1,
            {German.Item.cache
                    { id := x.1, state := x.2.2.2.2.2.2.2.1, ch1 := x.2.2.2.2.2.2.2.2.1, ch2 := x.2.2.2.2.2.2.2.2.2.1,
                      ch3 := German.Ack.invAck }} +
                {German.Item.dir
                    { cmd := x.2.2.2.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.2.2.2.1,
                      exGntd := x.2.2.2.2.2.2.2.2.2.2.2.2.1, shr := {x.1} + x.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
                      inv := x.2.2.2.2.2.2.2.2.2.2.2.2.2.2 }} +
              x.2.2.2.2.2.2.1),
        Unification.Unifier.bind
          fun
            (x :
              German.CacheState ×
                German.Req × German.Gnt × ℕ × German.Req × German.Cmd × ℕ × German.Oids × German.Items) =>
          ((x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, true, x.2.2.2.1, ∅, x.2.2.2.2.2.2.2.1, x.1, x.2.1, x.2.2.1,
              {German.Item.cache
                    { id := x.2.2.2.1, state := German.CacheState.invalid, ch1 := x.2.2.2.2.1, ch2 := German.Gnt.gntE,
                      ch3 := German.Ack.noAck }} +
                x.2.2.2.2.2.2.2.2),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
            {German.Item.cache
                  { id := x.2.2.2.1, state := x.1, ch1 := x.2.1, ch2 := x.2.2.1, ch3 := German.Ack.invAck }} +
              x.2.2.2.2.2.2.2.2)] := by
  udf_certify

theorem German.recvInvAckS_inv.obligation_6 :
    Unification.sound (Narrowing.mayFire German.recvInvAckS German.ownG)
      [Unification.Unifier.bind
          fun
            (x :
              ℕ ×
                ℕ ×
                  German.Req ×
                    German.Cmd ×
                      ℕ ×
                        German.Oids ×
                          German.Items ×
                            German.CacheState ×
                              German.Req × German.Gnt × German.Cmd × ℕ × Bool × German.Oids × German.Oids) =>
          ((x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2.1, x.1,
              x.2.2.2.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2.2.2, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.2.2.2.1,
              {German.Item.cache
                      { id := x.2.1, state := German.CacheState.invalid, ch1 := x.2.2.1, ch2 := German.Gnt.gntE,
                        ch3 := German.Ack.noAck }} +
                  {German.Item.dir
                      { cmd := x.2.2.2.1, ptr := x.2.2.2.2.1, exGntd := true, shr := {x.2.1}, inv := x.2.2.2.2.2.1 }} +
                x.2.2.2.2.2.2.1),
            x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.1, x.2.2.1,
            {German.Item.cache
                    { id := x.1, state := x.2.2.2.2.2.2.2.1, ch1 := x.2.2.2.2.2.2.2.2.1, ch2 := x.2.2.2.2.2.2.2.2.2.1,
                      ch3 := German.Ack.invAck }} +
                {German.Item.dir
                    { cmd := x.2.2.2.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.2.2.2.1,
                      exGntd := x.2.2.2.2.2.2.2.2.2.2.2.2.1, shr := {x.1} + x.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
                      inv := x.2.2.2.2.2.2.2.2.2.2.2.2.2.2 }} +
              x.2.2.2.2.2.2.1),
        Unification.Unifier.bind
          fun
            (x :
              German.CacheState ×
                German.Req × German.Gnt × ℕ × German.Req × German.Cmd × ℕ × German.Oids × German.Items) =>
          ((x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, true, x.2.2.2.1, ∅, x.2.2.2.2.2.2.2.1, x.1, x.2.1, x.2.2.1,
              {German.Item.cache
                    { id := x.2.2.2.1, state := German.CacheState.invalid, ch1 := x.2.2.2.2.1, ch2 := German.Gnt.gntE,
                      ch3 := German.Ack.noAck }} +
                x.2.2.2.2.2.2.2.2),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
            {German.Item.cache
                  { id := x.2.2.2.1, state := x.1, ch1 := x.2.1, ch2 := x.2.2.1, ch3 := German.Ack.invAck }} +
              x.2.2.2.2.2.2.2.2)] := by
  -- each unifier, instantiated, solves the problem
  simp only [sound, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  repeat' apply And.intro
  all_goals
    rintro γ ⟨x, rfl⟩
    simp only [unifiedBy, Narrowing.mayFire, German.recvInvAckS, German.ownG]
  all_goals first
    | rfl
    | ac_rfl
    | simp only [ACU.plus_unit, ACU.unit_plus, ACU.plus_comm, ACU.plus_left_comm, ACU.plus_assoc]

theorem German.recvInvAckS_inv.obligation_7 :
    Unification.complete (Narrowing.mayFire German.recvInvAckS German.ownInv)
      [Unification.Unifier.bind
          fun
            (x :
              ℕ ×
                ℕ ×
                  German.Req ×
                    German.Cmd ×
                      ℕ ×
                        German.Items ×
                          German.CacheState ×
                            German.Req × German.Gnt × German.Cmd × ℕ × Bool × German.Oids × German.Oids) =>
          ((x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.1, x.1, x.2.2.2.2.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.2.2.2.2.2.2.2, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1,
              {German.Item.cache
                      { id := x.2.1, state := German.CacheState.exclusive, ch1 := x.2.2.1, ch2 := German.Gnt.inv,
                        ch3 := German.Ack.noAck }} +
                  {German.Item.dir { cmd := x.2.2.2.1, ptr := x.2.2.2.2.1, exGntd := true, shr := {x.2.1}, inv := ∅ }} +
                x.2.2.2.2.2.1),
            x.2.2.2.1, x.2.2.2.2.1, x.2.1, x.2.2.1,
            {German.Item.cache
                    { id := x.1, state := x.2.2.2.2.2.2.1, ch1 := x.2.2.2.2.2.2.2.1, ch2 := x.2.2.2.2.2.2.2.2.1,
                      ch3 := German.Ack.invAck }} +
                {German.Item.dir
                    { cmd := x.2.2.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.2.2.2.1,
                      shr := {x.1} + x.2.2.2.2.2.2.2.2.2.2.2.2.1, inv := x.2.2.2.2.2.2.2.2.2.2.2.2.2 }} +
              x.2.2.2.2.2.1),
        Unification.Unifier.bind
          fun (x : German.CacheState × German.Req × German.Gnt × ℕ × German.Req × German.Cmd × ℕ × German.Items) =>
          ((x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, true, x.2.2.2.1, ∅, ∅, x.1, x.2.1, x.2.2.1,
              {German.Item.cache
                    { id := x.2.2.2.1, state := German.CacheState.exclusive, ch1 := x.2.2.2.2.1, ch2 := German.Gnt.inv,
                      ch3 := German.Ack.noAck }} +
                x.2.2.2.2.2.2.2),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
            {German.Item.cache
                  { id := x.2.2.2.1, state := x.1, ch1 := x.2.1, ch2 := x.2.2.1, ch3 := German.Ack.invAck }} +
              x.2.2.2.2.2.2.2)] := by
  udf_certify

theorem German.recvInvAckS_inv.obligation_8 :
    Unification.sound (Narrowing.mayFire German.recvInvAckS German.ownInv)
      [Unification.Unifier.bind
          fun
            (x :
              ℕ ×
                ℕ ×
                  German.Req ×
                    German.Cmd ×
                      ℕ ×
                        German.Items ×
                          German.CacheState ×
                            German.Req × German.Gnt × German.Cmd × ℕ × Bool × German.Oids × German.Oids) =>
          ((x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.1, x.1, x.2.2.2.2.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.2.2.2.2.2.2.2, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1,
              {German.Item.cache
                      { id := x.2.1, state := German.CacheState.exclusive, ch1 := x.2.2.1, ch2 := German.Gnt.inv,
                        ch3 := German.Ack.noAck }} +
                  {German.Item.dir { cmd := x.2.2.2.1, ptr := x.2.2.2.2.1, exGntd := true, shr := {x.2.1}, inv := ∅ }} +
                x.2.2.2.2.2.1),
            x.2.2.2.1, x.2.2.2.2.1, x.2.1, x.2.2.1,
            {German.Item.cache
                    { id := x.1, state := x.2.2.2.2.2.2.1, ch1 := x.2.2.2.2.2.2.2.1, ch2 := x.2.2.2.2.2.2.2.2.1,
                      ch3 := German.Ack.invAck }} +
                {German.Item.dir
                    { cmd := x.2.2.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.2.2.2.1,
                      shr := {x.1} + x.2.2.2.2.2.2.2.2.2.2.2.2.1, inv := x.2.2.2.2.2.2.2.2.2.2.2.2.2 }} +
              x.2.2.2.2.2.1),
        Unification.Unifier.bind
          fun (x : German.CacheState × German.Req × German.Gnt × ℕ × German.Req × German.Cmd × ℕ × German.Items) =>
          ((x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, true, x.2.2.2.1, ∅, ∅, x.1, x.2.1, x.2.2.1,
              {German.Item.cache
                    { id := x.2.2.2.1, state := German.CacheState.exclusive, ch1 := x.2.2.2.2.1, ch2 := German.Gnt.inv,
                      ch3 := German.Ack.noAck }} +
                x.2.2.2.2.2.2.2),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
            {German.Item.cache
                  { id := x.2.2.2.1, state := x.1, ch1 := x.2.1, ch2 := x.2.2.1, ch3 := German.Ack.invAck }} +
              x.2.2.2.2.2.2.2)] := by
  -- each unifier, instantiated, solves the problem
  simp only [sound, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  repeat' apply And.intro
  all_goals
    rintro γ ⟨x, rfl⟩
    simp only [unifiedBy, Narrowing.mayFire, German.recvInvAckS, German.ownInv]
  all_goals first
    | rfl
    | ac_rfl
    | simp only [ACU.plus_unit, ACU.unit_plus, ACU.plus_comm, ACU.plus_left_comm, ACU.plus_assoc]

theorem German.recvInvAckS_inv.obligation_9 :
    Unification.complete (Narrowing.mayFire German.recvInvAckS German.ownAck)
      [Unification.Unifier.bind
          fun
            (x :
              ℕ ×
                ℕ ×
                  German.Req ×
                    German.Cmd ×
                      ℕ ×
                        German.Items ×
                          German.CacheState ×
                            German.Req × German.Gnt × German.Cmd × ℕ × Bool × German.Oids × German.Oids) =>
          ((x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.1, x.1, x.2.2.2.2.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.2.2.2.2.2.2.2, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1,
              {German.Item.cache
                      { id := x.2.1, state := German.CacheState.invalid, ch1 := x.2.2.1, ch2 := German.Gnt.noGnt,
                        ch3 := German.Ack.invAck }} +
                  {German.Item.dir { cmd := x.2.2.2.1, ptr := x.2.2.2.2.1, exGntd := true, shr := {x.2.1}, inv := ∅ }} +
                x.2.2.2.2.2.1),
            x.2.2.2.1, x.2.2.2.2.1, x.2.1, x.2.2.1,
            {German.Item.cache
                    { id := x.1, state := x.2.2.2.2.2.2.1, ch1 := x.2.2.2.2.2.2.2.1, ch2 := x.2.2.2.2.2.2.2.2.1,
                      ch3 := German.Ack.invAck }} +
                {German.Item.dir
                    { cmd := x.2.2.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.2.2.2.1,
                      shr := {x.1} + x.2.2.2.2.2.2.2.2.2.2.2.2.1, inv := x.2.2.2.2.2.2.2.2.2.2.2.2.2 }} +
              x.2.2.2.2.2.1),
        Unification.Unifier.bind
          fun
            (x : German.Cmd × German.Items × ℕ × Bool × German.Oids × German.Oids × ℕ × German.Req × German.Cmd × ℕ) =>
          ((x.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, German.CacheState.invalid,
              x.2.2.2.2.2.2.2.1, German.Gnt.noGnt,
              {German.Item.dir
                    { cmd := x.2.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.2, exGntd := true, shr := {x.2.2.2.2.2.2.1},
                      inv := ∅ }} +
                x.2.1),
            x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1,
            {German.Item.dir
                  { cmd := x.1, ptr := x.2.2.1, exGntd := x.2.2.2.1, shr := x.2.2.2.2.1 + {x.2.2.2.2.2.2.1},
                    inv := x.2.2.2.2.2.1 }} +
              x.2.1),
        Unification.Unifier.bind
          fun (x : German.CacheState × German.Req × German.Gnt × ℕ × German.Req × German.Cmd × ℕ × German.Items) =>
          ((x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, true, x.2.2.2.1, ∅, ∅, x.1, x.2.1, x.2.2.1,
              {German.Item.cache
                    { id := x.2.2.2.1, state := German.CacheState.invalid, ch1 := x.2.2.2.2.1, ch2 := German.Gnt.noGnt,
                      ch3 := German.Ack.invAck }} +
                x.2.2.2.2.2.2.2),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
            {German.Item.cache
                  { id := x.2.2.2.1, state := x.1, ch1 := x.2.1, ch2 := x.2.2.1, ch3 := German.Ack.invAck }} +
              x.2.2.2.2.2.2.2),
        Unification.Unifier.bind fun (x : German.Items × ℕ × German.Req × German.Cmd × ℕ) =>
          ((x.2.2.2.1, x.2.2.2.2, true, x.2.1, ∅, ∅, German.CacheState.invalid, x.2.2.1, German.Gnt.noGnt, x.1),
            x.2.2.2.1, x.2.2.2.2, x.2.1, x.2.2.1, x.1)] := by
  udf_certify

theorem German.recvInvAckS_inv.obligation_10 :
    Unification.sound (Narrowing.mayFire German.recvInvAckS German.ownAck)
      [Unification.Unifier.bind
          fun
            (x :
              ℕ ×
                ℕ ×
                  German.Req ×
                    German.Cmd ×
                      ℕ ×
                        German.Items ×
                          German.CacheState ×
                            German.Req × German.Gnt × German.Cmd × ℕ × Bool × German.Oids × German.Oids) =>
          ((x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.1, x.1, x.2.2.2.2.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.2.2.2.2.2.2.2, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1,
              {German.Item.cache
                      { id := x.2.1, state := German.CacheState.invalid, ch1 := x.2.2.1, ch2 := German.Gnt.noGnt,
                        ch3 := German.Ack.invAck }} +
                  {German.Item.dir { cmd := x.2.2.2.1, ptr := x.2.2.2.2.1, exGntd := true, shr := {x.2.1}, inv := ∅ }} +
                x.2.2.2.2.2.1),
            x.2.2.2.1, x.2.2.2.2.1, x.2.1, x.2.2.1,
            {German.Item.cache
                    { id := x.1, state := x.2.2.2.2.2.2.1, ch1 := x.2.2.2.2.2.2.2.1, ch2 := x.2.2.2.2.2.2.2.2.1,
                      ch3 := German.Ack.invAck }} +
                {German.Item.dir
                    { cmd := x.2.2.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.2.2.2.1,
                      shr := {x.1} + x.2.2.2.2.2.2.2.2.2.2.2.2.1, inv := x.2.2.2.2.2.2.2.2.2.2.2.2.2 }} +
              x.2.2.2.2.2.1),
        Unification.Unifier.bind
          fun
            (x : German.Cmd × German.Items × ℕ × Bool × German.Oids × German.Oids × ℕ × German.Req × German.Cmd × ℕ) =>
          ((x.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, German.CacheState.invalid,
              x.2.2.2.2.2.2.2.1, German.Gnt.noGnt,
              {German.Item.dir
                    { cmd := x.2.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.2, exGntd := true, shr := {x.2.2.2.2.2.2.1},
                      inv := ∅ }} +
                x.2.1),
            x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1,
            {German.Item.dir
                  { cmd := x.1, ptr := x.2.2.1, exGntd := x.2.2.2.1, shr := x.2.2.2.2.1 + {x.2.2.2.2.2.2.1},
                    inv := x.2.2.2.2.2.1 }} +
              x.2.1),
        Unification.Unifier.bind
          fun (x : German.CacheState × German.Req × German.Gnt × ℕ × German.Req × German.Cmd × ℕ × German.Items) =>
          ((x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, true, x.2.2.2.1, ∅, ∅, x.1, x.2.1, x.2.2.1,
              {German.Item.cache
                    { id := x.2.2.2.1, state := German.CacheState.invalid, ch1 := x.2.2.2.2.1, ch2 := German.Gnt.noGnt,
                      ch3 := German.Ack.invAck }} +
                x.2.2.2.2.2.2.2),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
            {German.Item.cache
                  { id := x.2.2.2.1, state := x.1, ch1 := x.2.1, ch2 := x.2.2.1, ch3 := German.Ack.invAck }} +
              x.2.2.2.2.2.2.2),
        Unification.Unifier.bind fun (x : German.Items × ℕ × German.Req × German.Cmd × ℕ) =>
          ((x.2.2.2.1, x.2.2.2.2, true, x.2.1, ∅, ∅, German.CacheState.invalid, x.2.2.1, German.Gnt.noGnt, x.1),
            x.2.2.2.1, x.2.2.2.2, x.2.1, x.2.2.1, x.1)] := by
  -- each unifier, instantiated, solves the problem
  simp only [sound, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  repeat' apply And.intro
  all_goals
    rintro γ ⟨x, rfl⟩
    simp only [unifiedBy, Narrowing.mayFire, German.recvInvAckS, German.ownAck]
  all_goals first
    | rfl
    | ac_rfl
    | simp only [ACU.plus_unit, ACU.unit_plus, ACU.plus_comm, ACU.plus_left_comm, ACU.plus_assoc]

theorem German.recvInvAckN_inv.obligation_1 :
    Unification.complete (Narrowing.mayFire German.recvInvAckN German.freeP)
      [Unification.Unifier.bind
          fun
            (x :
              ℕ ×
                German.Cmd ×
                  ℕ ×
                    German.Oids ×
                      German.Oids ×
                        German.Items ×
                          German.CacheState ×
                            German.Req × German.Gnt × German.Cmd × ℕ × Bool × German.Oids × German.Oids) =>
          ((x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.2.2.2.2.2.2.2, x.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1,
              {German.Item.dir
                    { cmd := x.2.1, ptr := x.2.2.1, exGntd := false, shr := x.2.2.2.1, inv := x.2.2.2.2.1 }} +
                x.2.2.2.2.2.1),
            x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
            {German.Item.cache
                    { id := x.1, state := x.2.2.2.2.2.2.1, ch1 := x.2.2.2.2.2.2.2.1, ch2 := x.2.2.2.2.2.2.2.2.1,
                      ch3 := German.Ack.invAck }} +
                {German.Item.dir
                    { cmd := x.2.2.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.2.2.2.1,
                      shr := x.2.2.2.2.2.2.2.2.2.2.2.2.1, inv := x.2.2.2.2.2.2.2.2.2.2.2.2.2 }} +
              x.2.2.2.2.2.1),
        Unification.Unifier.bind
          fun
            (x :
              German.Items ×
                ℕ × German.CacheState × German.Req × German.Gnt × German.Cmd × ℕ × German.Oids × German.Oids) =>
          ((x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, false, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2, x.2.1, x.2.2.1, x.2.2.2.1,
              x.2.2.2.2.1, x.1),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2,
            {German.Item.cache
                  { id := x.2.1, state := x.2.2.1, ch1 := x.2.2.2.1, ch2 := x.2.2.2.2.1, ch3 := German.Ack.invAck }} +
              x.1)] := by
  udf_certify

theorem German.recvInvAckN_inv.obligation_2 :
    Unification.sound (Narrowing.mayFire German.recvInvAckN German.freeP)
      [Unification.Unifier.bind
          fun
            (x :
              ℕ ×
                German.Cmd ×
                  ℕ ×
                    German.Oids ×
                      German.Oids ×
                        German.Items ×
                          German.CacheState ×
                            German.Req × German.Gnt × German.Cmd × ℕ × Bool × German.Oids × German.Oids) =>
          ((x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.2.2.2.2.2.2.2, x.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1,
              {German.Item.dir
                    { cmd := x.2.1, ptr := x.2.2.1, exGntd := false, shr := x.2.2.2.1, inv := x.2.2.2.2.1 }} +
                x.2.2.2.2.2.1),
            x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
            {German.Item.cache
                    { id := x.1, state := x.2.2.2.2.2.2.1, ch1 := x.2.2.2.2.2.2.2.1, ch2 := x.2.2.2.2.2.2.2.2.1,
                      ch3 := German.Ack.invAck }} +
                {German.Item.dir
                    { cmd := x.2.2.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.2.2.2.1,
                      shr := x.2.2.2.2.2.2.2.2.2.2.2.2.1, inv := x.2.2.2.2.2.2.2.2.2.2.2.2.2 }} +
              x.2.2.2.2.2.1),
        Unification.Unifier.bind
          fun
            (x :
              German.Items ×
                ℕ × German.CacheState × German.Req × German.Gnt × German.Cmd × ℕ × German.Oids × German.Oids) =>
          ((x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, false, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2, x.2.1, x.2.2.1, x.2.2.2.1,
              x.2.2.2.2.1, x.1),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2,
            {German.Item.cache
                  { id := x.2.1, state := x.2.2.1, ch1 := x.2.2.2.1, ch2 := x.2.2.2.2.1, ch3 := German.Ack.invAck }} +
              x.1)] := by
  -- each unifier, instantiated, solves the problem
  simp only [sound, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  repeat' apply And.intro
  all_goals
    rintro γ ⟨x, rfl⟩
    simp only [unifiedBy, Narrowing.mayFire, German.recvInvAckN, German.freeP]
  all_goals first
    | rfl
    | ac_rfl
    | simp only [ACU.plus_unit, ACU.unit_plus, ACU.plus_comm, ACU.plus_left_comm, ACU.plus_assoc]

theorem German.recvInvAckN_inv.obligation_3 :
    Unification.complete (Narrowing.mayFire German.recvInvAckN German.ownE)
      [Unification.Unifier.bind
          fun
            (x :
              ℕ ×
                ℕ ×
                  German.Req ×
                    German.Cmd ×
                      ℕ ×
                        German.Oids ×
                          German.Items ×
                            German.CacheState ×
                              German.Req × German.Gnt × German.Cmd × ℕ × Bool × German.Oids × German.Oids) =>
          ((x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2.2.2, x.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.2.2.2.1,
              {German.Item.cache
                      { id := x.2.1, state := German.CacheState.exclusive, ch1 := x.2.2.1, ch2 := German.Gnt.noGnt,
                        ch3 := German.Ack.noAck }} +
                  {German.Item.dir
                      { cmd := x.2.2.2.1, ptr := x.2.2.2.2.1, exGntd := true, shr := {x.2.1}, inv := x.2.2.2.2.2.1 }} +
                x.2.2.2.2.2.2.1),
            x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.1, x.2.2.1,
            {German.Item.cache
                    { id := x.1, state := x.2.2.2.2.2.2.2.1, ch1 := x.2.2.2.2.2.2.2.2.1, ch2 := x.2.2.2.2.2.2.2.2.2.1,
                      ch3 := German.Ack.invAck }} +
                {German.Item.dir
                    { cmd := x.2.2.2.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.2.2.2.1,
                      exGntd := x.2.2.2.2.2.2.2.2.2.2.2.2.1, shr := x.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
                      inv := x.2.2.2.2.2.2.2.2.2.2.2.2.2.2 }} +
              x.2.2.2.2.2.2.1),
        Unification.Unifier.bind
          fun
            (x :
              ℕ ×
                German.Items ×
                  German.CacheState × German.Req × German.Gnt × ℕ × German.Req × German.Cmd × ℕ × German.Oids) =>
          ((x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1, true, {x.2.2.2.2.2.1}, x.2.2.2.2.2.2.2.2.2, x.1, x.2.2.1, x.2.2.2.1,
              x.2.2.2.2.1,
              {German.Item.cache
                    { id := x.2.2.2.2.2.1, state := German.CacheState.exclusive, ch1 := x.2.2.2.2.2.2.1,
                      ch2 := German.Gnt.noGnt, ch3 := German.Ack.noAck }} +
                x.2.1),
            x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
            {German.Item.cache
                  { id := x.1, state := x.2.2.1, ch1 := x.2.2.2.1, ch2 := x.2.2.2.2.1, ch3 := German.Ack.invAck }} +
              x.2.1)] := by
  udf_certify

theorem German.recvInvAckN_inv.obligation_4 :
    Unification.sound (Narrowing.mayFire German.recvInvAckN German.ownE)
      [Unification.Unifier.bind
          fun
            (x :
              ℕ ×
                ℕ ×
                  German.Req ×
                    German.Cmd ×
                      ℕ ×
                        German.Oids ×
                          German.Items ×
                            German.CacheState ×
                              German.Req × German.Gnt × German.Cmd × ℕ × Bool × German.Oids × German.Oids) =>
          ((x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2.2.2, x.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.2.2.2.1,
              {German.Item.cache
                      { id := x.2.1, state := German.CacheState.exclusive, ch1 := x.2.2.1, ch2 := German.Gnt.noGnt,
                        ch3 := German.Ack.noAck }} +
                  {German.Item.dir
                      { cmd := x.2.2.2.1, ptr := x.2.2.2.2.1, exGntd := true, shr := {x.2.1}, inv := x.2.2.2.2.2.1 }} +
                x.2.2.2.2.2.2.1),
            x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.1, x.2.2.1,
            {German.Item.cache
                    { id := x.1, state := x.2.2.2.2.2.2.2.1, ch1 := x.2.2.2.2.2.2.2.2.1, ch2 := x.2.2.2.2.2.2.2.2.2.1,
                      ch3 := German.Ack.invAck }} +
                {German.Item.dir
                    { cmd := x.2.2.2.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.2.2.2.1,
                      exGntd := x.2.2.2.2.2.2.2.2.2.2.2.2.1, shr := x.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
                      inv := x.2.2.2.2.2.2.2.2.2.2.2.2.2.2 }} +
              x.2.2.2.2.2.2.1),
        Unification.Unifier.bind
          fun
            (x :
              ℕ ×
                German.Items ×
                  German.CacheState × German.Req × German.Gnt × ℕ × German.Req × German.Cmd × ℕ × German.Oids) =>
          ((x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1, true, {x.2.2.2.2.2.1}, x.2.2.2.2.2.2.2.2.2, x.1, x.2.2.1, x.2.2.2.1,
              x.2.2.2.2.1,
              {German.Item.cache
                    { id := x.2.2.2.2.2.1, state := German.CacheState.exclusive, ch1 := x.2.2.2.2.2.2.1,
                      ch2 := German.Gnt.noGnt, ch3 := German.Ack.noAck }} +
                x.2.1),
            x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
            {German.Item.cache
                  { id := x.1, state := x.2.2.1, ch1 := x.2.2.2.1, ch2 := x.2.2.2.2.1, ch3 := German.Ack.invAck }} +
              x.2.1)] := by
  -- each unifier, instantiated, solves the problem
  simp only [sound, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  repeat' apply And.intro
  all_goals
    rintro γ ⟨x, rfl⟩
    simp only [unifiedBy, Narrowing.mayFire, German.recvInvAckN, German.ownE]
  all_goals first
    | rfl
    | ac_rfl
    | simp only [ACU.plus_unit, ACU.unit_plus, ACU.plus_comm, ACU.plus_left_comm, ACU.plus_assoc]

theorem German.recvInvAckN_inv.obligation_5 :
    Unification.complete (Narrowing.mayFire German.recvInvAckN German.ownG)
      [Unification.Unifier.bind
          fun
            (x :
              ℕ ×
                ℕ ×
                  German.Req ×
                    German.Cmd ×
                      ℕ ×
                        German.Oids ×
                          German.Items ×
                            German.CacheState ×
                              German.Req × German.Gnt × German.Cmd × ℕ × Bool × German.Oids × German.Oids) =>
          ((x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2.2.2, x.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.2.2.2.1,
              {German.Item.cache
                      { id := x.2.1, state := German.CacheState.invalid, ch1 := x.2.2.1, ch2 := German.Gnt.gntE,
                        ch3 := German.Ack.noAck }} +
                  {German.Item.dir
                      { cmd := x.2.2.2.1, ptr := x.2.2.2.2.1, exGntd := true, shr := {x.2.1}, inv := x.2.2.2.2.2.1 }} +
                x.2.2.2.2.2.2.1),
            x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.1, x.2.2.1,
            {German.Item.cache
                    { id := x.1, state := x.2.2.2.2.2.2.2.1, ch1 := x.2.2.2.2.2.2.2.2.1, ch2 := x.2.2.2.2.2.2.2.2.2.1,
                      ch3 := German.Ack.invAck }} +
                {German.Item.dir
                    { cmd := x.2.2.2.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.2.2.2.1,
                      exGntd := x.2.2.2.2.2.2.2.2.2.2.2.2.1, shr := x.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
                      inv := x.2.2.2.2.2.2.2.2.2.2.2.2.2.2 }} +
              x.2.2.2.2.2.2.1),
        Unification.Unifier.bind
          fun
            (x :
              ℕ ×
                German.Items ×
                  German.CacheState × German.Req × German.Gnt × ℕ × German.Req × German.Cmd × ℕ × German.Oids) =>
          ((x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1, true, {x.2.2.2.2.2.1}, x.2.2.2.2.2.2.2.2.2, x.1, x.2.2.1, x.2.2.2.1,
              x.2.2.2.2.1,
              {German.Item.cache
                    { id := x.2.2.2.2.2.1, state := German.CacheState.invalid, ch1 := x.2.2.2.2.2.2.1,
                      ch2 := German.Gnt.gntE, ch3 := German.Ack.noAck }} +
                x.2.1),
            x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
            {German.Item.cache
                  { id := x.1, state := x.2.2.1, ch1 := x.2.2.2.1, ch2 := x.2.2.2.2.1, ch3 := German.Ack.invAck }} +
              x.2.1)] := by
  udf_certify

theorem German.recvInvAckN_inv.obligation_6 :
    Unification.sound (Narrowing.mayFire German.recvInvAckN German.ownG)
      [Unification.Unifier.bind
          fun
            (x :
              ℕ ×
                ℕ ×
                  German.Req ×
                    German.Cmd ×
                      ℕ ×
                        German.Oids ×
                          German.Items ×
                            German.CacheState ×
                              German.Req × German.Gnt × German.Cmd × ℕ × Bool × German.Oids × German.Oids) =>
          ((x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2.2.2, x.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.2.2.2.1,
              {German.Item.cache
                      { id := x.2.1, state := German.CacheState.invalid, ch1 := x.2.2.1, ch2 := German.Gnt.gntE,
                        ch3 := German.Ack.noAck }} +
                  {German.Item.dir
                      { cmd := x.2.2.2.1, ptr := x.2.2.2.2.1, exGntd := true, shr := {x.2.1}, inv := x.2.2.2.2.2.1 }} +
                x.2.2.2.2.2.2.1),
            x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.1, x.2.2.1,
            {German.Item.cache
                    { id := x.1, state := x.2.2.2.2.2.2.2.1, ch1 := x.2.2.2.2.2.2.2.2.1, ch2 := x.2.2.2.2.2.2.2.2.2.1,
                      ch3 := German.Ack.invAck }} +
                {German.Item.dir
                    { cmd := x.2.2.2.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.2.2.2.1,
                      exGntd := x.2.2.2.2.2.2.2.2.2.2.2.2.1, shr := x.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
                      inv := x.2.2.2.2.2.2.2.2.2.2.2.2.2.2 }} +
              x.2.2.2.2.2.2.1),
        Unification.Unifier.bind
          fun
            (x :
              ℕ ×
                German.Items ×
                  German.CacheState × German.Req × German.Gnt × ℕ × German.Req × German.Cmd × ℕ × German.Oids) =>
          ((x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1, true, {x.2.2.2.2.2.1}, x.2.2.2.2.2.2.2.2.2, x.1, x.2.2.1, x.2.2.2.1,
              x.2.2.2.2.1,
              {German.Item.cache
                    { id := x.2.2.2.2.2.1, state := German.CacheState.invalid, ch1 := x.2.2.2.2.2.2.1,
                      ch2 := German.Gnt.gntE, ch3 := German.Ack.noAck }} +
                x.2.1),
            x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
            {German.Item.cache
                  { id := x.1, state := x.2.2.1, ch1 := x.2.2.2.1, ch2 := x.2.2.2.2.1, ch3 := German.Ack.invAck }} +
              x.2.1)] := by
  -- each unifier, instantiated, solves the problem
  simp only [sound, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  repeat' apply And.intro
  all_goals
    rintro γ ⟨x, rfl⟩
    simp only [unifiedBy, Narrowing.mayFire, German.recvInvAckN, German.ownG]
  all_goals first
    | rfl
    | ac_rfl
    | simp only [ACU.plus_unit, ACU.unit_plus, ACU.plus_comm, ACU.plus_left_comm, ACU.plus_assoc]

theorem German.recvInvAckN_inv.obligation_7 :
    Unification.complete (Narrowing.mayFire German.recvInvAckN German.ownInv)
      [Unification.Unifier.bind
          fun
            (x :
              ℕ ×
                ℕ ×
                  German.Req ×
                    German.Cmd ×
                      ℕ ×
                        German.Items ×
                          German.CacheState ×
                            German.Req × German.Gnt × German.Cmd × ℕ × Bool × German.Oids × German.Oids) =>
          ((x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.2.2.2.2.2.2.2, x.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1,
              {German.Item.cache
                      { id := x.2.1, state := German.CacheState.exclusive, ch1 := x.2.2.1, ch2 := German.Gnt.inv,
                        ch3 := German.Ack.noAck }} +
                  {German.Item.dir { cmd := x.2.2.2.1, ptr := x.2.2.2.2.1, exGntd := true, shr := {x.2.1}, inv := ∅ }} +
                x.2.2.2.2.2.1),
            x.2.2.2.1, x.2.2.2.2.1, x.2.1, x.2.2.1,
            {German.Item.cache
                    { id := x.1, state := x.2.2.2.2.2.2.1, ch1 := x.2.2.2.2.2.2.2.1, ch2 := x.2.2.2.2.2.2.2.2.1,
                      ch3 := German.Ack.invAck }} +
                {German.Item.dir
                    { cmd := x.2.2.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.2.2.2.1,
                      shr := x.2.2.2.2.2.2.2.2.2.2.2.2.1, inv := x.2.2.2.2.2.2.2.2.2.2.2.2.2 }} +
              x.2.2.2.2.2.1),
        Unification.Unifier.bind
          fun (x : ℕ × German.CacheState × German.Req × German.Gnt × ℕ × German.Req × German.Cmd × ℕ × German.Items) =>
          ((x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, true, {x.2.2.2.2.1}, ∅, x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {German.Item.cache
                    { id := x.2.2.2.2.1, state := German.CacheState.exclusive, ch1 := x.2.2.2.2.2.1,
                      ch2 := German.Gnt.inv, ch3 := German.Ack.noAck }} +
                x.2.2.2.2.2.2.2.2),
            x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
            {German.Item.cache
                  { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := x.2.2.2.1, ch3 := German.Ack.invAck }} +
              x.2.2.2.2.2.2.2.2)] := by
  udf_certify

theorem German.recvInvAckN_inv.obligation_8 :
    Unification.sound (Narrowing.mayFire German.recvInvAckN German.ownInv)
      [Unification.Unifier.bind
          fun
            (x :
              ℕ ×
                ℕ ×
                  German.Req ×
                    German.Cmd ×
                      ℕ ×
                        German.Items ×
                          German.CacheState ×
                            German.Req × German.Gnt × German.Cmd × ℕ × Bool × German.Oids × German.Oids) =>
          ((x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.2.2.2.2.2.2.2, x.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1,
              {German.Item.cache
                      { id := x.2.1, state := German.CacheState.exclusive, ch1 := x.2.2.1, ch2 := German.Gnt.inv,
                        ch3 := German.Ack.noAck }} +
                  {German.Item.dir { cmd := x.2.2.2.1, ptr := x.2.2.2.2.1, exGntd := true, shr := {x.2.1}, inv := ∅ }} +
                x.2.2.2.2.2.1),
            x.2.2.2.1, x.2.2.2.2.1, x.2.1, x.2.2.1,
            {German.Item.cache
                    { id := x.1, state := x.2.2.2.2.2.2.1, ch1 := x.2.2.2.2.2.2.2.1, ch2 := x.2.2.2.2.2.2.2.2.1,
                      ch3 := German.Ack.invAck }} +
                {German.Item.dir
                    { cmd := x.2.2.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.2.2.2.1,
                      shr := x.2.2.2.2.2.2.2.2.2.2.2.2.1, inv := x.2.2.2.2.2.2.2.2.2.2.2.2.2 }} +
              x.2.2.2.2.2.1),
        Unification.Unifier.bind
          fun (x : ℕ × German.CacheState × German.Req × German.Gnt × ℕ × German.Req × German.Cmd × ℕ × German.Items) =>
          ((x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, true, {x.2.2.2.2.1}, ∅, x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {German.Item.cache
                    { id := x.2.2.2.2.1, state := German.CacheState.exclusive, ch1 := x.2.2.2.2.2.1,
                      ch2 := German.Gnt.inv, ch3 := German.Ack.noAck }} +
                x.2.2.2.2.2.2.2.2),
            x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
            {German.Item.cache
                  { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := x.2.2.2.1, ch3 := German.Ack.invAck }} +
              x.2.2.2.2.2.2.2.2)] := by
  -- each unifier, instantiated, solves the problem
  simp only [sound, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  repeat' apply And.intro
  all_goals
    rintro γ ⟨x, rfl⟩
    simp only [unifiedBy, Narrowing.mayFire, German.recvInvAckN, German.ownInv]
  all_goals first
    | rfl
    | ac_rfl
    | simp only [ACU.plus_unit, ACU.unit_plus, ACU.plus_comm, ACU.plus_left_comm, ACU.plus_assoc]

theorem German.recvInvAckN_inv.obligation_9 :
    Unification.complete (Narrowing.mayFire German.recvInvAckN German.ownAck)
      [Unification.Unifier.bind
          fun
            (x :
              ℕ ×
                ℕ ×
                  German.Req ×
                    German.Cmd ×
                      ℕ ×
                        German.Items ×
                          German.CacheState ×
                            German.Req × German.Gnt × German.Cmd × ℕ × Bool × German.Oids × German.Oids) =>
          ((x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.2.2.2.2.2.2.2, x.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1,
              {German.Item.cache
                      { id := x.2.1, state := German.CacheState.invalid, ch1 := x.2.2.1, ch2 := German.Gnt.noGnt,
                        ch3 := German.Ack.invAck }} +
                  {German.Item.dir { cmd := x.2.2.2.1, ptr := x.2.2.2.2.1, exGntd := true, shr := {x.2.1}, inv := ∅ }} +
                x.2.2.2.2.2.1),
            x.2.2.2.1, x.2.2.2.2.1, x.2.1, x.2.2.1,
            {German.Item.cache
                    { id := x.1, state := x.2.2.2.2.2.2.1, ch1 := x.2.2.2.2.2.2.2.1, ch2 := x.2.2.2.2.2.2.2.2.1,
                      ch3 := German.Ack.invAck }} +
                {German.Item.dir
                    { cmd := x.2.2.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.2.2.2.1,
                      shr := x.2.2.2.2.2.2.2.2.2.2.2.2.1, inv := x.2.2.2.2.2.2.2.2.2.2.2.2.2 }} +
              x.2.2.2.2.2.1),
        Unification.Unifier.bind
          fun
            (x : German.Cmd × German.Items × ℕ × Bool × German.Oids × German.Oids × ℕ × German.Req × German.Cmd × ℕ) =>
          ((x.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, German.CacheState.invalid,
              x.2.2.2.2.2.2.2.1, German.Gnt.noGnt,
              {German.Item.dir
                    { cmd := x.2.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.2, exGntd := true, shr := {x.2.2.2.2.2.2.1},
                      inv := ∅ }} +
                x.2.1),
            x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1,
            {German.Item.dir
                  { cmd := x.1, ptr := x.2.2.1, exGntd := x.2.2.2.1, shr := x.2.2.2.2.1, inv := x.2.2.2.2.2.1 }} +
              x.2.1),
        Unification.Unifier.bind
          fun (x : ℕ × German.CacheState × German.Req × German.Gnt × ℕ × German.Req × German.Cmd × ℕ × German.Items) =>
          ((x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, true, {x.2.2.2.2.1}, ∅, x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {German.Item.cache
                    { id := x.2.2.2.2.1, state := German.CacheState.invalid, ch1 := x.2.2.2.2.2.1,
                      ch2 := German.Gnt.noGnt, ch3 := German.Ack.invAck }} +
                x.2.2.2.2.2.2.2.2),
            x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
            {German.Item.cache
                  { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := x.2.2.2.1, ch3 := German.Ack.invAck }} +
              x.2.2.2.2.2.2.2.2),
        Unification.Unifier.bind fun (x : German.Items × ℕ × German.Req × German.Cmd × ℕ) =>
          ((x.2.2.2.1, x.2.2.2.2, true, {x.2.1}, ∅, x.2.1, German.CacheState.invalid, x.2.2.1, German.Gnt.noGnt, x.1),
            x.2.2.2.1, x.2.2.2.2, x.2.1, x.2.2.1, x.1)] := by
  udf_certify

theorem German.recvInvAckN_inv.obligation_10 :
    Unification.sound (Narrowing.mayFire German.recvInvAckN German.ownAck)
      [Unification.Unifier.bind
          fun
            (x :
              ℕ ×
                ℕ ×
                  German.Req ×
                    German.Cmd ×
                      ℕ ×
                        German.Items ×
                          German.CacheState ×
                            German.Req × German.Gnt × German.Cmd × ℕ × Bool × German.Oids × German.Oids) =>
          ((x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.2.2.2.2.2.2.2, x.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1,
              {German.Item.cache
                      { id := x.2.1, state := German.CacheState.invalid, ch1 := x.2.2.1, ch2 := German.Gnt.noGnt,
                        ch3 := German.Ack.invAck }} +
                  {German.Item.dir { cmd := x.2.2.2.1, ptr := x.2.2.2.2.1, exGntd := true, shr := {x.2.1}, inv := ∅ }} +
                x.2.2.2.2.2.1),
            x.2.2.2.1, x.2.2.2.2.1, x.2.1, x.2.2.1,
            {German.Item.cache
                    { id := x.1, state := x.2.2.2.2.2.2.1, ch1 := x.2.2.2.2.2.2.2.1, ch2 := x.2.2.2.2.2.2.2.2.1,
                      ch3 := German.Ack.invAck }} +
                {German.Item.dir
                    { cmd := x.2.2.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.2.2.2.1,
                      shr := x.2.2.2.2.2.2.2.2.2.2.2.2.1, inv := x.2.2.2.2.2.2.2.2.2.2.2.2.2 }} +
              x.2.2.2.2.2.1),
        Unification.Unifier.bind
          fun
            (x : German.Cmd × German.Items × ℕ × Bool × German.Oids × German.Oids × ℕ × German.Req × German.Cmd × ℕ) =>
          ((x.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, German.CacheState.invalid,
              x.2.2.2.2.2.2.2.1, German.Gnt.noGnt,
              {German.Item.dir
                    { cmd := x.2.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.2, exGntd := true, shr := {x.2.2.2.2.2.2.1},
                      inv := ∅ }} +
                x.2.1),
            x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1,
            {German.Item.dir
                  { cmd := x.1, ptr := x.2.2.1, exGntd := x.2.2.2.1, shr := x.2.2.2.2.1, inv := x.2.2.2.2.2.1 }} +
              x.2.1),
        Unification.Unifier.bind
          fun (x : ℕ × German.CacheState × German.Req × German.Gnt × ℕ × German.Req × German.Cmd × ℕ × German.Items) =>
          ((x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, true, {x.2.2.2.2.1}, ∅, x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {German.Item.cache
                    { id := x.2.2.2.2.1, state := German.CacheState.invalid, ch1 := x.2.2.2.2.2.1,
                      ch2 := German.Gnt.noGnt, ch3 := German.Ack.invAck }} +
                x.2.2.2.2.2.2.2.2),
            x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
            {German.Item.cache
                  { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := x.2.2.2.1, ch3 := German.Ack.invAck }} +
              x.2.2.2.2.2.2.2.2),
        Unification.Unifier.bind fun (x : German.Items × ℕ × German.Req × German.Cmd × ℕ) =>
          ((x.2.2.2.1, x.2.2.2.2, true, {x.2.1}, ∅, x.2.1, German.CacheState.invalid, x.2.2.1, German.Gnt.noGnt, x.1),
            x.2.2.2.1, x.2.2.2.2, x.2.1, x.2.2.1, x.1)] := by
  -- each unifier, instantiated, solves the problem
  simp only [sound, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  repeat' apply And.intro
  all_goals
    rintro γ ⟨x, rfl⟩
    simp only [unifiedBy, Narrowing.mayFire, German.recvInvAckN, German.ownAck]
  all_goals first
    | rfl
    | ac_rfl
    | simp only [ACU.plus_unit, ACU.unit_plus, ACU.plus_comm, ACU.plus_left_comm, ACU.plus_assoc]

theorem German.sendGntSN_inv.obligation_1 :
    Unification.complete (Narrowing.mayFire German.sendGntSN German.freeP)
      [Unification.Unifier.bind
          fun
            (x :
              ℕ ×
                German.Oids ×
                  German.Items ×
                    German.CacheState ×
                      German.Req × German.Ack × German.Oids × German.Oids × German.Cmd × ℕ × German.Oids) =>
          ((x.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
              {German.Item.dir
                    { cmd := x.2.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.2.1, exGntd := false,
                      shr := x.2.2.2.2.2.2.2.2.2.2, inv := x.2.1 }} +
                x.2.2.1),
            x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2, x.2.1,
            {German.Item.cache
                    { id := x.1, state := x.2.2.2.1, ch1 := x.2.2.2.2.1, ch2 := German.Gnt.noGnt,
                      ch3 := x.2.2.2.2.2.1 }} +
                {German.Item.dir
                    { cmd := German.Cmd.cmdS, ptr := x.1, exGntd := false, shr := x.2.2.2.2.2.2.1,
                      inv := x.2.2.2.2.2.2.2.1 }} +
              x.2.2.1),
        Unification.Unifier.bind
          fun (x : German.Items × German.CacheState × German.Req × German.Ack × ℕ × German.Oids × German.Oids) =>
          ((x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2, x.2.1, x.2.2.1, x.2.2.2.1, x.1), German.Cmd.cmdS, x.2.2.2.2.1,
            x.2.2.2.2.2.1, x.2.2.2.2.2.2,
            {German.Item.cache
                  { id := x.2.2.2.2.1, state := x.2.1, ch1 := x.2.2.1, ch2 := German.Gnt.noGnt, ch3 := x.2.2.2.1 }} +
              x.1)] := by
  udf_certify

theorem German.sendGntSN_inv.obligation_2 :
    Unification.sound (Narrowing.mayFire German.sendGntSN German.freeP)
      [Unification.Unifier.bind
          fun
            (x :
              ℕ ×
                German.Oids ×
                  German.Items ×
                    German.CacheState ×
                      German.Req × German.Ack × German.Oids × German.Oids × German.Cmd × ℕ × German.Oids) =>
          ((x.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
              {German.Item.dir
                    { cmd := x.2.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.2.1, exGntd := false,
                      shr := x.2.2.2.2.2.2.2.2.2.2, inv := x.2.1 }} +
                x.2.2.1),
            x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2, x.2.1,
            {German.Item.cache
                    { id := x.1, state := x.2.2.2.1, ch1 := x.2.2.2.2.1, ch2 := German.Gnt.noGnt,
                      ch3 := x.2.2.2.2.2.1 }} +
                {German.Item.dir
                    { cmd := German.Cmd.cmdS, ptr := x.1, exGntd := false, shr := x.2.2.2.2.2.2.1,
                      inv := x.2.2.2.2.2.2.2.1 }} +
              x.2.2.1),
        Unification.Unifier.bind
          fun (x : German.Items × German.CacheState × German.Req × German.Ack × ℕ × German.Oids × German.Oids) =>
          ((x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2, x.2.1, x.2.2.1, x.2.2.2.1, x.1), German.Cmd.cmdS, x.2.2.2.2.1,
            x.2.2.2.2.2.1, x.2.2.2.2.2.2,
            {German.Item.cache
                  { id := x.2.2.2.2.1, state := x.2.1, ch1 := x.2.2.1, ch2 := German.Gnt.noGnt, ch3 := x.2.2.2.1 }} +
              x.1)] := by
  -- each unifier, instantiated, solves the problem
  simp only [sound, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  repeat' apply And.intro
  all_goals
    rintro γ ⟨x, rfl⟩
    simp only [unifiedBy, Narrowing.mayFire, German.sendGntSN, German.freeP]
  all_goals first
    | rfl
    | ac_rfl
    | simp only [ACU.plus_unit, ACU.unit_plus, ACU.plus_comm, ACU.plus_left_comm, ACU.plus_assoc]

theorem German.sendGntSN_inv.obligation_3 :
    Unification.complete (Narrowing.mayFire German.sendGntSN German.ownE)
      [Unification.Unifier.bind
          fun
            (x :
              ℕ ×
                ℕ ×
                  German.Oids ×
                    German.Items ×
                      German.CacheState ×
                        German.Req × German.Ack × German.Oids × German.Oids × ℕ × German.Req × German.Cmd) =>
          ((x.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
              {German.Item.cache
                      { id := x.2.2.2.2.2.2.2.2.2.1, state := German.CacheState.exclusive,
                        ch1 := x.2.2.2.2.2.2.2.2.2.2.1, ch2 := German.Gnt.noGnt, ch3 := German.Ack.noAck }} +
                  {German.Item.dir
                      { cmd := x.2.2.2.2.2.2.2.2.2.2.2, ptr := x.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.2.1},
                        inv := x.2.2.1 }} +
                x.2.2.2.1),
            x.2.2.2.2.2.2.2.2.2.2.2, x.2.1, x.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1,
            {German.Item.cache
                    { id := x.1, state := x.2.2.2.2.1, ch1 := x.2.2.2.2.2.1, ch2 := German.Gnt.noGnt,
                      ch3 := x.2.2.2.2.2.2.1 }} +
                {German.Item.dir
                    { cmd := German.Cmd.cmdS, ptr := x.1, exGntd := false, shr := x.2.2.2.2.2.2.2.1,
                      inv := x.2.2.2.2.2.2.2.2.1 }} +
              x.2.2.2.1),
        Unification.Unifier.bind
          fun (x : German.Oids × German.Oids × ℕ × German.Req × German.Cmd × ℕ × German.Oids × German.Items) =>
          ((x.2.2.1, x.1, x.2.1, German.CacheState.exclusive, x.2.2.2.1, German.Ack.noAck,
              {German.Item.dir
                    { cmd := x.2.2.2.2.1, ptr := x.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.1},
                      inv := x.2.2.2.2.2.2.1 }} +
                x.2.2.2.2.2.2.2),
            x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.1, x.2.2.2.1,
            {German.Item.dir { cmd := German.Cmd.cmdS, ptr := x.2.2.1, exGntd := false, shr := x.1, inv := x.2.1 }} +
              x.2.2.2.2.2.2.2)] := by
  udf_certify

theorem German.sendGntSN_inv.obligation_4 :
    Unification.sound (Narrowing.mayFire German.sendGntSN German.ownE)
      [Unification.Unifier.bind
          fun
            (x :
              ℕ ×
                ℕ ×
                  German.Oids ×
                    German.Items ×
                      German.CacheState ×
                        German.Req × German.Ack × German.Oids × German.Oids × ℕ × German.Req × German.Cmd) =>
          ((x.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
              {German.Item.cache
                      { id := x.2.2.2.2.2.2.2.2.2.1, state := German.CacheState.exclusive,
                        ch1 := x.2.2.2.2.2.2.2.2.2.2.1, ch2 := German.Gnt.noGnt, ch3 := German.Ack.noAck }} +
                  {German.Item.dir
                      { cmd := x.2.2.2.2.2.2.2.2.2.2.2, ptr := x.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.2.1},
                        inv := x.2.2.1 }} +
                x.2.2.2.1),
            x.2.2.2.2.2.2.2.2.2.2.2, x.2.1, x.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1,
            {German.Item.cache
                    { id := x.1, state := x.2.2.2.2.1, ch1 := x.2.2.2.2.2.1, ch2 := German.Gnt.noGnt,
                      ch3 := x.2.2.2.2.2.2.1 }} +
                {German.Item.dir
                    { cmd := German.Cmd.cmdS, ptr := x.1, exGntd := false, shr := x.2.2.2.2.2.2.2.1,
                      inv := x.2.2.2.2.2.2.2.2.1 }} +
              x.2.2.2.1),
        Unification.Unifier.bind
          fun (x : German.Oids × German.Oids × ℕ × German.Req × German.Cmd × ℕ × German.Oids × German.Items) =>
          ((x.2.2.1, x.1, x.2.1, German.CacheState.exclusive, x.2.2.2.1, German.Ack.noAck,
              {German.Item.dir
                    { cmd := x.2.2.2.2.1, ptr := x.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.1},
                      inv := x.2.2.2.2.2.2.1 }} +
                x.2.2.2.2.2.2.2),
            x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.1, x.2.2.2.1,
            {German.Item.dir { cmd := German.Cmd.cmdS, ptr := x.2.2.1, exGntd := false, shr := x.1, inv := x.2.1 }} +
              x.2.2.2.2.2.2.2)] := by
  -- each unifier, instantiated, solves the problem
  simp only [sound, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  repeat' apply And.intro
  all_goals
    rintro γ ⟨x, rfl⟩
    simp only [unifiedBy, Narrowing.mayFire, German.sendGntSN, German.ownE]
  all_goals first
    | rfl
    | ac_rfl
    | simp only [ACU.plus_unit, ACU.unit_plus, ACU.plus_comm, ACU.plus_left_comm, ACU.plus_assoc]

theorem German.sendGntSN_inv.obligation_5 :
    Unification.complete (Narrowing.mayFire German.sendGntSN German.ownG)
      [Unification.Unifier.bind
          fun
            (x :
              ℕ ×
                ℕ ×
                  German.Oids ×
                    German.Items ×
                      German.CacheState ×
                        German.Req × German.Ack × German.Oids × German.Oids × ℕ × German.Req × German.Cmd) =>
          ((x.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
              {German.Item.cache
                      { id := x.2.2.2.2.2.2.2.2.2.1, state := German.CacheState.invalid, ch1 := x.2.2.2.2.2.2.2.2.2.2.1,
                        ch2 := German.Gnt.gntE, ch3 := German.Ack.noAck }} +
                  {German.Item.dir
                      { cmd := x.2.2.2.2.2.2.2.2.2.2.2, ptr := x.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.2.1},
                        inv := x.2.2.1 }} +
                x.2.2.2.1),
            x.2.2.2.2.2.2.2.2.2.2.2, x.2.1, x.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1,
            {German.Item.cache
                    { id := x.1, state := x.2.2.2.2.1, ch1 := x.2.2.2.2.2.1, ch2 := German.Gnt.noGnt,
                      ch3 := x.2.2.2.2.2.2.1 }} +
                {German.Item.dir
                    { cmd := German.Cmd.cmdS, ptr := x.1, exGntd := false, shr := x.2.2.2.2.2.2.2.1,
                      inv := x.2.2.2.2.2.2.2.2.1 }} +
              x.2.2.2.1)] := by
  udf_certify

theorem German.sendGntSN_inv.obligation_6 :
    Unification.sound (Narrowing.mayFire German.sendGntSN German.ownG)
      [Unification.Unifier.bind
          fun
            (x :
              ℕ ×
                ℕ ×
                  German.Oids ×
                    German.Items ×
                      German.CacheState ×
                        German.Req × German.Ack × German.Oids × German.Oids × ℕ × German.Req × German.Cmd) =>
          ((x.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
              {German.Item.cache
                      { id := x.2.2.2.2.2.2.2.2.2.1, state := German.CacheState.invalid, ch1 := x.2.2.2.2.2.2.2.2.2.2.1,
                        ch2 := German.Gnt.gntE, ch3 := German.Ack.noAck }} +
                  {German.Item.dir
                      { cmd := x.2.2.2.2.2.2.2.2.2.2.2, ptr := x.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.2.1},
                        inv := x.2.2.1 }} +
                x.2.2.2.1),
            x.2.2.2.2.2.2.2.2.2.2.2, x.2.1, x.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1,
            {German.Item.cache
                    { id := x.1, state := x.2.2.2.2.1, ch1 := x.2.2.2.2.2.1, ch2 := German.Gnt.noGnt,
                      ch3 := x.2.2.2.2.2.2.1 }} +
                {German.Item.dir
                    { cmd := German.Cmd.cmdS, ptr := x.1, exGntd := false, shr := x.2.2.2.2.2.2.2.1,
                      inv := x.2.2.2.2.2.2.2.2.1 }} +
              x.2.2.2.1)] := by
  -- each unifier, instantiated, solves the problem
  simp only [sound, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  repeat' apply And.intro
  all_goals
    rintro γ ⟨x, rfl⟩
    simp only [unifiedBy, Narrowing.mayFire, German.sendGntSN, German.ownG]
  all_goals first
    | rfl
    | ac_rfl
    | simp only [ACU.plus_unit, ACU.unit_plus, ACU.plus_comm, ACU.plus_left_comm, ACU.plus_assoc]

theorem German.sendGntSN_inv.obligation_7 :
    Unification.complete (Narrowing.mayFire German.sendGntSN German.ownInv)
      [Unification.Unifier.bind
          fun
            (x :
              ℕ ×
                ℕ ×
                  German.Items ×
                    German.CacheState ×
                      German.Req × German.Ack × German.Oids × German.Oids × ℕ × German.Req × German.Cmd) =>
          ((x.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
              {German.Item.cache
                      { id := x.2.2.2.2.2.2.2.2.1, state := German.CacheState.exclusive, ch1 := x.2.2.2.2.2.2.2.2.2.1,
                        ch2 := German.Gnt.inv, ch3 := German.Ack.noAck }} +
                  {German.Item.dir
                      { cmd := x.2.2.2.2.2.2.2.2.2.2, ptr := x.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.1},
                        inv := ∅ }} +
                x.2.2.1),
            x.2.2.2.2.2.2.2.2.2.2, x.2.1, x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1,
            {German.Item.cache
                    { id := x.1, state := x.2.2.2.1, ch1 := x.2.2.2.2.1, ch2 := German.Gnt.noGnt,
                      ch3 := x.2.2.2.2.2.1 }} +
                {German.Item.dir
                    { cmd := German.Cmd.cmdS, ptr := x.1, exGntd := false, shr := x.2.2.2.2.2.2.1,
                      inv := x.2.2.2.2.2.2.2.1 }} +
              x.2.2.1)] := by
  udf_certify

theorem German.sendGntSN_inv.obligation_8 :
    Unification.sound (Narrowing.mayFire German.sendGntSN German.ownInv)
      [Unification.Unifier.bind
          fun
            (x :
              ℕ ×
                ℕ ×
                  German.Items ×
                    German.CacheState ×
                      German.Req × German.Ack × German.Oids × German.Oids × ℕ × German.Req × German.Cmd) =>
          ((x.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
              {German.Item.cache
                      { id := x.2.2.2.2.2.2.2.2.1, state := German.CacheState.exclusive, ch1 := x.2.2.2.2.2.2.2.2.2.1,
                        ch2 := German.Gnt.inv, ch3 := German.Ack.noAck }} +
                  {German.Item.dir
                      { cmd := x.2.2.2.2.2.2.2.2.2.2, ptr := x.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.1},
                        inv := ∅ }} +
                x.2.2.1),
            x.2.2.2.2.2.2.2.2.2.2, x.2.1, x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1,
            {German.Item.cache
                    { id := x.1, state := x.2.2.2.1, ch1 := x.2.2.2.2.1, ch2 := German.Gnt.noGnt,
                      ch3 := x.2.2.2.2.2.1 }} +
                {German.Item.dir
                    { cmd := German.Cmd.cmdS, ptr := x.1, exGntd := false, shr := x.2.2.2.2.2.2.1,
                      inv := x.2.2.2.2.2.2.2.1 }} +
              x.2.2.1)] := by
  -- each unifier, instantiated, solves the problem
  simp only [sound, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  repeat' apply And.intro
  all_goals
    rintro γ ⟨x, rfl⟩
    simp only [unifiedBy, Narrowing.mayFire, German.sendGntSN, German.ownInv]
  all_goals first
    | rfl
    | ac_rfl
    | simp only [ACU.plus_unit, ACU.unit_plus, ACU.plus_comm, ACU.plus_left_comm, ACU.plus_assoc]

theorem German.sendGntSN_inv.obligation_9 :
    Unification.complete (Narrowing.mayFire German.sendGntSN German.ownAck)
      [Unification.Unifier.bind
          fun
            (x :
              ℕ ×
                ℕ ×
                  German.Items ×
                    German.CacheState ×
                      German.Req × German.Ack × German.Oids × German.Oids × ℕ × German.Req × German.Cmd) =>
          ((x.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
              {German.Item.cache
                      { id := x.2.2.2.2.2.2.2.2.1, state := German.CacheState.invalid, ch1 := x.2.2.2.2.2.2.2.2.2.1,
                        ch2 := German.Gnt.noGnt, ch3 := German.Ack.invAck }} +
                  {German.Item.dir
                      { cmd := x.2.2.2.2.2.2.2.2.2.2, ptr := x.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.1},
                        inv := ∅ }} +
                x.2.2.1),
            x.2.2.2.2.2.2.2.2.2.2, x.2.1, x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1,
            {German.Item.cache
                    { id := x.1, state := x.2.2.2.1, ch1 := x.2.2.2.2.1, ch2 := German.Gnt.noGnt,
                      ch3 := x.2.2.2.2.2.1 }} +
                {German.Item.dir
                    { cmd := German.Cmd.cmdS, ptr := x.1, exGntd := false, shr := x.2.2.2.2.2.2.1,
                      inv := x.2.2.2.2.2.2.2.1 }} +
              x.2.2.1),
        Unification.Unifier.bind fun (x : German.Oids × German.Oids × ℕ × German.Req × German.Cmd × ℕ × German.Items) =>
          ((x.2.2.1, x.1, x.2.1, German.CacheState.invalid, x.2.2.2.1, German.Ack.invAck,
              {German.Item.dir
                    { cmd := x.2.2.2.2.1, ptr := x.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.1}, inv := ∅ }} +
                x.2.2.2.2.2.2),
            x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.1, x.2.2.2.1,
            {German.Item.dir { cmd := German.Cmd.cmdS, ptr := x.2.2.1, exGntd := false, shr := x.1, inv := x.2.1 }} +
              x.2.2.2.2.2.2)] := by
  udf_certify

theorem German.sendGntSN_inv.obligation_10 :
    Unification.sound (Narrowing.mayFire German.sendGntSN German.ownAck)
      [Unification.Unifier.bind
          fun
            (x :
              ℕ ×
                ℕ ×
                  German.Items ×
                    German.CacheState ×
                      German.Req × German.Ack × German.Oids × German.Oids × ℕ × German.Req × German.Cmd) =>
          ((x.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
              {German.Item.cache
                      { id := x.2.2.2.2.2.2.2.2.1, state := German.CacheState.invalid, ch1 := x.2.2.2.2.2.2.2.2.2.1,
                        ch2 := German.Gnt.noGnt, ch3 := German.Ack.invAck }} +
                  {German.Item.dir
                      { cmd := x.2.2.2.2.2.2.2.2.2.2, ptr := x.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.1},
                        inv := ∅ }} +
                x.2.2.1),
            x.2.2.2.2.2.2.2.2.2.2, x.2.1, x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1,
            {German.Item.cache
                    { id := x.1, state := x.2.2.2.1, ch1 := x.2.2.2.2.1, ch2 := German.Gnt.noGnt,
                      ch3 := x.2.2.2.2.2.1 }} +
                {German.Item.dir
                    { cmd := German.Cmd.cmdS, ptr := x.1, exGntd := false, shr := x.2.2.2.2.2.2.1,
                      inv := x.2.2.2.2.2.2.2.1 }} +
              x.2.2.1),
        Unification.Unifier.bind fun (x : German.Oids × German.Oids × ℕ × German.Req × German.Cmd × ℕ × German.Items) =>
          ((x.2.2.1, x.1, x.2.1, German.CacheState.invalid, x.2.2.2.1, German.Ack.invAck,
              {German.Item.dir
                    { cmd := x.2.2.2.2.1, ptr := x.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.1}, inv := ∅ }} +
                x.2.2.2.2.2.2),
            x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.1, x.2.2.2.1,
            {German.Item.dir { cmd := German.Cmd.cmdS, ptr := x.2.2.1, exGntd := false, shr := x.1, inv := x.2.1 }} +
              x.2.2.2.2.2.2)] := by
  -- each unifier, instantiated, solves the problem
  simp only [sound, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  repeat' apply And.intro
  all_goals
    rintro γ ⟨x, rfl⟩
    simp only [unifiedBy, Narrowing.mayFire, German.sendGntSN, German.ownAck]
  all_goals first
    | rfl
    | ac_rfl
    | simp only [ACU.plus_unit, ACU.unit_plus, ACU.plus_comm, ACU.plus_left_comm, ACU.plus_assoc]

theorem German.sendGntSS_inv.obligation_1 :
    Unification.complete (Narrowing.mayFire German.sendGntSS German.freeP)
      [Unification.Unifier.bind
          fun
            (x :
              ℕ ×
                German.Oids ×
                  German.Items ×
                    German.CacheState ×
                      German.Req × German.Ack × German.Oids × German.Oids × German.Cmd × ℕ × German.Oids) =>
          ((x.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
              {German.Item.dir
                    { cmd := x.2.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.2.1, exGntd := false,
                      shr := x.2.2.2.2.2.2.2.2.2.2, inv := x.2.1 }} +
                x.2.2.1),
            x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2, x.2.1,
            {German.Item.cache
                    { id := x.1, state := x.2.2.2.1, ch1 := x.2.2.2.2.1, ch2 := German.Gnt.noGnt,
                      ch3 := x.2.2.2.2.2.1 }} +
                {German.Item.dir
                    { cmd := German.Cmd.cmdS, ptr := x.1, exGntd := false, shr := {x.1} + x.2.2.2.2.2.2.1,
                      inv := x.2.2.2.2.2.2.2.1 }} +
              x.2.2.1),
        Unification.Unifier.bind
          fun (x : German.Items × German.CacheState × German.Req × German.Ack × German.Oids × ℕ × German.Oids) =>
          ((x.2.2.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.2, x.2.1, x.2.2.1, x.2.2.2.1, x.1), German.Cmd.cmdS, x.2.2.2.2.2.1,
            x.2.2.2.2.1 + {x.2.2.2.2.2.1}, x.2.2.2.2.2.2,
            {German.Item.cache
                  { id := x.2.2.2.2.2.1, state := x.2.1, ch1 := x.2.2.1, ch2 := German.Gnt.noGnt, ch3 := x.2.2.2.1 }} +
              x.1)] := by
  udf_certify

theorem German.sendGntSS_inv.obligation_2 :
    Unification.sound (Narrowing.mayFire German.sendGntSS German.freeP)
      [Unification.Unifier.bind
          fun
            (x :
              ℕ ×
                German.Oids ×
                  German.Items ×
                    German.CacheState ×
                      German.Req × German.Ack × German.Oids × German.Oids × German.Cmd × ℕ × German.Oids) =>
          ((x.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
              {German.Item.dir
                    { cmd := x.2.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.2.1, exGntd := false,
                      shr := x.2.2.2.2.2.2.2.2.2.2, inv := x.2.1 }} +
                x.2.2.1),
            x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2, x.2.1,
            {German.Item.cache
                    { id := x.1, state := x.2.2.2.1, ch1 := x.2.2.2.2.1, ch2 := German.Gnt.noGnt,
                      ch3 := x.2.2.2.2.2.1 }} +
                {German.Item.dir
                    { cmd := German.Cmd.cmdS, ptr := x.1, exGntd := false, shr := {x.1} + x.2.2.2.2.2.2.1,
                      inv := x.2.2.2.2.2.2.2.1 }} +
              x.2.2.1),
        Unification.Unifier.bind
          fun (x : German.Items × German.CacheState × German.Req × German.Ack × German.Oids × ℕ × German.Oids) =>
          ((x.2.2.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.2, x.2.1, x.2.2.1, x.2.2.2.1, x.1), German.Cmd.cmdS, x.2.2.2.2.2.1,
            x.2.2.2.2.1 + {x.2.2.2.2.2.1}, x.2.2.2.2.2.2,
            {German.Item.cache
                  { id := x.2.2.2.2.2.1, state := x.2.1, ch1 := x.2.2.1, ch2 := German.Gnt.noGnt, ch3 := x.2.2.2.1 }} +
              x.1)] := by
  -- each unifier, instantiated, solves the problem
  simp only [sound, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  repeat' apply And.intro
  all_goals
    rintro γ ⟨x, rfl⟩
    simp only [unifiedBy, Narrowing.mayFire, German.sendGntSS, German.freeP]
  all_goals first
    | rfl
    | ac_rfl
    | simp only [ACU.plus_unit, ACU.unit_plus, ACU.plus_comm, ACU.plus_left_comm, ACU.plus_assoc]

theorem German.sendGntSS_inv.obligation_3 :
    Unification.complete (Narrowing.mayFire German.sendGntSS German.ownE)
      [Unification.Unifier.bind
          fun
            (x :
              ℕ ×
                ℕ ×
                  German.Oids ×
                    German.Items ×
                      German.CacheState ×
                        German.Req × German.Ack × German.Oids × German.Oids × ℕ × German.Req × German.Cmd) =>
          ((x.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
              {German.Item.cache
                      { id := x.2.2.2.2.2.2.2.2.2.1, state := German.CacheState.exclusive,
                        ch1 := x.2.2.2.2.2.2.2.2.2.2.1, ch2 := German.Gnt.noGnt, ch3 := German.Ack.noAck }} +
                  {German.Item.dir
                      { cmd := x.2.2.2.2.2.2.2.2.2.2.2, ptr := x.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.2.1},
                        inv := x.2.2.1 }} +
                x.2.2.2.1),
            x.2.2.2.2.2.2.2.2.2.2.2, x.2.1, x.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1,
            {German.Item.cache
                    { id := x.1, state := x.2.2.2.2.1, ch1 := x.2.2.2.2.2.1, ch2 := German.Gnt.noGnt,
                      ch3 := x.2.2.2.2.2.2.1 }} +
                {German.Item.dir
                    { cmd := German.Cmd.cmdS, ptr := x.1, exGntd := false, shr := {x.1} + x.2.2.2.2.2.2.2.1,
                      inv := x.2.2.2.2.2.2.2.2.1 }} +
              x.2.2.2.1),
        Unification.Unifier.bind
          fun (x : German.Oids × German.Oids × ℕ × German.Req × German.Cmd × ℕ × German.Oids × German.Items) =>
          ((x.2.2.1, x.1, x.2.1, German.CacheState.exclusive, x.2.2.2.1, German.Ack.noAck,
              {German.Item.dir
                    { cmd := x.2.2.2.2.1, ptr := x.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.1},
                      inv := x.2.2.2.2.2.2.1 }} +
                x.2.2.2.2.2.2.2),
            x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.1, x.2.2.2.1,
            {German.Item.dir
                  { cmd := German.Cmd.cmdS, ptr := x.2.2.1, exGntd := false, shr := x.1 + {x.2.2.1}, inv := x.2.1 }} +
              x.2.2.2.2.2.2.2)] := by
  udf_certify

theorem German.sendGntSS_inv.obligation_4 :
    Unification.sound (Narrowing.mayFire German.sendGntSS German.ownE)
      [Unification.Unifier.bind
          fun
            (x :
              ℕ ×
                ℕ ×
                  German.Oids ×
                    German.Items ×
                      German.CacheState ×
                        German.Req × German.Ack × German.Oids × German.Oids × ℕ × German.Req × German.Cmd) =>
          ((x.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
              {German.Item.cache
                      { id := x.2.2.2.2.2.2.2.2.2.1, state := German.CacheState.exclusive,
                        ch1 := x.2.2.2.2.2.2.2.2.2.2.1, ch2 := German.Gnt.noGnt, ch3 := German.Ack.noAck }} +
                  {German.Item.dir
                      { cmd := x.2.2.2.2.2.2.2.2.2.2.2, ptr := x.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.2.1},
                        inv := x.2.2.1 }} +
                x.2.2.2.1),
            x.2.2.2.2.2.2.2.2.2.2.2, x.2.1, x.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1,
            {German.Item.cache
                    { id := x.1, state := x.2.2.2.2.1, ch1 := x.2.2.2.2.2.1, ch2 := German.Gnt.noGnt,
                      ch3 := x.2.2.2.2.2.2.1 }} +
                {German.Item.dir
                    { cmd := German.Cmd.cmdS, ptr := x.1, exGntd := false, shr := {x.1} + x.2.2.2.2.2.2.2.1,
                      inv := x.2.2.2.2.2.2.2.2.1 }} +
              x.2.2.2.1),
        Unification.Unifier.bind
          fun (x : German.Oids × German.Oids × ℕ × German.Req × German.Cmd × ℕ × German.Oids × German.Items) =>
          ((x.2.2.1, x.1, x.2.1, German.CacheState.exclusive, x.2.2.2.1, German.Ack.noAck,
              {German.Item.dir
                    { cmd := x.2.2.2.2.1, ptr := x.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.1},
                      inv := x.2.2.2.2.2.2.1 }} +
                x.2.2.2.2.2.2.2),
            x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.1, x.2.2.2.1,
            {German.Item.dir
                  { cmd := German.Cmd.cmdS, ptr := x.2.2.1, exGntd := false, shr := x.1 + {x.2.2.1}, inv := x.2.1 }} +
              x.2.2.2.2.2.2.2)] := by
  -- each unifier, instantiated, solves the problem
  simp only [sound, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  repeat' apply And.intro
  all_goals
    rintro γ ⟨x, rfl⟩
    simp only [unifiedBy, Narrowing.mayFire, German.sendGntSS, German.ownE]
  all_goals first
    | rfl
    | ac_rfl
    | simp only [ACU.plus_unit, ACU.unit_plus, ACU.plus_comm, ACU.plus_left_comm, ACU.plus_assoc]

theorem German.sendGntSS_inv.obligation_5 :
    Unification.complete (Narrowing.mayFire German.sendGntSS German.ownG)
      [Unification.Unifier.bind
          fun
            (x :
              ℕ ×
                ℕ ×
                  German.Oids ×
                    German.Items ×
                      German.CacheState ×
                        German.Req × German.Ack × German.Oids × German.Oids × ℕ × German.Req × German.Cmd) =>
          ((x.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
              {German.Item.cache
                      { id := x.2.2.2.2.2.2.2.2.2.1, state := German.CacheState.invalid, ch1 := x.2.2.2.2.2.2.2.2.2.2.1,
                        ch2 := German.Gnt.gntE, ch3 := German.Ack.noAck }} +
                  {German.Item.dir
                      { cmd := x.2.2.2.2.2.2.2.2.2.2.2, ptr := x.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.2.1},
                        inv := x.2.2.1 }} +
                x.2.2.2.1),
            x.2.2.2.2.2.2.2.2.2.2.2, x.2.1, x.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1,
            {German.Item.cache
                    { id := x.1, state := x.2.2.2.2.1, ch1 := x.2.2.2.2.2.1, ch2 := German.Gnt.noGnt,
                      ch3 := x.2.2.2.2.2.2.1 }} +
                {German.Item.dir
                    { cmd := German.Cmd.cmdS, ptr := x.1, exGntd := false, shr := {x.1} + x.2.2.2.2.2.2.2.1,
                      inv := x.2.2.2.2.2.2.2.2.1 }} +
              x.2.2.2.1)] := by
  udf_certify

theorem German.sendGntSS_inv.obligation_6 :
    Unification.sound (Narrowing.mayFire German.sendGntSS German.ownG)
      [Unification.Unifier.bind
          fun
            (x :
              ℕ ×
                ℕ ×
                  German.Oids ×
                    German.Items ×
                      German.CacheState ×
                        German.Req × German.Ack × German.Oids × German.Oids × ℕ × German.Req × German.Cmd) =>
          ((x.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
              {German.Item.cache
                      { id := x.2.2.2.2.2.2.2.2.2.1, state := German.CacheState.invalid, ch1 := x.2.2.2.2.2.2.2.2.2.2.1,
                        ch2 := German.Gnt.gntE, ch3 := German.Ack.noAck }} +
                  {German.Item.dir
                      { cmd := x.2.2.2.2.2.2.2.2.2.2.2, ptr := x.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.2.1},
                        inv := x.2.2.1 }} +
                x.2.2.2.1),
            x.2.2.2.2.2.2.2.2.2.2.2, x.2.1, x.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1,
            {German.Item.cache
                    { id := x.1, state := x.2.2.2.2.1, ch1 := x.2.2.2.2.2.1, ch2 := German.Gnt.noGnt,
                      ch3 := x.2.2.2.2.2.2.1 }} +
                {German.Item.dir
                    { cmd := German.Cmd.cmdS, ptr := x.1, exGntd := false, shr := {x.1} + x.2.2.2.2.2.2.2.1,
                      inv := x.2.2.2.2.2.2.2.2.1 }} +
              x.2.2.2.1)] := by
  -- each unifier, instantiated, solves the problem
  simp only [sound, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  repeat' apply And.intro
  all_goals
    rintro γ ⟨x, rfl⟩
    simp only [unifiedBy, Narrowing.mayFire, German.sendGntSS, German.ownG]
  all_goals first
    | rfl
    | ac_rfl
    | simp only [ACU.plus_unit, ACU.unit_plus, ACU.plus_comm, ACU.plus_left_comm, ACU.plus_assoc]

theorem German.sendGntSS_inv.obligation_7 :
    Unification.complete (Narrowing.mayFire German.sendGntSS German.ownInv)
      [Unification.Unifier.bind
          fun
            (x :
              ℕ ×
                ℕ ×
                  German.Items ×
                    German.CacheState ×
                      German.Req × German.Ack × German.Oids × German.Oids × ℕ × German.Req × German.Cmd) =>
          ((x.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
              {German.Item.cache
                      { id := x.2.2.2.2.2.2.2.2.1, state := German.CacheState.exclusive, ch1 := x.2.2.2.2.2.2.2.2.2.1,
                        ch2 := German.Gnt.inv, ch3 := German.Ack.noAck }} +
                  {German.Item.dir
                      { cmd := x.2.2.2.2.2.2.2.2.2.2, ptr := x.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.1},
                        inv := ∅ }} +
                x.2.2.1),
            x.2.2.2.2.2.2.2.2.2.2, x.2.1, x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1,
            {German.Item.cache
                    { id := x.1, state := x.2.2.2.1, ch1 := x.2.2.2.2.1, ch2 := German.Gnt.noGnt,
                      ch3 := x.2.2.2.2.2.1 }} +
                {German.Item.dir
                    { cmd := German.Cmd.cmdS, ptr := x.1, exGntd := false, shr := {x.1} + x.2.2.2.2.2.2.1,
                      inv := x.2.2.2.2.2.2.2.1 }} +
              x.2.2.1)] := by
  udf_certify

theorem German.sendGntSS_inv.obligation_8 :
    Unification.sound (Narrowing.mayFire German.sendGntSS German.ownInv)
      [Unification.Unifier.bind
          fun
            (x :
              ℕ ×
                ℕ ×
                  German.Items ×
                    German.CacheState ×
                      German.Req × German.Ack × German.Oids × German.Oids × ℕ × German.Req × German.Cmd) =>
          ((x.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
              {German.Item.cache
                      { id := x.2.2.2.2.2.2.2.2.1, state := German.CacheState.exclusive, ch1 := x.2.2.2.2.2.2.2.2.2.1,
                        ch2 := German.Gnt.inv, ch3 := German.Ack.noAck }} +
                  {German.Item.dir
                      { cmd := x.2.2.2.2.2.2.2.2.2.2, ptr := x.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.1},
                        inv := ∅ }} +
                x.2.2.1),
            x.2.2.2.2.2.2.2.2.2.2, x.2.1, x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1,
            {German.Item.cache
                    { id := x.1, state := x.2.2.2.1, ch1 := x.2.2.2.2.1, ch2 := German.Gnt.noGnt,
                      ch3 := x.2.2.2.2.2.1 }} +
                {German.Item.dir
                    { cmd := German.Cmd.cmdS, ptr := x.1, exGntd := false, shr := {x.1} + x.2.2.2.2.2.2.1,
                      inv := x.2.2.2.2.2.2.2.1 }} +
              x.2.2.1)] := by
  -- each unifier, instantiated, solves the problem
  simp only [sound, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  repeat' apply And.intro
  all_goals
    rintro γ ⟨x, rfl⟩
    simp only [unifiedBy, Narrowing.mayFire, German.sendGntSS, German.ownInv]
  all_goals first
    | rfl
    | ac_rfl
    | simp only [ACU.plus_unit, ACU.unit_plus, ACU.plus_comm, ACU.plus_left_comm, ACU.plus_assoc]

theorem German.sendGntSS_inv.obligation_9 :
    Unification.complete (Narrowing.mayFire German.sendGntSS German.ownAck)
      [Unification.Unifier.bind
          fun
            (x :
              ℕ ×
                ℕ ×
                  German.Items ×
                    German.CacheState ×
                      German.Req × German.Ack × German.Oids × German.Oids × ℕ × German.Req × German.Cmd) =>
          ((x.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
              {German.Item.cache
                      { id := x.2.2.2.2.2.2.2.2.1, state := German.CacheState.invalid, ch1 := x.2.2.2.2.2.2.2.2.2.1,
                        ch2 := German.Gnt.noGnt, ch3 := German.Ack.invAck }} +
                  {German.Item.dir
                      { cmd := x.2.2.2.2.2.2.2.2.2.2, ptr := x.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.1},
                        inv := ∅ }} +
                x.2.2.1),
            x.2.2.2.2.2.2.2.2.2.2, x.2.1, x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1,
            {German.Item.cache
                    { id := x.1, state := x.2.2.2.1, ch1 := x.2.2.2.2.1, ch2 := German.Gnt.noGnt,
                      ch3 := x.2.2.2.2.2.1 }} +
                {German.Item.dir
                    { cmd := German.Cmd.cmdS, ptr := x.1, exGntd := false, shr := {x.1} + x.2.2.2.2.2.2.1,
                      inv := x.2.2.2.2.2.2.2.1 }} +
              x.2.2.1),
        Unification.Unifier.bind fun (x : German.Oids × German.Oids × ℕ × German.Req × German.Cmd × ℕ × German.Items) =>
          ((x.2.2.1, x.1, x.2.1, German.CacheState.invalid, x.2.2.2.1, German.Ack.invAck,
              {German.Item.dir
                    { cmd := x.2.2.2.2.1, ptr := x.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.1}, inv := ∅ }} +
                x.2.2.2.2.2.2),
            x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.1, x.2.2.2.1,
            {German.Item.dir
                  { cmd := German.Cmd.cmdS, ptr := x.2.2.1, exGntd := false, shr := x.1 + {x.2.2.1}, inv := x.2.1 }} +
              x.2.2.2.2.2.2)] := by
  udf_certify

theorem German.sendGntSS_inv.obligation_10 :
    Unification.sound (Narrowing.mayFire German.sendGntSS German.ownAck)
      [Unification.Unifier.bind
          fun
            (x :
              ℕ ×
                ℕ ×
                  German.Items ×
                    German.CacheState ×
                      German.Req × German.Ack × German.Oids × German.Oids × ℕ × German.Req × German.Cmd) =>
          ((x.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
              {German.Item.cache
                      { id := x.2.2.2.2.2.2.2.2.1, state := German.CacheState.invalid, ch1 := x.2.2.2.2.2.2.2.2.2.1,
                        ch2 := German.Gnt.noGnt, ch3 := German.Ack.invAck }} +
                  {German.Item.dir
                      { cmd := x.2.2.2.2.2.2.2.2.2.2, ptr := x.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.1},
                        inv := ∅ }} +
                x.2.2.1),
            x.2.2.2.2.2.2.2.2.2.2, x.2.1, x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1,
            {German.Item.cache
                    { id := x.1, state := x.2.2.2.1, ch1 := x.2.2.2.2.1, ch2 := German.Gnt.noGnt,
                      ch3 := x.2.2.2.2.2.1 }} +
                {German.Item.dir
                    { cmd := German.Cmd.cmdS, ptr := x.1, exGntd := false, shr := {x.1} + x.2.2.2.2.2.2.1,
                      inv := x.2.2.2.2.2.2.2.1 }} +
              x.2.2.1),
        Unification.Unifier.bind fun (x : German.Oids × German.Oids × ℕ × German.Req × German.Cmd × ℕ × German.Items) =>
          ((x.2.2.1, x.1, x.2.1, German.CacheState.invalid, x.2.2.2.1, German.Ack.invAck,
              {German.Item.dir
                    { cmd := x.2.2.2.2.1, ptr := x.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.1}, inv := ∅ }} +
                x.2.2.2.2.2.2),
            x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.1, x.2.2.2.1,
            {German.Item.dir
                  { cmd := German.Cmd.cmdS, ptr := x.2.2.1, exGntd := false, shr := x.1 + {x.2.2.1}, inv := x.2.1 }} +
              x.2.2.2.2.2.2)] := by
  -- each unifier, instantiated, solves the problem
  simp only [sound, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  repeat' apply And.intro
  all_goals
    rintro γ ⟨x, rfl⟩
    simp only [unifiedBy, Narrowing.mayFire, German.sendGntSS, German.ownAck]
  all_goals first
    | rfl
    | ac_rfl
    | simp only [ACU.plus_unit, ACU.unit_plus, ACU.plus_comm, ACU.plus_left_comm, ACU.plus_assoc]

theorem German.sendGntE_inv.obligation_1 :
    Unification.complete (Narrowing.mayFire German.sendGntE German.freeP)
      [Unification.Unifier.bind
          fun
            (x :
              ℕ ×
                German.Items ×
                  German.CacheState ×
                    German.Req × German.Ack × German.Oids × German.Cmd × ℕ × German.Oids × German.Oids) =>
          ((x.1, x.2.2.2.2.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
              {German.Item.dir
                    { cmd := x.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.1, exGntd := false, shr := x.2.2.2.2.2.2.2.2.1,
                      inv := x.2.2.2.2.2.2.2.2.2 }} +
                x.2.1),
            x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2,
            {German.Item.cache
                    { id := x.1, state := x.2.2.1, ch1 := x.2.2.2.1, ch2 := German.Gnt.noGnt, ch3 := x.2.2.2.2.1 }} +
                {German.Item.dir
                    { cmd := German.Cmd.cmdE, ptr := x.1, exGntd := false, shr := ∅, inv := x.2.2.2.2.2.1 }} +
              x.2.1),
        Unification.Unifier.bind
          fun (x : German.Items × German.CacheState × German.Req × German.Ack × ℕ × German.Oids) =>
          ((x.2.2.2.2.1, x.2.2.2.2.2, x.2.1, x.2.2.1, x.2.2.2.1, x.1), German.Cmd.cmdE, x.2.2.2.2.1, ∅, x.2.2.2.2.2,
            {German.Item.cache
                  { id := x.2.2.2.2.1, state := x.2.1, ch1 := x.2.2.1, ch2 := German.Gnt.noGnt, ch3 := x.2.2.2.1 }} +
              x.1)] := by
  udf_certify

theorem German.sendGntE_inv.obligation_2 :
    Unification.sound (Narrowing.mayFire German.sendGntE German.freeP)
      [Unification.Unifier.bind
          fun
            (x :
              ℕ ×
                German.Items ×
                  German.CacheState ×
                    German.Req × German.Ack × German.Oids × German.Cmd × ℕ × German.Oids × German.Oids) =>
          ((x.1, x.2.2.2.2.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
              {German.Item.dir
                    { cmd := x.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.1, exGntd := false, shr := x.2.2.2.2.2.2.2.2.1,
                      inv := x.2.2.2.2.2.2.2.2.2 }} +
                x.2.1),
            x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2,
            {German.Item.cache
                    { id := x.1, state := x.2.2.1, ch1 := x.2.2.2.1, ch2 := German.Gnt.noGnt, ch3 := x.2.2.2.2.1 }} +
                {German.Item.dir
                    { cmd := German.Cmd.cmdE, ptr := x.1, exGntd := false, shr := ∅, inv := x.2.2.2.2.2.1 }} +
              x.2.1),
        Unification.Unifier.bind
          fun (x : German.Items × German.CacheState × German.Req × German.Ack × ℕ × German.Oids) =>
          ((x.2.2.2.2.1, x.2.2.2.2.2, x.2.1, x.2.2.1, x.2.2.2.1, x.1), German.Cmd.cmdE, x.2.2.2.2.1, ∅, x.2.2.2.2.2,
            {German.Item.cache
                  { id := x.2.2.2.2.1, state := x.2.1, ch1 := x.2.2.1, ch2 := German.Gnt.noGnt, ch3 := x.2.2.2.1 }} +
              x.1)] := by
  -- each unifier, instantiated, solves the problem
  simp only [sound, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  repeat' apply And.intro
  all_goals
    rintro γ ⟨x, rfl⟩
    simp only [unifiedBy, Narrowing.mayFire, German.sendGntE, German.freeP]
  all_goals first
    | rfl
    | ac_rfl
    | simp only [ACU.plus_unit, ACU.unit_plus, ACU.plus_comm, ACU.plus_left_comm, ACU.plus_assoc]

theorem German.sendGntE_inv.obligation_3 :
    Unification.complete (Narrowing.mayFire German.sendGntE German.ownE)
      [Unification.Unifier.bind
          fun
            (x :
              ℕ ×
                German.Oids ×
                  German.Items ×
                    German.CacheState × German.Req × German.Ack × German.Oids × ℕ × German.Req × German.Cmd × ℕ) =>
          ((x.1, x.2.2.2.2.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
              {German.Item.cache
                      { id := x.2.2.2.2.2.2.2.1, state := German.CacheState.exclusive, ch1 := x.2.2.2.2.2.2.2.2.1,
                        ch2 := German.Gnt.noGnt, ch3 := German.Ack.noAck }} +
                  {German.Item.dir
                      { cmd := x.2.2.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.2.2, exGntd := true,
                        shr := {x.2.2.2.2.2.2.2.1}, inv := x.2.1 }} +
                x.2.2.1),
            x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2, x.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1,
            {German.Item.cache
                    { id := x.1, state := x.2.2.2.1, ch1 := x.2.2.2.2.1, ch2 := German.Gnt.noGnt,
                      ch3 := x.2.2.2.2.2.1 }} +
                {German.Item.dir
                    { cmd := German.Cmd.cmdE, ptr := x.1, exGntd := false, shr := ∅, inv := x.2.2.2.2.2.2.1 }} +
              x.2.2.1),
        Unification.Unifier.bind fun (x : German.Oids × ℕ × German.Req × German.Cmd × ℕ × German.Oids × German.Items) =>
          ((x.2.1, x.1, German.CacheState.exclusive, x.2.2.1, German.Ack.noAck,
              {German.Item.dir
                    { cmd := x.2.2.2.1, ptr := x.2.2.2.2.1, exGntd := true, shr := {x.2.1}, inv := x.2.2.2.2.2.1 }} +
                x.2.2.2.2.2.2),
            x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.1, x.2.2.1,
            {German.Item.dir { cmd := German.Cmd.cmdE, ptr := x.2.1, exGntd := false, shr := ∅, inv := x.1 }} +
              x.2.2.2.2.2.2)] := by
  udf_certify

theorem German.sendGntE_inv.obligation_4 :
    Unification.sound (Narrowing.mayFire German.sendGntE German.ownE)
      [Unification.Unifier.bind
          fun
            (x :
              ℕ ×
                German.Oids ×
                  German.Items ×
                    German.CacheState × German.Req × German.Ack × German.Oids × ℕ × German.Req × German.Cmd × ℕ) =>
          ((x.1, x.2.2.2.2.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
              {German.Item.cache
                      { id := x.2.2.2.2.2.2.2.1, state := German.CacheState.exclusive, ch1 := x.2.2.2.2.2.2.2.2.1,
                        ch2 := German.Gnt.noGnt, ch3 := German.Ack.noAck }} +
                  {German.Item.dir
                      { cmd := x.2.2.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.2.2, exGntd := true,
                        shr := {x.2.2.2.2.2.2.2.1}, inv := x.2.1 }} +
                x.2.2.1),
            x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2, x.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1,
            {German.Item.cache
                    { id := x.1, state := x.2.2.2.1, ch1 := x.2.2.2.2.1, ch2 := German.Gnt.noGnt,
                      ch3 := x.2.2.2.2.2.1 }} +
                {German.Item.dir
                    { cmd := German.Cmd.cmdE, ptr := x.1, exGntd := false, shr := ∅, inv := x.2.2.2.2.2.2.1 }} +
              x.2.2.1),
        Unification.Unifier.bind fun (x : German.Oids × ℕ × German.Req × German.Cmd × ℕ × German.Oids × German.Items) =>
          ((x.2.1, x.1, German.CacheState.exclusive, x.2.2.1, German.Ack.noAck,
              {German.Item.dir
                    { cmd := x.2.2.2.1, ptr := x.2.2.2.2.1, exGntd := true, shr := {x.2.1}, inv := x.2.2.2.2.2.1 }} +
                x.2.2.2.2.2.2),
            x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.1, x.2.2.1,
            {German.Item.dir { cmd := German.Cmd.cmdE, ptr := x.2.1, exGntd := false, shr := ∅, inv := x.1 }} +
              x.2.2.2.2.2.2)] := by
  -- each unifier, instantiated, solves the problem
  simp only [sound, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  repeat' apply And.intro
  all_goals
    rintro γ ⟨x, rfl⟩
    simp only [unifiedBy, Narrowing.mayFire, German.sendGntE, German.ownE]
  all_goals first
    | rfl
    | ac_rfl
    | simp only [ACU.plus_unit, ACU.unit_plus, ACU.plus_comm, ACU.plus_left_comm, ACU.plus_assoc]

theorem German.sendGntE_inv.obligation_5 :
    Unification.complete (Narrowing.mayFire German.sendGntE German.ownG)
      [Unification.Unifier.bind
          fun
            (x :
              ℕ ×
                German.Oids ×
                  German.Items ×
                    German.CacheState × German.Req × German.Ack × German.Oids × ℕ × German.Req × German.Cmd × ℕ) =>
          ((x.1, x.2.2.2.2.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
              {German.Item.cache
                      { id := x.2.2.2.2.2.2.2.1, state := German.CacheState.invalid, ch1 := x.2.2.2.2.2.2.2.2.1,
                        ch2 := German.Gnt.gntE, ch3 := German.Ack.noAck }} +
                  {German.Item.dir
                      { cmd := x.2.2.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.2.2, exGntd := true,
                        shr := {x.2.2.2.2.2.2.2.1}, inv := x.2.1 }} +
                x.2.2.1),
            x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2, x.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1,
            {German.Item.cache
                    { id := x.1, state := x.2.2.2.1, ch1 := x.2.2.2.2.1, ch2 := German.Gnt.noGnt,
                      ch3 := x.2.2.2.2.2.1 }} +
                {German.Item.dir
                    { cmd := German.Cmd.cmdE, ptr := x.1, exGntd := false, shr := ∅, inv := x.2.2.2.2.2.2.1 }} +
              x.2.2.1)] := by
  udf_certify

theorem German.sendGntE_inv.obligation_6 :
    Unification.sound (Narrowing.mayFire German.sendGntE German.ownG)
      [Unification.Unifier.bind
          fun
            (x :
              ℕ ×
                German.Oids ×
                  German.Items ×
                    German.CacheState × German.Req × German.Ack × German.Oids × ℕ × German.Req × German.Cmd × ℕ) =>
          ((x.1, x.2.2.2.2.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
              {German.Item.cache
                      { id := x.2.2.2.2.2.2.2.1, state := German.CacheState.invalid, ch1 := x.2.2.2.2.2.2.2.2.1,
                        ch2 := German.Gnt.gntE, ch3 := German.Ack.noAck }} +
                  {German.Item.dir
                      { cmd := x.2.2.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.2.2, exGntd := true,
                        shr := {x.2.2.2.2.2.2.2.1}, inv := x.2.1 }} +
                x.2.2.1),
            x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2, x.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1,
            {German.Item.cache
                    { id := x.1, state := x.2.2.2.1, ch1 := x.2.2.2.2.1, ch2 := German.Gnt.noGnt,
                      ch3 := x.2.2.2.2.2.1 }} +
                {German.Item.dir
                    { cmd := German.Cmd.cmdE, ptr := x.1, exGntd := false, shr := ∅, inv := x.2.2.2.2.2.2.1 }} +
              x.2.2.1)] := by
  -- each unifier, instantiated, solves the problem
  simp only [sound, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  repeat' apply And.intro
  all_goals
    rintro γ ⟨x, rfl⟩
    simp only [unifiedBy, Narrowing.mayFire, German.sendGntE, German.ownG]
  all_goals first
    | rfl
    | ac_rfl
    | simp only [ACU.plus_unit, ACU.unit_plus, ACU.plus_comm, ACU.plus_left_comm, ACU.plus_assoc]

theorem German.sendGntE_inv.obligation_7 :
    Unification.complete (Narrowing.mayFire German.sendGntE German.ownInv)
      [Unification.Unifier.bind
          fun
            (x :
              ℕ ×
                German.Items ×
                  German.CacheState × German.Req × German.Ack × German.Oids × ℕ × German.Req × German.Cmd × ℕ) =>
          ((x.1, x.2.2.2.2.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
              {German.Item.cache
                      { id := x.2.2.2.2.2.2.1, state := German.CacheState.exclusive, ch1 := x.2.2.2.2.2.2.2.1,
                        ch2 := German.Gnt.inv, ch3 := German.Ack.noAck }} +
                  {German.Item.dir
                      { cmd := x.2.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.2, exGntd := true,
                        shr := {x.2.2.2.2.2.2.1}, inv := ∅ }} +
                x.2.1),
            x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1,
            {German.Item.cache
                    { id := x.1, state := x.2.2.1, ch1 := x.2.2.2.1, ch2 := German.Gnt.noGnt, ch3 := x.2.2.2.2.1 }} +
                {German.Item.dir
                    { cmd := German.Cmd.cmdE, ptr := x.1, exGntd := false, shr := ∅, inv := x.2.2.2.2.2.1 }} +
              x.2.1)] := by
  udf_certify

theorem German.sendGntE_inv.obligation_8 :
    Unification.sound (Narrowing.mayFire German.sendGntE German.ownInv)
      [Unification.Unifier.bind
          fun
            (x :
              ℕ ×
                German.Items ×
                  German.CacheState × German.Req × German.Ack × German.Oids × ℕ × German.Req × German.Cmd × ℕ) =>
          ((x.1, x.2.2.2.2.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
              {German.Item.cache
                      { id := x.2.2.2.2.2.2.1, state := German.CacheState.exclusive, ch1 := x.2.2.2.2.2.2.2.1,
                        ch2 := German.Gnt.inv, ch3 := German.Ack.noAck }} +
                  {German.Item.dir
                      { cmd := x.2.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.2, exGntd := true,
                        shr := {x.2.2.2.2.2.2.1}, inv := ∅ }} +
                x.2.1),
            x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1,
            {German.Item.cache
                    { id := x.1, state := x.2.2.1, ch1 := x.2.2.2.1, ch2 := German.Gnt.noGnt, ch3 := x.2.2.2.2.1 }} +
                {German.Item.dir
                    { cmd := German.Cmd.cmdE, ptr := x.1, exGntd := false, shr := ∅, inv := x.2.2.2.2.2.1 }} +
              x.2.1)] := by
  -- each unifier, instantiated, solves the problem
  simp only [sound, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  repeat' apply And.intro
  all_goals
    rintro γ ⟨x, rfl⟩
    simp only [unifiedBy, Narrowing.mayFire, German.sendGntE, German.ownInv]
  all_goals first
    | rfl
    | ac_rfl
    | simp only [ACU.plus_unit, ACU.unit_plus, ACU.plus_comm, ACU.plus_left_comm, ACU.plus_assoc]

theorem German.sendGntE_inv.obligation_9 :
    Unification.complete (Narrowing.mayFire German.sendGntE German.ownAck)
      [Unification.Unifier.bind
          fun
            (x :
              ℕ ×
                German.Items ×
                  German.CacheState × German.Req × German.Ack × German.Oids × ℕ × German.Req × German.Cmd × ℕ) =>
          ((x.1, x.2.2.2.2.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
              {German.Item.cache
                      { id := x.2.2.2.2.2.2.1, state := German.CacheState.invalid, ch1 := x.2.2.2.2.2.2.2.1,
                        ch2 := German.Gnt.noGnt, ch3 := German.Ack.invAck }} +
                  {German.Item.dir
                      { cmd := x.2.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.2, exGntd := true,
                        shr := {x.2.2.2.2.2.2.1}, inv := ∅ }} +
                x.2.1),
            x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1,
            {German.Item.cache
                    { id := x.1, state := x.2.2.1, ch1 := x.2.2.2.1, ch2 := German.Gnt.noGnt, ch3 := x.2.2.2.2.1 }} +
                {German.Item.dir
                    { cmd := German.Cmd.cmdE, ptr := x.1, exGntd := false, shr := ∅, inv := x.2.2.2.2.2.1 }} +
              x.2.1),
        Unification.Unifier.bind fun (x : German.Oids × ℕ × German.Req × German.Cmd × ℕ × German.Items) =>
          ((x.2.1, x.1, German.CacheState.invalid, x.2.2.1, German.Ack.invAck,
              {German.Item.dir { cmd := x.2.2.2.1, ptr := x.2.2.2.2.1, exGntd := true, shr := {x.2.1}, inv := ∅ }} +
                x.2.2.2.2.2),
            x.2.2.2.1, x.2.2.2.2.1, x.2.1, x.2.2.1,
            {German.Item.dir { cmd := German.Cmd.cmdE, ptr := x.2.1, exGntd := false, shr := ∅, inv := x.1 }} +
              x.2.2.2.2.2)] := by
  udf_certify

theorem German.sendGntE_inv.obligation_10 :
    Unification.sound (Narrowing.mayFire German.sendGntE German.ownAck)
      [Unification.Unifier.bind
          fun
            (x :
              ℕ ×
                German.Items ×
                  German.CacheState × German.Req × German.Ack × German.Oids × ℕ × German.Req × German.Cmd × ℕ) =>
          ((x.1, x.2.2.2.2.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
              {German.Item.cache
                      { id := x.2.2.2.2.2.2.1, state := German.CacheState.invalid, ch1 := x.2.2.2.2.2.2.2.1,
                        ch2 := German.Gnt.noGnt, ch3 := German.Ack.invAck }} +
                  {German.Item.dir
                      { cmd := x.2.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.2, exGntd := true,
                        shr := {x.2.2.2.2.2.2.1}, inv := ∅ }} +
                x.2.1),
            x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1,
            {German.Item.cache
                    { id := x.1, state := x.2.2.1, ch1 := x.2.2.2.1, ch2 := German.Gnt.noGnt, ch3 := x.2.2.2.2.1 }} +
                {German.Item.dir
                    { cmd := German.Cmd.cmdE, ptr := x.1, exGntd := false, shr := ∅, inv := x.2.2.2.2.2.1 }} +
              x.2.1),
        Unification.Unifier.bind fun (x : German.Oids × ℕ × German.Req × German.Cmd × ℕ × German.Items) =>
          ((x.2.1, x.1, German.CacheState.invalid, x.2.2.1, German.Ack.invAck,
              {German.Item.dir { cmd := x.2.2.2.1, ptr := x.2.2.2.2.1, exGntd := true, shr := {x.2.1}, inv := ∅ }} +
                x.2.2.2.2.2),
            x.2.2.2.1, x.2.2.2.2.1, x.2.1, x.2.2.1,
            {German.Item.dir { cmd := German.Cmd.cmdE, ptr := x.2.1, exGntd := false, shr := ∅, inv := x.1 }} +
              x.2.2.2.2.2)] := by
  -- each unifier, instantiated, solves the problem
  simp only [sound, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  repeat' apply And.intro
  all_goals
    rintro γ ⟨x, rfl⟩
    simp only [unifiedBy, Narrowing.mayFire, German.sendGntE, German.ownAck]
  all_goals first
    | rfl
    | ac_rfl
    | simp only [ACU.plus_unit, ACU.unit_plus, ACU.plus_comm, ACU.plus_left_comm, ACU.plus_assoc]

theorem German.recvGntS_inv.obligation_1 :
    Unification.complete (Narrowing.mayFire German.recvGntS German.freeP)
      [Unification.Unifier.bind
          fun
            (x :
              ℕ ×
                German.CacheState ×
                  German.Req × German.Ack × German.Cmd × ℕ × German.Oids × German.Oids × German.Items) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {German.Item.dir
                    { cmd := x.2.2.2.2.1, ptr := x.2.2.2.2.2.1, exGntd := false, shr := x.2.2.2.2.2.2.1,
                      inv := x.2.2.2.2.2.2.2.1 }} +
                x.2.2.2.2.2.2.2.2),
            x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1,
            {German.Item.cache
                  { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := German.Gnt.gntS, ch3 := x.2.2.2.1 }} +
              x.2.2.2.2.2.2.2.2)] := by
  udf_certify

theorem German.recvGntS_inv.obligation_2 :
    Unification.sound (Narrowing.mayFire German.recvGntS German.freeP)
      [Unification.Unifier.bind
          fun
            (x :
              ℕ ×
                German.CacheState ×
                  German.Req × German.Ack × German.Cmd × ℕ × German.Oids × German.Oids × German.Items) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {German.Item.dir
                    { cmd := x.2.2.2.2.1, ptr := x.2.2.2.2.2.1, exGntd := false, shr := x.2.2.2.2.2.2.1,
                      inv := x.2.2.2.2.2.2.2.1 }} +
                x.2.2.2.2.2.2.2.2),
            x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1,
            {German.Item.cache
                  { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := German.Gnt.gntS, ch3 := x.2.2.2.1 }} +
              x.2.2.2.2.2.2.2.2)] := by
  -- each unifier, instantiated, solves the problem
  simp only [sound, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  repeat' apply And.intro
  all_goals
    rintro γ ⟨x, rfl⟩
    simp only [unifiedBy, Narrowing.mayFire, German.recvGntS, German.freeP]
  all_goals first
    | rfl
    | ac_rfl
    | simp only [ACU.plus_unit, ACU.unit_plus, ACU.plus_comm, ACU.plus_left_comm, ACU.plus_assoc]

theorem German.recvGntS_inv.obligation_3 :
    Unification.complete (Narrowing.mayFire German.recvGntS German.ownE)
      [Unification.Unifier.bind
          fun
            (x :
              ℕ ×
                German.Items ×
                  German.CacheState × German.Req × German.Ack × ℕ × German.Req × German.Cmd × ℕ × German.Oids) =>
          ((x.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
              {German.Item.cache
                      { id := x.2.2.2.2.2.1, state := German.CacheState.exclusive, ch1 := x.2.2.2.2.2.2.1,
                        ch2 := German.Gnt.noGnt, ch3 := German.Ack.noAck }} +
                  {German.Item.dir
                      { cmd := x.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.2.1},
                        inv := x.2.2.2.2.2.2.2.2.2 }} +
                x.2.1),
            x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
            {German.Item.cache
                  { id := x.1, state := x.2.2.1, ch1 := x.2.2.2.1, ch2 := German.Gnt.gntS, ch3 := x.2.2.2.2.1 }} +
              x.2.1)] := by
  udf_certify

theorem German.recvGntS_inv.obligation_4 :
    Unification.sound (Narrowing.mayFire German.recvGntS German.ownE)
      [Unification.Unifier.bind
          fun
            (x :
              ℕ ×
                German.Items ×
                  German.CacheState × German.Req × German.Ack × ℕ × German.Req × German.Cmd × ℕ × German.Oids) =>
          ((x.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
              {German.Item.cache
                      { id := x.2.2.2.2.2.1, state := German.CacheState.exclusive, ch1 := x.2.2.2.2.2.2.1,
                        ch2 := German.Gnt.noGnt, ch3 := German.Ack.noAck }} +
                  {German.Item.dir
                      { cmd := x.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.2.1},
                        inv := x.2.2.2.2.2.2.2.2.2 }} +
                x.2.1),
            x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
            {German.Item.cache
                  { id := x.1, state := x.2.2.1, ch1 := x.2.2.2.1, ch2 := German.Gnt.gntS, ch3 := x.2.2.2.2.1 }} +
              x.2.1)] := by
  -- each unifier, instantiated, solves the problem
  simp only [sound, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  repeat' apply And.intro
  all_goals
    rintro γ ⟨x, rfl⟩
    simp only [unifiedBy, Narrowing.mayFire, German.recvGntS, German.ownE]
  all_goals first
    | rfl
    | ac_rfl
    | simp only [ACU.plus_unit, ACU.unit_plus, ACU.plus_comm, ACU.plus_left_comm, ACU.plus_assoc]

theorem German.recvGntS_inv.obligation_5 :
    Unification.complete (Narrowing.mayFire German.recvGntS German.ownG)
      [Unification.Unifier.bind
          fun
            (x :
              ℕ ×
                German.Items ×
                  German.CacheState × German.Req × German.Ack × ℕ × German.Req × German.Cmd × ℕ × German.Oids) =>
          ((x.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
              {German.Item.cache
                      { id := x.2.2.2.2.2.1, state := German.CacheState.invalid, ch1 := x.2.2.2.2.2.2.1,
                        ch2 := German.Gnt.gntE, ch3 := German.Ack.noAck }} +
                  {German.Item.dir
                      { cmd := x.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.2.1},
                        inv := x.2.2.2.2.2.2.2.2.2 }} +
                x.2.1),
            x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
            {German.Item.cache
                  { id := x.1, state := x.2.2.1, ch1 := x.2.2.2.1, ch2 := German.Gnt.gntS, ch3 := x.2.2.2.2.1 }} +
              x.2.1)] := by
  udf_certify

theorem German.recvGntS_inv.obligation_6 :
    Unification.sound (Narrowing.mayFire German.recvGntS German.ownG)
      [Unification.Unifier.bind
          fun
            (x :
              ℕ ×
                German.Items ×
                  German.CacheState × German.Req × German.Ack × ℕ × German.Req × German.Cmd × ℕ × German.Oids) =>
          ((x.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
              {German.Item.cache
                      { id := x.2.2.2.2.2.1, state := German.CacheState.invalid, ch1 := x.2.2.2.2.2.2.1,
                        ch2 := German.Gnt.gntE, ch3 := German.Ack.noAck }} +
                  {German.Item.dir
                      { cmd := x.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.2.1},
                        inv := x.2.2.2.2.2.2.2.2.2 }} +
                x.2.1),
            x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
            {German.Item.cache
                  { id := x.1, state := x.2.2.1, ch1 := x.2.2.2.1, ch2 := German.Gnt.gntS, ch3 := x.2.2.2.2.1 }} +
              x.2.1)] := by
  -- each unifier, instantiated, solves the problem
  simp only [sound, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  repeat' apply And.intro
  all_goals
    rintro γ ⟨x, rfl⟩
    simp only [unifiedBy, Narrowing.mayFire, German.recvGntS, German.ownG]
  all_goals first
    | rfl
    | ac_rfl
    | simp only [ACU.plus_unit, ACU.unit_plus, ACU.plus_comm, ACU.plus_left_comm, ACU.plus_assoc]

theorem German.recvGntS_inv.obligation_7 :
    Unification.complete (Narrowing.mayFire German.recvGntS German.ownInv)
      [Unification.Unifier.bind
          fun (x : ℕ × German.CacheState × German.Req × German.Ack × ℕ × German.Req × German.Cmd × ℕ × German.Items) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {German.Item.cache
                      { id := x.2.2.2.2.1, state := German.CacheState.exclusive, ch1 := x.2.2.2.2.2.1,
                        ch2 := German.Gnt.inv, ch3 := German.Ack.noAck }} +
                  {German.Item.dir
                      { cmd := x.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.1},
                        inv := ∅ }} +
                x.2.2.2.2.2.2.2.2),
            x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
            {German.Item.cache
                  { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := German.Gnt.gntS, ch3 := x.2.2.2.1 }} +
              x.2.2.2.2.2.2.2.2)] := by
  udf_certify

theorem German.recvGntS_inv.obligation_8 :
    Unification.sound (Narrowing.mayFire German.recvGntS German.ownInv)
      [Unification.Unifier.bind
          fun (x : ℕ × German.CacheState × German.Req × German.Ack × ℕ × German.Req × German.Cmd × ℕ × German.Items) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {German.Item.cache
                      { id := x.2.2.2.2.1, state := German.CacheState.exclusive, ch1 := x.2.2.2.2.2.1,
                        ch2 := German.Gnt.inv, ch3 := German.Ack.noAck }} +
                  {German.Item.dir
                      { cmd := x.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.1},
                        inv := ∅ }} +
                x.2.2.2.2.2.2.2.2),
            x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
            {German.Item.cache
                  { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := German.Gnt.gntS, ch3 := x.2.2.2.1 }} +
              x.2.2.2.2.2.2.2.2)] := by
  -- each unifier, instantiated, solves the problem
  simp only [sound, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  repeat' apply And.intro
  all_goals
    rintro γ ⟨x, rfl⟩
    simp only [unifiedBy, Narrowing.mayFire, German.recvGntS, German.ownInv]
  all_goals first
    | rfl
    | ac_rfl
    | simp only [ACU.plus_unit, ACU.unit_plus, ACU.plus_comm, ACU.plus_left_comm, ACU.plus_assoc]

theorem German.recvGntS_inv.obligation_9 :
    Unification.complete (Narrowing.mayFire German.recvGntS German.ownAck)
      [Unification.Unifier.bind
          fun (x : ℕ × German.CacheState × German.Req × German.Ack × ℕ × German.Req × German.Cmd × ℕ × German.Items) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {German.Item.cache
                      { id := x.2.2.2.2.1, state := German.CacheState.invalid, ch1 := x.2.2.2.2.2.1,
                        ch2 := German.Gnt.noGnt, ch3 := German.Ack.invAck }} +
                  {German.Item.dir
                      { cmd := x.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.1},
                        inv := ∅ }} +
                x.2.2.2.2.2.2.2.2),
            x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
            {German.Item.cache
                  { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := German.Gnt.gntS, ch3 := x.2.2.2.1 }} +
              x.2.2.2.2.2.2.2.2)] := by
  udf_certify

theorem German.recvGntS_inv.obligation_10 :
    Unification.sound (Narrowing.mayFire German.recvGntS German.ownAck)
      [Unification.Unifier.bind
          fun (x : ℕ × German.CacheState × German.Req × German.Ack × ℕ × German.Req × German.Cmd × ℕ × German.Items) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {German.Item.cache
                      { id := x.2.2.2.2.1, state := German.CacheState.invalid, ch1 := x.2.2.2.2.2.1,
                        ch2 := German.Gnt.noGnt, ch3 := German.Ack.invAck }} +
                  {German.Item.dir
                      { cmd := x.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.1},
                        inv := ∅ }} +
                x.2.2.2.2.2.2.2.2),
            x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
            {German.Item.cache
                  { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := German.Gnt.gntS, ch3 := x.2.2.2.1 }} +
              x.2.2.2.2.2.2.2.2)] := by
  -- each unifier, instantiated, solves the problem
  simp only [sound, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  repeat' apply And.intro
  all_goals
    rintro γ ⟨x, rfl⟩
    simp only [unifiedBy, Narrowing.mayFire, German.recvGntS, German.ownAck]
  all_goals first
    | rfl
    | ac_rfl
    | simp only [ACU.plus_unit, ACU.unit_plus, ACU.plus_comm, ACU.plus_left_comm, ACU.plus_assoc]

theorem German.recvGntE_inv.obligation_1 :
    Unification.complete (Narrowing.mayFire German.recvGntE German.freeP)
      [Unification.Unifier.bind
          fun
            (x :
              ℕ ×
                German.CacheState ×
                  German.Req × German.Ack × German.Cmd × ℕ × German.Oids × German.Oids × German.Items) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {German.Item.dir
                    { cmd := x.2.2.2.2.1, ptr := x.2.2.2.2.2.1, exGntd := false, shr := x.2.2.2.2.2.2.1,
                      inv := x.2.2.2.2.2.2.2.1 }} +
                x.2.2.2.2.2.2.2.2),
            x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1,
            {German.Item.cache
                  { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := German.Gnt.gntE, ch3 := x.2.2.2.1 }} +
              x.2.2.2.2.2.2.2.2)] := by
  udf_certify

theorem German.recvGntE_inv.obligation_2 :
    Unification.sound (Narrowing.mayFire German.recvGntE German.freeP)
      [Unification.Unifier.bind
          fun
            (x :
              ℕ ×
                German.CacheState ×
                  German.Req × German.Ack × German.Cmd × ℕ × German.Oids × German.Oids × German.Items) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {German.Item.dir
                    { cmd := x.2.2.2.2.1, ptr := x.2.2.2.2.2.1, exGntd := false, shr := x.2.2.2.2.2.2.1,
                      inv := x.2.2.2.2.2.2.2.1 }} +
                x.2.2.2.2.2.2.2.2),
            x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1,
            {German.Item.cache
                  { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := German.Gnt.gntE, ch3 := x.2.2.2.1 }} +
              x.2.2.2.2.2.2.2.2)] := by
  -- each unifier, instantiated, solves the problem
  simp only [sound, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  repeat' apply And.intro
  all_goals
    rintro γ ⟨x, rfl⟩
    simp only [unifiedBy, Narrowing.mayFire, German.recvGntE, German.freeP]
  all_goals first
    | rfl
    | ac_rfl
    | simp only [ACU.plus_unit, ACU.unit_plus, ACU.plus_comm, ACU.plus_left_comm, ACU.plus_assoc]

theorem German.recvGntE_inv.obligation_3 :
    Unification.complete (Narrowing.mayFire German.recvGntE German.ownE)
      [Unification.Unifier.bind
          fun
            (x :
              ℕ ×
                German.Items ×
                  German.CacheState × German.Req × German.Ack × ℕ × German.Req × German.Cmd × ℕ × German.Oids) =>
          ((x.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
              {German.Item.cache
                      { id := x.2.2.2.2.2.1, state := German.CacheState.exclusive, ch1 := x.2.2.2.2.2.2.1,
                        ch2 := German.Gnt.noGnt, ch3 := German.Ack.noAck }} +
                  {German.Item.dir
                      { cmd := x.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.2.1},
                        inv := x.2.2.2.2.2.2.2.2.2 }} +
                x.2.1),
            x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
            {German.Item.cache
                  { id := x.1, state := x.2.2.1, ch1 := x.2.2.2.1, ch2 := German.Gnt.gntE, ch3 := x.2.2.2.2.1 }} +
              x.2.1)] := by
  udf_certify

theorem German.recvGntE_inv.obligation_4 :
    Unification.sound (Narrowing.mayFire German.recvGntE German.ownE)
      [Unification.Unifier.bind
          fun
            (x :
              ℕ ×
                German.Items ×
                  German.CacheState × German.Req × German.Ack × ℕ × German.Req × German.Cmd × ℕ × German.Oids) =>
          ((x.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
              {German.Item.cache
                      { id := x.2.2.2.2.2.1, state := German.CacheState.exclusive, ch1 := x.2.2.2.2.2.2.1,
                        ch2 := German.Gnt.noGnt, ch3 := German.Ack.noAck }} +
                  {German.Item.dir
                      { cmd := x.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.2.1},
                        inv := x.2.2.2.2.2.2.2.2.2 }} +
                x.2.1),
            x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
            {German.Item.cache
                  { id := x.1, state := x.2.2.1, ch1 := x.2.2.2.1, ch2 := German.Gnt.gntE, ch3 := x.2.2.2.2.1 }} +
              x.2.1)] := by
  -- each unifier, instantiated, solves the problem
  simp only [sound, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  repeat' apply And.intro
  all_goals
    rintro γ ⟨x, rfl⟩
    simp only [unifiedBy, Narrowing.mayFire, German.recvGntE, German.ownE]
  all_goals first
    | rfl
    | ac_rfl
    | simp only [ACU.plus_unit, ACU.unit_plus, ACU.plus_comm, ACU.plus_left_comm, ACU.plus_assoc]

theorem German.recvGntE_inv.obligation_5 :
    Unification.complete (Narrowing.mayFire German.recvGntE German.ownG)
      [Unification.Unifier.bind
          fun
            (x :
              ℕ ×
                German.Items ×
                  German.CacheState × German.Req × German.Ack × ℕ × German.Req × German.Cmd × ℕ × German.Oids) =>
          ((x.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
              {German.Item.cache
                      { id := x.2.2.2.2.2.1, state := German.CacheState.invalid, ch1 := x.2.2.2.2.2.2.1,
                        ch2 := German.Gnt.gntE, ch3 := German.Ack.noAck }} +
                  {German.Item.dir
                      { cmd := x.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.2.1},
                        inv := x.2.2.2.2.2.2.2.2.2 }} +
                x.2.1),
            x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
            {German.Item.cache
                  { id := x.1, state := x.2.2.1, ch1 := x.2.2.2.1, ch2 := German.Gnt.gntE, ch3 := x.2.2.2.2.1 }} +
              x.2.1),
        Unification.Unifier.bind fun (x : German.Items × ℕ × German.Req × German.Cmd × ℕ × German.Oids) =>
          ((x.2.1, German.CacheState.invalid, x.2.2.1, German.Ack.noAck,
              {German.Item.dir
                    { cmd := x.2.2.2.1, ptr := x.2.2.2.2.1, exGntd := true, shr := {x.2.1}, inv := x.2.2.2.2.2 }} +
                x.1),
            x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2, x.2.1, x.2.2.1, x.1)] := by
  udf_certify

theorem German.recvGntE_inv.obligation_6 :
    Unification.sound (Narrowing.mayFire German.recvGntE German.ownG)
      [Unification.Unifier.bind
          fun
            (x :
              ℕ ×
                German.Items ×
                  German.CacheState × German.Req × German.Ack × ℕ × German.Req × German.Cmd × ℕ × German.Oids) =>
          ((x.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
              {German.Item.cache
                      { id := x.2.2.2.2.2.1, state := German.CacheState.invalid, ch1 := x.2.2.2.2.2.2.1,
                        ch2 := German.Gnt.gntE, ch3 := German.Ack.noAck }} +
                  {German.Item.dir
                      { cmd := x.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.2.1},
                        inv := x.2.2.2.2.2.2.2.2.2 }} +
                x.2.1),
            x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
            {German.Item.cache
                  { id := x.1, state := x.2.2.1, ch1 := x.2.2.2.1, ch2 := German.Gnt.gntE, ch3 := x.2.2.2.2.1 }} +
              x.2.1),
        Unification.Unifier.bind fun (x : German.Items × ℕ × German.Req × German.Cmd × ℕ × German.Oids) =>
          ((x.2.1, German.CacheState.invalid, x.2.2.1, German.Ack.noAck,
              {German.Item.dir
                    { cmd := x.2.2.2.1, ptr := x.2.2.2.2.1, exGntd := true, shr := {x.2.1}, inv := x.2.2.2.2.2 }} +
                x.1),
            x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2, x.2.1, x.2.2.1, x.1)] := by
  -- each unifier, instantiated, solves the problem
  simp only [sound, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  repeat' apply And.intro
  all_goals
    rintro γ ⟨x, rfl⟩
    simp only [unifiedBy, Narrowing.mayFire, German.recvGntE, German.ownG]
  all_goals first
    | rfl
    | ac_rfl
    | simp only [ACU.plus_unit, ACU.unit_plus, ACU.plus_comm, ACU.plus_left_comm, ACU.plus_assoc]

theorem German.recvGntE_inv.obligation_7 :
    Unification.complete (Narrowing.mayFire German.recvGntE German.ownInv)
      [Unification.Unifier.bind
          fun (x : ℕ × German.CacheState × German.Req × German.Ack × ℕ × German.Req × German.Cmd × ℕ × German.Items) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {German.Item.cache
                      { id := x.2.2.2.2.1, state := German.CacheState.exclusive, ch1 := x.2.2.2.2.2.1,
                        ch2 := German.Gnt.inv, ch3 := German.Ack.noAck }} +
                  {German.Item.dir
                      { cmd := x.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.1},
                        inv := ∅ }} +
                x.2.2.2.2.2.2.2.2),
            x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
            {German.Item.cache
                  { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := German.Gnt.gntE, ch3 := x.2.2.2.1 }} +
              x.2.2.2.2.2.2.2.2)] := by
  udf_certify

theorem German.recvGntE_inv.obligation_8 :
    Unification.sound (Narrowing.mayFire German.recvGntE German.ownInv)
      [Unification.Unifier.bind
          fun (x : ℕ × German.CacheState × German.Req × German.Ack × ℕ × German.Req × German.Cmd × ℕ × German.Items) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {German.Item.cache
                      { id := x.2.2.2.2.1, state := German.CacheState.exclusive, ch1 := x.2.2.2.2.2.1,
                        ch2 := German.Gnt.inv, ch3 := German.Ack.noAck }} +
                  {German.Item.dir
                      { cmd := x.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.1},
                        inv := ∅ }} +
                x.2.2.2.2.2.2.2.2),
            x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
            {German.Item.cache
                  { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := German.Gnt.gntE, ch3 := x.2.2.2.1 }} +
              x.2.2.2.2.2.2.2.2)] := by
  -- each unifier, instantiated, solves the problem
  simp only [sound, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  repeat' apply And.intro
  all_goals
    rintro γ ⟨x, rfl⟩
    simp only [unifiedBy, Narrowing.mayFire, German.recvGntE, German.ownInv]
  all_goals first
    | rfl
    | ac_rfl
    | simp only [ACU.plus_unit, ACU.unit_plus, ACU.plus_comm, ACU.plus_left_comm, ACU.plus_assoc]

theorem German.recvGntE_inv.obligation_9 :
    Unification.complete (Narrowing.mayFire German.recvGntE German.ownAck)
      [Unification.Unifier.bind
          fun (x : ℕ × German.CacheState × German.Req × German.Ack × ℕ × German.Req × German.Cmd × ℕ × German.Items) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {German.Item.cache
                      { id := x.2.2.2.2.1, state := German.CacheState.invalid, ch1 := x.2.2.2.2.2.1,
                        ch2 := German.Gnt.noGnt, ch3 := German.Ack.invAck }} +
                  {German.Item.dir
                      { cmd := x.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.1},
                        inv := ∅ }} +
                x.2.2.2.2.2.2.2.2),
            x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
            {German.Item.cache
                  { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := German.Gnt.gntE, ch3 := x.2.2.2.1 }} +
              x.2.2.2.2.2.2.2.2)] := by
  udf_certify

theorem German.recvGntE_inv.obligation_10 :
    Unification.sound (Narrowing.mayFire German.recvGntE German.ownAck)
      [Unification.Unifier.bind
          fun (x : ℕ × German.CacheState × German.Req × German.Ack × ℕ × German.Req × German.Cmd × ℕ × German.Items) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {German.Item.cache
                      { id := x.2.2.2.2.1, state := German.CacheState.invalid, ch1 := x.2.2.2.2.2.1,
                        ch2 := German.Gnt.noGnt, ch3 := German.Ack.invAck }} +
                  {German.Item.dir
                      { cmd := x.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.1},
                        inv := ∅ }} +
                x.2.2.2.2.2.2.2.2),
            x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
            {German.Item.cache
                  { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := German.Gnt.gntE, ch3 := x.2.2.2.1 }} +
              x.2.2.2.2.2.2.2.2)] := by
  -- each unifier, instantiated, solves the problem
  simp only [sound, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  repeat' apply And.intro
  all_goals
    rintro γ ⟨x, rfl⟩
    simp only [unifiedBy, Narrowing.mayFire, German.recvGntE, German.ownAck]
  all_goals first
    | rfl
    | ac_rfl
    | simp only [ACU.plus_unit, ACU.unit_plus, ACU.plus_comm, ACU.plus_left_comm, ACU.plus_assoc]

