import examples.TwoPC.proof
import conPanna.Reflect.Tactic

/-!
Two-phase commit: the certification obligations of `twoPC_inv`, as `#obligations` prints them.
Completeness: the certificate narrowing stored for the claim, checked by reflection
(`certify_comp`). Soundness: each unifier, substituted into both sides, gives terms equal
modulo ACU, checked by reflection (`certify_sound`).
-/

set_option linter.style.longLine false

open Expresso Unification Narrowing

theorem TwoPC.twoPC_inv.obligation_1 :
    Unification.complete (Narrowing.mayFire TwoPC.voteYes TwoPC.collP)
      [Unification.Unifier.bind fun (x : ℕ × ℕ × TwoPC.Oids × TwoPC.Oids × TwoPC.Items × ℕ) =>
          ((x.1, x.2.2.2.2.2,
              {TwoPC.Item.coord
                    { id := x.2.1, phase := TwoPC.CState.collecting, parts := x.2.2.1, wait := x.2.2.2.1 }} +
                x.2.2.2.2.1),
            x.2.1, x.2.2.1, x.2.2.2.1,
            {TwoPC.Item.part { id := x.1, state := TwoPC.PState.working }} + x.2.2.2.2.1)] := by
  certify_comp

theorem TwoPC.twoPC_inv.obligation_2 :
    Unification.sound (Narrowing.mayFire TwoPC.voteYes TwoPC.collP)
      [Unification.Unifier.bind fun (x : ℕ × ℕ × TwoPC.Oids × TwoPC.Oids × TwoPC.Items × ℕ) =>
          ((x.1, x.2.2.2.2.2,
              {TwoPC.Item.coord
                    { id := x.2.1, phase := TwoPC.CState.collecting, parts := x.2.2.1, wait := x.2.2.2.1 }} +
                x.2.2.2.2.1),
            x.2.1, x.2.2.1, x.2.2.2.1,
            {TwoPC.Item.part { id := x.1, state := TwoPC.PState.working }} + x.2.2.2.2.1)] := by
  certify_sound

theorem TwoPC.twoPC_inv.obligation_3 :
    Unification.complete (Narrowing.mayFire TwoPC.voteYes TwoPC.commP)
      [Unification.Unifier.bind fun (x : ℕ × ℕ × TwoPC.Oids × TwoPC.Oids × TwoPC.Items × ℕ) =>
          ((x.1, x.2.2.2.2.2,
              {TwoPC.Item.coord
                    { id := x.2.1, phase := TwoPC.CState.committing, parts := x.2.2.1, wait := x.2.2.2.1 }} +
                x.2.2.2.2.1),
            x.2.1, x.2.2.1, x.2.2.2.1,
            {TwoPC.Item.part { id := x.1, state := TwoPC.PState.working }} + x.2.2.2.2.1)] := by
  certify_comp

theorem TwoPC.twoPC_inv.obligation_4 :
    Unification.sound (Narrowing.mayFire TwoPC.voteYes TwoPC.commP)
      [Unification.Unifier.bind fun (x : ℕ × ℕ × TwoPC.Oids × TwoPC.Oids × TwoPC.Items × ℕ) =>
          ((x.1, x.2.2.2.2.2,
              {TwoPC.Item.coord
                    { id := x.2.1, phase := TwoPC.CState.committing, parts := x.2.2.1, wait := x.2.2.2.1 }} +
                x.2.2.2.2.1),
            x.2.1, x.2.2.1, x.2.2.2.1,
            {TwoPC.Item.part { id := x.1, state := TwoPC.PState.working }} + x.2.2.2.2.1)] := by
  certify_sound

theorem TwoPC.twoPC_inv.obligation_5 :
    Unification.complete (Narrowing.mayFire TwoPC.voteYes TwoPC.abrtP)
      [Unification.Unifier.bind fun (x : ℕ × ℕ × TwoPC.Oids × TwoPC.Oids × TwoPC.Items × ℕ) =>
          ((x.1, x.2.2.2.2.2,
              {TwoPC.Item.coord { id := x.2.1, phase := TwoPC.CState.aborting, parts := x.2.2.1, wait := x.2.2.2.1 }} +
                x.2.2.2.2.1),
            x.2.1, x.2.2.1, x.2.2.2.1,
            {TwoPC.Item.part { id := x.1, state := TwoPC.PState.working }} + x.2.2.2.2.1)] := by
  certify_comp

theorem TwoPC.twoPC_inv.obligation_6 :
    Unification.sound (Narrowing.mayFire TwoPC.voteYes TwoPC.abrtP)
      [Unification.Unifier.bind fun (x : ℕ × ℕ × TwoPC.Oids × TwoPC.Oids × TwoPC.Items × ℕ) =>
          ((x.1, x.2.2.2.2.2,
              {TwoPC.Item.coord { id := x.2.1, phase := TwoPC.CState.aborting, parts := x.2.2.1, wait := x.2.2.2.1 }} +
                x.2.2.2.2.1),
            x.2.1, x.2.2.1, x.2.2.2.1,
            {TwoPC.Item.part { id := x.1, state := TwoPC.PState.working }} + x.2.2.2.2.1)] := by
  certify_sound

theorem TwoPC.twoPC_inv.obligation_7 :
    Unification.complete (Narrowing.mayFire TwoPC.voteNo TwoPC.collP)
      [Unification.Unifier.bind fun (x : ℕ × ℕ × TwoPC.Oids × TwoPC.Oids × TwoPC.Items × ℕ) =>
          ((x.1, x.2.2.2.2.2,
              {TwoPC.Item.coord
                    { id := x.2.1, phase := TwoPC.CState.collecting, parts := x.2.2.1, wait := x.2.2.2.1 }} +
                x.2.2.2.2.1),
            x.2.1, x.2.2.1, x.2.2.2.1,
            {TwoPC.Item.part { id := x.1, state := TwoPC.PState.working }} + x.2.2.2.2.1)] := by
  certify_comp

theorem TwoPC.twoPC_inv.obligation_8 :
    Unification.sound (Narrowing.mayFire TwoPC.voteNo TwoPC.collP)
      [Unification.Unifier.bind fun (x : ℕ × ℕ × TwoPC.Oids × TwoPC.Oids × TwoPC.Items × ℕ) =>
          ((x.1, x.2.2.2.2.2,
              {TwoPC.Item.coord
                    { id := x.2.1, phase := TwoPC.CState.collecting, parts := x.2.2.1, wait := x.2.2.2.1 }} +
                x.2.2.2.2.1),
            x.2.1, x.2.2.1, x.2.2.2.1,
            {TwoPC.Item.part { id := x.1, state := TwoPC.PState.working }} + x.2.2.2.2.1)] := by
  certify_sound

theorem TwoPC.twoPC_inv.obligation_9 :
    Unification.complete (Narrowing.mayFire TwoPC.voteNo TwoPC.commP)
      [Unification.Unifier.bind fun (x : ℕ × ℕ × TwoPC.Oids × TwoPC.Oids × TwoPC.Items × ℕ) =>
          ((x.1, x.2.2.2.2.2,
              {TwoPC.Item.coord
                    { id := x.2.1, phase := TwoPC.CState.committing, parts := x.2.2.1, wait := x.2.2.2.1 }} +
                x.2.2.2.2.1),
            x.2.1, x.2.2.1, x.2.2.2.1,
            {TwoPC.Item.part { id := x.1, state := TwoPC.PState.working }} + x.2.2.2.2.1)] := by
  certify_comp

theorem TwoPC.twoPC_inv.obligation_10 :
    Unification.sound (Narrowing.mayFire TwoPC.voteNo TwoPC.commP)
      [Unification.Unifier.bind fun (x : ℕ × ℕ × TwoPC.Oids × TwoPC.Oids × TwoPC.Items × ℕ) =>
          ((x.1, x.2.2.2.2.2,
              {TwoPC.Item.coord
                    { id := x.2.1, phase := TwoPC.CState.committing, parts := x.2.2.1, wait := x.2.2.2.1 }} +
                x.2.2.2.2.1),
            x.2.1, x.2.2.1, x.2.2.2.1,
            {TwoPC.Item.part { id := x.1, state := TwoPC.PState.working }} + x.2.2.2.2.1)] := by
  certify_sound

theorem TwoPC.twoPC_inv.obligation_11 :
    Unification.complete (Narrowing.mayFire TwoPC.voteNo TwoPC.abrtP)
      [Unification.Unifier.bind fun (x : ℕ × ℕ × TwoPC.Oids × TwoPC.Oids × TwoPC.Items × ℕ) =>
          ((x.1, x.2.2.2.2.2,
              {TwoPC.Item.coord { id := x.2.1, phase := TwoPC.CState.aborting, parts := x.2.2.1, wait := x.2.2.2.1 }} +
                x.2.2.2.2.1),
            x.2.1, x.2.2.1, x.2.2.2.1,
            {TwoPC.Item.part { id := x.1, state := TwoPC.PState.working }} + x.2.2.2.2.1)] := by
  certify_comp

theorem TwoPC.twoPC_inv.obligation_12 :
    Unification.sound (Narrowing.mayFire TwoPC.voteNo TwoPC.abrtP)
      [Unification.Unifier.bind fun (x : ℕ × ℕ × TwoPC.Oids × TwoPC.Oids × TwoPC.Items × ℕ) =>
          ((x.1, x.2.2.2.2.2,
              {TwoPC.Item.coord { id := x.2.1, phase := TwoPC.CState.aborting, parts := x.2.2.1, wait := x.2.2.2.1 }} +
                x.2.2.2.2.1),
            x.2.1, x.2.2.1, x.2.2.2.1,
            {TwoPC.Item.part { id := x.1, state := TwoPC.PState.working }} + x.2.2.2.2.1)] := by
  certify_sound

theorem TwoPC.twoPC_inv.obligation_13 :
    Unification.complete (Narrowing.mayFire TwoPC.recvYes TwoPC.collP)
      [Unification.Unifier.bind fun (x : ℕ × TwoPC.Oids × ℕ × TwoPC.Oids × ℕ × TwoPC.Oids × TwoPC.Oids × TwoPC.Items) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {TwoPC.Item.coord
                    { id := x.2.2.2.2.1, phase := TwoPC.CState.collecting, parts := x.2.2.2.2.2.1,
                      wait := x.2.2.2.2.2.2.1 }} +
                x.2.2.2.2.2.2.2),
            x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
            {TwoPC.Item.coord
                    { id := x.1, phase := TwoPC.CState.collecting, parts := x.2.1, wait := {x.2.2.1} + x.2.2.2.1 }} +
                {TwoPC.Item.msg (TwoPC.Msg.vote true x.2.2.1 x.1)} +
              x.2.2.2.2.2.2.2),
        Unification.Unifier.bind fun (x : TwoPC.Items × ℕ × TwoPC.Oids × ℕ × TwoPC.Oids) =>
          ((x.2.2.2.1, x.2.2.2.2, x.2.1, x.2.2.1, x.1), x.2.2.2.1, x.2.2.2.2, {x.2.1} + x.2.2.1,
            {TwoPC.Item.msg (TwoPC.Msg.vote true x.2.1 x.2.2.2.1)} + x.1)] := by
  certify_comp

theorem TwoPC.twoPC_inv.obligation_14 :
    Unification.sound (Narrowing.mayFire TwoPC.recvYes TwoPC.collP)
      [Unification.Unifier.bind fun (x : ℕ × TwoPC.Oids × ℕ × TwoPC.Oids × ℕ × TwoPC.Oids × TwoPC.Oids × TwoPC.Items) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {TwoPC.Item.coord
                    { id := x.2.2.2.2.1, phase := TwoPC.CState.collecting, parts := x.2.2.2.2.2.1,
                      wait := x.2.2.2.2.2.2.1 }} +
                x.2.2.2.2.2.2.2),
            x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
            {TwoPC.Item.coord
                    { id := x.1, phase := TwoPC.CState.collecting, parts := x.2.1, wait := {x.2.2.1} + x.2.2.2.1 }} +
                {TwoPC.Item.msg (TwoPC.Msg.vote true x.2.2.1 x.1)} +
              x.2.2.2.2.2.2.2),
        Unification.Unifier.bind fun (x : TwoPC.Items × ℕ × TwoPC.Oids × ℕ × TwoPC.Oids) =>
          ((x.2.2.2.1, x.2.2.2.2, x.2.1, x.2.2.1, x.1), x.2.2.2.1, x.2.2.2.2, {x.2.1} + x.2.2.1,
            {TwoPC.Item.msg (TwoPC.Msg.vote true x.2.1 x.2.2.2.1)} + x.1)] := by
  certify_sound

theorem TwoPC.twoPC_inv.obligation_15 :
    Unification.complete (Narrowing.mayFire TwoPC.recvYes TwoPC.commP)
      [Unification.Unifier.bind fun (x : ℕ × TwoPC.Oids × ℕ × TwoPC.Oids × ℕ × TwoPC.Oids × TwoPC.Oids × TwoPC.Items) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {TwoPC.Item.coord
                    { id := x.2.2.2.2.1, phase := TwoPC.CState.committing, parts := x.2.2.2.2.2.1,
                      wait := x.2.2.2.2.2.2.1 }} +
                x.2.2.2.2.2.2.2),
            x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
            {TwoPC.Item.coord
                    { id := x.1, phase := TwoPC.CState.collecting, parts := x.2.1, wait := {x.2.2.1} + x.2.2.2.1 }} +
                {TwoPC.Item.msg (TwoPC.Msg.vote true x.2.2.1 x.1)} +
              x.2.2.2.2.2.2.2)] := by
  certify_comp

theorem TwoPC.twoPC_inv.obligation_16 :
    Unification.sound (Narrowing.mayFire TwoPC.recvYes TwoPC.commP)
      [Unification.Unifier.bind fun (x : ℕ × TwoPC.Oids × ℕ × TwoPC.Oids × ℕ × TwoPC.Oids × TwoPC.Oids × TwoPC.Items) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {TwoPC.Item.coord
                    { id := x.2.2.2.2.1, phase := TwoPC.CState.committing, parts := x.2.2.2.2.2.1,
                      wait := x.2.2.2.2.2.2.1 }} +
                x.2.2.2.2.2.2.2),
            x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
            {TwoPC.Item.coord
                    { id := x.1, phase := TwoPC.CState.collecting, parts := x.2.1, wait := {x.2.2.1} + x.2.2.2.1 }} +
                {TwoPC.Item.msg (TwoPC.Msg.vote true x.2.2.1 x.1)} +
              x.2.2.2.2.2.2.2)] := by
  certify_sound

theorem TwoPC.twoPC_inv.obligation_17 :
    Unification.complete (Narrowing.mayFire TwoPC.recvYes TwoPC.abrtP)
      [Unification.Unifier.bind fun (x : ℕ × TwoPC.Oids × ℕ × TwoPC.Oids × ℕ × TwoPC.Oids × TwoPC.Oids × TwoPC.Items) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {TwoPC.Item.coord
                    { id := x.2.2.2.2.1, phase := TwoPC.CState.aborting, parts := x.2.2.2.2.2.1,
                      wait := x.2.2.2.2.2.2.1 }} +
                x.2.2.2.2.2.2.2),
            x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
            {TwoPC.Item.coord
                    { id := x.1, phase := TwoPC.CState.collecting, parts := x.2.1, wait := {x.2.2.1} + x.2.2.2.1 }} +
                {TwoPC.Item.msg (TwoPC.Msg.vote true x.2.2.1 x.1)} +
              x.2.2.2.2.2.2.2)] := by
  certify_comp

theorem TwoPC.twoPC_inv.obligation_18 :
    Unification.sound (Narrowing.mayFire TwoPC.recvYes TwoPC.abrtP)
      [Unification.Unifier.bind fun (x : ℕ × TwoPC.Oids × ℕ × TwoPC.Oids × ℕ × TwoPC.Oids × TwoPC.Oids × TwoPC.Items) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {TwoPC.Item.coord
                    { id := x.2.2.2.2.1, phase := TwoPC.CState.aborting, parts := x.2.2.2.2.2.1,
                      wait := x.2.2.2.2.2.2.1 }} +
                x.2.2.2.2.2.2.2),
            x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
            {TwoPC.Item.coord
                    { id := x.1, phase := TwoPC.CState.collecting, parts := x.2.1, wait := {x.2.2.1} + x.2.2.2.1 }} +
                {TwoPC.Item.msg (TwoPC.Msg.vote true x.2.2.1 x.1)} +
              x.2.2.2.2.2.2.2)] := by
  certify_sound

theorem TwoPC.twoPC_inv.obligation_19 :
    Unification.complete (Narrowing.mayFire TwoPC.decideCommit TwoPC.collP)
      [Unification.Unifier.bind fun (x : ℕ × TwoPC.Oids × ℕ × TwoPC.Oids × TwoPC.Oids × TwoPC.Items) =>
          ((x.1, x.2.1,
              {TwoPC.Item.coord
                    { id := x.2.2.1, phase := TwoPC.CState.collecting, parts := x.2.2.2.1, wait := x.2.2.2.2.1 }} +
                x.2.2.2.2.2),
            x.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
            {TwoPC.Item.coord { id := x.1, phase := TwoPC.CState.collecting, parts := x.2.1, wait := ∅ }} +
              x.2.2.2.2.2),
        Unification.Unifier.bind fun (x : TwoPC.Items × ℕ × TwoPC.Oids) =>
          ((x.2.1, x.2.2, x.1), x.2.1, x.2.2, ∅, x.1)] := by
  certify_comp

theorem TwoPC.twoPC_inv.obligation_20 :
    Unification.sound (Narrowing.mayFire TwoPC.decideCommit TwoPC.collP)
      [Unification.Unifier.bind fun (x : ℕ × TwoPC.Oids × ℕ × TwoPC.Oids × TwoPC.Oids × TwoPC.Items) =>
          ((x.1, x.2.1,
              {TwoPC.Item.coord
                    { id := x.2.2.1, phase := TwoPC.CState.collecting, parts := x.2.2.2.1, wait := x.2.2.2.2.1 }} +
                x.2.2.2.2.2),
            x.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
            {TwoPC.Item.coord { id := x.1, phase := TwoPC.CState.collecting, parts := x.2.1, wait := ∅ }} +
              x.2.2.2.2.2),
        Unification.Unifier.bind fun (x : TwoPC.Items × ℕ × TwoPC.Oids) =>
          ((x.2.1, x.2.2, x.1), x.2.1, x.2.2, ∅, x.1)] := by
  certify_sound

theorem TwoPC.twoPC_inv.obligation_21 :
    Unification.complete (Narrowing.mayFire TwoPC.decideCommit TwoPC.commP)
      [Unification.Unifier.bind fun (x : ℕ × TwoPC.Oids × ℕ × TwoPC.Oids × TwoPC.Oids × TwoPC.Items) =>
          ((x.1, x.2.1,
              {TwoPC.Item.coord
                    { id := x.2.2.1, phase := TwoPC.CState.committing, parts := x.2.2.2.1, wait := x.2.2.2.2.1 }} +
                x.2.2.2.2.2),
            x.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
            {TwoPC.Item.coord { id := x.1, phase := TwoPC.CState.collecting, parts := x.2.1, wait := ∅ }} +
              x.2.2.2.2.2)] := by
  certify_comp

theorem TwoPC.twoPC_inv.obligation_22 :
    Unification.sound (Narrowing.mayFire TwoPC.decideCommit TwoPC.commP)
      [Unification.Unifier.bind fun (x : ℕ × TwoPC.Oids × ℕ × TwoPC.Oids × TwoPC.Oids × TwoPC.Items) =>
          ((x.1, x.2.1,
              {TwoPC.Item.coord
                    { id := x.2.2.1, phase := TwoPC.CState.committing, parts := x.2.2.2.1, wait := x.2.2.2.2.1 }} +
                x.2.2.2.2.2),
            x.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
            {TwoPC.Item.coord { id := x.1, phase := TwoPC.CState.collecting, parts := x.2.1, wait := ∅ }} +
              x.2.2.2.2.2)] := by
  certify_sound

theorem TwoPC.twoPC_inv.obligation_23 :
    Unification.complete (Narrowing.mayFire TwoPC.decideCommit TwoPC.abrtP)
      [Unification.Unifier.bind fun (x : ℕ × TwoPC.Oids × ℕ × TwoPC.Oids × TwoPC.Oids × TwoPC.Items) =>
          ((x.1, x.2.1,
              {TwoPC.Item.coord
                    { id := x.2.2.1, phase := TwoPC.CState.aborting, parts := x.2.2.2.1, wait := x.2.2.2.2.1 }} +
                x.2.2.2.2.2),
            x.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
            {TwoPC.Item.coord { id := x.1, phase := TwoPC.CState.collecting, parts := x.2.1, wait := ∅ }} +
              x.2.2.2.2.2)] := by
  certify_comp

theorem TwoPC.twoPC_inv.obligation_24 :
    Unification.sound (Narrowing.mayFire TwoPC.decideCommit TwoPC.abrtP)
      [Unification.Unifier.bind fun (x : ℕ × TwoPC.Oids × ℕ × TwoPC.Oids × TwoPC.Oids × TwoPC.Items) =>
          ((x.1, x.2.1,
              {TwoPC.Item.coord
                    { id := x.2.2.1, phase := TwoPC.CState.aborting, parts := x.2.2.2.1, wait := x.2.2.2.2.1 }} +
                x.2.2.2.2.2),
            x.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
            {TwoPC.Item.coord { id := x.1, phase := TwoPC.CState.collecting, parts := x.2.1, wait := ∅ }} +
              x.2.2.2.2.2)] := by
  certify_sound

theorem TwoPC.twoPC_inv.obligation_25 :
    Unification.complete (Narrowing.mayFire TwoPC.recvNo TwoPC.collP)
      [Unification.Unifier.bind fun (x : ℕ × TwoPC.Oids × TwoPC.Oids × ℕ × ℕ × TwoPC.Oids × TwoPC.Oids × TwoPC.Items) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {TwoPC.Item.coord
                    { id := x.2.2.2.2.1, phase := TwoPC.CState.collecting, parts := x.2.2.2.2.2.1,
                      wait := x.2.2.2.2.2.2.1 }} +
                x.2.2.2.2.2.2.2),
            x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
            {TwoPC.Item.coord { id := x.1, phase := TwoPC.CState.collecting, parts := x.2.1, wait := x.2.2.1 }} +
                {TwoPC.Item.msg (TwoPC.Msg.vote false x.2.2.2.1 x.1)} +
              x.2.2.2.2.2.2.2),
        Unification.Unifier.bind fun (x : TwoPC.Items × ℕ × ℕ × TwoPC.Oids × TwoPC.Oids) =>
          ((x.2.2.1, x.2.2.2.1, x.2.2.2.2, x.2.1, x.1), x.2.2.1, x.2.2.2.1, x.2.2.2.2,
            {TwoPC.Item.msg (TwoPC.Msg.vote false x.2.1 x.2.2.1)} + x.1)] := by
  certify_comp

theorem TwoPC.twoPC_inv.obligation_26 :
    Unification.sound (Narrowing.mayFire TwoPC.recvNo TwoPC.collP)
      [Unification.Unifier.bind fun (x : ℕ × TwoPC.Oids × TwoPC.Oids × ℕ × ℕ × TwoPC.Oids × TwoPC.Oids × TwoPC.Items) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {TwoPC.Item.coord
                    { id := x.2.2.2.2.1, phase := TwoPC.CState.collecting, parts := x.2.2.2.2.2.1,
                      wait := x.2.2.2.2.2.2.1 }} +
                x.2.2.2.2.2.2.2),
            x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
            {TwoPC.Item.coord { id := x.1, phase := TwoPC.CState.collecting, parts := x.2.1, wait := x.2.2.1 }} +
                {TwoPC.Item.msg (TwoPC.Msg.vote false x.2.2.2.1 x.1)} +
              x.2.2.2.2.2.2.2),
        Unification.Unifier.bind fun (x : TwoPC.Items × ℕ × ℕ × TwoPC.Oids × TwoPC.Oids) =>
          ((x.2.2.1, x.2.2.2.1, x.2.2.2.2, x.2.1, x.1), x.2.2.1, x.2.2.2.1, x.2.2.2.2,
            {TwoPC.Item.msg (TwoPC.Msg.vote false x.2.1 x.2.2.1)} + x.1)] := by
  certify_sound

theorem TwoPC.twoPC_inv.obligation_27 :
    Unification.complete (Narrowing.mayFire TwoPC.recvNo TwoPC.commP)
      [Unification.Unifier.bind fun (x : ℕ × TwoPC.Oids × TwoPC.Oids × ℕ × ℕ × TwoPC.Oids × TwoPC.Oids × TwoPC.Items) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {TwoPC.Item.coord
                    { id := x.2.2.2.2.1, phase := TwoPC.CState.committing, parts := x.2.2.2.2.2.1,
                      wait := x.2.2.2.2.2.2.1 }} +
                x.2.2.2.2.2.2.2),
            x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
            {TwoPC.Item.coord { id := x.1, phase := TwoPC.CState.collecting, parts := x.2.1, wait := x.2.2.1 }} +
                {TwoPC.Item.msg (TwoPC.Msg.vote false x.2.2.2.1 x.1)} +
              x.2.2.2.2.2.2.2)] := by
  certify_comp

theorem TwoPC.twoPC_inv.obligation_28 :
    Unification.sound (Narrowing.mayFire TwoPC.recvNo TwoPC.commP)
      [Unification.Unifier.bind fun (x : ℕ × TwoPC.Oids × TwoPC.Oids × ℕ × ℕ × TwoPC.Oids × TwoPC.Oids × TwoPC.Items) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {TwoPC.Item.coord
                    { id := x.2.2.2.2.1, phase := TwoPC.CState.committing, parts := x.2.2.2.2.2.1,
                      wait := x.2.2.2.2.2.2.1 }} +
                x.2.2.2.2.2.2.2),
            x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
            {TwoPC.Item.coord { id := x.1, phase := TwoPC.CState.collecting, parts := x.2.1, wait := x.2.2.1 }} +
                {TwoPC.Item.msg (TwoPC.Msg.vote false x.2.2.2.1 x.1)} +
              x.2.2.2.2.2.2.2)] := by
  certify_sound

theorem TwoPC.twoPC_inv.obligation_29 :
    Unification.complete (Narrowing.mayFire TwoPC.recvNo TwoPC.abrtP)
      [Unification.Unifier.bind fun (x : ℕ × TwoPC.Oids × TwoPC.Oids × ℕ × ℕ × TwoPC.Oids × TwoPC.Oids × TwoPC.Items) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {TwoPC.Item.coord
                    { id := x.2.2.2.2.1, phase := TwoPC.CState.aborting, parts := x.2.2.2.2.2.1,
                      wait := x.2.2.2.2.2.2.1 }} +
                x.2.2.2.2.2.2.2),
            x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
            {TwoPC.Item.coord { id := x.1, phase := TwoPC.CState.collecting, parts := x.2.1, wait := x.2.2.1 }} +
                {TwoPC.Item.msg (TwoPC.Msg.vote false x.2.2.2.1 x.1)} +
              x.2.2.2.2.2.2.2)] := by
  certify_comp

theorem TwoPC.twoPC_inv.obligation_30 :
    Unification.sound (Narrowing.mayFire TwoPC.recvNo TwoPC.abrtP)
      [Unification.Unifier.bind fun (x : ℕ × TwoPC.Oids × TwoPC.Oids × ℕ × ℕ × TwoPC.Oids × TwoPC.Oids × TwoPC.Items) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {TwoPC.Item.coord
                    { id := x.2.2.2.2.1, phase := TwoPC.CState.aborting, parts := x.2.2.2.2.2.1,
                      wait := x.2.2.2.2.2.2.1 }} +
                x.2.2.2.2.2.2.2),
            x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
            {TwoPC.Item.coord { id := x.1, phase := TwoPC.CState.collecting, parts := x.2.1, wait := x.2.2.1 }} +
                {TwoPC.Item.msg (TwoPC.Msg.vote false x.2.2.2.1 x.1)} +
              x.2.2.2.2.2.2.2)] := by
  certify_sound

theorem TwoPC.twoPC_inv.obligation_31 :
    Unification.complete (Narrowing.mayFire TwoPC.timeout TwoPC.collP)
      [Unification.Unifier.bind fun (x : ℕ × TwoPC.Oids × TwoPC.Oids × ℕ × TwoPC.Oids × TwoPC.Oids × TwoPC.Items) =>
          ((x.1, x.2.1, x.2.2.1,
              {TwoPC.Item.coord
                    { id := x.2.2.2.1, phase := TwoPC.CState.collecting, parts := x.2.2.2.2.1,
                      wait := x.2.2.2.2.2.1 }} +
                x.2.2.2.2.2.2),
            x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
            {TwoPC.Item.coord { id := x.1, phase := TwoPC.CState.collecting, parts := x.2.1, wait := x.2.2.1 }} +
              x.2.2.2.2.2.2),
        Unification.Unifier.bind fun (x : TwoPC.Items × ℕ × TwoPC.Oids × TwoPC.Oids) =>
          ((x.2.1, x.2.2.1, x.2.2.2, x.1), x.2.1, x.2.2.1, x.2.2.2, x.1)] := by
  certify_comp

theorem TwoPC.twoPC_inv.obligation_32 :
    Unification.sound (Narrowing.mayFire TwoPC.timeout TwoPC.collP)
      [Unification.Unifier.bind fun (x : ℕ × TwoPC.Oids × TwoPC.Oids × ℕ × TwoPC.Oids × TwoPC.Oids × TwoPC.Items) =>
          ((x.1, x.2.1, x.2.2.1,
              {TwoPC.Item.coord
                    { id := x.2.2.2.1, phase := TwoPC.CState.collecting, parts := x.2.2.2.2.1,
                      wait := x.2.2.2.2.2.1 }} +
                x.2.2.2.2.2.2),
            x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
            {TwoPC.Item.coord { id := x.1, phase := TwoPC.CState.collecting, parts := x.2.1, wait := x.2.2.1 }} +
              x.2.2.2.2.2.2),
        Unification.Unifier.bind fun (x : TwoPC.Items × ℕ × TwoPC.Oids × TwoPC.Oids) =>
          ((x.2.1, x.2.2.1, x.2.2.2, x.1), x.2.1, x.2.2.1, x.2.2.2, x.1)] := by
  certify_sound

theorem TwoPC.twoPC_inv.obligation_33 :
    Unification.complete (Narrowing.mayFire TwoPC.timeout TwoPC.commP)
      [Unification.Unifier.bind fun (x : ℕ × TwoPC.Oids × TwoPC.Oids × ℕ × TwoPC.Oids × TwoPC.Oids × TwoPC.Items) =>
          ((x.1, x.2.1, x.2.2.1,
              {TwoPC.Item.coord
                    { id := x.2.2.2.1, phase := TwoPC.CState.committing, parts := x.2.2.2.2.1,
                      wait := x.2.2.2.2.2.1 }} +
                x.2.2.2.2.2.2),
            x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
            {TwoPC.Item.coord { id := x.1, phase := TwoPC.CState.collecting, parts := x.2.1, wait := x.2.2.1 }} +
              x.2.2.2.2.2.2)] := by
  certify_comp

theorem TwoPC.twoPC_inv.obligation_34 :
    Unification.sound (Narrowing.mayFire TwoPC.timeout TwoPC.commP)
      [Unification.Unifier.bind fun (x : ℕ × TwoPC.Oids × TwoPC.Oids × ℕ × TwoPC.Oids × TwoPC.Oids × TwoPC.Items) =>
          ((x.1, x.2.1, x.2.2.1,
              {TwoPC.Item.coord
                    { id := x.2.2.2.1, phase := TwoPC.CState.committing, parts := x.2.2.2.2.1,
                      wait := x.2.2.2.2.2.1 }} +
                x.2.2.2.2.2.2),
            x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
            {TwoPC.Item.coord { id := x.1, phase := TwoPC.CState.collecting, parts := x.2.1, wait := x.2.2.1 }} +
              x.2.2.2.2.2.2)] := by
  certify_sound

theorem TwoPC.twoPC_inv.obligation_35 :
    Unification.complete (Narrowing.mayFire TwoPC.timeout TwoPC.abrtP)
      [Unification.Unifier.bind fun (x : ℕ × TwoPC.Oids × TwoPC.Oids × ℕ × TwoPC.Oids × TwoPC.Oids × TwoPC.Items) =>
          ((x.1, x.2.1, x.2.2.1,
              {TwoPC.Item.coord
                    { id := x.2.2.2.1, phase := TwoPC.CState.aborting, parts := x.2.2.2.2.1, wait := x.2.2.2.2.2.1 }} +
                x.2.2.2.2.2.2),
            x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
            {TwoPC.Item.coord { id := x.1, phase := TwoPC.CState.collecting, parts := x.2.1, wait := x.2.2.1 }} +
              x.2.2.2.2.2.2)] := by
  certify_comp

theorem TwoPC.twoPC_inv.obligation_36 :
    Unification.sound (Narrowing.mayFire TwoPC.timeout TwoPC.abrtP)
      [Unification.Unifier.bind fun (x : ℕ × TwoPC.Oids × TwoPC.Oids × ℕ × TwoPC.Oids × TwoPC.Oids × TwoPC.Items) =>
          ((x.1, x.2.1, x.2.2.1,
              {TwoPC.Item.coord
                    { id := x.2.2.2.1, phase := TwoPC.CState.aborting, parts := x.2.2.2.2.1, wait := x.2.2.2.2.2.1 }} +
                x.2.2.2.2.2.2),
            x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
            {TwoPC.Item.coord { id := x.1, phase := TwoPC.CState.collecting, parts := x.2.1, wait := x.2.2.1 }} +
              x.2.2.2.2.2.2)] := by
  certify_sound

theorem TwoPC.twoPC_inv.obligation_37 :
    Unification.complete (Narrowing.mayFire TwoPC.deliverCommit TwoPC.collP)
      [Unification.Unifier.bind
          fun (x : ℕ × ℕ × TwoPC.Oids × TwoPC.PState × ℕ × TwoPC.Oids × TwoPC.Oids × TwoPC.Items) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {TwoPC.Item.coord
                    { id := x.2.2.2.2.1, phase := TwoPC.CState.collecting, parts := x.2.2.2.2.2.1,
                      wait := x.2.2.2.2.2.2.1 }} +
                x.2.2.2.2.2.2.2),
            x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
            {TwoPC.Item.msg (TwoPC.Msg.decision true x.1 ({x.2.1} + x.2.2.1))} +
                {TwoPC.Item.part { id := x.2.1, state := x.2.2.2.1 }} +
              x.2.2.2.2.2.2.2)] := by
  certify_comp

theorem TwoPC.twoPC_inv.obligation_38 :
    Unification.sound (Narrowing.mayFire TwoPC.deliverCommit TwoPC.collP)
      [Unification.Unifier.bind
          fun (x : ℕ × ℕ × TwoPC.Oids × TwoPC.PState × ℕ × TwoPC.Oids × TwoPC.Oids × TwoPC.Items) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {TwoPC.Item.coord
                    { id := x.2.2.2.2.1, phase := TwoPC.CState.collecting, parts := x.2.2.2.2.2.1,
                      wait := x.2.2.2.2.2.2.1 }} +
                x.2.2.2.2.2.2.2),
            x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
            {TwoPC.Item.msg (TwoPC.Msg.decision true x.1 ({x.2.1} + x.2.2.1))} +
                {TwoPC.Item.part { id := x.2.1, state := x.2.2.2.1 }} +
              x.2.2.2.2.2.2.2)] := by
  certify_sound

theorem TwoPC.twoPC_inv.obligation_39 :
    Unification.complete (Narrowing.mayFire TwoPC.deliverCommit TwoPC.commP)
      [Unification.Unifier.bind
          fun (x : ℕ × ℕ × TwoPC.Oids × TwoPC.PState × ℕ × TwoPC.Oids × TwoPC.Oids × TwoPC.Items) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {TwoPC.Item.coord
                    { id := x.2.2.2.2.1, phase := TwoPC.CState.committing, parts := x.2.2.2.2.2.1,
                      wait := x.2.2.2.2.2.2.1 }} +
                x.2.2.2.2.2.2.2),
            x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
            {TwoPC.Item.msg (TwoPC.Msg.decision true x.1 ({x.2.1} + x.2.2.1))} +
                {TwoPC.Item.part { id := x.2.1, state := x.2.2.2.1 }} +
              x.2.2.2.2.2.2.2)] := by
  certify_comp

theorem TwoPC.twoPC_inv.obligation_40 :
    Unification.sound (Narrowing.mayFire TwoPC.deliverCommit TwoPC.commP)
      [Unification.Unifier.bind
          fun (x : ℕ × ℕ × TwoPC.Oids × TwoPC.PState × ℕ × TwoPC.Oids × TwoPC.Oids × TwoPC.Items) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {TwoPC.Item.coord
                    { id := x.2.2.2.2.1, phase := TwoPC.CState.committing, parts := x.2.2.2.2.2.1,
                      wait := x.2.2.2.2.2.2.1 }} +
                x.2.2.2.2.2.2.2),
            x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
            {TwoPC.Item.msg (TwoPC.Msg.decision true x.1 ({x.2.1} + x.2.2.1))} +
                {TwoPC.Item.part { id := x.2.1, state := x.2.2.2.1 }} +
              x.2.2.2.2.2.2.2)] := by
  certify_sound

theorem TwoPC.twoPC_inv.obligation_41 :
    Unification.complete (Narrowing.mayFire TwoPC.deliverCommit TwoPC.abrtP)
      [Unification.Unifier.bind
          fun (x : ℕ × ℕ × TwoPC.Oids × TwoPC.PState × ℕ × TwoPC.Oids × TwoPC.Oids × TwoPC.Items) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {TwoPC.Item.coord
                    { id := x.2.2.2.2.1, phase := TwoPC.CState.aborting, parts := x.2.2.2.2.2.1,
                      wait := x.2.2.2.2.2.2.1 }} +
                x.2.2.2.2.2.2.2),
            x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
            {TwoPC.Item.msg (TwoPC.Msg.decision true x.1 ({x.2.1} + x.2.2.1))} +
                {TwoPC.Item.part { id := x.2.1, state := x.2.2.2.1 }} +
              x.2.2.2.2.2.2.2)] := by
  certify_comp

theorem TwoPC.twoPC_inv.obligation_42 :
    Unification.sound (Narrowing.mayFire TwoPC.deliverCommit TwoPC.abrtP)
      [Unification.Unifier.bind
          fun (x : ℕ × ℕ × TwoPC.Oids × TwoPC.PState × ℕ × TwoPC.Oids × TwoPC.Oids × TwoPC.Items) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {TwoPC.Item.coord
                    { id := x.2.2.2.2.1, phase := TwoPC.CState.aborting, parts := x.2.2.2.2.2.1,
                      wait := x.2.2.2.2.2.2.1 }} +
                x.2.2.2.2.2.2.2),
            x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
            {TwoPC.Item.msg (TwoPC.Msg.decision true x.1 ({x.2.1} + x.2.2.1))} +
                {TwoPC.Item.part { id := x.2.1, state := x.2.2.2.1 }} +
              x.2.2.2.2.2.2.2)] := by
  certify_sound

theorem TwoPC.twoPC_inv.obligation_43 :
    Unification.complete (Narrowing.mayFire TwoPC.deliverAbort TwoPC.collP)
      [Unification.Unifier.bind
          fun (x : ℕ × ℕ × TwoPC.Oids × TwoPC.PState × ℕ × TwoPC.Oids × TwoPC.Oids × TwoPC.Items) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {TwoPC.Item.coord
                    { id := x.2.2.2.2.1, phase := TwoPC.CState.collecting, parts := x.2.2.2.2.2.1,
                      wait := x.2.2.2.2.2.2.1 }} +
                x.2.2.2.2.2.2.2),
            x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
            {TwoPC.Item.msg (TwoPC.Msg.decision false x.1 ({x.2.1} + x.2.2.1))} +
                {TwoPC.Item.part { id := x.2.1, state := x.2.2.2.1 }} +
              x.2.2.2.2.2.2.2)] := by
  certify_comp

theorem TwoPC.twoPC_inv.obligation_44 :
    Unification.sound (Narrowing.mayFire TwoPC.deliverAbort TwoPC.collP)
      [Unification.Unifier.bind
          fun (x : ℕ × ℕ × TwoPC.Oids × TwoPC.PState × ℕ × TwoPC.Oids × TwoPC.Oids × TwoPC.Items) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {TwoPC.Item.coord
                    { id := x.2.2.2.2.1, phase := TwoPC.CState.collecting, parts := x.2.2.2.2.2.1,
                      wait := x.2.2.2.2.2.2.1 }} +
                x.2.2.2.2.2.2.2),
            x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
            {TwoPC.Item.msg (TwoPC.Msg.decision false x.1 ({x.2.1} + x.2.2.1))} +
                {TwoPC.Item.part { id := x.2.1, state := x.2.2.2.1 }} +
              x.2.2.2.2.2.2.2)] := by
  certify_sound

theorem TwoPC.twoPC_inv.obligation_45 :
    Unification.complete (Narrowing.mayFire TwoPC.deliverAbort TwoPC.commP)
      [Unification.Unifier.bind
          fun (x : ℕ × ℕ × TwoPC.Oids × TwoPC.PState × ℕ × TwoPC.Oids × TwoPC.Oids × TwoPC.Items) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {TwoPC.Item.coord
                    { id := x.2.2.2.2.1, phase := TwoPC.CState.committing, parts := x.2.2.2.2.2.1,
                      wait := x.2.2.2.2.2.2.1 }} +
                x.2.2.2.2.2.2.2),
            x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
            {TwoPC.Item.msg (TwoPC.Msg.decision false x.1 ({x.2.1} + x.2.2.1))} +
                {TwoPC.Item.part { id := x.2.1, state := x.2.2.2.1 }} +
              x.2.2.2.2.2.2.2)] := by
  certify_comp

theorem TwoPC.twoPC_inv.obligation_46 :
    Unification.sound (Narrowing.mayFire TwoPC.deliverAbort TwoPC.commP)
      [Unification.Unifier.bind
          fun (x : ℕ × ℕ × TwoPC.Oids × TwoPC.PState × ℕ × TwoPC.Oids × TwoPC.Oids × TwoPC.Items) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {TwoPC.Item.coord
                    { id := x.2.2.2.2.1, phase := TwoPC.CState.committing, parts := x.2.2.2.2.2.1,
                      wait := x.2.2.2.2.2.2.1 }} +
                x.2.2.2.2.2.2.2),
            x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
            {TwoPC.Item.msg (TwoPC.Msg.decision false x.1 ({x.2.1} + x.2.2.1))} +
                {TwoPC.Item.part { id := x.2.1, state := x.2.2.2.1 }} +
              x.2.2.2.2.2.2.2)] := by
  certify_sound

theorem TwoPC.twoPC_inv.obligation_47 :
    Unification.complete (Narrowing.mayFire TwoPC.deliverAbort TwoPC.abrtP)
      [Unification.Unifier.bind
          fun (x : ℕ × ℕ × TwoPC.Oids × TwoPC.PState × ℕ × TwoPC.Oids × TwoPC.Oids × TwoPC.Items) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {TwoPC.Item.coord
                    { id := x.2.2.2.2.1, phase := TwoPC.CState.aborting, parts := x.2.2.2.2.2.1,
                      wait := x.2.2.2.2.2.2.1 }} +
                x.2.2.2.2.2.2.2),
            x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
            {TwoPC.Item.msg (TwoPC.Msg.decision false x.1 ({x.2.1} + x.2.2.1))} +
                {TwoPC.Item.part { id := x.2.1, state := x.2.2.2.1 }} +
              x.2.2.2.2.2.2.2)] := by
  certify_comp

theorem TwoPC.twoPC_inv.obligation_48 :
    Unification.sound (Narrowing.mayFire TwoPC.deliverAbort TwoPC.abrtP)
      [Unification.Unifier.bind
          fun (x : ℕ × ℕ × TwoPC.Oids × TwoPC.PState × ℕ × TwoPC.Oids × TwoPC.Oids × TwoPC.Items) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {TwoPC.Item.coord
                    { id := x.2.2.2.2.1, phase := TwoPC.CState.aborting, parts := x.2.2.2.2.2.1,
                      wait := x.2.2.2.2.2.2.1 }} +
                x.2.2.2.2.2.2.2),
            x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
            {TwoPC.Item.msg (TwoPC.Msg.decision false x.1 ({x.2.1} + x.2.2.1))} +
                {TwoPC.Item.part { id := x.2.1, state := x.2.2.2.1 }} +
              x.2.2.2.2.2.2.2)] := by
  certify_sound

theorem TwoPC.twoPC_inv.obligation_49 :
    Unification.complete (Narrowing.mayFire TwoPC.lossVote TwoPC.collP)
      [Unification.Unifier.bind fun (x : Bool × ℕ × ℕ × ℕ × TwoPC.Oids × TwoPC.Oids × TwoPC.Items) =>
          ((x.1, x.2.1, x.2.2.1,
              {TwoPC.Item.coord
                    { id := x.2.2.2.1, phase := TwoPC.CState.collecting, parts := x.2.2.2.2.1,
                      wait := x.2.2.2.2.2.1 }} +
                x.2.2.2.2.2.2),
            x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
            {TwoPC.Item.msg (TwoPC.Msg.vote x.1 x.2.1 x.2.2.1)} + x.2.2.2.2.2.2)] := by
  certify_comp

theorem TwoPC.twoPC_inv.obligation_50 :
    Unification.sound (Narrowing.mayFire TwoPC.lossVote TwoPC.collP)
      [Unification.Unifier.bind fun (x : Bool × ℕ × ℕ × ℕ × TwoPC.Oids × TwoPC.Oids × TwoPC.Items) =>
          ((x.1, x.2.1, x.2.2.1,
              {TwoPC.Item.coord
                    { id := x.2.2.2.1, phase := TwoPC.CState.collecting, parts := x.2.2.2.2.1,
                      wait := x.2.2.2.2.2.1 }} +
                x.2.2.2.2.2.2),
            x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
            {TwoPC.Item.msg (TwoPC.Msg.vote x.1 x.2.1 x.2.2.1)} + x.2.2.2.2.2.2)] := by
  certify_sound

theorem TwoPC.twoPC_inv.obligation_51 :
    Unification.complete (Narrowing.mayFire TwoPC.lossVote TwoPC.commP)
      [Unification.Unifier.bind fun (x : Bool × ℕ × ℕ × ℕ × TwoPC.Oids × TwoPC.Oids × TwoPC.Items) =>
          ((x.1, x.2.1, x.2.2.1,
              {TwoPC.Item.coord
                    { id := x.2.2.2.1, phase := TwoPC.CState.committing, parts := x.2.2.2.2.1,
                      wait := x.2.2.2.2.2.1 }} +
                x.2.2.2.2.2.2),
            x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
            {TwoPC.Item.msg (TwoPC.Msg.vote x.1 x.2.1 x.2.2.1)} + x.2.2.2.2.2.2)] := by
  certify_comp

theorem TwoPC.twoPC_inv.obligation_52 :
    Unification.sound (Narrowing.mayFire TwoPC.lossVote TwoPC.commP)
      [Unification.Unifier.bind fun (x : Bool × ℕ × ℕ × ℕ × TwoPC.Oids × TwoPC.Oids × TwoPC.Items) =>
          ((x.1, x.2.1, x.2.2.1,
              {TwoPC.Item.coord
                    { id := x.2.2.2.1, phase := TwoPC.CState.committing, parts := x.2.2.2.2.1,
                      wait := x.2.2.2.2.2.1 }} +
                x.2.2.2.2.2.2),
            x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
            {TwoPC.Item.msg (TwoPC.Msg.vote x.1 x.2.1 x.2.2.1)} + x.2.2.2.2.2.2)] := by
  certify_sound

theorem TwoPC.twoPC_inv.obligation_53 :
    Unification.complete (Narrowing.mayFire TwoPC.lossVote TwoPC.abrtP)
      [Unification.Unifier.bind fun (x : Bool × ℕ × ℕ × ℕ × TwoPC.Oids × TwoPC.Oids × TwoPC.Items) =>
          ((x.1, x.2.1, x.2.2.1,
              {TwoPC.Item.coord
                    { id := x.2.2.2.1, phase := TwoPC.CState.aborting, parts := x.2.2.2.2.1, wait := x.2.2.2.2.2.1 }} +
                x.2.2.2.2.2.2),
            x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
            {TwoPC.Item.msg (TwoPC.Msg.vote x.1 x.2.1 x.2.2.1)} + x.2.2.2.2.2.2)] := by
  certify_comp

theorem TwoPC.twoPC_inv.obligation_54 :
    Unification.sound (Narrowing.mayFire TwoPC.lossVote TwoPC.abrtP)
      [Unification.Unifier.bind fun (x : Bool × ℕ × ℕ × ℕ × TwoPC.Oids × TwoPC.Oids × TwoPC.Items) =>
          ((x.1, x.2.1, x.2.2.1,
              {TwoPC.Item.coord
                    { id := x.2.2.2.1, phase := TwoPC.CState.aborting, parts := x.2.2.2.2.1, wait := x.2.2.2.2.2.1 }} +
                x.2.2.2.2.2.2),
            x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
            {TwoPC.Item.msg (TwoPC.Msg.vote x.1 x.2.1 x.2.2.1)} + x.2.2.2.2.2.2)] := by
  certify_sound
