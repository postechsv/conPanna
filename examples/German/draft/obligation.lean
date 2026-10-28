import examples.German.draft.German
import conPanna.Unification.Tactics.maudeCertifyComp

/-!
German: the obligations of the per-rule narrowings, printed by `#obligations` and pasted
verbatim. Completeness is certified by Maude (`maude_certify_comp`); soundness is left
open for now.
-/

namespace German

open Expresso Unification Narrowing

-- the statements below are `#obligations`' output, pasted verbatim
set_option linter.style.longLine false

theorem sendReqS_inv.obligation_1 :
    Unification.complete (Narrowing.mayFire sendReqS freeP)
      [Unification.Unifier.bind fun (x : ℕ × Gnt × Ack × Cmd × ℕ × Oids × Oids) =>
          ((x.1, x.2.1, x.2.2.1,
              {Item.dir
                  { cmd := x.2.2.2.1, ptr := x.2.2.2.2.1, exGntd := false, shr := x.2.2.2.2.2.1,
                    inv := x.2.2.2.2.2.2 }}),
            x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2,
            {Item.cache { id := x.1, state := CacheState.invalid, ch1 := Req.noReq, ch2 := x.2.1, ch3 := x.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × Gnt × Ack × Cmd × ℕ × Oids × Oids × Items) =>
          ((x.1, x.2.1, x.2.2.1,
              x.2.2.2.2.2.2.2 +
                {Item.dir
                    { cmd := x.2.2.2.1, ptr := x.2.2.2.2.1, exGntd := false, shr := x.2.2.2.2.2.1,
                      inv := x.2.2.2.2.2.2.1 }}),
            x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
            x.2.2.2.2.2.2.2 +
              {Item.cache
                  { id := x.1, state := CacheState.invalid, ch1 := Req.noReq, ch2 := x.2.1, ch3 := x.2.2.1 }})] := by
  maude_certify_comp

theorem sendReqS_inv.obligation_2 :
    Unification.sound (Narrowing.mayFire sendReqS freeP)
      [Unification.Unifier.bind fun (x : ℕ × Gnt × Ack × Cmd × ℕ × Oids × Oids) =>
          ((x.1, x.2.1, x.2.2.1,
              {Item.dir
                  { cmd := x.2.2.2.1, ptr := x.2.2.2.2.1, exGntd := false, shr := x.2.2.2.2.2.1,
                    inv := x.2.2.2.2.2.2 }}),
            x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2,
            {Item.cache { id := x.1, state := CacheState.invalid, ch1 := Req.noReq, ch2 := x.2.1, ch3 := x.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × Gnt × Ack × Cmd × ℕ × Oids × Oids × Items) =>
          ((x.1, x.2.1, x.2.2.1,
              x.2.2.2.2.2.2.2 +
                {Item.dir
                    { cmd := x.2.2.2.1, ptr := x.2.2.2.2.1, exGntd := false, shr := x.2.2.2.2.2.1,
                      inv := x.2.2.2.2.2.2.1 }}),
            x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
            x.2.2.2.2.2.2.2 +
              {Item.cache
                  { id := x.1, state := CacheState.invalid, ch1 := Req.noReq, ch2 := x.2.1, ch3 := x.2.2.1 }})] := by
  sorry

theorem sendReqS_inv.obligation_3 :
    Unification.complete (Narrowing.mayFire sendReqS ownE)
      [Unification.Unifier.bind fun (x : ℕ × Gnt × Ack × ℕ × Req × Cmd × ℕ × Oids) =>
          ((x.1, x.2.1, x.2.2.1,
              {Item.cache
                    { id := x.2.2.2.1, state := CacheState.exclusive, ch1 := x.2.2.2.2.1, ch2 := Gnt.noGnt,
                      ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.1},
                      inv := x.2.2.2.2.2.2.2 }}),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2, x.2.2.2.1, x.2.2.2.2.1,
            {Item.cache { id := x.1, state := CacheState.invalid, ch1 := Req.noReq, ch2 := x.2.1, ch3 := x.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × Gnt × Ack × ℕ × Req × Cmd × ℕ × Oids × Items) =>
          ((x.1, x.2.1, x.2.2.1,
              x.2.2.2.2.2.2.2.2 +
                  {Item.cache
                      { id := x.2.2.2.1, state := CacheState.exclusive, ch1 := x.2.2.2.2.1, ch2 := Gnt.noGnt,
                        ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.1},
                      inv := x.2.2.2.2.2.2.2.1 }}),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
            x.2.2.2.2.2.2.2.2 +
              {Item.cache
                  { id := x.1, state := CacheState.invalid, ch1 := Req.noReq, ch2 := x.2.1, ch3 := x.2.2.1 }})] := by
  maude_certify_comp

theorem sendReqS_inv.obligation_4 :
    Unification.sound (Narrowing.mayFire sendReqS ownE)
      [Unification.Unifier.bind fun (x : ℕ × Gnt × Ack × ℕ × Req × Cmd × ℕ × Oids) =>
          ((x.1, x.2.1, x.2.2.1,
              {Item.cache
                    { id := x.2.2.2.1, state := CacheState.exclusive, ch1 := x.2.2.2.2.1, ch2 := Gnt.noGnt,
                      ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.1},
                      inv := x.2.2.2.2.2.2.2 }}),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2, x.2.2.2.1, x.2.2.2.2.1,
            {Item.cache { id := x.1, state := CacheState.invalid, ch1 := Req.noReq, ch2 := x.2.1, ch3 := x.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × Gnt × Ack × ℕ × Req × Cmd × ℕ × Oids × Items) =>
          ((x.1, x.2.1, x.2.2.1,
              x.2.2.2.2.2.2.2.2 +
                  {Item.cache
                      { id := x.2.2.2.1, state := CacheState.exclusive, ch1 := x.2.2.2.2.1, ch2 := Gnt.noGnt,
                        ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.1},
                      inv := x.2.2.2.2.2.2.2.1 }}),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
            x.2.2.2.2.2.2.2.2 +
              {Item.cache
                  { id := x.1, state := CacheState.invalid, ch1 := Req.noReq, ch2 := x.2.1, ch3 := x.2.2.1 }})] := by
  sorry

theorem sendReqS_inv.obligation_5 :
    Unification.complete (Narrowing.mayFire sendReqS ownG)
      [Unification.Unifier.bind fun (x : ℕ × Gnt × Ack × ℕ × Req × Cmd × ℕ × Oids) =>
          ((x.1, x.2.1, x.2.2.1,
              {Item.cache
                    { id := x.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.1, ch2 := Gnt.gntE,
                      ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.1},
                      inv := x.2.2.2.2.2.2.2 }}),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2, x.2.2.2.1, x.2.2.2.2.1,
            {Item.cache { id := x.1, state := CacheState.invalid, ch1 := Req.noReq, ch2 := x.2.1, ch3 := x.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × Gnt × Ack × ℕ × Req × Cmd × ℕ × Oids × Items) =>
          ((x.1, x.2.1, x.2.2.1,
              x.2.2.2.2.2.2.2.2 +
                  {Item.cache
                      { id := x.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.1, ch2 := Gnt.gntE,
                        ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.1},
                      inv := x.2.2.2.2.2.2.2.1 }}),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
            x.2.2.2.2.2.2.2.2 +
              {Item.cache { id := x.1, state := CacheState.invalid, ch1 := Req.noReq, ch2 := x.2.1, ch3 := x.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × Cmd × ℕ × Oids) =>
          ((x.1, Gnt.gntE, Ack.noAck,
              {Item.dir { cmd := x.2.1, ptr := x.2.2.1, exGntd := true, shr := {x.1}, inv := x.2.2.2 }}),
            x.2.1, x.2.2.1, x.2.2.2, x.1, Req.noReq, ∅),
        Unification.Unifier.bind fun (x : Items × ℕ × Cmd × ℕ × Oids) =>
          ((x.2.1, Gnt.gntE, Ack.noAck,
              x.1 + {Item.dir { cmd := x.2.2.1, ptr := x.2.2.2.1, exGntd := true, shr := {x.2.1}, inv := x.2.2.2.2 }}),
            x.2.2.1, x.2.2.2.1, x.2.2.2.2, x.2.1, Req.noReq, x.1)] := by
  maude_certify_comp

theorem sendReqS_inv.obligation_6 :
    Unification.sound (Narrowing.mayFire sendReqS ownG)
      [Unification.Unifier.bind fun (x : ℕ × Gnt × Ack × ℕ × Req × Cmd × ℕ × Oids) =>
          ((x.1, x.2.1, x.2.2.1,
              {Item.cache
                    { id := x.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.1, ch2 := Gnt.gntE,
                      ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.1},
                      inv := x.2.2.2.2.2.2.2 }}),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2, x.2.2.2.1, x.2.2.2.2.1,
            {Item.cache { id := x.1, state := CacheState.invalid, ch1 := Req.noReq, ch2 := x.2.1, ch3 := x.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × Gnt × Ack × ℕ × Req × Cmd × ℕ × Oids × Items) =>
          ((x.1, x.2.1, x.2.2.1,
              x.2.2.2.2.2.2.2.2 +
                  {Item.cache
                      { id := x.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.1, ch2 := Gnt.gntE,
                        ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.1},
                      inv := x.2.2.2.2.2.2.2.1 }}),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
            x.2.2.2.2.2.2.2.2 +
              {Item.cache { id := x.1, state := CacheState.invalid, ch1 := Req.noReq, ch2 := x.2.1, ch3 := x.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × Cmd × ℕ × Oids) =>
          ((x.1, Gnt.gntE, Ack.noAck,
              {Item.dir { cmd := x.2.1, ptr := x.2.2.1, exGntd := true, shr := {x.1}, inv := x.2.2.2 }}),
            x.2.1, x.2.2.1, x.2.2.2, x.1, Req.noReq, ∅),
        Unification.Unifier.bind fun (x : Items × ℕ × Cmd × ℕ × Oids) =>
          ((x.2.1, Gnt.gntE, Ack.noAck,
              x.1 + {Item.dir { cmd := x.2.2.1, ptr := x.2.2.2.1, exGntd := true, shr := {x.2.1}, inv := x.2.2.2.2 }}),
            x.2.2.1, x.2.2.2.1, x.2.2.2.2, x.2.1, Req.noReq, x.1)] := by
  sorry

theorem sendReqS_inv.obligation_7 :
    Unification.complete (Narrowing.mayFire sendReqS ownInv)
      [Unification.Unifier.bind fun (x : ℕ × Gnt × Ack × ℕ × Req × Cmd × ℕ) =>
          ((x.1, x.2.1, x.2.2.1,
              {Item.cache
                    { id := x.2.2.2.1, state := CacheState.exclusive, ch1 := x.2.2.2.2.1, ch2 := Gnt.inv,
                      ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2, exGntd := true, shr := {x.2.2.2.1}, inv := ∅ }}),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2, x.2.2.2.1, x.2.2.2.2.1,
            {Item.cache { id := x.1, state := CacheState.invalid, ch1 := Req.noReq, ch2 := x.2.1, ch3 := x.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × Gnt × Ack × ℕ × Req × Cmd × ℕ × Items) =>
          ((x.1, x.2.1, x.2.2.1,
              x.2.2.2.2.2.2.2 +
                  {Item.cache
                      { id := x.2.2.2.1, state := CacheState.exclusive, ch1 := x.2.2.2.2.1, ch2 := Gnt.inv,
                        ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.1}, inv := ∅ }}),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
            x.2.2.2.2.2.2.2 +
              {Item.cache
                  { id := x.1, state := CacheState.invalid, ch1 := Req.noReq, ch2 := x.2.1, ch3 := x.2.2.1 }})] := by
  maude_certify_comp

theorem sendReqS_inv.obligation_8 :
    Unification.sound (Narrowing.mayFire sendReqS ownInv)
      [Unification.Unifier.bind fun (x : ℕ × Gnt × Ack × ℕ × Req × Cmd × ℕ) =>
          ((x.1, x.2.1, x.2.2.1,
              {Item.cache
                    { id := x.2.2.2.1, state := CacheState.exclusive, ch1 := x.2.2.2.2.1, ch2 := Gnt.inv,
                      ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2, exGntd := true, shr := {x.2.2.2.1}, inv := ∅ }}),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2, x.2.2.2.1, x.2.2.2.2.1,
            {Item.cache { id := x.1, state := CacheState.invalid, ch1 := Req.noReq, ch2 := x.2.1, ch3 := x.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × Gnt × Ack × ℕ × Req × Cmd × ℕ × Items) =>
          ((x.1, x.2.1, x.2.2.1,
              x.2.2.2.2.2.2.2 +
                  {Item.cache
                      { id := x.2.2.2.1, state := CacheState.exclusive, ch1 := x.2.2.2.2.1, ch2 := Gnt.inv,
                        ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.1}, inv := ∅ }}),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
            x.2.2.2.2.2.2.2 +
              {Item.cache
                  { id := x.1, state := CacheState.invalid, ch1 := Req.noReq, ch2 := x.2.1, ch3 := x.2.2.1 }})] := by
  sorry

theorem sendReqS_inv.obligation_9 :
    Unification.complete (Narrowing.mayFire sendReqS ownAck)
      [Unification.Unifier.bind fun (x : ℕ × Gnt × Ack × ℕ × Req × Cmd × ℕ) =>
          ((x.1, x.2.1, x.2.2.1,
              {Item.cache
                    { id := x.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.1, ch2 := Gnt.noGnt,
                      ch3 := Ack.invAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2, exGntd := true, shr := {x.2.2.2.1}, inv := ∅ }}),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2, x.2.2.2.1, x.2.2.2.2.1,
            {Item.cache { id := x.1, state := CacheState.invalid, ch1 := Req.noReq, ch2 := x.2.1, ch3 := x.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × Gnt × Ack × ℕ × Req × Cmd × ℕ × Items) =>
          ((x.1, x.2.1, x.2.2.1,
              x.2.2.2.2.2.2.2 +
                  {Item.cache
                      { id := x.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.1, ch2 := Gnt.noGnt,
                        ch3 := Ack.invAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.1}, inv := ∅ }}),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
            x.2.2.2.2.2.2.2 +
              {Item.cache { id := x.1, state := CacheState.invalid, ch1 := Req.noReq, ch2 := x.2.1, ch3 := x.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × Cmd × ℕ) =>
          ((x.1, Gnt.noGnt, Ack.invAck,
              {Item.dir { cmd := x.2.1, ptr := x.2.2, exGntd := true, shr := {x.1}, inv := ∅ }}),
            x.2.1, x.2.2, x.1, Req.noReq, ∅),
        Unification.Unifier.bind fun (x : Items × ℕ × Cmd × ℕ) =>
          ((x.2.1, Gnt.noGnt, Ack.invAck,
              x.1 + {Item.dir { cmd := x.2.2.1, ptr := x.2.2.2, exGntd := true, shr := {x.2.1}, inv := ∅ }}),
            x.2.2.1, x.2.2.2, x.2.1, Req.noReq, x.1)] := by
  maude_certify_comp

theorem sendReqS_inv.obligation_10 :
    Unification.sound (Narrowing.mayFire sendReqS ownAck)
      [Unification.Unifier.bind fun (x : ℕ × Gnt × Ack × ℕ × Req × Cmd × ℕ) =>
          ((x.1, x.2.1, x.2.2.1,
              {Item.cache
                    { id := x.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.1, ch2 := Gnt.noGnt,
                      ch3 := Ack.invAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2, exGntd := true, shr := {x.2.2.2.1}, inv := ∅ }}),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2, x.2.2.2.1, x.2.2.2.2.1,
            {Item.cache { id := x.1, state := CacheState.invalid, ch1 := Req.noReq, ch2 := x.2.1, ch3 := x.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × Gnt × Ack × ℕ × Req × Cmd × ℕ × Items) =>
          ((x.1, x.2.1, x.2.2.1,
              x.2.2.2.2.2.2.2 +
                  {Item.cache
                      { id := x.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.1, ch2 := Gnt.noGnt,
                        ch3 := Ack.invAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.1}, inv := ∅ }}),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
            x.2.2.2.2.2.2.2 +
              {Item.cache { id := x.1, state := CacheState.invalid, ch1 := Req.noReq, ch2 := x.2.1, ch3 := x.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × Cmd × ℕ) =>
          ((x.1, Gnt.noGnt, Ack.invAck,
              {Item.dir { cmd := x.2.1, ptr := x.2.2, exGntd := true, shr := {x.1}, inv := ∅ }}),
            x.2.1, x.2.2, x.1, Req.noReq, ∅),
        Unification.Unifier.bind fun (x : Items × ℕ × Cmd × ℕ) =>
          ((x.2.1, Gnt.noGnt, Ack.invAck,
              x.1 + {Item.dir { cmd := x.2.2.1, ptr := x.2.2.2, exGntd := true, shr := {x.2.1}, inv := ∅ }}),
            x.2.2.1, x.2.2.2, x.2.1, Req.noReq, x.1)] := by
  sorry

theorem sendReqEI_inv.obligation_1 :
    Unification.complete (Narrowing.mayFire sendReqEI freeP)
      [Unification.Unifier.bind fun (x : ℕ × Gnt × Ack × Cmd × ℕ × Oids × Oids) =>
          ((x.1, x.2.1, x.2.2.1,
              {Item.dir
                  { cmd := x.2.2.2.1, ptr := x.2.2.2.2.1, exGntd := false, shr := x.2.2.2.2.2.1,
                    inv := x.2.2.2.2.2.2 }}),
            x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2,
            {Item.cache { id := x.1, state := CacheState.invalid, ch1 := Req.noReq, ch2 := x.2.1, ch3 := x.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × Gnt × Ack × Cmd × ℕ × Oids × Oids × Items) =>
          ((x.1, x.2.1, x.2.2.1,
              x.2.2.2.2.2.2.2 +
                {Item.dir
                    { cmd := x.2.2.2.1, ptr := x.2.2.2.2.1, exGntd := false, shr := x.2.2.2.2.2.1,
                      inv := x.2.2.2.2.2.2.1 }}),
            x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
            x.2.2.2.2.2.2.2 +
              {Item.cache
                  { id := x.1, state := CacheState.invalid, ch1 := Req.noReq, ch2 := x.2.1, ch3 := x.2.2.1 }})] := by
  maude_certify_comp

theorem sendReqEI_inv.obligation_2 :
    Unification.sound (Narrowing.mayFire sendReqEI freeP)
      [Unification.Unifier.bind fun (x : ℕ × Gnt × Ack × Cmd × ℕ × Oids × Oids) =>
          ((x.1, x.2.1, x.2.2.1,
              {Item.dir
                  { cmd := x.2.2.2.1, ptr := x.2.2.2.2.1, exGntd := false, shr := x.2.2.2.2.2.1,
                    inv := x.2.2.2.2.2.2 }}),
            x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2,
            {Item.cache { id := x.1, state := CacheState.invalid, ch1 := Req.noReq, ch2 := x.2.1, ch3 := x.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × Gnt × Ack × Cmd × ℕ × Oids × Oids × Items) =>
          ((x.1, x.2.1, x.2.2.1,
              x.2.2.2.2.2.2.2 +
                {Item.dir
                    { cmd := x.2.2.2.1, ptr := x.2.2.2.2.1, exGntd := false, shr := x.2.2.2.2.2.1,
                      inv := x.2.2.2.2.2.2.1 }}),
            x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
            x.2.2.2.2.2.2.2 +
              {Item.cache
                  { id := x.1, state := CacheState.invalid, ch1 := Req.noReq, ch2 := x.2.1, ch3 := x.2.2.1 }})] := by
  sorry

theorem sendReqEI_inv.obligation_3 :
    Unification.complete (Narrowing.mayFire sendReqEI ownE)
      [Unification.Unifier.bind fun (x : ℕ × Gnt × Ack × ℕ × Req × Cmd × ℕ × Oids) =>
          ((x.1, x.2.1, x.2.2.1,
              {Item.cache
                    { id := x.2.2.2.1, state := CacheState.exclusive, ch1 := x.2.2.2.2.1, ch2 := Gnt.noGnt,
                      ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.1},
                      inv := x.2.2.2.2.2.2.2 }}),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2, x.2.2.2.1, x.2.2.2.2.1,
            {Item.cache { id := x.1, state := CacheState.invalid, ch1 := Req.noReq, ch2 := x.2.1, ch3 := x.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × Gnt × Ack × ℕ × Req × Cmd × ℕ × Oids × Items) =>
          ((x.1, x.2.1, x.2.2.1,
              x.2.2.2.2.2.2.2.2 +
                  {Item.cache
                      { id := x.2.2.2.1, state := CacheState.exclusive, ch1 := x.2.2.2.2.1, ch2 := Gnt.noGnt,
                        ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.1},
                      inv := x.2.2.2.2.2.2.2.1 }}),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
            x.2.2.2.2.2.2.2.2 +
              {Item.cache
                  { id := x.1, state := CacheState.invalid, ch1 := Req.noReq, ch2 := x.2.1, ch3 := x.2.2.1 }})] := by
  maude_certify_comp

theorem sendReqEI_inv.obligation_4 :
    Unification.sound (Narrowing.mayFire sendReqEI ownE)
      [Unification.Unifier.bind fun (x : ℕ × Gnt × Ack × ℕ × Req × Cmd × ℕ × Oids) =>
          ((x.1, x.2.1, x.2.2.1,
              {Item.cache
                    { id := x.2.2.2.1, state := CacheState.exclusive, ch1 := x.2.2.2.2.1, ch2 := Gnt.noGnt,
                      ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.1},
                      inv := x.2.2.2.2.2.2.2 }}),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2, x.2.2.2.1, x.2.2.2.2.1,
            {Item.cache { id := x.1, state := CacheState.invalid, ch1 := Req.noReq, ch2 := x.2.1, ch3 := x.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × Gnt × Ack × ℕ × Req × Cmd × ℕ × Oids × Items) =>
          ((x.1, x.2.1, x.2.2.1,
              x.2.2.2.2.2.2.2.2 +
                  {Item.cache
                      { id := x.2.2.2.1, state := CacheState.exclusive, ch1 := x.2.2.2.2.1, ch2 := Gnt.noGnt,
                        ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.1},
                      inv := x.2.2.2.2.2.2.2.1 }}),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
            x.2.2.2.2.2.2.2.2 +
              {Item.cache
                  { id := x.1, state := CacheState.invalid, ch1 := Req.noReq, ch2 := x.2.1, ch3 := x.2.2.1 }})] := by
  sorry

theorem sendReqEI_inv.obligation_5 :
    Unification.complete (Narrowing.mayFire sendReqEI ownG)
      [Unification.Unifier.bind fun (x : ℕ × Gnt × Ack × ℕ × Req × Cmd × ℕ × Oids) =>
          ((x.1, x.2.1, x.2.2.1,
              {Item.cache
                    { id := x.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.1, ch2 := Gnt.gntE,
                      ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.1},
                      inv := x.2.2.2.2.2.2.2 }}),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2, x.2.2.2.1, x.2.2.2.2.1,
            {Item.cache { id := x.1, state := CacheState.invalid, ch1 := Req.noReq, ch2 := x.2.1, ch3 := x.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × Gnt × Ack × ℕ × Req × Cmd × ℕ × Oids × Items) =>
          ((x.1, x.2.1, x.2.2.1,
              x.2.2.2.2.2.2.2.2 +
                  {Item.cache
                      { id := x.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.1, ch2 := Gnt.gntE,
                        ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.1},
                      inv := x.2.2.2.2.2.2.2.1 }}),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
            x.2.2.2.2.2.2.2.2 +
              {Item.cache { id := x.1, state := CacheState.invalid, ch1 := Req.noReq, ch2 := x.2.1, ch3 := x.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × Cmd × ℕ × Oids) =>
          ((x.1, Gnt.gntE, Ack.noAck,
              {Item.dir { cmd := x.2.1, ptr := x.2.2.1, exGntd := true, shr := {x.1}, inv := x.2.2.2 }}),
            x.2.1, x.2.2.1, x.2.2.2, x.1, Req.noReq, ∅),
        Unification.Unifier.bind fun (x : Items × ℕ × Cmd × ℕ × Oids) =>
          ((x.2.1, Gnt.gntE, Ack.noAck,
              x.1 + {Item.dir { cmd := x.2.2.1, ptr := x.2.2.2.1, exGntd := true, shr := {x.2.1}, inv := x.2.2.2.2 }}),
            x.2.2.1, x.2.2.2.1, x.2.2.2.2, x.2.1, Req.noReq, x.1)] := by
  maude_certify_comp

theorem sendReqEI_inv.obligation_6 :
    Unification.sound (Narrowing.mayFire sendReqEI ownG)
      [Unification.Unifier.bind fun (x : ℕ × Gnt × Ack × ℕ × Req × Cmd × ℕ × Oids) =>
          ((x.1, x.2.1, x.2.2.1,
              {Item.cache
                    { id := x.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.1, ch2 := Gnt.gntE,
                      ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.1},
                      inv := x.2.2.2.2.2.2.2 }}),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2, x.2.2.2.1, x.2.2.2.2.1,
            {Item.cache { id := x.1, state := CacheState.invalid, ch1 := Req.noReq, ch2 := x.2.1, ch3 := x.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × Gnt × Ack × ℕ × Req × Cmd × ℕ × Oids × Items) =>
          ((x.1, x.2.1, x.2.2.1,
              x.2.2.2.2.2.2.2.2 +
                  {Item.cache
                      { id := x.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.1, ch2 := Gnt.gntE,
                        ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.1},
                      inv := x.2.2.2.2.2.2.2.1 }}),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
            x.2.2.2.2.2.2.2.2 +
              {Item.cache { id := x.1, state := CacheState.invalid, ch1 := Req.noReq, ch2 := x.2.1, ch3 := x.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × Cmd × ℕ × Oids) =>
          ((x.1, Gnt.gntE, Ack.noAck,
              {Item.dir { cmd := x.2.1, ptr := x.2.2.1, exGntd := true, shr := {x.1}, inv := x.2.2.2 }}),
            x.2.1, x.2.2.1, x.2.2.2, x.1, Req.noReq, ∅),
        Unification.Unifier.bind fun (x : Items × ℕ × Cmd × ℕ × Oids) =>
          ((x.2.1, Gnt.gntE, Ack.noAck,
              x.1 + {Item.dir { cmd := x.2.2.1, ptr := x.2.2.2.1, exGntd := true, shr := {x.2.1}, inv := x.2.2.2.2 }}),
            x.2.2.1, x.2.2.2.1, x.2.2.2.2, x.2.1, Req.noReq, x.1)] := by
  sorry

theorem sendReqEI_inv.obligation_7 :
    Unification.complete (Narrowing.mayFire sendReqEI ownInv)
      [Unification.Unifier.bind fun (x : ℕ × Gnt × Ack × ℕ × Req × Cmd × ℕ) =>
          ((x.1, x.2.1, x.2.2.1,
              {Item.cache
                    { id := x.2.2.2.1, state := CacheState.exclusive, ch1 := x.2.2.2.2.1, ch2 := Gnt.inv,
                      ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2, exGntd := true, shr := {x.2.2.2.1}, inv := ∅ }}),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2, x.2.2.2.1, x.2.2.2.2.1,
            {Item.cache { id := x.1, state := CacheState.invalid, ch1 := Req.noReq, ch2 := x.2.1, ch3 := x.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × Gnt × Ack × ℕ × Req × Cmd × ℕ × Items) =>
          ((x.1, x.2.1, x.2.2.1,
              x.2.2.2.2.2.2.2 +
                  {Item.cache
                      { id := x.2.2.2.1, state := CacheState.exclusive, ch1 := x.2.2.2.2.1, ch2 := Gnt.inv,
                        ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.1}, inv := ∅ }}),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
            x.2.2.2.2.2.2.2 +
              {Item.cache
                  { id := x.1, state := CacheState.invalid, ch1 := Req.noReq, ch2 := x.2.1, ch3 := x.2.2.1 }})] := by
  maude_certify_comp

theorem sendReqEI_inv.obligation_8 :
    Unification.sound (Narrowing.mayFire sendReqEI ownInv)
      [Unification.Unifier.bind fun (x : ℕ × Gnt × Ack × ℕ × Req × Cmd × ℕ) =>
          ((x.1, x.2.1, x.2.2.1,
              {Item.cache
                    { id := x.2.2.2.1, state := CacheState.exclusive, ch1 := x.2.2.2.2.1, ch2 := Gnt.inv,
                      ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2, exGntd := true, shr := {x.2.2.2.1}, inv := ∅ }}),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2, x.2.2.2.1, x.2.2.2.2.1,
            {Item.cache { id := x.1, state := CacheState.invalid, ch1 := Req.noReq, ch2 := x.2.1, ch3 := x.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × Gnt × Ack × ℕ × Req × Cmd × ℕ × Items) =>
          ((x.1, x.2.1, x.2.2.1,
              x.2.2.2.2.2.2.2 +
                  {Item.cache
                      { id := x.2.2.2.1, state := CacheState.exclusive, ch1 := x.2.2.2.2.1, ch2 := Gnt.inv,
                        ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.1}, inv := ∅ }}),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
            x.2.2.2.2.2.2.2 +
              {Item.cache
                  { id := x.1, state := CacheState.invalid, ch1 := Req.noReq, ch2 := x.2.1, ch3 := x.2.2.1 }})] := by
  sorry

theorem sendReqEI_inv.obligation_9 :
    Unification.complete (Narrowing.mayFire sendReqEI ownAck)
      [Unification.Unifier.bind fun (x : ℕ × Gnt × Ack × ℕ × Req × Cmd × ℕ) =>
          ((x.1, x.2.1, x.2.2.1,
              {Item.cache
                    { id := x.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.1, ch2 := Gnt.noGnt,
                      ch3 := Ack.invAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2, exGntd := true, shr := {x.2.2.2.1}, inv := ∅ }}),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2, x.2.2.2.1, x.2.2.2.2.1,
            {Item.cache { id := x.1, state := CacheState.invalid, ch1 := Req.noReq, ch2 := x.2.1, ch3 := x.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × Gnt × Ack × ℕ × Req × Cmd × ℕ × Items) =>
          ((x.1, x.2.1, x.2.2.1,
              x.2.2.2.2.2.2.2 +
                  {Item.cache
                      { id := x.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.1, ch2 := Gnt.noGnt,
                        ch3 := Ack.invAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.1}, inv := ∅ }}),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
            x.2.2.2.2.2.2.2 +
              {Item.cache { id := x.1, state := CacheState.invalid, ch1 := Req.noReq, ch2 := x.2.1, ch3 := x.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × Cmd × ℕ) =>
          ((x.1, Gnt.noGnt, Ack.invAck,
              {Item.dir { cmd := x.2.1, ptr := x.2.2, exGntd := true, shr := {x.1}, inv := ∅ }}),
            x.2.1, x.2.2, x.1, Req.noReq, ∅),
        Unification.Unifier.bind fun (x : Items × ℕ × Cmd × ℕ) =>
          ((x.2.1, Gnt.noGnt, Ack.invAck,
              x.1 + {Item.dir { cmd := x.2.2.1, ptr := x.2.2.2, exGntd := true, shr := {x.2.1}, inv := ∅ }}),
            x.2.2.1, x.2.2.2, x.2.1, Req.noReq, x.1)] := by
  maude_certify_comp

theorem sendReqEI_inv.obligation_10 :
    Unification.sound (Narrowing.mayFire sendReqEI ownAck)
      [Unification.Unifier.bind fun (x : ℕ × Gnt × Ack × ℕ × Req × Cmd × ℕ) =>
          ((x.1, x.2.1, x.2.2.1,
              {Item.cache
                    { id := x.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.1, ch2 := Gnt.noGnt,
                      ch3 := Ack.invAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2, exGntd := true, shr := {x.2.2.2.1}, inv := ∅ }}),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2, x.2.2.2.1, x.2.2.2.2.1,
            {Item.cache { id := x.1, state := CacheState.invalid, ch1 := Req.noReq, ch2 := x.2.1, ch3 := x.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × Gnt × Ack × ℕ × Req × Cmd × ℕ × Items) =>
          ((x.1, x.2.1, x.2.2.1,
              x.2.2.2.2.2.2.2 +
                  {Item.cache
                      { id := x.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.1, ch2 := Gnt.noGnt,
                        ch3 := Ack.invAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.1}, inv := ∅ }}),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
            x.2.2.2.2.2.2.2 +
              {Item.cache { id := x.1, state := CacheState.invalid, ch1 := Req.noReq, ch2 := x.2.1, ch3 := x.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × Cmd × ℕ) =>
          ((x.1, Gnt.noGnt, Ack.invAck,
              {Item.dir { cmd := x.2.1, ptr := x.2.2, exGntd := true, shr := {x.1}, inv := ∅ }}),
            x.2.1, x.2.2, x.1, Req.noReq, ∅),
        Unification.Unifier.bind fun (x : Items × ℕ × Cmd × ℕ) =>
          ((x.2.1, Gnt.noGnt, Ack.invAck,
              x.1 + {Item.dir { cmd := x.2.2.1, ptr := x.2.2.2, exGntd := true, shr := {x.2.1}, inv := ∅ }}),
            x.2.2.1, x.2.2.2, x.2.1, Req.noReq, x.1)] := by
  sorry

theorem sendReqES_inv.obligation_1 :
    Unification.complete (Narrowing.mayFire sendReqES freeP)
      [Unification.Unifier.bind fun (x : ℕ × Gnt × Ack × Cmd × ℕ × Oids × Oids) =>
          ((x.1, x.2.1, x.2.2.1,
              {Item.dir
                  { cmd := x.2.2.2.1, ptr := x.2.2.2.2.1, exGntd := false, shr := x.2.2.2.2.2.1,
                    inv := x.2.2.2.2.2.2 }}),
            x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2,
            {Item.cache { id := x.1, state := CacheState.shared, ch1 := Req.noReq, ch2 := x.2.1, ch3 := x.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × Gnt × Ack × Cmd × ℕ × Oids × Oids × Items) =>
          ((x.1, x.2.1, x.2.2.1,
              x.2.2.2.2.2.2.2 +
                {Item.dir
                    { cmd := x.2.2.2.1, ptr := x.2.2.2.2.1, exGntd := false, shr := x.2.2.2.2.2.1,
                      inv := x.2.2.2.2.2.2.1 }}),
            x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
            x.2.2.2.2.2.2.2 +
              {Item.cache
                  { id := x.1, state := CacheState.shared, ch1 := Req.noReq, ch2 := x.2.1, ch3 := x.2.2.1 }})] := by
  maude_certify_comp

theorem sendReqES_inv.obligation_2 :
    Unification.sound (Narrowing.mayFire sendReqES freeP)
      [Unification.Unifier.bind fun (x : ℕ × Gnt × Ack × Cmd × ℕ × Oids × Oids) =>
          ((x.1, x.2.1, x.2.2.1,
              {Item.dir
                  { cmd := x.2.2.2.1, ptr := x.2.2.2.2.1, exGntd := false, shr := x.2.2.2.2.2.1,
                    inv := x.2.2.2.2.2.2 }}),
            x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2,
            {Item.cache { id := x.1, state := CacheState.shared, ch1 := Req.noReq, ch2 := x.2.1, ch3 := x.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × Gnt × Ack × Cmd × ℕ × Oids × Oids × Items) =>
          ((x.1, x.2.1, x.2.2.1,
              x.2.2.2.2.2.2.2 +
                {Item.dir
                    { cmd := x.2.2.2.1, ptr := x.2.2.2.2.1, exGntd := false, shr := x.2.2.2.2.2.1,
                      inv := x.2.2.2.2.2.2.1 }}),
            x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
            x.2.2.2.2.2.2.2 +
              {Item.cache
                  { id := x.1, state := CacheState.shared, ch1 := Req.noReq, ch2 := x.2.1, ch3 := x.2.2.1 }})] := by
  sorry

theorem sendReqES_inv.obligation_3 :
    Unification.complete (Narrowing.mayFire sendReqES ownE)
      [Unification.Unifier.bind fun (x : ℕ × Gnt × Ack × ℕ × Req × Cmd × ℕ × Oids) =>
          ((x.1, x.2.1, x.2.2.1,
              {Item.cache
                    { id := x.2.2.2.1, state := CacheState.exclusive, ch1 := x.2.2.2.2.1, ch2 := Gnt.noGnt,
                      ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.1},
                      inv := x.2.2.2.2.2.2.2 }}),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2, x.2.2.2.1, x.2.2.2.2.1,
            {Item.cache { id := x.1, state := CacheState.shared, ch1 := Req.noReq, ch2 := x.2.1, ch3 := x.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × Gnt × Ack × ℕ × Req × Cmd × ℕ × Oids × Items) =>
          ((x.1, x.2.1, x.2.2.1,
              x.2.2.2.2.2.2.2.2 +
                  {Item.cache
                      { id := x.2.2.2.1, state := CacheState.exclusive, ch1 := x.2.2.2.2.1, ch2 := Gnt.noGnt,
                        ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.1},
                      inv := x.2.2.2.2.2.2.2.1 }}),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
            x.2.2.2.2.2.2.2.2 +
              {Item.cache
                  { id := x.1, state := CacheState.shared, ch1 := Req.noReq, ch2 := x.2.1, ch3 := x.2.2.1 }})] := by
  maude_certify_comp

theorem sendReqES_inv.obligation_4 :
    Unification.sound (Narrowing.mayFire sendReqES ownE)
      [Unification.Unifier.bind fun (x : ℕ × Gnt × Ack × ℕ × Req × Cmd × ℕ × Oids) =>
          ((x.1, x.2.1, x.2.2.1,
              {Item.cache
                    { id := x.2.2.2.1, state := CacheState.exclusive, ch1 := x.2.2.2.2.1, ch2 := Gnt.noGnt,
                      ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.1},
                      inv := x.2.2.2.2.2.2.2 }}),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2, x.2.2.2.1, x.2.2.2.2.1,
            {Item.cache { id := x.1, state := CacheState.shared, ch1 := Req.noReq, ch2 := x.2.1, ch3 := x.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × Gnt × Ack × ℕ × Req × Cmd × ℕ × Oids × Items) =>
          ((x.1, x.2.1, x.2.2.1,
              x.2.2.2.2.2.2.2.2 +
                  {Item.cache
                      { id := x.2.2.2.1, state := CacheState.exclusive, ch1 := x.2.2.2.2.1, ch2 := Gnt.noGnt,
                        ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.1},
                      inv := x.2.2.2.2.2.2.2.1 }}),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
            x.2.2.2.2.2.2.2.2 +
              {Item.cache
                  { id := x.1, state := CacheState.shared, ch1 := Req.noReq, ch2 := x.2.1, ch3 := x.2.2.1 }})] := by
  sorry

theorem sendReqES_inv.obligation_5 :
    Unification.complete (Narrowing.mayFire sendReqES ownG)
      [Unification.Unifier.bind fun (x : ℕ × Gnt × Ack × ℕ × Req × Cmd × ℕ × Oids) =>
          ((x.1, x.2.1, x.2.2.1,
              {Item.cache
                    { id := x.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.1, ch2 := Gnt.gntE,
                      ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.1},
                      inv := x.2.2.2.2.2.2.2 }}),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2, x.2.2.2.1, x.2.2.2.2.1,
            {Item.cache { id := x.1, state := CacheState.shared, ch1 := Req.noReq, ch2 := x.2.1, ch3 := x.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × Gnt × Ack × ℕ × Req × Cmd × ℕ × Oids × Items) =>
          ((x.1, x.2.1, x.2.2.1,
              x.2.2.2.2.2.2.2.2 +
                  {Item.cache
                      { id := x.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.1, ch2 := Gnt.gntE,
                        ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.1},
                      inv := x.2.2.2.2.2.2.2.1 }}),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
            x.2.2.2.2.2.2.2.2 +
              {Item.cache
                  { id := x.1, state := CacheState.shared, ch1 := Req.noReq, ch2 := x.2.1, ch3 := x.2.2.1 }})] := by
  maude_certify_comp

theorem sendReqES_inv.obligation_6 :
    Unification.sound (Narrowing.mayFire sendReqES ownG)
      [Unification.Unifier.bind fun (x : ℕ × Gnt × Ack × ℕ × Req × Cmd × ℕ × Oids) =>
          ((x.1, x.2.1, x.2.2.1,
              {Item.cache
                    { id := x.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.1, ch2 := Gnt.gntE,
                      ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.1},
                      inv := x.2.2.2.2.2.2.2 }}),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2, x.2.2.2.1, x.2.2.2.2.1,
            {Item.cache { id := x.1, state := CacheState.shared, ch1 := Req.noReq, ch2 := x.2.1, ch3 := x.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × Gnt × Ack × ℕ × Req × Cmd × ℕ × Oids × Items) =>
          ((x.1, x.2.1, x.2.2.1,
              x.2.2.2.2.2.2.2.2 +
                  {Item.cache
                      { id := x.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.1, ch2 := Gnt.gntE,
                        ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.1},
                      inv := x.2.2.2.2.2.2.2.1 }}),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
            x.2.2.2.2.2.2.2.2 +
              {Item.cache
                  { id := x.1, state := CacheState.shared, ch1 := Req.noReq, ch2 := x.2.1, ch3 := x.2.2.1 }})] := by
  sorry

theorem sendReqES_inv.obligation_7 :
    Unification.complete (Narrowing.mayFire sendReqES ownInv)
      [Unification.Unifier.bind fun (x : ℕ × Gnt × Ack × ℕ × Req × Cmd × ℕ) =>
          ((x.1, x.2.1, x.2.2.1,
              {Item.cache
                    { id := x.2.2.2.1, state := CacheState.exclusive, ch1 := x.2.2.2.2.1, ch2 := Gnt.inv,
                      ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2, exGntd := true, shr := {x.2.2.2.1}, inv := ∅ }}),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2, x.2.2.2.1, x.2.2.2.2.1,
            {Item.cache { id := x.1, state := CacheState.shared, ch1 := Req.noReq, ch2 := x.2.1, ch3 := x.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × Gnt × Ack × ℕ × Req × Cmd × ℕ × Items) =>
          ((x.1, x.2.1, x.2.2.1,
              x.2.2.2.2.2.2.2 +
                  {Item.cache
                      { id := x.2.2.2.1, state := CacheState.exclusive, ch1 := x.2.2.2.2.1, ch2 := Gnt.inv,
                        ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.1}, inv := ∅ }}),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
            x.2.2.2.2.2.2.2 +
              {Item.cache
                  { id := x.1, state := CacheState.shared, ch1 := Req.noReq, ch2 := x.2.1, ch3 := x.2.2.1 }})] := by
  maude_certify_comp

theorem sendReqES_inv.obligation_8 :
    Unification.sound (Narrowing.mayFire sendReqES ownInv)
      [Unification.Unifier.bind fun (x : ℕ × Gnt × Ack × ℕ × Req × Cmd × ℕ) =>
          ((x.1, x.2.1, x.2.2.1,
              {Item.cache
                    { id := x.2.2.2.1, state := CacheState.exclusive, ch1 := x.2.2.2.2.1, ch2 := Gnt.inv,
                      ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2, exGntd := true, shr := {x.2.2.2.1}, inv := ∅ }}),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2, x.2.2.2.1, x.2.2.2.2.1,
            {Item.cache { id := x.1, state := CacheState.shared, ch1 := Req.noReq, ch2 := x.2.1, ch3 := x.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × Gnt × Ack × ℕ × Req × Cmd × ℕ × Items) =>
          ((x.1, x.2.1, x.2.2.1,
              x.2.2.2.2.2.2.2 +
                  {Item.cache
                      { id := x.2.2.2.1, state := CacheState.exclusive, ch1 := x.2.2.2.2.1, ch2 := Gnt.inv,
                        ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.1}, inv := ∅ }}),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
            x.2.2.2.2.2.2.2 +
              {Item.cache
                  { id := x.1, state := CacheState.shared, ch1 := Req.noReq, ch2 := x.2.1, ch3 := x.2.2.1 }})] := by
  sorry

theorem sendReqES_inv.obligation_9 :
    Unification.complete (Narrowing.mayFire sendReqES ownAck)
      [Unification.Unifier.bind fun (x : ℕ × Gnt × Ack × ℕ × Req × Cmd × ℕ) =>
          ((x.1, x.2.1, x.2.2.1,
              {Item.cache
                    { id := x.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.1, ch2 := Gnt.noGnt,
                      ch3 := Ack.invAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2, exGntd := true, shr := {x.2.2.2.1}, inv := ∅ }}),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2, x.2.2.2.1, x.2.2.2.2.1,
            {Item.cache { id := x.1, state := CacheState.shared, ch1 := Req.noReq, ch2 := x.2.1, ch3 := x.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × Gnt × Ack × ℕ × Req × Cmd × ℕ × Items) =>
          ((x.1, x.2.1, x.2.2.1,
              x.2.2.2.2.2.2.2 +
                  {Item.cache
                      { id := x.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.1, ch2 := Gnt.noGnt,
                        ch3 := Ack.invAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.1}, inv := ∅ }}),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
            x.2.2.2.2.2.2.2 +
              {Item.cache
                  { id := x.1, state := CacheState.shared, ch1 := Req.noReq, ch2 := x.2.1, ch3 := x.2.2.1 }})] := by
  maude_certify_comp

theorem sendReqES_inv.obligation_10 :
    Unification.sound (Narrowing.mayFire sendReqES ownAck)
      [Unification.Unifier.bind fun (x : ℕ × Gnt × Ack × ℕ × Req × Cmd × ℕ) =>
          ((x.1, x.2.1, x.2.2.1,
              {Item.cache
                    { id := x.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.1, ch2 := Gnt.noGnt,
                      ch3 := Ack.invAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2, exGntd := true, shr := {x.2.2.2.1}, inv := ∅ }}),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2, x.2.2.2.1, x.2.2.2.2.1,
            {Item.cache { id := x.1, state := CacheState.shared, ch1 := Req.noReq, ch2 := x.2.1, ch3 := x.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × Gnt × Ack × ℕ × Req × Cmd × ℕ × Items) =>
          ((x.1, x.2.1, x.2.2.1,
              x.2.2.2.2.2.2.2 +
                  {Item.cache
                      { id := x.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.1, ch2 := Gnt.noGnt,
                        ch3 := Ack.invAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.1}, inv := ∅ }}),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
            x.2.2.2.2.2.2.2 +
              {Item.cache
                  { id := x.1, state := CacheState.shared, ch1 := Req.noReq, ch2 := x.2.1, ch3 := x.2.2.1 }})] := by
  sorry

theorem recvReqS_inv.obligation_1 :
    Unification.complete (Narrowing.mayFire recvReqS freeP)
      [Unification.Unifier.bind fun (x : ℕ × ℕ × Oids × Oids × CacheState × Gnt × Ack × ℕ × Bool × Oids × Oids × Cmd) =>
          ((x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.1, x.2.2.2.2.1,
              x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
              {Item.dir
                  { cmd := x.2.2.2.2.2.2.2.2.2.2.2, ptr := x.2.1, exGntd := false, shr := x.2.2.1, inv := x.2.2.2.1 }}),
            x.2.2.2.2.2.2.2.2.2.2.2, x.2.1, x.2.2.1, x.2.2.2.1,
            {Item.cache
                  { id := x.1, state := x.2.2.2.2.1, ch1 := Req.reqS, ch2 := x.2.2.2.2.2.1, ch3 := x.2.2.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.idle, ptr := x.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.1,
                    shr := x.2.2.2.2.2.2.2.2.2.1, inv := x.2.2.2.2.2.2.2.2.2.2.1 }}),
        Unification.Unifier.bind
          fun (x : ℕ × ℕ × Oids × Oids × Items × CacheState × Gnt × Ack × ℕ × Bool × Oids × Oids × Cmd) =>
          ((x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.1, x.1,
              x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1,
              x.2.2.2.2.1 +
                {Item.dir
                    { cmd := x.2.2.2.2.2.2.2.2.2.2.2.2, ptr := x.2.1, exGntd := false, shr := x.2.2.1,
                      inv := x.2.2.2.1 }}),
            x.2.2.2.2.2.2.2.2.2.2.2.2, x.2.1, x.2.2.1, x.2.2.2.1,
            x.2.2.2.2.1 +
                {Item.cache
                    { id := x.1, state := x.2.2.2.2.2.1, ch1 := Req.reqS, ch2 := x.2.2.2.2.2.2.1,
                      ch3 := x.2.2.2.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.idle, ptr := x.2.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.2.1,
                    shr := x.2.2.2.2.2.2.2.2.2.2.1, inv := x.2.2.2.2.2.2.2.2.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × CacheState × Gnt × Ack × ℕ × Oids × Oids) =>
          ((x.2.2.2.2.1, false, x.2.2.2.2.2.1, x.2.2.2.2.2.2, x.1, x.2.1, x.2.2.1, x.2.2.2.1, ∅), Cmd.idle, x.2.2.2.2.1,
            x.2.2.2.2.2.1, x.2.2.2.2.2.2,
            {Item.cache { id := x.1, state := x.2.1, ch1 := Req.reqS, ch2 := x.2.2.1, ch3 := x.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : Items × ℕ × CacheState × Gnt × Ack × ℕ × Oids × Oids) =>
          ((x.2.2.2.2.2.1, false, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.1),
            Cmd.idle, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2,
            x.1 +
              {Item.cache
                  { id := x.2.1, state := x.2.2.1, ch1 := Req.reqS, ch2 := x.2.2.2.1, ch3 := x.2.2.2.2.1 }})] := by
  maude_certify_comp

theorem recvReqS_inv.obligation_2 :
    Unification.sound (Narrowing.mayFire recvReqS freeP)
      [Unification.Unifier.bind fun (x : ℕ × ℕ × Oids × Oids × CacheState × Gnt × Ack × ℕ × Bool × Oids × Oids × Cmd) =>
          ((x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.1, x.2.2.2.2.1,
              x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
              {Item.dir
                  { cmd := x.2.2.2.2.2.2.2.2.2.2.2, ptr := x.2.1, exGntd := false, shr := x.2.2.1, inv := x.2.2.2.1 }}),
            x.2.2.2.2.2.2.2.2.2.2.2, x.2.1, x.2.2.1, x.2.2.2.1,
            {Item.cache
                  { id := x.1, state := x.2.2.2.2.1, ch1 := Req.reqS, ch2 := x.2.2.2.2.2.1, ch3 := x.2.2.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.idle, ptr := x.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.1,
                    shr := x.2.2.2.2.2.2.2.2.2.1, inv := x.2.2.2.2.2.2.2.2.2.2.1 }}),
        Unification.Unifier.bind
          fun (x : ℕ × ℕ × Oids × Oids × Items × CacheState × Gnt × Ack × ℕ × Bool × Oids × Oids × Cmd) =>
          ((x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.1, x.1,
              x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1,
              x.2.2.2.2.1 +
                {Item.dir
                    { cmd := x.2.2.2.2.2.2.2.2.2.2.2.2, ptr := x.2.1, exGntd := false, shr := x.2.2.1,
                      inv := x.2.2.2.1 }}),
            x.2.2.2.2.2.2.2.2.2.2.2.2, x.2.1, x.2.2.1, x.2.2.2.1,
            x.2.2.2.2.1 +
                {Item.cache
                    { id := x.1, state := x.2.2.2.2.2.1, ch1 := Req.reqS, ch2 := x.2.2.2.2.2.2.1,
                      ch3 := x.2.2.2.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.idle, ptr := x.2.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.2.1,
                    shr := x.2.2.2.2.2.2.2.2.2.2.1, inv := x.2.2.2.2.2.2.2.2.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × CacheState × Gnt × Ack × ℕ × Oids × Oids) =>
          ((x.2.2.2.2.1, false, x.2.2.2.2.2.1, x.2.2.2.2.2.2, x.1, x.2.1, x.2.2.1, x.2.2.2.1, ∅), Cmd.idle, x.2.2.2.2.1,
            x.2.2.2.2.2.1, x.2.2.2.2.2.2,
            {Item.cache { id := x.1, state := x.2.1, ch1 := Req.reqS, ch2 := x.2.2.1, ch3 := x.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : Items × ℕ × CacheState × Gnt × Ack × ℕ × Oids × Oids) =>
          ((x.2.2.2.2.2.1, false, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.1),
            Cmd.idle, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2,
            x.1 +
              {Item.cache
                  { id := x.2.1, state := x.2.2.1, ch1 := Req.reqS, ch2 := x.2.2.2.1, ch3 := x.2.2.2.2.1 }})] := by
  sorry

theorem recvReqS_inv.obligation_3 :
    Unification.complete (Narrowing.mayFire recvReqS ownE)
      [Unification.Unifier.bind
          fun (x : ℕ × Req × Cmd × ℕ × Oids × CacheState × Gnt × Ack × ℕ × Bool × Oids × Oids × ℕ) =>
          ((x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.1, x.1,
              x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1,
              {Item.cache
                    { id := x.2.2.2.2.2.2.2.2.2.2.2.2, state := CacheState.exclusive, ch1 := x.2.1, ch2 := Gnt.noGnt,
                      ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.1, ptr := x.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.2.2.2.2},
                      inv := x.2.2.2.2.1 }}),
            x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2, x.2.1,
            {Item.cache
                  { id := x.1, state := x.2.2.2.2.2.1, ch1 := Req.reqS, ch2 := x.2.2.2.2.2.2.1,
                    ch3 := x.2.2.2.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.idle, ptr := x.2.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.2.1,
                    shr := x.2.2.2.2.2.2.2.2.2.2.1, inv := x.2.2.2.2.2.2.2.2.2.2.2.1 }}),
        Unification.Unifier.bind
          fun (x : ℕ × Req × Cmd × ℕ × Oids × Items × CacheState × Gnt × Ack × ℕ × Bool × Oids × Oids × ℕ) =>
          ((x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2.1, x.1,
              x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.1 +
                  {Item.cache
                      { id := x.2.2.2.2.2.2.2.2.2.2.2.2.2, state := CacheState.exclusive, ch1 := x.2.1,
                        ch2 := Gnt.noGnt, ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.1, ptr := x.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.2.2.2.2.2},
                      inv := x.2.2.2.2.1 }}),
            x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2.2, x.2.1,
            x.2.2.2.2.2.1 +
                {Item.cache
                    { id := x.1, state := x.2.2.2.2.2.2.1, ch1 := Req.reqS, ch2 := x.2.2.2.2.2.2.2.1,
                      ch3 := x.2.2.2.2.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.idle, ptr := x.2.2.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.2.2.1,
                    shr := x.2.2.2.2.2.2.2.2.2.2.2.1, inv := x.2.2.2.2.2.2.2.2.2.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × Bool × Oids × Oids × ℕ × Cmd × ℕ × Oids) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, CacheState.exclusive, Gnt.noGnt, Ack.noAck,
              {Item.dir
                  { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.1},
                    inv := x.2.2.2.2.2.2.2 }}),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2, x.2.2.2.2.1, Req.reqS,
            {Item.dir { cmd := Cmd.idle, ptr := x.1, exGntd := x.2.1, shr := x.2.2.1, inv := x.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × Bool × Oids × Oids × ℕ × Cmd × ℕ × Oids × Items) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, CacheState.exclusive, Gnt.noGnt, Ack.noAck,
              x.2.2.2.2.2.2.2.2 +
                {Item.dir
                    { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.1},
                      inv := x.2.2.2.2.2.2.2.1 }}),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.1, Req.reqS,
            x.2.2.2.2.2.2.2.2 +
              {Item.dir { cmd := Cmd.idle, ptr := x.1, exGntd := x.2.1, shr := x.2.2.1, inv := x.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × CacheState × Gnt × Ack × ℕ × Req × ℕ × Oids) =>
          ((x.2.2.2.2.2.2.1, true, {x.2.2.2.2.1}, x.2.2.2.2.2.2.2, x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {Item.cache
                  { id := x.2.2.2.2.1, state := CacheState.exclusive, ch1 := x.2.2.2.2.2.1, ch2 := Gnt.noGnt,
                    ch3 := Ack.noAck }}),
            Cmd.idle, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2, x.2.2.2.2.1, x.2.2.2.2.2.1,
            {Item.cache { id := x.1, state := x.2.1, ch1 := Req.reqS, ch2 := x.2.2.1, ch3 := x.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × CacheState × Gnt × Ack × ℕ × Req × ℕ × Oids × Items) =>
          ((x.2.2.2.2.2.2.1, true, {x.2.2.2.2.1}, x.2.2.2.2.2.2.2.1, x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              x.2.2.2.2.2.2.2.2 +
                {Item.cache
                    { id := x.2.2.2.2.1, state := CacheState.exclusive, ch1 := x.2.2.2.2.2.1, ch2 := Gnt.noGnt,
                      ch3 := Ack.noAck }}),
            Cmd.idle, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
            x.2.2.2.2.2.2.2.2 +
              {Item.cache { id := x.1, state := x.2.1, ch1 := Req.reqS, ch2 := x.2.2.1, ch3 := x.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × ℕ × Oids) =>
          ((x.2.1, true, {x.1}, x.2.2, x.1, CacheState.exclusive, Gnt.noGnt, Ack.noAck, ∅), Cmd.idle, x.2.1, x.2.2, x.1,
            Req.reqS, ∅),
        Unification.Unifier.bind fun (x : Items × ℕ × ℕ × Oids) =>
          ((x.2.2.1, true, {x.2.1}, x.2.2.2, x.2.1, CacheState.exclusive, Gnt.noGnt, Ack.noAck, x.1), Cmd.idle, x.2.2.1,
            x.2.2.2, x.2.1, Req.reqS, x.1)] := by
  maude_certify_comp

theorem recvReqS_inv.obligation_4 :
    Unification.sound (Narrowing.mayFire recvReqS ownE)
      [Unification.Unifier.bind
          fun (x : ℕ × Req × Cmd × ℕ × Oids × CacheState × Gnt × Ack × ℕ × Bool × Oids × Oids × ℕ) =>
          ((x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.1, x.1,
              x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1,
              {Item.cache
                    { id := x.2.2.2.2.2.2.2.2.2.2.2.2, state := CacheState.exclusive, ch1 := x.2.1, ch2 := Gnt.noGnt,
                      ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.1, ptr := x.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.2.2.2.2},
                      inv := x.2.2.2.2.1 }}),
            x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2, x.2.1,
            {Item.cache
                  { id := x.1, state := x.2.2.2.2.2.1, ch1 := Req.reqS, ch2 := x.2.2.2.2.2.2.1,
                    ch3 := x.2.2.2.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.idle, ptr := x.2.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.2.1,
                    shr := x.2.2.2.2.2.2.2.2.2.2.1, inv := x.2.2.2.2.2.2.2.2.2.2.2.1 }}),
        Unification.Unifier.bind
          fun (x : ℕ × Req × Cmd × ℕ × Oids × Items × CacheState × Gnt × Ack × ℕ × Bool × Oids × Oids × ℕ) =>
          ((x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2.1, x.1,
              x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.1 +
                  {Item.cache
                      { id := x.2.2.2.2.2.2.2.2.2.2.2.2.2, state := CacheState.exclusive, ch1 := x.2.1,
                        ch2 := Gnt.noGnt, ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.1, ptr := x.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.2.2.2.2.2},
                      inv := x.2.2.2.2.1 }}),
            x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2.2, x.2.1,
            x.2.2.2.2.2.1 +
                {Item.cache
                    { id := x.1, state := x.2.2.2.2.2.2.1, ch1 := Req.reqS, ch2 := x.2.2.2.2.2.2.2.1,
                      ch3 := x.2.2.2.2.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.idle, ptr := x.2.2.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.2.2.1,
                    shr := x.2.2.2.2.2.2.2.2.2.2.2.1, inv := x.2.2.2.2.2.2.2.2.2.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × Bool × Oids × Oids × ℕ × Cmd × ℕ × Oids) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, CacheState.exclusive, Gnt.noGnt, Ack.noAck,
              {Item.dir
                  { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.1},
                    inv := x.2.2.2.2.2.2.2 }}),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2, x.2.2.2.2.1, Req.reqS,
            {Item.dir { cmd := Cmd.idle, ptr := x.1, exGntd := x.2.1, shr := x.2.2.1, inv := x.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × Bool × Oids × Oids × ℕ × Cmd × ℕ × Oids × Items) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, CacheState.exclusive, Gnt.noGnt, Ack.noAck,
              x.2.2.2.2.2.2.2.2 +
                {Item.dir
                    { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.1},
                      inv := x.2.2.2.2.2.2.2.1 }}),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.1, Req.reqS,
            x.2.2.2.2.2.2.2.2 +
              {Item.dir { cmd := Cmd.idle, ptr := x.1, exGntd := x.2.1, shr := x.2.2.1, inv := x.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × CacheState × Gnt × Ack × ℕ × Req × ℕ × Oids) =>
          ((x.2.2.2.2.2.2.1, true, {x.2.2.2.2.1}, x.2.2.2.2.2.2.2, x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {Item.cache
                  { id := x.2.2.2.2.1, state := CacheState.exclusive, ch1 := x.2.2.2.2.2.1, ch2 := Gnt.noGnt,
                    ch3 := Ack.noAck }}),
            Cmd.idle, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2, x.2.2.2.2.1, x.2.2.2.2.2.1,
            {Item.cache { id := x.1, state := x.2.1, ch1 := Req.reqS, ch2 := x.2.2.1, ch3 := x.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × CacheState × Gnt × Ack × ℕ × Req × ℕ × Oids × Items) =>
          ((x.2.2.2.2.2.2.1, true, {x.2.2.2.2.1}, x.2.2.2.2.2.2.2.1, x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              x.2.2.2.2.2.2.2.2 +
                {Item.cache
                    { id := x.2.2.2.2.1, state := CacheState.exclusive, ch1 := x.2.2.2.2.2.1, ch2 := Gnt.noGnt,
                      ch3 := Ack.noAck }}),
            Cmd.idle, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
            x.2.2.2.2.2.2.2.2 +
              {Item.cache { id := x.1, state := x.2.1, ch1 := Req.reqS, ch2 := x.2.2.1, ch3 := x.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × ℕ × Oids) =>
          ((x.2.1, true, {x.1}, x.2.2, x.1, CacheState.exclusive, Gnt.noGnt, Ack.noAck, ∅), Cmd.idle, x.2.1, x.2.2, x.1,
            Req.reqS, ∅),
        Unification.Unifier.bind fun (x : Items × ℕ × ℕ × Oids) =>
          ((x.2.2.1, true, {x.2.1}, x.2.2.2, x.2.1, CacheState.exclusive, Gnt.noGnt, Ack.noAck, x.1), Cmd.idle, x.2.2.1,
            x.2.2.2, x.2.1, Req.reqS, x.1)] := by
  sorry

theorem recvReqS_inv.obligation_5 :
    Unification.complete (Narrowing.mayFire recvReqS ownG)
      [Unification.Unifier.bind
          fun (x : ℕ × Req × Cmd × ℕ × Oids × CacheState × Gnt × Ack × ℕ × Bool × Oids × Oids × ℕ) =>
          ((x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.1, x.1,
              x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1,
              {Item.cache
                    { id := x.2.2.2.2.2.2.2.2.2.2.2.2, state := CacheState.invalid, ch1 := x.2.1, ch2 := Gnt.gntE,
                      ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.1, ptr := x.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.2.2.2.2},
                      inv := x.2.2.2.2.1 }}),
            x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2, x.2.1,
            {Item.cache
                  { id := x.1, state := x.2.2.2.2.2.1, ch1 := Req.reqS, ch2 := x.2.2.2.2.2.2.1,
                    ch3 := x.2.2.2.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.idle, ptr := x.2.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.2.1,
                    shr := x.2.2.2.2.2.2.2.2.2.2.1, inv := x.2.2.2.2.2.2.2.2.2.2.2.1 }}),
        Unification.Unifier.bind
          fun (x : ℕ × Req × Cmd × ℕ × Oids × Items × CacheState × Gnt × Ack × ℕ × Bool × Oids × Oids × ℕ) =>
          ((x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2.1, x.1,
              x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.1 +
                  {Item.cache
                      { id := x.2.2.2.2.2.2.2.2.2.2.2.2.2, state := CacheState.invalid, ch1 := x.2.1, ch2 := Gnt.gntE,
                        ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.1, ptr := x.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.2.2.2.2.2},
                      inv := x.2.2.2.2.1 }}),
            x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2.2, x.2.1,
            x.2.2.2.2.2.1 +
                {Item.cache
                    { id := x.1, state := x.2.2.2.2.2.2.1, ch1 := Req.reqS, ch2 := x.2.2.2.2.2.2.2.1,
                      ch3 := x.2.2.2.2.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.idle, ptr := x.2.2.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.2.2.1,
                    shr := x.2.2.2.2.2.2.2.2.2.2.2.1, inv := x.2.2.2.2.2.2.2.2.2.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × Bool × Oids × Oids × ℕ × Cmd × ℕ × Oids) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, CacheState.invalid, Gnt.gntE, Ack.noAck,
              {Item.dir
                  { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.1},
                    inv := x.2.2.2.2.2.2.2 }}),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2, x.2.2.2.2.1, Req.reqS,
            {Item.dir { cmd := Cmd.idle, ptr := x.1, exGntd := x.2.1, shr := x.2.2.1, inv := x.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × Bool × Oids × Oids × ℕ × Cmd × ℕ × Oids × Items) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, CacheState.invalid, Gnt.gntE, Ack.noAck,
              x.2.2.2.2.2.2.2.2 +
                {Item.dir
                    { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.1},
                      inv := x.2.2.2.2.2.2.2.1 }}),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.1, Req.reqS,
            x.2.2.2.2.2.2.2.2 +
              {Item.dir { cmd := Cmd.idle, ptr := x.1, exGntd := x.2.1, shr := x.2.2.1, inv := x.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × CacheState × Gnt × Ack × ℕ × Req × ℕ × Oids) =>
          ((x.2.2.2.2.2.2.1, true, {x.2.2.2.2.1}, x.2.2.2.2.2.2.2, x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {Item.cache
                  { id := x.2.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.2.1, ch2 := Gnt.gntE,
                    ch3 := Ack.noAck }}),
            Cmd.idle, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2, x.2.2.2.2.1, x.2.2.2.2.2.1,
            {Item.cache { id := x.1, state := x.2.1, ch1 := Req.reqS, ch2 := x.2.2.1, ch3 := x.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × CacheState × Gnt × Ack × ℕ × Req × ℕ × Oids × Items) =>
          ((x.2.2.2.2.2.2.1, true, {x.2.2.2.2.1}, x.2.2.2.2.2.2.2.1, x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              x.2.2.2.2.2.2.2.2 +
                {Item.cache
                    { id := x.2.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.2.1, ch2 := Gnt.gntE,
                      ch3 := Ack.noAck }}),
            Cmd.idle, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
            x.2.2.2.2.2.2.2.2 +
              {Item.cache { id := x.1, state := x.2.1, ch1 := Req.reqS, ch2 := x.2.2.1, ch3 := x.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × ℕ × Oids) =>
          ((x.2.1, true, {x.1}, x.2.2, x.1, CacheState.invalid, Gnt.gntE, Ack.noAck, ∅), Cmd.idle, x.2.1, x.2.2, x.1,
            Req.reqS, ∅),
        Unification.Unifier.bind fun (x : Items × ℕ × ℕ × Oids) =>
          ((x.2.2.1, true, {x.2.1}, x.2.2.2, x.2.1, CacheState.invalid, Gnt.gntE, Ack.noAck, x.1), Cmd.idle, x.2.2.1,
            x.2.2.2, x.2.1, Req.reqS, x.1)] := by
  maude_certify_comp

theorem recvReqS_inv.obligation_6 :
    Unification.sound (Narrowing.mayFire recvReqS ownG)
      [Unification.Unifier.bind
          fun (x : ℕ × Req × Cmd × ℕ × Oids × CacheState × Gnt × Ack × ℕ × Bool × Oids × Oids × ℕ) =>
          ((x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.1, x.1,
              x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1,
              {Item.cache
                    { id := x.2.2.2.2.2.2.2.2.2.2.2.2, state := CacheState.invalid, ch1 := x.2.1, ch2 := Gnt.gntE,
                      ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.1, ptr := x.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.2.2.2.2},
                      inv := x.2.2.2.2.1 }}),
            x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2, x.2.1,
            {Item.cache
                  { id := x.1, state := x.2.2.2.2.2.1, ch1 := Req.reqS, ch2 := x.2.2.2.2.2.2.1,
                    ch3 := x.2.2.2.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.idle, ptr := x.2.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.2.1,
                    shr := x.2.2.2.2.2.2.2.2.2.2.1, inv := x.2.2.2.2.2.2.2.2.2.2.2.1 }}),
        Unification.Unifier.bind
          fun (x : ℕ × Req × Cmd × ℕ × Oids × Items × CacheState × Gnt × Ack × ℕ × Bool × Oids × Oids × ℕ) =>
          ((x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2.1, x.1,
              x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.1 +
                  {Item.cache
                      { id := x.2.2.2.2.2.2.2.2.2.2.2.2.2, state := CacheState.invalid, ch1 := x.2.1, ch2 := Gnt.gntE,
                        ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.1, ptr := x.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.2.2.2.2.2},
                      inv := x.2.2.2.2.1 }}),
            x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2.2, x.2.1,
            x.2.2.2.2.2.1 +
                {Item.cache
                    { id := x.1, state := x.2.2.2.2.2.2.1, ch1 := Req.reqS, ch2 := x.2.2.2.2.2.2.2.1,
                      ch3 := x.2.2.2.2.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.idle, ptr := x.2.2.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.2.2.1,
                    shr := x.2.2.2.2.2.2.2.2.2.2.2.1, inv := x.2.2.2.2.2.2.2.2.2.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × Bool × Oids × Oids × ℕ × Cmd × ℕ × Oids) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, CacheState.invalid, Gnt.gntE, Ack.noAck,
              {Item.dir
                  { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.1},
                    inv := x.2.2.2.2.2.2.2 }}),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2, x.2.2.2.2.1, Req.reqS,
            {Item.dir { cmd := Cmd.idle, ptr := x.1, exGntd := x.2.1, shr := x.2.2.1, inv := x.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × Bool × Oids × Oids × ℕ × Cmd × ℕ × Oids × Items) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, CacheState.invalid, Gnt.gntE, Ack.noAck,
              x.2.2.2.2.2.2.2.2 +
                {Item.dir
                    { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.1},
                      inv := x.2.2.2.2.2.2.2.1 }}),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.1, Req.reqS,
            x.2.2.2.2.2.2.2.2 +
              {Item.dir { cmd := Cmd.idle, ptr := x.1, exGntd := x.2.1, shr := x.2.2.1, inv := x.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × CacheState × Gnt × Ack × ℕ × Req × ℕ × Oids) =>
          ((x.2.2.2.2.2.2.1, true, {x.2.2.2.2.1}, x.2.2.2.2.2.2.2, x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {Item.cache
                  { id := x.2.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.2.1, ch2 := Gnt.gntE,
                    ch3 := Ack.noAck }}),
            Cmd.idle, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2, x.2.2.2.2.1, x.2.2.2.2.2.1,
            {Item.cache { id := x.1, state := x.2.1, ch1 := Req.reqS, ch2 := x.2.2.1, ch3 := x.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × CacheState × Gnt × Ack × ℕ × Req × ℕ × Oids × Items) =>
          ((x.2.2.2.2.2.2.1, true, {x.2.2.2.2.1}, x.2.2.2.2.2.2.2.1, x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              x.2.2.2.2.2.2.2.2 +
                {Item.cache
                    { id := x.2.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.2.1, ch2 := Gnt.gntE,
                      ch3 := Ack.noAck }}),
            Cmd.idle, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
            x.2.2.2.2.2.2.2.2 +
              {Item.cache { id := x.1, state := x.2.1, ch1 := Req.reqS, ch2 := x.2.2.1, ch3 := x.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × ℕ × Oids) =>
          ((x.2.1, true, {x.1}, x.2.2, x.1, CacheState.invalid, Gnt.gntE, Ack.noAck, ∅), Cmd.idle, x.2.1, x.2.2, x.1,
            Req.reqS, ∅),
        Unification.Unifier.bind fun (x : Items × ℕ × ℕ × Oids) =>
          ((x.2.2.1, true, {x.2.1}, x.2.2.2, x.2.1, CacheState.invalid, Gnt.gntE, Ack.noAck, x.1), Cmd.idle, x.2.2.1,
            x.2.2.2, x.2.1, Req.reqS, x.1)] := by
  sorry

theorem recvReqS_inv.obligation_7 :
    Unification.complete (Narrowing.mayFire recvReqS ownInv)
      [Unification.Unifier.bind fun (x : ℕ × Req × Cmd × ℕ × CacheState × Gnt × Ack × ℕ × Bool × Oids × Oids × ℕ) =>
          ((x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.1, x.2.2.2.2.1,
              x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
              {Item.cache
                    { id := x.2.2.2.2.2.2.2.2.2.2.2, state := CacheState.exclusive, ch1 := x.2.1, ch2 := Gnt.inv,
                      ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.1, ptr := x.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.2.2.2}, inv := ∅ }}),
            x.2.2.1, x.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2, x.2.1,
            {Item.cache
                  { id := x.1, state := x.2.2.2.2.1, ch1 := Req.reqS, ch2 := x.2.2.2.2.2.1, ch3 := x.2.2.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.idle, ptr := x.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.1,
                    shr := x.2.2.2.2.2.2.2.2.2.1, inv := x.2.2.2.2.2.2.2.2.2.2.1 }}),
        Unification.Unifier.bind
          fun (x : ℕ × Req × Cmd × ℕ × Items × CacheState × Gnt × Ack × ℕ × Bool × Oids × Oids × ℕ) =>
          ((x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.1, x.1,
              x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1,
              x.2.2.2.2.1 +
                  {Item.cache
                      { id := x.2.2.2.2.2.2.2.2.2.2.2.2, state := CacheState.exclusive, ch1 := x.2.1, ch2 := Gnt.inv,
                        ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.1, ptr := x.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.2.2.2.2},
                      inv := ∅ }}),
            x.2.2.1, x.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2, x.2.1,
            x.2.2.2.2.1 +
                {Item.cache
                    { id := x.1, state := x.2.2.2.2.2.1, ch1 := Req.reqS, ch2 := x.2.2.2.2.2.2.1,
                      ch3 := x.2.2.2.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.idle, ptr := x.2.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.2.1,
                    shr := x.2.2.2.2.2.2.2.2.2.2.1, inv := x.2.2.2.2.2.2.2.2.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × Bool × Oids × Oids × ℕ × Cmd × ℕ) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, CacheState.exclusive, Gnt.inv, Ack.noAck,
              {Item.dir
                  { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2, exGntd := true, shr := {x.2.2.2.2.1}, inv := ∅ }}),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2, x.2.2.2.2.1, Req.reqS,
            {Item.dir { cmd := Cmd.idle, ptr := x.1, exGntd := x.2.1, shr := x.2.2.1, inv := x.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × Bool × Oids × Oids × ℕ × Cmd × ℕ × Items) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, CacheState.exclusive, Gnt.inv, Ack.noAck,
              x.2.2.2.2.2.2.2 +
                {Item.dir
                    { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.1}, inv := ∅ }}),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.1, Req.reqS,
            x.2.2.2.2.2.2.2 +
              {Item.dir { cmd := Cmd.idle, ptr := x.1, exGntd := x.2.1, shr := x.2.2.1, inv := x.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × CacheState × Gnt × Ack × ℕ × Req × ℕ) =>
          ((x.2.2.2.2.2.2, true, {x.2.2.2.2.1}, ∅, x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {Item.cache
                  { id := x.2.2.2.2.1, state := CacheState.exclusive, ch1 := x.2.2.2.2.2.1, ch2 := Gnt.inv,
                    ch3 := Ack.noAck }}),
            Cmd.idle, x.2.2.2.2.2.2, x.2.2.2.2.1, x.2.2.2.2.2.1,
            {Item.cache { id := x.1, state := x.2.1, ch1 := Req.reqS, ch2 := x.2.2.1, ch3 := x.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × CacheState × Gnt × Ack × ℕ × Req × ℕ × Items) =>
          ((x.2.2.2.2.2.2.1, true, {x.2.2.2.2.1}, ∅, x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              x.2.2.2.2.2.2.2 +
                {Item.cache
                    { id := x.2.2.2.2.1, state := CacheState.exclusive, ch1 := x.2.2.2.2.2.1, ch2 := Gnt.inv,
                      ch3 := Ack.noAck }}),
            Cmd.idle, x.2.2.2.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
            x.2.2.2.2.2.2.2 +
              {Item.cache { id := x.1, state := x.2.1, ch1 := Req.reqS, ch2 := x.2.2.1, ch3 := x.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × ℕ) =>
          ((x.2, true, {x.1}, ∅, x.1, CacheState.exclusive, Gnt.inv, Ack.noAck, ∅), Cmd.idle, x.2, x.1, Req.reqS, ∅),
        Unification.Unifier.bind fun (x : Items × ℕ × ℕ) =>
          ((x.2.2, true, {x.2.1}, ∅, x.2.1, CacheState.exclusive, Gnt.inv, Ack.noAck, x.1), Cmd.idle, x.2.2, x.2.1,
            Req.reqS, x.1)] := by
  maude_certify_comp

theorem recvReqS_inv.obligation_8 :
    Unification.sound (Narrowing.mayFire recvReqS ownInv)
      [Unification.Unifier.bind fun (x : ℕ × Req × Cmd × ℕ × CacheState × Gnt × Ack × ℕ × Bool × Oids × Oids × ℕ) =>
          ((x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.1, x.2.2.2.2.1,
              x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
              {Item.cache
                    { id := x.2.2.2.2.2.2.2.2.2.2.2, state := CacheState.exclusive, ch1 := x.2.1, ch2 := Gnt.inv,
                      ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.1, ptr := x.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.2.2.2}, inv := ∅ }}),
            x.2.2.1, x.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2, x.2.1,
            {Item.cache
                  { id := x.1, state := x.2.2.2.2.1, ch1 := Req.reqS, ch2 := x.2.2.2.2.2.1, ch3 := x.2.2.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.idle, ptr := x.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.1,
                    shr := x.2.2.2.2.2.2.2.2.2.1, inv := x.2.2.2.2.2.2.2.2.2.2.1 }}),
        Unification.Unifier.bind
          fun (x : ℕ × Req × Cmd × ℕ × Items × CacheState × Gnt × Ack × ℕ × Bool × Oids × Oids × ℕ) =>
          ((x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.1, x.1,
              x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1,
              x.2.2.2.2.1 +
                  {Item.cache
                      { id := x.2.2.2.2.2.2.2.2.2.2.2.2, state := CacheState.exclusive, ch1 := x.2.1, ch2 := Gnt.inv,
                        ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.1, ptr := x.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.2.2.2.2},
                      inv := ∅ }}),
            x.2.2.1, x.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2, x.2.1,
            x.2.2.2.2.1 +
                {Item.cache
                    { id := x.1, state := x.2.2.2.2.2.1, ch1 := Req.reqS, ch2 := x.2.2.2.2.2.2.1,
                      ch3 := x.2.2.2.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.idle, ptr := x.2.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.2.1,
                    shr := x.2.2.2.2.2.2.2.2.2.2.1, inv := x.2.2.2.2.2.2.2.2.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × Bool × Oids × Oids × ℕ × Cmd × ℕ) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, CacheState.exclusive, Gnt.inv, Ack.noAck,
              {Item.dir
                  { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2, exGntd := true, shr := {x.2.2.2.2.1}, inv := ∅ }}),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2, x.2.2.2.2.1, Req.reqS,
            {Item.dir { cmd := Cmd.idle, ptr := x.1, exGntd := x.2.1, shr := x.2.2.1, inv := x.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × Bool × Oids × Oids × ℕ × Cmd × ℕ × Items) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, CacheState.exclusive, Gnt.inv, Ack.noAck,
              x.2.2.2.2.2.2.2 +
                {Item.dir
                    { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.1}, inv := ∅ }}),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.1, Req.reqS,
            x.2.2.2.2.2.2.2 +
              {Item.dir { cmd := Cmd.idle, ptr := x.1, exGntd := x.2.1, shr := x.2.2.1, inv := x.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × CacheState × Gnt × Ack × ℕ × Req × ℕ) =>
          ((x.2.2.2.2.2.2, true, {x.2.2.2.2.1}, ∅, x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {Item.cache
                  { id := x.2.2.2.2.1, state := CacheState.exclusive, ch1 := x.2.2.2.2.2.1, ch2 := Gnt.inv,
                    ch3 := Ack.noAck }}),
            Cmd.idle, x.2.2.2.2.2.2, x.2.2.2.2.1, x.2.2.2.2.2.1,
            {Item.cache { id := x.1, state := x.2.1, ch1 := Req.reqS, ch2 := x.2.2.1, ch3 := x.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × CacheState × Gnt × Ack × ℕ × Req × ℕ × Items) =>
          ((x.2.2.2.2.2.2.1, true, {x.2.2.2.2.1}, ∅, x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              x.2.2.2.2.2.2.2 +
                {Item.cache
                    { id := x.2.2.2.2.1, state := CacheState.exclusive, ch1 := x.2.2.2.2.2.1, ch2 := Gnt.inv,
                      ch3 := Ack.noAck }}),
            Cmd.idle, x.2.2.2.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
            x.2.2.2.2.2.2.2 +
              {Item.cache { id := x.1, state := x.2.1, ch1 := Req.reqS, ch2 := x.2.2.1, ch3 := x.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × ℕ) =>
          ((x.2, true, {x.1}, ∅, x.1, CacheState.exclusive, Gnt.inv, Ack.noAck, ∅), Cmd.idle, x.2, x.1, Req.reqS, ∅),
        Unification.Unifier.bind fun (x : Items × ℕ × ℕ) =>
          ((x.2.2, true, {x.2.1}, ∅, x.2.1, CacheState.exclusive, Gnt.inv, Ack.noAck, x.1), Cmd.idle, x.2.2, x.2.1,
            Req.reqS, x.1)] := by
  sorry

theorem recvReqS_inv.obligation_9 :
    Unification.complete (Narrowing.mayFire recvReqS ownAck)
      [Unification.Unifier.bind fun (x : ℕ × Req × Cmd × ℕ × CacheState × Gnt × Ack × ℕ × Bool × Oids × Oids × ℕ) =>
          ((x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.1, x.2.2.2.2.1,
              x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
              {Item.cache
                    { id := x.2.2.2.2.2.2.2.2.2.2.2, state := CacheState.invalid, ch1 := x.2.1, ch2 := Gnt.noGnt,
                      ch3 := Ack.invAck }} +
                {Item.dir
                    { cmd := x.2.2.1, ptr := x.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.2.2.2}, inv := ∅ }}),
            x.2.2.1, x.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2, x.2.1,
            {Item.cache
                  { id := x.1, state := x.2.2.2.2.1, ch1 := Req.reqS, ch2 := x.2.2.2.2.2.1, ch3 := x.2.2.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.idle, ptr := x.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.1,
                    shr := x.2.2.2.2.2.2.2.2.2.1, inv := x.2.2.2.2.2.2.2.2.2.2.1 }}),
        Unification.Unifier.bind
          fun (x : ℕ × Req × Cmd × ℕ × Items × CacheState × Gnt × Ack × ℕ × Bool × Oids × Oids × ℕ) =>
          ((x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.1, x.1,
              x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1,
              x.2.2.2.2.1 +
                  {Item.cache
                      { id := x.2.2.2.2.2.2.2.2.2.2.2.2, state := CacheState.invalid, ch1 := x.2.1, ch2 := Gnt.noGnt,
                        ch3 := Ack.invAck }} +
                {Item.dir
                    { cmd := x.2.2.1, ptr := x.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.2.2.2.2},
                      inv := ∅ }}),
            x.2.2.1, x.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2, x.2.1,
            x.2.2.2.2.1 +
                {Item.cache
                    { id := x.1, state := x.2.2.2.2.2.1, ch1 := Req.reqS, ch2 := x.2.2.2.2.2.2.1,
                      ch3 := x.2.2.2.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.idle, ptr := x.2.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.2.1,
                    shr := x.2.2.2.2.2.2.2.2.2.2.1, inv := x.2.2.2.2.2.2.2.2.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × Bool × Oids × Oids × ℕ × Cmd × ℕ) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, CacheState.invalid, Gnt.noGnt, Ack.invAck,
              {Item.dir
                  { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2, exGntd := true, shr := {x.2.2.2.2.1}, inv := ∅ }}),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2, x.2.2.2.2.1, Req.reqS,
            {Item.dir { cmd := Cmd.idle, ptr := x.1, exGntd := x.2.1, shr := x.2.2.1, inv := x.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × Bool × Oids × Oids × ℕ × Cmd × ℕ × Items) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, CacheState.invalid, Gnt.noGnt, Ack.invAck,
              x.2.2.2.2.2.2.2 +
                {Item.dir
                    { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.1}, inv := ∅ }}),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.1, Req.reqS,
            x.2.2.2.2.2.2.2 +
              {Item.dir { cmd := Cmd.idle, ptr := x.1, exGntd := x.2.1, shr := x.2.2.1, inv := x.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × CacheState × Gnt × Ack × ℕ × Req × ℕ) =>
          ((x.2.2.2.2.2.2, true, {x.2.2.2.2.1}, ∅, x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {Item.cache
                  { id := x.2.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.2.1, ch2 := Gnt.noGnt,
                    ch3 := Ack.invAck }}),
            Cmd.idle, x.2.2.2.2.2.2, x.2.2.2.2.1, x.2.2.2.2.2.1,
            {Item.cache { id := x.1, state := x.2.1, ch1 := Req.reqS, ch2 := x.2.2.1, ch3 := x.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × CacheState × Gnt × Ack × ℕ × Req × ℕ × Items) =>
          ((x.2.2.2.2.2.2.1, true, {x.2.2.2.2.1}, ∅, x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              x.2.2.2.2.2.2.2 +
                {Item.cache
                    { id := x.2.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.2.1, ch2 := Gnt.noGnt,
                      ch3 := Ack.invAck }}),
            Cmd.idle, x.2.2.2.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
            x.2.2.2.2.2.2.2 +
              {Item.cache { id := x.1, state := x.2.1, ch1 := Req.reqS, ch2 := x.2.2.1, ch3 := x.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × ℕ) =>
          ((x.2, true, {x.1}, ∅, x.1, CacheState.invalid, Gnt.noGnt, Ack.invAck, ∅), Cmd.idle, x.2, x.1, Req.reqS, ∅),
        Unification.Unifier.bind fun (x : Items × ℕ × ℕ) =>
          ((x.2.2, true, {x.2.1}, ∅, x.2.1, CacheState.invalid, Gnt.noGnt, Ack.invAck, x.1), Cmd.idle, x.2.2, x.2.1,
            Req.reqS, x.1)] := by
  maude_certify_comp

theorem recvReqS_inv.obligation_10 :
    Unification.sound (Narrowing.mayFire recvReqS ownAck)
      [Unification.Unifier.bind fun (x : ℕ × Req × Cmd × ℕ × CacheState × Gnt × Ack × ℕ × Bool × Oids × Oids × ℕ) =>
          ((x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.1, x.2.2.2.2.1,
              x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
              {Item.cache
                    { id := x.2.2.2.2.2.2.2.2.2.2.2, state := CacheState.invalid, ch1 := x.2.1, ch2 := Gnt.noGnt,
                      ch3 := Ack.invAck }} +
                {Item.dir
                    { cmd := x.2.2.1, ptr := x.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.2.2.2}, inv := ∅ }}),
            x.2.2.1, x.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2, x.2.1,
            {Item.cache
                  { id := x.1, state := x.2.2.2.2.1, ch1 := Req.reqS, ch2 := x.2.2.2.2.2.1, ch3 := x.2.2.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.idle, ptr := x.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.1,
                    shr := x.2.2.2.2.2.2.2.2.2.1, inv := x.2.2.2.2.2.2.2.2.2.2.1 }}),
        Unification.Unifier.bind
          fun (x : ℕ × Req × Cmd × ℕ × Items × CacheState × Gnt × Ack × ℕ × Bool × Oids × Oids × ℕ) =>
          ((x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.1, x.1,
              x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1,
              x.2.2.2.2.1 +
                  {Item.cache
                      { id := x.2.2.2.2.2.2.2.2.2.2.2.2, state := CacheState.invalid, ch1 := x.2.1, ch2 := Gnt.noGnt,
                        ch3 := Ack.invAck }} +
                {Item.dir
                    { cmd := x.2.2.1, ptr := x.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.2.2.2.2},
                      inv := ∅ }}),
            x.2.2.1, x.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2, x.2.1,
            x.2.2.2.2.1 +
                {Item.cache
                    { id := x.1, state := x.2.2.2.2.2.1, ch1 := Req.reqS, ch2 := x.2.2.2.2.2.2.1,
                      ch3 := x.2.2.2.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.idle, ptr := x.2.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.2.1,
                    shr := x.2.2.2.2.2.2.2.2.2.2.1, inv := x.2.2.2.2.2.2.2.2.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × Bool × Oids × Oids × ℕ × Cmd × ℕ) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, CacheState.invalid, Gnt.noGnt, Ack.invAck,
              {Item.dir
                  { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2, exGntd := true, shr := {x.2.2.2.2.1}, inv := ∅ }}),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2, x.2.2.2.2.1, Req.reqS,
            {Item.dir { cmd := Cmd.idle, ptr := x.1, exGntd := x.2.1, shr := x.2.2.1, inv := x.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × Bool × Oids × Oids × ℕ × Cmd × ℕ × Items) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, CacheState.invalid, Gnt.noGnt, Ack.invAck,
              x.2.2.2.2.2.2.2 +
                {Item.dir
                    { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.1}, inv := ∅ }}),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.1, Req.reqS,
            x.2.2.2.2.2.2.2 +
              {Item.dir { cmd := Cmd.idle, ptr := x.1, exGntd := x.2.1, shr := x.2.2.1, inv := x.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × CacheState × Gnt × Ack × ℕ × Req × ℕ) =>
          ((x.2.2.2.2.2.2, true, {x.2.2.2.2.1}, ∅, x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {Item.cache
                  { id := x.2.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.2.1, ch2 := Gnt.noGnt,
                    ch3 := Ack.invAck }}),
            Cmd.idle, x.2.2.2.2.2.2, x.2.2.2.2.1, x.2.2.2.2.2.1,
            {Item.cache { id := x.1, state := x.2.1, ch1 := Req.reqS, ch2 := x.2.2.1, ch3 := x.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × CacheState × Gnt × Ack × ℕ × Req × ℕ × Items) =>
          ((x.2.2.2.2.2.2.1, true, {x.2.2.2.2.1}, ∅, x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              x.2.2.2.2.2.2.2 +
                {Item.cache
                    { id := x.2.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.2.1, ch2 := Gnt.noGnt,
                      ch3 := Ack.invAck }}),
            Cmd.idle, x.2.2.2.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
            x.2.2.2.2.2.2.2 +
              {Item.cache { id := x.1, state := x.2.1, ch1 := Req.reqS, ch2 := x.2.2.1, ch3 := x.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × ℕ) =>
          ((x.2, true, {x.1}, ∅, x.1, CacheState.invalid, Gnt.noGnt, Ack.invAck, ∅), Cmd.idle, x.2, x.1, Req.reqS, ∅),
        Unification.Unifier.bind fun (x : Items × ℕ × ℕ) =>
          ((x.2.2, true, {x.2.1}, ∅, x.2.1, CacheState.invalid, Gnt.noGnt, Ack.invAck, x.1), Cmd.idle, x.2.2, x.2.1,
            Req.reqS, x.1)] := by
  sorry

theorem recvReqE_inv.obligation_1 :
    Unification.complete (Narrowing.mayFire recvReqE freeP)
      [Unification.Unifier.bind fun (x : ℕ × ℕ × Oids × Oids × CacheState × Gnt × Ack × ℕ × Bool × Oids × Oids × Cmd) =>
          ((x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.1, x.2.2.2.2.1,
              x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
              {Item.dir
                  { cmd := x.2.2.2.2.2.2.2.2.2.2.2, ptr := x.2.1, exGntd := false, shr := x.2.2.1, inv := x.2.2.2.1 }}),
            x.2.2.2.2.2.2.2.2.2.2.2, x.2.1, x.2.2.1, x.2.2.2.1,
            {Item.cache
                  { id := x.1, state := x.2.2.2.2.1, ch1 := Req.reqE, ch2 := x.2.2.2.2.2.1, ch3 := x.2.2.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.idle, ptr := x.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.1,
                    shr := x.2.2.2.2.2.2.2.2.2.1, inv := x.2.2.2.2.2.2.2.2.2.2.1 }}),
        Unification.Unifier.bind
          fun (x : ℕ × ℕ × Oids × Oids × Items × CacheState × Gnt × Ack × ℕ × Bool × Oids × Oids × Cmd) =>
          ((x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.1, x.1,
              x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1,
              x.2.2.2.2.1 +
                {Item.dir
                    { cmd := x.2.2.2.2.2.2.2.2.2.2.2.2, ptr := x.2.1, exGntd := false, shr := x.2.2.1,
                      inv := x.2.2.2.1 }}),
            x.2.2.2.2.2.2.2.2.2.2.2.2, x.2.1, x.2.2.1, x.2.2.2.1,
            x.2.2.2.2.1 +
                {Item.cache
                    { id := x.1, state := x.2.2.2.2.2.1, ch1 := Req.reqE, ch2 := x.2.2.2.2.2.2.1,
                      ch3 := x.2.2.2.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.idle, ptr := x.2.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.2.1,
                    shr := x.2.2.2.2.2.2.2.2.2.2.1, inv := x.2.2.2.2.2.2.2.2.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × CacheState × Gnt × Ack × ℕ × Oids × Oids) =>
          ((x.2.2.2.2.1, false, x.2.2.2.2.2.1, x.2.2.2.2.2.2, x.1, x.2.1, x.2.2.1, x.2.2.2.1, ∅), Cmd.idle, x.2.2.2.2.1,
            x.2.2.2.2.2.1, x.2.2.2.2.2.2,
            {Item.cache { id := x.1, state := x.2.1, ch1 := Req.reqE, ch2 := x.2.2.1, ch3 := x.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : Items × ℕ × CacheState × Gnt × Ack × ℕ × Oids × Oids) =>
          ((x.2.2.2.2.2.1, false, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.1),
            Cmd.idle, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2,
            x.1 +
              {Item.cache
                  { id := x.2.1, state := x.2.2.1, ch1 := Req.reqE, ch2 := x.2.2.2.1, ch3 := x.2.2.2.2.1 }})] := by
  maude_certify_comp

theorem recvReqE_inv.obligation_2 :
    Unification.sound (Narrowing.mayFire recvReqE freeP)
      [Unification.Unifier.bind fun (x : ℕ × ℕ × Oids × Oids × CacheState × Gnt × Ack × ℕ × Bool × Oids × Oids × Cmd) =>
          ((x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.1, x.2.2.2.2.1,
              x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
              {Item.dir
                  { cmd := x.2.2.2.2.2.2.2.2.2.2.2, ptr := x.2.1, exGntd := false, shr := x.2.2.1, inv := x.2.2.2.1 }}),
            x.2.2.2.2.2.2.2.2.2.2.2, x.2.1, x.2.2.1, x.2.2.2.1,
            {Item.cache
                  { id := x.1, state := x.2.2.2.2.1, ch1 := Req.reqE, ch2 := x.2.2.2.2.2.1, ch3 := x.2.2.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.idle, ptr := x.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.1,
                    shr := x.2.2.2.2.2.2.2.2.2.1, inv := x.2.2.2.2.2.2.2.2.2.2.1 }}),
        Unification.Unifier.bind
          fun (x : ℕ × ℕ × Oids × Oids × Items × CacheState × Gnt × Ack × ℕ × Bool × Oids × Oids × Cmd) =>
          ((x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.1, x.1,
              x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1,
              x.2.2.2.2.1 +
                {Item.dir
                    { cmd := x.2.2.2.2.2.2.2.2.2.2.2.2, ptr := x.2.1, exGntd := false, shr := x.2.2.1,
                      inv := x.2.2.2.1 }}),
            x.2.2.2.2.2.2.2.2.2.2.2.2, x.2.1, x.2.2.1, x.2.2.2.1,
            x.2.2.2.2.1 +
                {Item.cache
                    { id := x.1, state := x.2.2.2.2.2.1, ch1 := Req.reqE, ch2 := x.2.2.2.2.2.2.1,
                      ch3 := x.2.2.2.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.idle, ptr := x.2.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.2.1,
                    shr := x.2.2.2.2.2.2.2.2.2.2.1, inv := x.2.2.2.2.2.2.2.2.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × CacheState × Gnt × Ack × ℕ × Oids × Oids) =>
          ((x.2.2.2.2.1, false, x.2.2.2.2.2.1, x.2.2.2.2.2.2, x.1, x.2.1, x.2.2.1, x.2.2.2.1, ∅), Cmd.idle, x.2.2.2.2.1,
            x.2.2.2.2.2.1, x.2.2.2.2.2.2,
            {Item.cache { id := x.1, state := x.2.1, ch1 := Req.reqE, ch2 := x.2.2.1, ch3 := x.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : Items × ℕ × CacheState × Gnt × Ack × ℕ × Oids × Oids) =>
          ((x.2.2.2.2.2.1, false, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.1),
            Cmd.idle, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2,
            x.1 +
              {Item.cache
                  { id := x.2.1, state := x.2.2.1, ch1 := Req.reqE, ch2 := x.2.2.2.1, ch3 := x.2.2.2.2.1 }})] := by
  sorry

theorem recvReqE_inv.obligation_3 :
    Unification.complete (Narrowing.mayFire recvReqE ownE)
      [Unification.Unifier.bind
          fun (x : ℕ × Req × Cmd × ℕ × Oids × CacheState × Gnt × Ack × ℕ × Bool × Oids × Oids × ℕ) =>
          ((x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.1, x.1,
              x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1,
              {Item.cache
                    { id := x.2.2.2.2.2.2.2.2.2.2.2.2, state := CacheState.exclusive, ch1 := x.2.1, ch2 := Gnt.noGnt,
                      ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.1, ptr := x.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.2.2.2.2},
                      inv := x.2.2.2.2.1 }}),
            x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2, x.2.1,
            {Item.cache
                  { id := x.1, state := x.2.2.2.2.2.1, ch1 := Req.reqE, ch2 := x.2.2.2.2.2.2.1,
                    ch3 := x.2.2.2.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.idle, ptr := x.2.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.2.1,
                    shr := x.2.2.2.2.2.2.2.2.2.2.1, inv := x.2.2.2.2.2.2.2.2.2.2.2.1 }}),
        Unification.Unifier.bind
          fun (x : ℕ × Req × Cmd × ℕ × Oids × Items × CacheState × Gnt × Ack × ℕ × Bool × Oids × Oids × ℕ) =>
          ((x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2.1, x.1,
              x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.1 +
                  {Item.cache
                      { id := x.2.2.2.2.2.2.2.2.2.2.2.2.2, state := CacheState.exclusive, ch1 := x.2.1,
                        ch2 := Gnt.noGnt, ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.1, ptr := x.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.2.2.2.2.2},
                      inv := x.2.2.2.2.1 }}),
            x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2.2, x.2.1,
            x.2.2.2.2.2.1 +
                {Item.cache
                    { id := x.1, state := x.2.2.2.2.2.2.1, ch1 := Req.reqE, ch2 := x.2.2.2.2.2.2.2.1,
                      ch3 := x.2.2.2.2.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.idle, ptr := x.2.2.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.2.2.1,
                    shr := x.2.2.2.2.2.2.2.2.2.2.2.1, inv := x.2.2.2.2.2.2.2.2.2.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × Bool × Oids × Oids × ℕ × Cmd × ℕ × Oids) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, CacheState.exclusive, Gnt.noGnt, Ack.noAck,
              {Item.dir
                  { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.1},
                    inv := x.2.2.2.2.2.2.2 }}),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2, x.2.2.2.2.1, Req.reqE,
            {Item.dir { cmd := Cmd.idle, ptr := x.1, exGntd := x.2.1, shr := x.2.2.1, inv := x.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × Bool × Oids × Oids × ℕ × Cmd × ℕ × Oids × Items) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, CacheState.exclusive, Gnt.noGnt, Ack.noAck,
              x.2.2.2.2.2.2.2.2 +
                {Item.dir
                    { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.1},
                      inv := x.2.2.2.2.2.2.2.1 }}),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.1, Req.reqE,
            x.2.2.2.2.2.2.2.2 +
              {Item.dir { cmd := Cmd.idle, ptr := x.1, exGntd := x.2.1, shr := x.2.2.1, inv := x.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × CacheState × Gnt × Ack × ℕ × Req × ℕ × Oids) =>
          ((x.2.2.2.2.2.2.1, true, {x.2.2.2.2.1}, x.2.2.2.2.2.2.2, x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {Item.cache
                  { id := x.2.2.2.2.1, state := CacheState.exclusive, ch1 := x.2.2.2.2.2.1, ch2 := Gnt.noGnt,
                    ch3 := Ack.noAck }}),
            Cmd.idle, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2, x.2.2.2.2.1, x.2.2.2.2.2.1,
            {Item.cache { id := x.1, state := x.2.1, ch1 := Req.reqE, ch2 := x.2.2.1, ch3 := x.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × CacheState × Gnt × Ack × ℕ × Req × ℕ × Oids × Items) =>
          ((x.2.2.2.2.2.2.1, true, {x.2.2.2.2.1}, x.2.2.2.2.2.2.2.1, x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              x.2.2.2.2.2.2.2.2 +
                {Item.cache
                    { id := x.2.2.2.2.1, state := CacheState.exclusive, ch1 := x.2.2.2.2.2.1, ch2 := Gnt.noGnt,
                      ch3 := Ack.noAck }}),
            Cmd.idle, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
            x.2.2.2.2.2.2.2.2 +
              {Item.cache { id := x.1, state := x.2.1, ch1 := Req.reqE, ch2 := x.2.2.1, ch3 := x.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × ℕ × Oids) =>
          ((x.2.1, true, {x.1}, x.2.2, x.1, CacheState.exclusive, Gnt.noGnt, Ack.noAck, ∅), Cmd.idle, x.2.1, x.2.2, x.1,
            Req.reqE, ∅),
        Unification.Unifier.bind fun (x : Items × ℕ × ℕ × Oids) =>
          ((x.2.2.1, true, {x.2.1}, x.2.2.2, x.2.1, CacheState.exclusive, Gnt.noGnt, Ack.noAck, x.1), Cmd.idle, x.2.2.1,
            x.2.2.2, x.2.1, Req.reqE, x.1)] := by
  maude_certify_comp

theorem recvReqE_inv.obligation_4 :
    Unification.sound (Narrowing.mayFire recvReqE ownE)
      [Unification.Unifier.bind
          fun (x : ℕ × Req × Cmd × ℕ × Oids × CacheState × Gnt × Ack × ℕ × Bool × Oids × Oids × ℕ) =>
          ((x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.1, x.1,
              x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1,
              {Item.cache
                    { id := x.2.2.2.2.2.2.2.2.2.2.2.2, state := CacheState.exclusive, ch1 := x.2.1, ch2 := Gnt.noGnt,
                      ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.1, ptr := x.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.2.2.2.2},
                      inv := x.2.2.2.2.1 }}),
            x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2, x.2.1,
            {Item.cache
                  { id := x.1, state := x.2.2.2.2.2.1, ch1 := Req.reqE, ch2 := x.2.2.2.2.2.2.1,
                    ch3 := x.2.2.2.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.idle, ptr := x.2.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.2.1,
                    shr := x.2.2.2.2.2.2.2.2.2.2.1, inv := x.2.2.2.2.2.2.2.2.2.2.2.1 }}),
        Unification.Unifier.bind
          fun (x : ℕ × Req × Cmd × ℕ × Oids × Items × CacheState × Gnt × Ack × ℕ × Bool × Oids × Oids × ℕ) =>
          ((x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2.1, x.1,
              x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.1 +
                  {Item.cache
                      { id := x.2.2.2.2.2.2.2.2.2.2.2.2.2, state := CacheState.exclusive, ch1 := x.2.1,
                        ch2 := Gnt.noGnt, ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.1, ptr := x.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.2.2.2.2.2},
                      inv := x.2.2.2.2.1 }}),
            x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2.2, x.2.1,
            x.2.2.2.2.2.1 +
                {Item.cache
                    { id := x.1, state := x.2.2.2.2.2.2.1, ch1 := Req.reqE, ch2 := x.2.2.2.2.2.2.2.1,
                      ch3 := x.2.2.2.2.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.idle, ptr := x.2.2.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.2.2.1,
                    shr := x.2.2.2.2.2.2.2.2.2.2.2.1, inv := x.2.2.2.2.2.2.2.2.2.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × Bool × Oids × Oids × ℕ × Cmd × ℕ × Oids) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, CacheState.exclusive, Gnt.noGnt, Ack.noAck,
              {Item.dir
                  { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.1},
                    inv := x.2.2.2.2.2.2.2 }}),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2, x.2.2.2.2.1, Req.reqE,
            {Item.dir { cmd := Cmd.idle, ptr := x.1, exGntd := x.2.1, shr := x.2.2.1, inv := x.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × Bool × Oids × Oids × ℕ × Cmd × ℕ × Oids × Items) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, CacheState.exclusive, Gnt.noGnt, Ack.noAck,
              x.2.2.2.2.2.2.2.2 +
                {Item.dir
                    { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.1},
                      inv := x.2.2.2.2.2.2.2.1 }}),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.1, Req.reqE,
            x.2.2.2.2.2.2.2.2 +
              {Item.dir { cmd := Cmd.idle, ptr := x.1, exGntd := x.2.1, shr := x.2.2.1, inv := x.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × CacheState × Gnt × Ack × ℕ × Req × ℕ × Oids) =>
          ((x.2.2.2.2.2.2.1, true, {x.2.2.2.2.1}, x.2.2.2.2.2.2.2, x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {Item.cache
                  { id := x.2.2.2.2.1, state := CacheState.exclusive, ch1 := x.2.2.2.2.2.1, ch2 := Gnt.noGnt,
                    ch3 := Ack.noAck }}),
            Cmd.idle, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2, x.2.2.2.2.1, x.2.2.2.2.2.1,
            {Item.cache { id := x.1, state := x.2.1, ch1 := Req.reqE, ch2 := x.2.2.1, ch3 := x.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × CacheState × Gnt × Ack × ℕ × Req × ℕ × Oids × Items) =>
          ((x.2.2.2.2.2.2.1, true, {x.2.2.2.2.1}, x.2.2.2.2.2.2.2.1, x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              x.2.2.2.2.2.2.2.2 +
                {Item.cache
                    { id := x.2.2.2.2.1, state := CacheState.exclusive, ch1 := x.2.2.2.2.2.1, ch2 := Gnt.noGnt,
                      ch3 := Ack.noAck }}),
            Cmd.idle, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
            x.2.2.2.2.2.2.2.2 +
              {Item.cache { id := x.1, state := x.2.1, ch1 := Req.reqE, ch2 := x.2.2.1, ch3 := x.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × ℕ × Oids) =>
          ((x.2.1, true, {x.1}, x.2.2, x.1, CacheState.exclusive, Gnt.noGnt, Ack.noAck, ∅), Cmd.idle, x.2.1, x.2.2, x.1,
            Req.reqE, ∅),
        Unification.Unifier.bind fun (x : Items × ℕ × ℕ × Oids) =>
          ((x.2.2.1, true, {x.2.1}, x.2.2.2, x.2.1, CacheState.exclusive, Gnt.noGnt, Ack.noAck, x.1), Cmd.idle, x.2.2.1,
            x.2.2.2, x.2.1, Req.reqE, x.1)] := by
  sorry

theorem recvReqE_inv.obligation_5 :
    Unification.complete (Narrowing.mayFire recvReqE ownG)
      [Unification.Unifier.bind
          fun (x : ℕ × Req × Cmd × ℕ × Oids × CacheState × Gnt × Ack × ℕ × Bool × Oids × Oids × ℕ) =>
          ((x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.1, x.1,
              x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1,
              {Item.cache
                    { id := x.2.2.2.2.2.2.2.2.2.2.2.2, state := CacheState.invalid, ch1 := x.2.1, ch2 := Gnt.gntE,
                      ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.1, ptr := x.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.2.2.2.2},
                      inv := x.2.2.2.2.1 }}),
            x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2, x.2.1,
            {Item.cache
                  { id := x.1, state := x.2.2.2.2.2.1, ch1 := Req.reqE, ch2 := x.2.2.2.2.2.2.1,
                    ch3 := x.2.2.2.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.idle, ptr := x.2.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.2.1,
                    shr := x.2.2.2.2.2.2.2.2.2.2.1, inv := x.2.2.2.2.2.2.2.2.2.2.2.1 }}),
        Unification.Unifier.bind
          fun (x : ℕ × Req × Cmd × ℕ × Oids × Items × CacheState × Gnt × Ack × ℕ × Bool × Oids × Oids × ℕ) =>
          ((x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2.1, x.1,
              x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.1 +
                  {Item.cache
                      { id := x.2.2.2.2.2.2.2.2.2.2.2.2.2, state := CacheState.invalid, ch1 := x.2.1, ch2 := Gnt.gntE,
                        ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.1, ptr := x.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.2.2.2.2.2},
                      inv := x.2.2.2.2.1 }}),
            x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2.2, x.2.1,
            x.2.2.2.2.2.1 +
                {Item.cache
                    { id := x.1, state := x.2.2.2.2.2.2.1, ch1 := Req.reqE, ch2 := x.2.2.2.2.2.2.2.1,
                      ch3 := x.2.2.2.2.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.idle, ptr := x.2.2.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.2.2.1,
                    shr := x.2.2.2.2.2.2.2.2.2.2.2.1, inv := x.2.2.2.2.2.2.2.2.2.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × Bool × Oids × Oids × ℕ × Cmd × ℕ × Oids) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, CacheState.invalid, Gnt.gntE, Ack.noAck,
              {Item.dir
                  { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.1},
                    inv := x.2.2.2.2.2.2.2 }}),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2, x.2.2.2.2.1, Req.reqE,
            {Item.dir { cmd := Cmd.idle, ptr := x.1, exGntd := x.2.1, shr := x.2.2.1, inv := x.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × Bool × Oids × Oids × ℕ × Cmd × ℕ × Oids × Items) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, CacheState.invalid, Gnt.gntE, Ack.noAck,
              x.2.2.2.2.2.2.2.2 +
                {Item.dir
                    { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.1},
                      inv := x.2.2.2.2.2.2.2.1 }}),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.1, Req.reqE,
            x.2.2.2.2.2.2.2.2 +
              {Item.dir { cmd := Cmd.idle, ptr := x.1, exGntd := x.2.1, shr := x.2.2.1, inv := x.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × CacheState × Gnt × Ack × ℕ × Req × ℕ × Oids) =>
          ((x.2.2.2.2.2.2.1, true, {x.2.2.2.2.1}, x.2.2.2.2.2.2.2, x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {Item.cache
                  { id := x.2.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.2.1, ch2 := Gnt.gntE,
                    ch3 := Ack.noAck }}),
            Cmd.idle, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2, x.2.2.2.2.1, x.2.2.2.2.2.1,
            {Item.cache { id := x.1, state := x.2.1, ch1 := Req.reqE, ch2 := x.2.2.1, ch3 := x.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × CacheState × Gnt × Ack × ℕ × Req × ℕ × Oids × Items) =>
          ((x.2.2.2.2.2.2.1, true, {x.2.2.2.2.1}, x.2.2.2.2.2.2.2.1, x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              x.2.2.2.2.2.2.2.2 +
                {Item.cache
                    { id := x.2.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.2.1, ch2 := Gnt.gntE,
                      ch3 := Ack.noAck }}),
            Cmd.idle, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
            x.2.2.2.2.2.2.2.2 +
              {Item.cache { id := x.1, state := x.2.1, ch1 := Req.reqE, ch2 := x.2.2.1, ch3 := x.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × ℕ × Oids) =>
          ((x.2.1, true, {x.1}, x.2.2, x.1, CacheState.invalid, Gnt.gntE, Ack.noAck, ∅), Cmd.idle, x.2.1, x.2.2, x.1,
            Req.reqE, ∅),
        Unification.Unifier.bind fun (x : Items × ℕ × ℕ × Oids) =>
          ((x.2.2.1, true, {x.2.1}, x.2.2.2, x.2.1, CacheState.invalid, Gnt.gntE, Ack.noAck, x.1), Cmd.idle, x.2.2.1,
            x.2.2.2, x.2.1, Req.reqE, x.1)] := by
  maude_certify_comp

theorem recvReqE_inv.obligation_6 :
    Unification.sound (Narrowing.mayFire recvReqE ownG)
      [Unification.Unifier.bind
          fun (x : ℕ × Req × Cmd × ℕ × Oids × CacheState × Gnt × Ack × ℕ × Bool × Oids × Oids × ℕ) =>
          ((x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.1, x.1,
              x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1,
              {Item.cache
                    { id := x.2.2.2.2.2.2.2.2.2.2.2.2, state := CacheState.invalid, ch1 := x.2.1, ch2 := Gnt.gntE,
                      ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.1, ptr := x.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.2.2.2.2},
                      inv := x.2.2.2.2.1 }}),
            x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2, x.2.1,
            {Item.cache
                  { id := x.1, state := x.2.2.2.2.2.1, ch1 := Req.reqE, ch2 := x.2.2.2.2.2.2.1,
                    ch3 := x.2.2.2.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.idle, ptr := x.2.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.2.1,
                    shr := x.2.2.2.2.2.2.2.2.2.2.1, inv := x.2.2.2.2.2.2.2.2.2.2.2.1 }}),
        Unification.Unifier.bind
          fun (x : ℕ × Req × Cmd × ℕ × Oids × Items × CacheState × Gnt × Ack × ℕ × Bool × Oids × Oids × ℕ) =>
          ((x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2.1, x.1,
              x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.1 +
                  {Item.cache
                      { id := x.2.2.2.2.2.2.2.2.2.2.2.2.2, state := CacheState.invalid, ch1 := x.2.1, ch2 := Gnt.gntE,
                        ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.1, ptr := x.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.2.2.2.2.2},
                      inv := x.2.2.2.2.1 }}),
            x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2.2, x.2.1,
            x.2.2.2.2.2.1 +
                {Item.cache
                    { id := x.1, state := x.2.2.2.2.2.2.1, ch1 := Req.reqE, ch2 := x.2.2.2.2.2.2.2.1,
                      ch3 := x.2.2.2.2.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.idle, ptr := x.2.2.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.2.2.1,
                    shr := x.2.2.2.2.2.2.2.2.2.2.2.1, inv := x.2.2.2.2.2.2.2.2.2.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × Bool × Oids × Oids × ℕ × Cmd × ℕ × Oids) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, CacheState.invalid, Gnt.gntE, Ack.noAck,
              {Item.dir
                  { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.1},
                    inv := x.2.2.2.2.2.2.2 }}),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2, x.2.2.2.2.1, Req.reqE,
            {Item.dir { cmd := Cmd.idle, ptr := x.1, exGntd := x.2.1, shr := x.2.2.1, inv := x.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × Bool × Oids × Oids × ℕ × Cmd × ℕ × Oids × Items) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, CacheState.invalid, Gnt.gntE, Ack.noAck,
              x.2.2.2.2.2.2.2.2 +
                {Item.dir
                    { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.1},
                      inv := x.2.2.2.2.2.2.2.1 }}),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.1, Req.reqE,
            x.2.2.2.2.2.2.2.2 +
              {Item.dir { cmd := Cmd.idle, ptr := x.1, exGntd := x.2.1, shr := x.2.2.1, inv := x.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × CacheState × Gnt × Ack × ℕ × Req × ℕ × Oids) =>
          ((x.2.2.2.2.2.2.1, true, {x.2.2.2.2.1}, x.2.2.2.2.2.2.2, x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {Item.cache
                  { id := x.2.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.2.1, ch2 := Gnt.gntE,
                    ch3 := Ack.noAck }}),
            Cmd.idle, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2, x.2.2.2.2.1, x.2.2.2.2.2.1,
            {Item.cache { id := x.1, state := x.2.1, ch1 := Req.reqE, ch2 := x.2.2.1, ch3 := x.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × CacheState × Gnt × Ack × ℕ × Req × ℕ × Oids × Items) =>
          ((x.2.2.2.2.2.2.1, true, {x.2.2.2.2.1}, x.2.2.2.2.2.2.2.1, x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              x.2.2.2.2.2.2.2.2 +
                {Item.cache
                    { id := x.2.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.2.1, ch2 := Gnt.gntE,
                      ch3 := Ack.noAck }}),
            Cmd.idle, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
            x.2.2.2.2.2.2.2.2 +
              {Item.cache { id := x.1, state := x.2.1, ch1 := Req.reqE, ch2 := x.2.2.1, ch3 := x.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × ℕ × Oids) =>
          ((x.2.1, true, {x.1}, x.2.2, x.1, CacheState.invalid, Gnt.gntE, Ack.noAck, ∅), Cmd.idle, x.2.1, x.2.2, x.1,
            Req.reqE, ∅),
        Unification.Unifier.bind fun (x : Items × ℕ × ℕ × Oids) =>
          ((x.2.2.1, true, {x.2.1}, x.2.2.2, x.2.1, CacheState.invalid, Gnt.gntE, Ack.noAck, x.1), Cmd.idle, x.2.2.1,
            x.2.2.2, x.2.1, Req.reqE, x.1)] := by
  sorry

theorem recvReqE_inv.obligation_7 :
    Unification.complete (Narrowing.mayFire recvReqE ownInv)
      [Unification.Unifier.bind fun (x : ℕ × Req × Cmd × ℕ × CacheState × Gnt × Ack × ℕ × Bool × Oids × Oids × ℕ) =>
          ((x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.1, x.2.2.2.2.1,
              x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
              {Item.cache
                    { id := x.2.2.2.2.2.2.2.2.2.2.2, state := CacheState.exclusive, ch1 := x.2.1, ch2 := Gnt.inv,
                      ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.1, ptr := x.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.2.2.2}, inv := ∅ }}),
            x.2.2.1, x.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2, x.2.1,
            {Item.cache
                  { id := x.1, state := x.2.2.2.2.1, ch1 := Req.reqE, ch2 := x.2.2.2.2.2.1, ch3 := x.2.2.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.idle, ptr := x.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.1,
                    shr := x.2.2.2.2.2.2.2.2.2.1, inv := x.2.2.2.2.2.2.2.2.2.2.1 }}),
        Unification.Unifier.bind
          fun (x : ℕ × Req × Cmd × ℕ × Items × CacheState × Gnt × Ack × ℕ × Bool × Oids × Oids × ℕ) =>
          ((x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.1, x.1,
              x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1,
              x.2.2.2.2.1 +
                  {Item.cache
                      { id := x.2.2.2.2.2.2.2.2.2.2.2.2, state := CacheState.exclusive, ch1 := x.2.1, ch2 := Gnt.inv,
                        ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.1, ptr := x.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.2.2.2.2},
                      inv := ∅ }}),
            x.2.2.1, x.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2, x.2.1,
            x.2.2.2.2.1 +
                {Item.cache
                    { id := x.1, state := x.2.2.2.2.2.1, ch1 := Req.reqE, ch2 := x.2.2.2.2.2.2.1,
                      ch3 := x.2.2.2.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.idle, ptr := x.2.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.2.1,
                    shr := x.2.2.2.2.2.2.2.2.2.2.1, inv := x.2.2.2.2.2.2.2.2.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × Bool × Oids × Oids × ℕ × Cmd × ℕ) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, CacheState.exclusive, Gnt.inv, Ack.noAck,
              {Item.dir
                  { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2, exGntd := true, shr := {x.2.2.2.2.1}, inv := ∅ }}),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2, x.2.2.2.2.1, Req.reqE,
            {Item.dir { cmd := Cmd.idle, ptr := x.1, exGntd := x.2.1, shr := x.2.2.1, inv := x.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × Bool × Oids × Oids × ℕ × Cmd × ℕ × Items) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, CacheState.exclusive, Gnt.inv, Ack.noAck,
              x.2.2.2.2.2.2.2 +
                {Item.dir
                    { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.1}, inv := ∅ }}),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.1, Req.reqE,
            x.2.2.2.2.2.2.2 +
              {Item.dir { cmd := Cmd.idle, ptr := x.1, exGntd := x.2.1, shr := x.2.2.1, inv := x.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × CacheState × Gnt × Ack × ℕ × Req × ℕ) =>
          ((x.2.2.2.2.2.2, true, {x.2.2.2.2.1}, ∅, x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {Item.cache
                  { id := x.2.2.2.2.1, state := CacheState.exclusive, ch1 := x.2.2.2.2.2.1, ch2 := Gnt.inv,
                    ch3 := Ack.noAck }}),
            Cmd.idle, x.2.2.2.2.2.2, x.2.2.2.2.1, x.2.2.2.2.2.1,
            {Item.cache { id := x.1, state := x.2.1, ch1 := Req.reqE, ch2 := x.2.2.1, ch3 := x.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × CacheState × Gnt × Ack × ℕ × Req × ℕ × Items) =>
          ((x.2.2.2.2.2.2.1, true, {x.2.2.2.2.1}, ∅, x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              x.2.2.2.2.2.2.2 +
                {Item.cache
                    { id := x.2.2.2.2.1, state := CacheState.exclusive, ch1 := x.2.2.2.2.2.1, ch2 := Gnt.inv,
                      ch3 := Ack.noAck }}),
            Cmd.idle, x.2.2.2.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
            x.2.2.2.2.2.2.2 +
              {Item.cache { id := x.1, state := x.2.1, ch1 := Req.reqE, ch2 := x.2.2.1, ch3 := x.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × ℕ) =>
          ((x.2, true, {x.1}, ∅, x.1, CacheState.exclusive, Gnt.inv, Ack.noAck, ∅), Cmd.idle, x.2, x.1, Req.reqE, ∅),
        Unification.Unifier.bind fun (x : Items × ℕ × ℕ) =>
          ((x.2.2, true, {x.2.1}, ∅, x.2.1, CacheState.exclusive, Gnt.inv, Ack.noAck, x.1), Cmd.idle, x.2.2, x.2.1,
            Req.reqE, x.1)] := by
  maude_certify_comp

theorem recvReqE_inv.obligation_8 :
    Unification.sound (Narrowing.mayFire recvReqE ownInv)
      [Unification.Unifier.bind fun (x : ℕ × Req × Cmd × ℕ × CacheState × Gnt × Ack × ℕ × Bool × Oids × Oids × ℕ) =>
          ((x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.1, x.2.2.2.2.1,
              x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
              {Item.cache
                    { id := x.2.2.2.2.2.2.2.2.2.2.2, state := CacheState.exclusive, ch1 := x.2.1, ch2 := Gnt.inv,
                      ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.1, ptr := x.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.2.2.2}, inv := ∅ }}),
            x.2.2.1, x.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2, x.2.1,
            {Item.cache
                  { id := x.1, state := x.2.2.2.2.1, ch1 := Req.reqE, ch2 := x.2.2.2.2.2.1, ch3 := x.2.2.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.idle, ptr := x.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.1,
                    shr := x.2.2.2.2.2.2.2.2.2.1, inv := x.2.2.2.2.2.2.2.2.2.2.1 }}),
        Unification.Unifier.bind
          fun (x : ℕ × Req × Cmd × ℕ × Items × CacheState × Gnt × Ack × ℕ × Bool × Oids × Oids × ℕ) =>
          ((x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.1, x.1,
              x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1,
              x.2.2.2.2.1 +
                  {Item.cache
                      { id := x.2.2.2.2.2.2.2.2.2.2.2.2, state := CacheState.exclusive, ch1 := x.2.1, ch2 := Gnt.inv,
                        ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.1, ptr := x.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.2.2.2.2},
                      inv := ∅ }}),
            x.2.2.1, x.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2, x.2.1,
            x.2.2.2.2.1 +
                {Item.cache
                    { id := x.1, state := x.2.2.2.2.2.1, ch1 := Req.reqE, ch2 := x.2.2.2.2.2.2.1,
                      ch3 := x.2.2.2.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.idle, ptr := x.2.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.2.1,
                    shr := x.2.2.2.2.2.2.2.2.2.2.1, inv := x.2.2.2.2.2.2.2.2.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × Bool × Oids × Oids × ℕ × Cmd × ℕ) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, CacheState.exclusive, Gnt.inv, Ack.noAck,
              {Item.dir
                  { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2, exGntd := true, shr := {x.2.2.2.2.1}, inv := ∅ }}),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2, x.2.2.2.2.1, Req.reqE,
            {Item.dir { cmd := Cmd.idle, ptr := x.1, exGntd := x.2.1, shr := x.2.2.1, inv := x.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × Bool × Oids × Oids × ℕ × Cmd × ℕ × Items) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, CacheState.exclusive, Gnt.inv, Ack.noAck,
              x.2.2.2.2.2.2.2 +
                {Item.dir
                    { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.1}, inv := ∅ }}),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.1, Req.reqE,
            x.2.2.2.2.2.2.2 +
              {Item.dir { cmd := Cmd.idle, ptr := x.1, exGntd := x.2.1, shr := x.2.2.1, inv := x.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × CacheState × Gnt × Ack × ℕ × Req × ℕ) =>
          ((x.2.2.2.2.2.2, true, {x.2.2.2.2.1}, ∅, x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {Item.cache
                  { id := x.2.2.2.2.1, state := CacheState.exclusive, ch1 := x.2.2.2.2.2.1, ch2 := Gnt.inv,
                    ch3 := Ack.noAck }}),
            Cmd.idle, x.2.2.2.2.2.2, x.2.2.2.2.1, x.2.2.2.2.2.1,
            {Item.cache { id := x.1, state := x.2.1, ch1 := Req.reqE, ch2 := x.2.2.1, ch3 := x.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × CacheState × Gnt × Ack × ℕ × Req × ℕ × Items) =>
          ((x.2.2.2.2.2.2.1, true, {x.2.2.2.2.1}, ∅, x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              x.2.2.2.2.2.2.2 +
                {Item.cache
                    { id := x.2.2.2.2.1, state := CacheState.exclusive, ch1 := x.2.2.2.2.2.1, ch2 := Gnt.inv,
                      ch3 := Ack.noAck }}),
            Cmd.idle, x.2.2.2.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
            x.2.2.2.2.2.2.2 +
              {Item.cache { id := x.1, state := x.2.1, ch1 := Req.reqE, ch2 := x.2.2.1, ch3 := x.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × ℕ) =>
          ((x.2, true, {x.1}, ∅, x.1, CacheState.exclusive, Gnt.inv, Ack.noAck, ∅), Cmd.idle, x.2, x.1, Req.reqE, ∅),
        Unification.Unifier.bind fun (x : Items × ℕ × ℕ) =>
          ((x.2.2, true, {x.2.1}, ∅, x.2.1, CacheState.exclusive, Gnt.inv, Ack.noAck, x.1), Cmd.idle, x.2.2, x.2.1,
            Req.reqE, x.1)] := by
  sorry

theorem recvReqE_inv.obligation_9 :
    Unification.complete (Narrowing.mayFire recvReqE ownAck)
      [Unification.Unifier.bind fun (x : ℕ × Req × Cmd × ℕ × CacheState × Gnt × Ack × ℕ × Bool × Oids × Oids × ℕ) =>
          ((x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.1, x.2.2.2.2.1,
              x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
              {Item.cache
                    { id := x.2.2.2.2.2.2.2.2.2.2.2, state := CacheState.invalid, ch1 := x.2.1, ch2 := Gnt.noGnt,
                      ch3 := Ack.invAck }} +
                {Item.dir
                    { cmd := x.2.2.1, ptr := x.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.2.2.2}, inv := ∅ }}),
            x.2.2.1, x.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2, x.2.1,
            {Item.cache
                  { id := x.1, state := x.2.2.2.2.1, ch1 := Req.reqE, ch2 := x.2.2.2.2.2.1, ch3 := x.2.2.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.idle, ptr := x.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.1,
                    shr := x.2.2.2.2.2.2.2.2.2.1, inv := x.2.2.2.2.2.2.2.2.2.2.1 }}),
        Unification.Unifier.bind
          fun (x : ℕ × Req × Cmd × ℕ × Items × CacheState × Gnt × Ack × ℕ × Bool × Oids × Oids × ℕ) =>
          ((x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.1, x.1,
              x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1,
              x.2.2.2.2.1 +
                  {Item.cache
                      { id := x.2.2.2.2.2.2.2.2.2.2.2.2, state := CacheState.invalid, ch1 := x.2.1, ch2 := Gnt.noGnt,
                        ch3 := Ack.invAck }} +
                {Item.dir
                    { cmd := x.2.2.1, ptr := x.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.2.2.2.2},
                      inv := ∅ }}),
            x.2.2.1, x.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2, x.2.1,
            x.2.2.2.2.1 +
                {Item.cache
                    { id := x.1, state := x.2.2.2.2.2.1, ch1 := Req.reqE, ch2 := x.2.2.2.2.2.2.1,
                      ch3 := x.2.2.2.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.idle, ptr := x.2.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.2.1,
                    shr := x.2.2.2.2.2.2.2.2.2.2.1, inv := x.2.2.2.2.2.2.2.2.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × Bool × Oids × Oids × ℕ × Cmd × ℕ) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, CacheState.invalid, Gnt.noGnt, Ack.invAck,
              {Item.dir
                  { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2, exGntd := true, shr := {x.2.2.2.2.1}, inv := ∅ }}),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2, x.2.2.2.2.1, Req.reqE,
            {Item.dir { cmd := Cmd.idle, ptr := x.1, exGntd := x.2.1, shr := x.2.2.1, inv := x.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × Bool × Oids × Oids × ℕ × Cmd × ℕ × Items) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, CacheState.invalid, Gnt.noGnt, Ack.invAck,
              x.2.2.2.2.2.2.2 +
                {Item.dir
                    { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.1}, inv := ∅ }}),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.1, Req.reqE,
            x.2.2.2.2.2.2.2 +
              {Item.dir { cmd := Cmd.idle, ptr := x.1, exGntd := x.2.1, shr := x.2.2.1, inv := x.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × CacheState × Gnt × Ack × ℕ × Req × ℕ) =>
          ((x.2.2.2.2.2.2, true, {x.2.2.2.2.1}, ∅, x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {Item.cache
                  { id := x.2.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.2.1, ch2 := Gnt.noGnt,
                    ch3 := Ack.invAck }}),
            Cmd.idle, x.2.2.2.2.2.2, x.2.2.2.2.1, x.2.2.2.2.2.1,
            {Item.cache { id := x.1, state := x.2.1, ch1 := Req.reqE, ch2 := x.2.2.1, ch3 := x.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × CacheState × Gnt × Ack × ℕ × Req × ℕ × Items) =>
          ((x.2.2.2.2.2.2.1, true, {x.2.2.2.2.1}, ∅, x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              x.2.2.2.2.2.2.2 +
                {Item.cache
                    { id := x.2.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.2.1, ch2 := Gnt.noGnt,
                      ch3 := Ack.invAck }}),
            Cmd.idle, x.2.2.2.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
            x.2.2.2.2.2.2.2 +
              {Item.cache { id := x.1, state := x.2.1, ch1 := Req.reqE, ch2 := x.2.2.1, ch3 := x.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × ℕ) =>
          ((x.2, true, {x.1}, ∅, x.1, CacheState.invalid, Gnt.noGnt, Ack.invAck, ∅), Cmd.idle, x.2, x.1, Req.reqE, ∅),
        Unification.Unifier.bind fun (x : Items × ℕ × ℕ) =>
          ((x.2.2, true, {x.2.1}, ∅, x.2.1, CacheState.invalid, Gnt.noGnt, Ack.invAck, x.1), Cmd.idle, x.2.2, x.2.1,
            Req.reqE, x.1)] := by
  maude_certify_comp

theorem recvReqE_inv.obligation_10 :
    Unification.sound (Narrowing.mayFire recvReqE ownAck)
      [Unification.Unifier.bind fun (x : ℕ × Req × Cmd × ℕ × CacheState × Gnt × Ack × ℕ × Bool × Oids × Oids × ℕ) =>
          ((x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.1, x.2.2.2.2.1,
              x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
              {Item.cache
                    { id := x.2.2.2.2.2.2.2.2.2.2.2, state := CacheState.invalid, ch1 := x.2.1, ch2 := Gnt.noGnt,
                      ch3 := Ack.invAck }} +
                {Item.dir
                    { cmd := x.2.2.1, ptr := x.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.2.2.2}, inv := ∅ }}),
            x.2.2.1, x.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2, x.2.1,
            {Item.cache
                  { id := x.1, state := x.2.2.2.2.1, ch1 := Req.reqE, ch2 := x.2.2.2.2.2.1, ch3 := x.2.2.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.idle, ptr := x.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.1,
                    shr := x.2.2.2.2.2.2.2.2.2.1, inv := x.2.2.2.2.2.2.2.2.2.2.1 }}),
        Unification.Unifier.bind
          fun (x : ℕ × Req × Cmd × ℕ × Items × CacheState × Gnt × Ack × ℕ × Bool × Oids × Oids × ℕ) =>
          ((x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.1, x.1,
              x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1,
              x.2.2.2.2.1 +
                  {Item.cache
                      { id := x.2.2.2.2.2.2.2.2.2.2.2.2, state := CacheState.invalid, ch1 := x.2.1, ch2 := Gnt.noGnt,
                        ch3 := Ack.invAck }} +
                {Item.dir
                    { cmd := x.2.2.1, ptr := x.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.2.2.2.2},
                      inv := ∅ }}),
            x.2.2.1, x.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2, x.2.1,
            x.2.2.2.2.1 +
                {Item.cache
                    { id := x.1, state := x.2.2.2.2.2.1, ch1 := Req.reqE, ch2 := x.2.2.2.2.2.2.1,
                      ch3 := x.2.2.2.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.idle, ptr := x.2.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.2.1,
                    shr := x.2.2.2.2.2.2.2.2.2.2.1, inv := x.2.2.2.2.2.2.2.2.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × Bool × Oids × Oids × ℕ × Cmd × ℕ) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, CacheState.invalid, Gnt.noGnt, Ack.invAck,
              {Item.dir
                  { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2, exGntd := true, shr := {x.2.2.2.2.1}, inv := ∅ }}),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2, x.2.2.2.2.1, Req.reqE,
            {Item.dir { cmd := Cmd.idle, ptr := x.1, exGntd := x.2.1, shr := x.2.2.1, inv := x.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × Bool × Oids × Oids × ℕ × Cmd × ℕ × Items) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, CacheState.invalid, Gnt.noGnt, Ack.invAck,
              x.2.2.2.2.2.2.2 +
                {Item.dir
                    { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.1}, inv := ∅ }}),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.1, Req.reqE,
            x.2.2.2.2.2.2.2 +
              {Item.dir { cmd := Cmd.idle, ptr := x.1, exGntd := x.2.1, shr := x.2.2.1, inv := x.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × CacheState × Gnt × Ack × ℕ × Req × ℕ) =>
          ((x.2.2.2.2.2.2, true, {x.2.2.2.2.1}, ∅, x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {Item.cache
                  { id := x.2.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.2.1, ch2 := Gnt.noGnt,
                    ch3 := Ack.invAck }}),
            Cmd.idle, x.2.2.2.2.2.2, x.2.2.2.2.1, x.2.2.2.2.2.1,
            {Item.cache { id := x.1, state := x.2.1, ch1 := Req.reqE, ch2 := x.2.2.1, ch3 := x.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × CacheState × Gnt × Ack × ℕ × Req × ℕ × Items) =>
          ((x.2.2.2.2.2.2.1, true, {x.2.2.2.2.1}, ∅, x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              x.2.2.2.2.2.2.2 +
                {Item.cache
                    { id := x.2.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.2.1, ch2 := Gnt.noGnt,
                      ch3 := Ack.invAck }}),
            Cmd.idle, x.2.2.2.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
            x.2.2.2.2.2.2.2 +
              {Item.cache { id := x.1, state := x.2.1, ch1 := Req.reqE, ch2 := x.2.2.1, ch3 := x.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × ℕ) =>
          ((x.2, true, {x.1}, ∅, x.1, CacheState.invalid, Gnt.noGnt, Ack.invAck, ∅), Cmd.idle, x.2, x.1, Req.reqE, ∅),
        Unification.Unifier.bind fun (x : Items × ℕ × ℕ) =>
          ((x.2.2, true, {x.2.1}, ∅, x.2.1, CacheState.invalid, Gnt.noGnt, Ack.invAck, x.1), Cmd.idle, x.2.2, x.2.1,
            Req.reqE, x.1)] := by
  sorry

theorem sendInvE_inv.obligation_1 :
    Unification.complete (Narrowing.mayFire sendInvE freeP)
      [Unification.Unifier.bind fun (x : ℕ × Oids × Oids × CacheState × Req × Ack × ℕ × Bool × Oids × Cmd × ℕ) =>
          ((x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1, x.1, ∅, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
              {Item.dir
                  { cmd := x.2.2.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.2.2, exGntd := false, shr := x.2.1,
                    inv := x.2.2.1 }}),
            x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2, x.2.1, x.2.2.1,
            {Item.cache { id := x.1, state := x.2.2.2.1, ch1 := x.2.2.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.cmdE, ptr := x.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.1, shr := x.2.2.2.2.2.2.2.2.1,
                    inv := {x.1} }}),
        Unification.Unifier.bind
          fun (x : ℕ × ℕ × Oids × Oids × CacheState × Req × Ack × ℕ × Bool × Oids × Oids × Cmd) =>
          ((x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.1,
              x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
              {Item.dir
                  { cmd := x.2.2.2.2.2.2.2.2.2.2.2, ptr := x.2.1, exGntd := false, shr := x.2.2.1, inv := x.2.2.2.1 }}),
            x.2.2.2.2.2.2.2.2.2.2.2, x.2.1, x.2.2.1, x.2.2.2.1,
            {Item.cache
                  { id := x.1, state := x.2.2.2.2.1, ch1 := x.2.2.2.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.cmdE, ptr := x.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.1,
                    shr := x.2.2.2.2.2.2.2.2.2.1, inv := {x.1} + x.2.2.2.2.2.2.2.2.2.2.1 }}),
        Unification.Unifier.bind
          fun (x : ℕ × Oids × Oids × Items × CacheState × Req × Ack × ℕ × Bool × Oids × Cmd × ℕ) =>
          ((x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.1, ∅, x.2.2.2.2.1, x.2.2.2.2.2.1,
              x.2.2.2.2.2.2.1,
              x.2.2.2.1 +
                {Item.dir
                    { cmd := x.2.2.2.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.2.2.2, exGntd := false, shr := x.2.1,
                      inv := x.2.2.1 }}),
            x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2, x.2.1, x.2.2.1,
            x.2.2.2.1 +
                {Item.cache
                    { id := x.1, state := x.2.2.2.2.1, ch1 := x.2.2.2.2.2.1, ch2 := Gnt.noGnt,
                      ch3 := x.2.2.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.cmdE, ptr := x.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.1,
                    shr := x.2.2.2.2.2.2.2.2.2.1, inv := {x.1} }}),
        Unification.Unifier.bind
          fun (x : ℕ × ℕ × Oids × Oids × Items × CacheState × Req × Ack × ℕ × Bool × Oids × Oids × Cmd) =>
          ((x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.1, x.2.2.2.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1,
              x.2.2.2.2.1 +
                {Item.dir
                    { cmd := x.2.2.2.2.2.2.2.2.2.2.2.2, ptr := x.2.1, exGntd := false, shr := x.2.2.1,
                      inv := x.2.2.2.1 }}),
            x.2.2.2.2.2.2.2.2.2.2.2.2, x.2.1, x.2.2.1, x.2.2.2.1,
            x.2.2.2.2.1 +
                {Item.cache
                    { id := x.1, state := x.2.2.2.2.2.1, ch1 := x.2.2.2.2.2.2.1, ch2 := Gnt.noGnt,
                      ch3 := x.2.2.2.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.cmdE, ptr := x.2.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.2.1,
                    shr := x.2.2.2.2.2.2.2.2.2.2.1, inv := {x.1} + x.2.2.2.2.2.2.2.2.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × CacheState × Req × Ack × ℕ × Oids) =>
          ((x.2.2.2.2.1, false, x.2.2.2.2.2, x.1, ∅, x.2.1, x.2.2.1, x.2.2.2.1, ∅), Cmd.cmdE, x.2.2.2.2.1, x.2.2.2.2.2,
            {x.1}, {Item.cache { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × CacheState × Req × Ack × Oids × ℕ × Oids) =>
          ((x.2.2.2.2.2.1, false, x.2.2.2.2.2.2, x.1, x.2.2.2.2.1, x.2.1, x.2.2.1, x.2.2.2.1, ∅), Cmd.cmdE,
            x.2.2.2.2.2.1, x.2.2.2.2.2.2, {x.1} + x.2.2.2.2.1,
            {Item.cache { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : Items × ℕ × CacheState × Req × Ack × ℕ × Oids) =>
          ((x.2.2.2.2.2.1, false, x.2.2.2.2.2.2, x.2.1, ∅, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.1), Cmd.cmdE,
            x.2.2.2.2.2.1, x.2.2.2.2.2.2, {x.2.1},
            x.1 +
              {Item.cache { id := x.2.1, state := x.2.2.1, ch1 := x.2.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : Items × ℕ × CacheState × Req × Ack × Oids × ℕ × Oids) =>
          ((x.2.2.2.2.2.2.1, false, x.2.2.2.2.2.2.2, x.2.1, x.2.2.2.2.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.1),
            Cmd.cmdE, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2, {x.2.1} + x.2.2.2.2.2.1,
            x.1 +
              {Item.cache
                  { id := x.2.1, state := x.2.2.1, ch1 := x.2.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.2.1 }})] := by
  maude_certify_comp

theorem sendInvE_inv.obligation_2 :
    Unification.sound (Narrowing.mayFire sendInvE freeP)
      [Unification.Unifier.bind fun (x : ℕ × Oids × Oids × CacheState × Req × Ack × ℕ × Bool × Oids × Cmd × ℕ) =>
          ((x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1, x.1, ∅, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
              {Item.dir
                  { cmd := x.2.2.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.2.2, exGntd := false, shr := x.2.1,
                    inv := x.2.2.1 }}),
            x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2, x.2.1, x.2.2.1,
            {Item.cache { id := x.1, state := x.2.2.2.1, ch1 := x.2.2.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.cmdE, ptr := x.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.1, shr := x.2.2.2.2.2.2.2.2.1,
                    inv := {x.1} }}),
        Unification.Unifier.bind
          fun (x : ℕ × ℕ × Oids × Oids × CacheState × Req × Ack × ℕ × Bool × Oids × Oids × Cmd) =>
          ((x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.1,
              x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
              {Item.dir
                  { cmd := x.2.2.2.2.2.2.2.2.2.2.2, ptr := x.2.1, exGntd := false, shr := x.2.2.1, inv := x.2.2.2.1 }}),
            x.2.2.2.2.2.2.2.2.2.2.2, x.2.1, x.2.2.1, x.2.2.2.1,
            {Item.cache
                  { id := x.1, state := x.2.2.2.2.1, ch1 := x.2.2.2.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.cmdE, ptr := x.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.1,
                    shr := x.2.2.2.2.2.2.2.2.2.1, inv := {x.1} + x.2.2.2.2.2.2.2.2.2.2.1 }}),
        Unification.Unifier.bind
          fun (x : ℕ × Oids × Oids × Items × CacheState × Req × Ack × ℕ × Bool × Oids × Cmd × ℕ) =>
          ((x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.1, ∅, x.2.2.2.2.1, x.2.2.2.2.2.1,
              x.2.2.2.2.2.2.1,
              x.2.2.2.1 +
                {Item.dir
                    { cmd := x.2.2.2.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.2.2.2, exGntd := false, shr := x.2.1,
                      inv := x.2.2.1 }}),
            x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2, x.2.1, x.2.2.1,
            x.2.2.2.1 +
                {Item.cache
                    { id := x.1, state := x.2.2.2.2.1, ch1 := x.2.2.2.2.2.1, ch2 := Gnt.noGnt,
                      ch3 := x.2.2.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.cmdE, ptr := x.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.1,
                    shr := x.2.2.2.2.2.2.2.2.2.1, inv := {x.1} }}),
        Unification.Unifier.bind
          fun (x : ℕ × ℕ × Oids × Oids × Items × CacheState × Req × Ack × ℕ × Bool × Oids × Oids × Cmd) =>
          ((x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.1, x.2.2.2.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1,
              x.2.2.2.2.1 +
                {Item.dir
                    { cmd := x.2.2.2.2.2.2.2.2.2.2.2.2, ptr := x.2.1, exGntd := false, shr := x.2.2.1,
                      inv := x.2.2.2.1 }}),
            x.2.2.2.2.2.2.2.2.2.2.2.2, x.2.1, x.2.2.1, x.2.2.2.1,
            x.2.2.2.2.1 +
                {Item.cache
                    { id := x.1, state := x.2.2.2.2.2.1, ch1 := x.2.2.2.2.2.2.1, ch2 := Gnt.noGnt,
                      ch3 := x.2.2.2.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.cmdE, ptr := x.2.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.2.1,
                    shr := x.2.2.2.2.2.2.2.2.2.2.1, inv := {x.1} + x.2.2.2.2.2.2.2.2.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × CacheState × Req × Ack × ℕ × Oids) =>
          ((x.2.2.2.2.1, false, x.2.2.2.2.2, x.1, ∅, x.2.1, x.2.2.1, x.2.2.2.1, ∅), Cmd.cmdE, x.2.2.2.2.1, x.2.2.2.2.2,
            {x.1}, {Item.cache { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × CacheState × Req × Ack × Oids × ℕ × Oids) =>
          ((x.2.2.2.2.2.1, false, x.2.2.2.2.2.2, x.1, x.2.2.2.2.1, x.2.1, x.2.2.1, x.2.2.2.1, ∅), Cmd.cmdE,
            x.2.2.2.2.2.1, x.2.2.2.2.2.2, {x.1} + x.2.2.2.2.1,
            {Item.cache { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : Items × ℕ × CacheState × Req × Ack × ℕ × Oids) =>
          ((x.2.2.2.2.2.1, false, x.2.2.2.2.2.2, x.2.1, ∅, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.1), Cmd.cmdE,
            x.2.2.2.2.2.1, x.2.2.2.2.2.2, {x.2.1},
            x.1 +
              {Item.cache { id := x.2.1, state := x.2.2.1, ch1 := x.2.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : Items × ℕ × CacheState × Req × Ack × Oids × ℕ × Oids) =>
          ((x.2.2.2.2.2.2.1, false, x.2.2.2.2.2.2.2, x.2.1, x.2.2.2.2.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.1),
            Cmd.cmdE, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2, {x.2.1} + x.2.2.2.2.2.1,
            x.1 +
              {Item.cache
                  { id := x.2.1, state := x.2.2.1, ch1 := x.2.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.2.1 }})] := by
  sorry

theorem sendInvE_inv.obligation_3 :
    Unification.complete (Narrowing.mayFire sendInvE ownE)
      [Unification.Unifier.bind fun (x : ℕ × Cmd × ℕ × Oids × CacheState × Req × Ack × ℕ × Bool × Oids × ℕ × Req) =>
          ((x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.1, ∅, x.2.2.2.2.1, x.2.2.2.2.2.1,
              x.2.2.2.2.2.2.1,
              {Item.cache
                    { id := x.2.2.2.2.2.2.2.2.2.2.1, state := CacheState.exclusive, ch1 := x.2.2.2.2.2.2.2.2.2.2.2,
                      ch2 := Gnt.noGnt, ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.1, ptr := x.2.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.2.2.1},
                      inv := x.2.2.2.1 }}),
            x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2,
            {Item.cache
                  { id := x.1, state := x.2.2.2.2.1, ch1 := x.2.2.2.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.cmdE, ptr := x.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.1,
                    shr := x.2.2.2.2.2.2.2.2.2.1, inv := {x.1} }}),
        Unification.Unifier.bind
          fun (x : ℕ × Req × Cmd × ℕ × Oids × CacheState × Req × Ack × ℕ × Bool × Oids × Oids × ℕ) =>
          ((x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.1, x.2.2.2.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1,
              {Item.cache
                    { id := x.2.2.2.2.2.2.2.2.2.2.2.2, state := CacheState.exclusive, ch1 := x.2.1, ch2 := Gnt.noGnt,
                      ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.1, ptr := x.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.2.2.2.2},
                      inv := x.2.2.2.2.1 }}),
            x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2, x.2.1,
            {Item.cache
                  { id := x.1, state := x.2.2.2.2.2.1, ch1 := x.2.2.2.2.2.2.1, ch2 := Gnt.noGnt,
                    ch3 := x.2.2.2.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.cmdE, ptr := x.2.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.2.1,
                    shr := x.2.2.2.2.2.2.2.2.2.2.1, inv := {x.1} + x.2.2.2.2.2.2.2.2.2.2.2.1 }}),
        Unification.Unifier.bind
          fun (x : ℕ × Cmd × ℕ × Oids × Items × CacheState × Req × Ack × ℕ × Bool × Oids × ℕ × Req) =>
          ((x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.1, ∅, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.2.1,
              x.2.2.2.2.1 +
                  {Item.cache
                      { id := x.2.2.2.2.2.2.2.2.2.2.2.1, state := CacheState.exclusive,
                        ch1 := x.2.2.2.2.2.2.2.2.2.2.2.2, ch2 := Gnt.noGnt, ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.1, ptr := x.2.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.2.2.2.1},
                      inv := x.2.2.2.1 }}),
            x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2,
            x.2.2.2.2.1 +
                {Item.cache
                    { id := x.1, state := x.2.2.2.2.2.1, ch1 := x.2.2.2.2.2.2.1, ch2 := Gnt.noGnt,
                      ch3 := x.2.2.2.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.cmdE, ptr := x.2.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.2.1,
                    shr := x.2.2.2.2.2.2.2.2.2.2.1, inv := {x.1} }}),
        Unification.Unifier.bind
          fun (x : ℕ × Req × Cmd × ℕ × Oids × Items × CacheState × Req × Ack × ℕ × Bool × Oids × Oids × ℕ) =>
          ((x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.1, x.1, x.2.2.2.2.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.1 +
                  {Item.cache
                      { id := x.2.2.2.2.2.2.2.2.2.2.2.2.2, state := CacheState.exclusive, ch1 := x.2.1,
                        ch2 := Gnt.noGnt, ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.1, ptr := x.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.2.2.2.2.2},
                      inv := x.2.2.2.2.1 }}),
            x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2.2, x.2.1,
            x.2.2.2.2.2.1 +
                {Item.cache
                    { id := x.1, state := x.2.2.2.2.2.2.1, ch1 := x.2.2.2.2.2.2.2.1, ch2 := Gnt.noGnt,
                      ch3 := x.2.2.2.2.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.cmdE, ptr := x.2.2.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.2.2.1,
                    shr := x.2.2.2.2.2.2.2.2.2.2.2.1, inv := {x.1} + x.2.2.2.2.2.2.2.2.2.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × Bool × Oids × ℕ × Req × Cmd × ℕ × Oids) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1, ∅, CacheState.exclusive, x.2.2.2.2.1, Ack.noAck,
              {Item.dir
                  { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.1},
                    inv := x.2.2.2.2.2.2.2 }}),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2, x.2.2.2.1, x.2.2.2.2.1,
            {Item.dir { cmd := Cmd.cmdE, ptr := x.1, exGntd := x.2.1, shr := x.2.2.1, inv := {x.2.2.2.1} }}),
        Unification.Unifier.bind fun (x : ℕ × Bool × Oids × Oids × ℕ × Req × Cmd × ℕ × Oids) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.2.1, x.2.2.2.1, CacheState.exclusive, x.2.2.2.2.2.1, Ack.noAck,
              {Item.dir
                  { cmd := x.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.1},
                    inv := x.2.2.2.2.2.2.2.2 }}),
            x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2, x.2.2.2.2.1, x.2.2.2.2.2.1,
            {Item.dir
                { cmd := Cmd.cmdE, ptr := x.1, exGntd := x.2.1, shr := x.2.2.1, inv := {x.2.2.2.2.1} + x.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × Bool × Oids × ℕ × Req × Cmd × ℕ × Oids × Items) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1, ∅, CacheState.exclusive, x.2.2.2.2.1, Ack.noAck,
              x.2.2.2.2.2.2.2.2 +
                {Item.dir
                    { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.1},
                      inv := x.2.2.2.2.2.2.2.1 }}),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
            x.2.2.2.2.2.2.2.2 +
              {Item.dir { cmd := Cmd.cmdE, ptr := x.1, exGntd := x.2.1, shr := x.2.2.1, inv := {x.2.2.2.1} }}),
        Unification.Unifier.bind fun (x : ℕ × Items × Bool × Oids × Oids × ℕ × Req × Cmd × ℕ × Oids) =>
          ((x.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.1, CacheState.exclusive, x.2.2.2.2.2.2.1, Ack.noAck,
              x.2.1 +
                {Item.dir
                    { cmd := x.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.2.1},
                      inv := x.2.2.2.2.2.2.2.2.2 }}),
            x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
            x.2.1 +
              {Item.dir
                  { cmd := Cmd.cmdE, ptr := x.1, exGntd := x.2.2.1, shr := x.2.2.2.1,
                    inv := {x.2.2.2.2.2.1} + x.2.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × CacheState × Req × Ack × ℕ × Req × ℕ) =>
          ((x.2.2.2.2.2.2, true, {x.2.2.2.2.1}, x.1, ∅, x.2.1, x.2.2.1, x.2.2.2.1,
              {Item.cache
                  { id := x.2.2.2.2.1, state := CacheState.exclusive, ch1 := x.2.2.2.2.2.1, ch2 := Gnt.noGnt,
                    ch3 := Ack.noAck }}),
            Cmd.cmdE, x.2.2.2.2.2.2, {x.1}, x.2.2.2.2.1, x.2.2.2.2.2.1,
            {Item.cache { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × CacheState × Req × Ack × Oids × ℕ × Req × ℕ) =>
          ((x.2.2.2.2.2.2.2, true, {x.2.2.2.2.2.1}, x.1, x.2.2.2.2.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {Item.cache
                  { id := x.2.2.2.2.2.1, state := CacheState.exclusive, ch1 := x.2.2.2.2.2.2.1, ch2 := Gnt.noGnt,
                    ch3 := Ack.noAck }}),
            Cmd.cmdE, x.2.2.2.2.2.2.2, {x.1} + x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
            {Item.cache { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × CacheState × Req × Ack × ℕ × Req × ℕ × Items) =>
          ((x.2.2.2.2.2.2.1, true, {x.2.2.2.2.1}, x.1, ∅, x.2.1, x.2.2.1, x.2.2.2.1,
              x.2.2.2.2.2.2.2 +
                {Item.cache
                    { id := x.2.2.2.2.1, state := CacheState.exclusive, ch1 := x.2.2.2.2.2.1, ch2 := Gnt.noGnt,
                      ch3 := Ack.noAck }}),
            Cmd.cmdE, x.2.2.2.2.2.2.1, {x.1}, x.2.2.2.2.1, x.2.2.2.2.2.1,
            x.2.2.2.2.2.2.2 +
              {Item.cache { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × CacheState × Req × Ack × Oids × ℕ × Req × ℕ × Items) =>
          ((x.2.2.2.2.2.2.2.1, true, {x.2.2.2.2.2.1}, x.1, x.2.2.2.2.1, x.2.1, x.2.2.1, x.2.2.2.1,
              x.2.2.2.2.2.2.2.2 +
                {Item.cache
                    { id := x.2.2.2.2.2.1, state := CacheState.exclusive, ch1 := x.2.2.2.2.2.2.1, ch2 := Gnt.noGnt,
                      ch3 := Ack.noAck }}),
            Cmd.cmdE, x.2.2.2.2.2.2.2.1, {x.1} + x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
            x.2.2.2.2.2.2.2.2 +
              {Item.cache { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × Req × ℕ) =>
          ((x.2.2, true, {x.1}, x.1, ∅, CacheState.exclusive, x.2.1, Ack.noAck, ∅), Cmd.cmdE, x.2.2, {x.1}, x.1, x.2.1,
            ∅),
        Unification.Unifier.bind fun (x : Oids × ℕ × Req × ℕ) =>
          ((x.2.2.2, true, {x.2.1}, x.2.1, x.1, CacheState.exclusive, x.2.2.1, Ack.noAck, ∅), Cmd.cmdE, x.2.2.2,
            {x.2.1} + x.1, x.2.1, x.2.2.1, ∅),
        Unification.Unifier.bind fun (x : Items × ℕ × Req × ℕ) =>
          ((x.2.2.2, true, {x.2.1}, x.2.1, ∅, CacheState.exclusive, x.2.2.1, Ack.noAck, x.1), Cmd.cmdE, x.2.2.2,
            {x.2.1}, x.2.1, x.2.2.1, x.1),
        Unification.Unifier.bind fun (x : Oids × Items × ℕ × Req × ℕ) =>
          ((x.2.2.2.2, true, {x.2.2.1}, x.2.2.1, x.1, CacheState.exclusive, x.2.2.2.1, Ack.noAck, x.2.1), Cmd.cmdE,
            x.2.2.2.2, {x.2.2.1} + x.1, x.2.2.1, x.2.2.2.1, x.2.1)] := by
  maude_certify_comp

theorem sendInvE_inv.obligation_4 :
    Unification.sound (Narrowing.mayFire sendInvE ownE)
      [Unification.Unifier.bind fun (x : ℕ × Cmd × ℕ × Oids × CacheState × Req × Ack × ℕ × Bool × Oids × ℕ × Req) =>
          ((x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.1, ∅, x.2.2.2.2.1, x.2.2.2.2.2.1,
              x.2.2.2.2.2.2.1,
              {Item.cache
                    { id := x.2.2.2.2.2.2.2.2.2.2.1, state := CacheState.exclusive, ch1 := x.2.2.2.2.2.2.2.2.2.2.2,
                      ch2 := Gnt.noGnt, ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.1, ptr := x.2.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.2.2.1},
                      inv := x.2.2.2.1 }}),
            x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2,
            {Item.cache
                  { id := x.1, state := x.2.2.2.2.1, ch1 := x.2.2.2.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.cmdE, ptr := x.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.1,
                    shr := x.2.2.2.2.2.2.2.2.2.1, inv := {x.1} }}),
        Unification.Unifier.bind
          fun (x : ℕ × Req × Cmd × ℕ × Oids × CacheState × Req × Ack × ℕ × Bool × Oids × Oids × ℕ) =>
          ((x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.1, x.2.2.2.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1,
              {Item.cache
                    { id := x.2.2.2.2.2.2.2.2.2.2.2.2, state := CacheState.exclusive, ch1 := x.2.1, ch2 := Gnt.noGnt,
                      ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.1, ptr := x.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.2.2.2.2},
                      inv := x.2.2.2.2.1 }}),
            x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2, x.2.1,
            {Item.cache
                  { id := x.1, state := x.2.2.2.2.2.1, ch1 := x.2.2.2.2.2.2.1, ch2 := Gnt.noGnt,
                    ch3 := x.2.2.2.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.cmdE, ptr := x.2.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.2.1,
                    shr := x.2.2.2.2.2.2.2.2.2.2.1, inv := {x.1} + x.2.2.2.2.2.2.2.2.2.2.2.1 }}),
        Unification.Unifier.bind
          fun (x : ℕ × Cmd × ℕ × Oids × Items × CacheState × Req × Ack × ℕ × Bool × Oids × ℕ × Req) =>
          ((x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.1, ∅, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.2.1,
              x.2.2.2.2.1 +
                  {Item.cache
                      { id := x.2.2.2.2.2.2.2.2.2.2.2.1, state := CacheState.exclusive,
                        ch1 := x.2.2.2.2.2.2.2.2.2.2.2.2, ch2 := Gnt.noGnt, ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.1, ptr := x.2.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.2.2.2.1},
                      inv := x.2.2.2.1 }}),
            x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2,
            x.2.2.2.2.1 +
                {Item.cache
                    { id := x.1, state := x.2.2.2.2.2.1, ch1 := x.2.2.2.2.2.2.1, ch2 := Gnt.noGnt,
                      ch3 := x.2.2.2.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.cmdE, ptr := x.2.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.2.1,
                    shr := x.2.2.2.2.2.2.2.2.2.2.1, inv := {x.1} }}),
        Unification.Unifier.bind
          fun (x : ℕ × Req × Cmd × ℕ × Oids × Items × CacheState × Req × Ack × ℕ × Bool × Oids × Oids × ℕ) =>
          ((x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.1, x.1, x.2.2.2.2.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.1 +
                  {Item.cache
                      { id := x.2.2.2.2.2.2.2.2.2.2.2.2.2, state := CacheState.exclusive, ch1 := x.2.1,
                        ch2 := Gnt.noGnt, ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.1, ptr := x.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.2.2.2.2.2},
                      inv := x.2.2.2.2.1 }}),
            x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2.2, x.2.1,
            x.2.2.2.2.2.1 +
                {Item.cache
                    { id := x.1, state := x.2.2.2.2.2.2.1, ch1 := x.2.2.2.2.2.2.2.1, ch2 := Gnt.noGnt,
                      ch3 := x.2.2.2.2.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.cmdE, ptr := x.2.2.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.2.2.1,
                    shr := x.2.2.2.2.2.2.2.2.2.2.2.1, inv := {x.1} + x.2.2.2.2.2.2.2.2.2.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × Bool × Oids × ℕ × Req × Cmd × ℕ × Oids) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1, ∅, CacheState.exclusive, x.2.2.2.2.1, Ack.noAck,
              {Item.dir
                  { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.1},
                    inv := x.2.2.2.2.2.2.2 }}),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2, x.2.2.2.1, x.2.2.2.2.1,
            {Item.dir { cmd := Cmd.cmdE, ptr := x.1, exGntd := x.2.1, shr := x.2.2.1, inv := {x.2.2.2.1} }}),
        Unification.Unifier.bind fun (x : ℕ × Bool × Oids × Oids × ℕ × Req × Cmd × ℕ × Oids) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.2.1, x.2.2.2.1, CacheState.exclusive, x.2.2.2.2.2.1, Ack.noAck,
              {Item.dir
                  { cmd := x.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.1},
                    inv := x.2.2.2.2.2.2.2.2 }}),
            x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2, x.2.2.2.2.1, x.2.2.2.2.2.1,
            {Item.dir
                { cmd := Cmd.cmdE, ptr := x.1, exGntd := x.2.1, shr := x.2.2.1, inv := {x.2.2.2.2.1} + x.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × Bool × Oids × ℕ × Req × Cmd × ℕ × Oids × Items) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1, ∅, CacheState.exclusive, x.2.2.2.2.1, Ack.noAck,
              x.2.2.2.2.2.2.2.2 +
                {Item.dir
                    { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.1},
                      inv := x.2.2.2.2.2.2.2.1 }}),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
            x.2.2.2.2.2.2.2.2 +
              {Item.dir { cmd := Cmd.cmdE, ptr := x.1, exGntd := x.2.1, shr := x.2.2.1, inv := {x.2.2.2.1} }}),
        Unification.Unifier.bind fun (x : ℕ × Items × Bool × Oids × Oids × ℕ × Req × Cmd × ℕ × Oids) =>
          ((x.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.1, CacheState.exclusive, x.2.2.2.2.2.2.1, Ack.noAck,
              x.2.1 +
                {Item.dir
                    { cmd := x.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.2.1},
                      inv := x.2.2.2.2.2.2.2.2.2 }}),
            x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
            x.2.1 +
              {Item.dir
                  { cmd := Cmd.cmdE, ptr := x.1, exGntd := x.2.2.1, shr := x.2.2.2.1,
                    inv := {x.2.2.2.2.2.1} + x.2.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × CacheState × Req × Ack × ℕ × Req × ℕ) =>
          ((x.2.2.2.2.2.2, true, {x.2.2.2.2.1}, x.1, ∅, x.2.1, x.2.2.1, x.2.2.2.1,
              {Item.cache
                  { id := x.2.2.2.2.1, state := CacheState.exclusive, ch1 := x.2.2.2.2.2.1, ch2 := Gnt.noGnt,
                    ch3 := Ack.noAck }}),
            Cmd.cmdE, x.2.2.2.2.2.2, {x.1}, x.2.2.2.2.1, x.2.2.2.2.2.1,
            {Item.cache { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × CacheState × Req × Ack × Oids × ℕ × Req × ℕ) =>
          ((x.2.2.2.2.2.2.2, true, {x.2.2.2.2.2.1}, x.1, x.2.2.2.2.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {Item.cache
                  { id := x.2.2.2.2.2.1, state := CacheState.exclusive, ch1 := x.2.2.2.2.2.2.1, ch2 := Gnt.noGnt,
                    ch3 := Ack.noAck }}),
            Cmd.cmdE, x.2.2.2.2.2.2.2, {x.1} + x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
            {Item.cache { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × CacheState × Req × Ack × ℕ × Req × ℕ × Items) =>
          ((x.2.2.2.2.2.2.1, true, {x.2.2.2.2.1}, x.1, ∅, x.2.1, x.2.2.1, x.2.2.2.1,
              x.2.2.2.2.2.2.2 +
                {Item.cache
                    { id := x.2.2.2.2.1, state := CacheState.exclusive, ch1 := x.2.2.2.2.2.1, ch2 := Gnt.noGnt,
                      ch3 := Ack.noAck }}),
            Cmd.cmdE, x.2.2.2.2.2.2.1, {x.1}, x.2.2.2.2.1, x.2.2.2.2.2.1,
            x.2.2.2.2.2.2.2 +
              {Item.cache { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × CacheState × Req × Ack × Oids × ℕ × Req × ℕ × Items) =>
          ((x.2.2.2.2.2.2.2.1, true, {x.2.2.2.2.2.1}, x.1, x.2.2.2.2.1, x.2.1, x.2.2.1, x.2.2.2.1,
              x.2.2.2.2.2.2.2.2 +
                {Item.cache
                    { id := x.2.2.2.2.2.1, state := CacheState.exclusive, ch1 := x.2.2.2.2.2.2.1, ch2 := Gnt.noGnt,
                      ch3 := Ack.noAck }}),
            Cmd.cmdE, x.2.2.2.2.2.2.2.1, {x.1} + x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
            x.2.2.2.2.2.2.2.2 +
              {Item.cache { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × Req × ℕ) =>
          ((x.2.2, true, {x.1}, x.1, ∅, CacheState.exclusive, x.2.1, Ack.noAck, ∅), Cmd.cmdE, x.2.2, {x.1}, x.1, x.2.1,
            ∅),
        Unification.Unifier.bind fun (x : Oids × ℕ × Req × ℕ) =>
          ((x.2.2.2, true, {x.2.1}, x.2.1, x.1, CacheState.exclusive, x.2.2.1, Ack.noAck, ∅), Cmd.cmdE, x.2.2.2,
            {x.2.1} + x.1, x.2.1, x.2.2.1, ∅),
        Unification.Unifier.bind fun (x : Items × ℕ × Req × ℕ) =>
          ((x.2.2.2, true, {x.2.1}, x.2.1, ∅, CacheState.exclusive, x.2.2.1, Ack.noAck, x.1), Cmd.cmdE, x.2.2.2,
            {x.2.1}, x.2.1, x.2.2.1, x.1),
        Unification.Unifier.bind fun (x : Oids × Items × ℕ × Req × ℕ) =>
          ((x.2.2.2.2, true, {x.2.2.1}, x.2.2.1, x.1, CacheState.exclusive, x.2.2.2.1, Ack.noAck, x.2.1), Cmd.cmdE,
            x.2.2.2.2, {x.2.2.1} + x.1, x.2.2.1, x.2.2.2.1, x.2.1)] := by
  sorry

theorem sendInvE_inv.obligation_5 :
    Unification.complete (Narrowing.mayFire sendInvE ownG)
      [Unification.Unifier.bind fun (x : ℕ × Cmd × ℕ × Oids × CacheState × Req × Ack × ℕ × Bool × Oids × ℕ × Req) =>
          ((x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.1, ∅, x.2.2.2.2.1, x.2.2.2.2.2.1,
              x.2.2.2.2.2.2.1,
              {Item.cache
                    { id := x.2.2.2.2.2.2.2.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.2.2.2.2.2.2.2,
                      ch2 := Gnt.gntE, ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.1, ptr := x.2.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.2.2.1},
                      inv := x.2.2.2.1 }}),
            x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2,
            {Item.cache
                  { id := x.1, state := x.2.2.2.2.1, ch1 := x.2.2.2.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.cmdE, ptr := x.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.1,
                    shr := x.2.2.2.2.2.2.2.2.2.1, inv := {x.1} }}),
        Unification.Unifier.bind
          fun (x : ℕ × Req × Cmd × ℕ × Oids × CacheState × Req × Ack × ℕ × Bool × Oids × Oids × ℕ) =>
          ((x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.1, x.2.2.2.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1,
              {Item.cache
                    { id := x.2.2.2.2.2.2.2.2.2.2.2.2, state := CacheState.invalid, ch1 := x.2.1, ch2 := Gnt.gntE,
                      ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.1, ptr := x.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.2.2.2.2},
                      inv := x.2.2.2.2.1 }}),
            x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2, x.2.1,
            {Item.cache
                  { id := x.1, state := x.2.2.2.2.2.1, ch1 := x.2.2.2.2.2.2.1, ch2 := Gnt.noGnt,
                    ch3 := x.2.2.2.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.cmdE, ptr := x.2.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.2.1,
                    shr := x.2.2.2.2.2.2.2.2.2.2.1, inv := {x.1} + x.2.2.2.2.2.2.2.2.2.2.2.1 }}),
        Unification.Unifier.bind
          fun (x : ℕ × Cmd × ℕ × Oids × Items × CacheState × Req × Ack × ℕ × Bool × Oids × ℕ × Req) =>
          ((x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.1, ∅, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.2.1,
              x.2.2.2.2.1 +
                  {Item.cache
                      { id := x.2.2.2.2.2.2.2.2.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.2.2.2.2.2.2.2.2,
                        ch2 := Gnt.gntE, ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.1, ptr := x.2.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.2.2.2.1},
                      inv := x.2.2.2.1 }}),
            x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2,
            x.2.2.2.2.1 +
                {Item.cache
                    { id := x.1, state := x.2.2.2.2.2.1, ch1 := x.2.2.2.2.2.2.1, ch2 := Gnt.noGnt,
                      ch3 := x.2.2.2.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.cmdE, ptr := x.2.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.2.1,
                    shr := x.2.2.2.2.2.2.2.2.2.2.1, inv := {x.1} }}),
        Unification.Unifier.bind
          fun (x : ℕ × Req × Cmd × ℕ × Oids × Items × CacheState × Req × Ack × ℕ × Bool × Oids × Oids × ℕ) =>
          ((x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.1, x.1, x.2.2.2.2.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.1 +
                  {Item.cache
                      { id := x.2.2.2.2.2.2.2.2.2.2.2.2.2, state := CacheState.invalid, ch1 := x.2.1, ch2 := Gnt.gntE,
                        ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.1, ptr := x.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.2.2.2.2.2},
                      inv := x.2.2.2.2.1 }}),
            x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2.2, x.2.1,
            x.2.2.2.2.2.1 +
                {Item.cache
                    { id := x.1, state := x.2.2.2.2.2.2.1, ch1 := x.2.2.2.2.2.2.2.1, ch2 := Gnt.noGnt,
                      ch3 := x.2.2.2.2.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.cmdE, ptr := x.2.2.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.2.2.1,
                    shr := x.2.2.2.2.2.2.2.2.2.2.2.1, inv := {x.1} + x.2.2.2.2.2.2.2.2.2.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × CacheState × Req × Ack × ℕ × Req × ℕ) =>
          ((x.2.2.2.2.2.2, true, {x.2.2.2.2.1}, x.1, ∅, x.2.1, x.2.2.1, x.2.2.2.1,
              {Item.cache
                  { id := x.2.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.2.1, ch2 := Gnt.gntE,
                    ch3 := Ack.noAck }}),
            Cmd.cmdE, x.2.2.2.2.2.2, {x.1}, x.2.2.2.2.1, x.2.2.2.2.2.1,
            {Item.cache { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × CacheState × Req × Ack × Oids × ℕ × Req × ℕ) =>
          ((x.2.2.2.2.2.2.2, true, {x.2.2.2.2.2.1}, x.1, x.2.2.2.2.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {Item.cache
                  { id := x.2.2.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.2.2.1, ch2 := Gnt.gntE,
                    ch3 := Ack.noAck }}),
            Cmd.cmdE, x.2.2.2.2.2.2.2, {x.1} + x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
            {Item.cache { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × CacheState × Req × Ack × ℕ × Req × ℕ × Items) =>
          ((x.2.2.2.2.2.2.1, true, {x.2.2.2.2.1}, x.1, ∅, x.2.1, x.2.2.1, x.2.2.2.1,
              x.2.2.2.2.2.2.2 +
                {Item.cache
                    { id := x.2.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.2.1, ch2 := Gnt.gntE,
                      ch3 := Ack.noAck }}),
            Cmd.cmdE, x.2.2.2.2.2.2.1, {x.1}, x.2.2.2.2.1, x.2.2.2.2.2.1,
            x.2.2.2.2.2.2.2 +
              {Item.cache { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × CacheState × Req × Ack × Oids × ℕ × Req × ℕ × Items) =>
          ((x.2.2.2.2.2.2.2.1, true, {x.2.2.2.2.2.1}, x.1, x.2.2.2.2.1, x.2.1, x.2.2.1, x.2.2.2.1,
              x.2.2.2.2.2.2.2.2 +
                {Item.cache
                    { id := x.2.2.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.2.2.1, ch2 := Gnt.gntE,
                      ch3 := Ack.noAck }}),
            Cmd.cmdE, x.2.2.2.2.2.2.2.1, {x.1} + x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
            x.2.2.2.2.2.2.2.2 +
              {Item.cache { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.1 }})] := by
  maude_certify_comp

theorem sendInvE_inv.obligation_6 :
    Unification.sound (Narrowing.mayFire sendInvE ownG)
      [Unification.Unifier.bind fun (x : ℕ × Cmd × ℕ × Oids × CacheState × Req × Ack × ℕ × Bool × Oids × ℕ × Req) =>
          ((x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.1, ∅, x.2.2.2.2.1, x.2.2.2.2.2.1,
              x.2.2.2.2.2.2.1,
              {Item.cache
                    { id := x.2.2.2.2.2.2.2.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.2.2.2.2.2.2.2,
                      ch2 := Gnt.gntE, ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.1, ptr := x.2.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.2.2.1},
                      inv := x.2.2.2.1 }}),
            x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2,
            {Item.cache
                  { id := x.1, state := x.2.2.2.2.1, ch1 := x.2.2.2.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.cmdE, ptr := x.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.1,
                    shr := x.2.2.2.2.2.2.2.2.2.1, inv := {x.1} }}),
        Unification.Unifier.bind
          fun (x : ℕ × Req × Cmd × ℕ × Oids × CacheState × Req × Ack × ℕ × Bool × Oids × Oids × ℕ) =>
          ((x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.1, x.2.2.2.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1,
              {Item.cache
                    { id := x.2.2.2.2.2.2.2.2.2.2.2.2, state := CacheState.invalid, ch1 := x.2.1, ch2 := Gnt.gntE,
                      ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.1, ptr := x.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.2.2.2.2},
                      inv := x.2.2.2.2.1 }}),
            x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2, x.2.1,
            {Item.cache
                  { id := x.1, state := x.2.2.2.2.2.1, ch1 := x.2.2.2.2.2.2.1, ch2 := Gnt.noGnt,
                    ch3 := x.2.2.2.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.cmdE, ptr := x.2.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.2.1,
                    shr := x.2.2.2.2.2.2.2.2.2.2.1, inv := {x.1} + x.2.2.2.2.2.2.2.2.2.2.2.1 }}),
        Unification.Unifier.bind
          fun (x : ℕ × Cmd × ℕ × Oids × Items × CacheState × Req × Ack × ℕ × Bool × Oids × ℕ × Req) =>
          ((x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.1, ∅, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.2.1,
              x.2.2.2.2.1 +
                  {Item.cache
                      { id := x.2.2.2.2.2.2.2.2.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.2.2.2.2.2.2.2.2,
                        ch2 := Gnt.gntE, ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.1, ptr := x.2.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.2.2.2.1},
                      inv := x.2.2.2.1 }}),
            x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2,
            x.2.2.2.2.1 +
                {Item.cache
                    { id := x.1, state := x.2.2.2.2.2.1, ch1 := x.2.2.2.2.2.2.1, ch2 := Gnt.noGnt,
                      ch3 := x.2.2.2.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.cmdE, ptr := x.2.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.2.1,
                    shr := x.2.2.2.2.2.2.2.2.2.2.1, inv := {x.1} }}),
        Unification.Unifier.bind
          fun (x : ℕ × Req × Cmd × ℕ × Oids × Items × CacheState × Req × Ack × ℕ × Bool × Oids × Oids × ℕ) =>
          ((x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.1, x.1, x.2.2.2.2.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.1 +
                  {Item.cache
                      { id := x.2.2.2.2.2.2.2.2.2.2.2.2.2, state := CacheState.invalid, ch1 := x.2.1, ch2 := Gnt.gntE,
                        ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.1, ptr := x.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.2.2.2.2.2},
                      inv := x.2.2.2.2.1 }}),
            x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2.2, x.2.1,
            x.2.2.2.2.2.1 +
                {Item.cache
                    { id := x.1, state := x.2.2.2.2.2.2.1, ch1 := x.2.2.2.2.2.2.2.1, ch2 := Gnt.noGnt,
                      ch3 := x.2.2.2.2.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.cmdE, ptr := x.2.2.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.2.2.1,
                    shr := x.2.2.2.2.2.2.2.2.2.2.2.1, inv := {x.1} + x.2.2.2.2.2.2.2.2.2.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × CacheState × Req × Ack × ℕ × Req × ℕ) =>
          ((x.2.2.2.2.2.2, true, {x.2.2.2.2.1}, x.1, ∅, x.2.1, x.2.2.1, x.2.2.2.1,
              {Item.cache
                  { id := x.2.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.2.1, ch2 := Gnt.gntE,
                    ch3 := Ack.noAck }}),
            Cmd.cmdE, x.2.2.2.2.2.2, {x.1}, x.2.2.2.2.1, x.2.2.2.2.2.1,
            {Item.cache { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × CacheState × Req × Ack × Oids × ℕ × Req × ℕ) =>
          ((x.2.2.2.2.2.2.2, true, {x.2.2.2.2.2.1}, x.1, x.2.2.2.2.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {Item.cache
                  { id := x.2.2.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.2.2.1, ch2 := Gnt.gntE,
                    ch3 := Ack.noAck }}),
            Cmd.cmdE, x.2.2.2.2.2.2.2, {x.1} + x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
            {Item.cache { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × CacheState × Req × Ack × ℕ × Req × ℕ × Items) =>
          ((x.2.2.2.2.2.2.1, true, {x.2.2.2.2.1}, x.1, ∅, x.2.1, x.2.2.1, x.2.2.2.1,
              x.2.2.2.2.2.2.2 +
                {Item.cache
                    { id := x.2.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.2.1, ch2 := Gnt.gntE,
                      ch3 := Ack.noAck }}),
            Cmd.cmdE, x.2.2.2.2.2.2.1, {x.1}, x.2.2.2.2.1, x.2.2.2.2.2.1,
            x.2.2.2.2.2.2.2 +
              {Item.cache { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × CacheState × Req × Ack × Oids × ℕ × Req × ℕ × Items) =>
          ((x.2.2.2.2.2.2.2.1, true, {x.2.2.2.2.2.1}, x.1, x.2.2.2.2.1, x.2.1, x.2.2.1, x.2.2.2.1,
              x.2.2.2.2.2.2.2.2 +
                {Item.cache
                    { id := x.2.2.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.2.2.1, ch2 := Gnt.gntE,
                      ch3 := Ack.noAck }}),
            Cmd.cmdE, x.2.2.2.2.2.2.2.1, {x.1} + x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
            x.2.2.2.2.2.2.2.2 +
              {Item.cache { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.1 }})] := by
  sorry

theorem sendInvE_inv.obligation_7 :
    Unification.complete (Narrowing.mayFire sendInvE ownInv)
      [Unification.Unifier.bind fun (x : ℕ × Cmd × ℕ × CacheState × Req × Ack × ℕ × Bool × Oids × ℕ × Req) =>
          ((x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1, x.1, ∅, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
              {Item.cache
                    { id := x.2.2.2.2.2.2.2.2.2.1, state := CacheState.exclusive, ch1 := x.2.2.2.2.2.2.2.2.2.2,
                      ch2 := Gnt.inv, ch3 := Ack.noAck }} +
                {Item.dir { cmd := x.2.1, ptr := x.2.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.2.1}, inv := ∅ }}),
            x.2.1, x.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2,
            {Item.cache { id := x.1, state := x.2.2.2.1, ch1 := x.2.2.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.cmdE, ptr := x.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.1, shr := x.2.2.2.2.2.2.2.2.1,
                    inv := {x.1} }}),
        Unification.Unifier.bind fun (x : ℕ × Req × Cmd × ℕ × CacheState × Req × Ack × ℕ × Bool × Oids × Oids × ℕ) =>
          ((x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.1,
              x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
              {Item.cache
                    { id := x.2.2.2.2.2.2.2.2.2.2.2, state := CacheState.exclusive, ch1 := x.2.1, ch2 := Gnt.inv,
                      ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.1, ptr := x.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.2.2.2}, inv := ∅ }}),
            x.2.2.1, x.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2, x.2.1,
            {Item.cache
                  { id := x.1, state := x.2.2.2.2.1, ch1 := x.2.2.2.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.cmdE, ptr := x.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.1,
                    shr := x.2.2.2.2.2.2.2.2.2.1, inv := {x.1} + x.2.2.2.2.2.2.2.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × Cmd × ℕ × Items × CacheState × Req × Ack × ℕ × Bool × Oids × ℕ × Req) =>
          ((x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.1, ∅, x.2.2.2.2.1, x.2.2.2.2.2.1,
              x.2.2.2.2.2.2.1,
              x.2.2.2.1 +
                  {Item.cache
                      { id := x.2.2.2.2.2.2.2.2.2.2.1, state := CacheState.exclusive, ch1 := x.2.2.2.2.2.2.2.2.2.2.2,
                        ch2 := Gnt.inv, ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.1, ptr := x.2.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.2.2.1}, inv := ∅ }}),
            x.2.1, x.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2,
            x.2.2.2.1 +
                {Item.cache
                    { id := x.1, state := x.2.2.2.2.1, ch1 := x.2.2.2.2.2.1, ch2 := Gnt.noGnt,
                      ch3 := x.2.2.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.cmdE, ptr := x.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.1,
                    shr := x.2.2.2.2.2.2.2.2.2.1, inv := {x.1} }}),
        Unification.Unifier.bind
          fun (x : ℕ × Req × Cmd × ℕ × Items × CacheState × Req × Ack × ℕ × Bool × Oids × Oids × ℕ) =>
          ((x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.1, x.2.2.2.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1,
              x.2.2.2.2.1 +
                  {Item.cache
                      { id := x.2.2.2.2.2.2.2.2.2.2.2.2, state := CacheState.exclusive, ch1 := x.2.1, ch2 := Gnt.inv,
                        ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.1, ptr := x.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.2.2.2.2},
                      inv := ∅ }}),
            x.2.2.1, x.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2, x.2.1,
            x.2.2.2.2.1 +
                {Item.cache
                    { id := x.1, state := x.2.2.2.2.2.1, ch1 := x.2.2.2.2.2.2.1, ch2 := Gnt.noGnt,
                      ch3 := x.2.2.2.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.cmdE, ptr := x.2.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.2.1,
                    shr := x.2.2.2.2.2.2.2.2.2.2.1, inv := {x.1} + x.2.2.2.2.2.2.2.2.2.2.2.1 }})] := by
  maude_certify_comp

theorem sendInvE_inv.obligation_8 :
    Unification.sound (Narrowing.mayFire sendInvE ownInv)
      [Unification.Unifier.bind fun (x : ℕ × Cmd × ℕ × CacheState × Req × Ack × ℕ × Bool × Oids × ℕ × Req) =>
          ((x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1, x.1, ∅, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
              {Item.cache
                    { id := x.2.2.2.2.2.2.2.2.2.1, state := CacheState.exclusive, ch1 := x.2.2.2.2.2.2.2.2.2.2,
                      ch2 := Gnt.inv, ch3 := Ack.noAck }} +
                {Item.dir { cmd := x.2.1, ptr := x.2.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.2.1}, inv := ∅ }}),
            x.2.1, x.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2,
            {Item.cache { id := x.1, state := x.2.2.2.1, ch1 := x.2.2.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.cmdE, ptr := x.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.1, shr := x.2.2.2.2.2.2.2.2.1,
                    inv := {x.1} }}),
        Unification.Unifier.bind fun (x : ℕ × Req × Cmd × ℕ × CacheState × Req × Ack × ℕ × Bool × Oids × Oids × ℕ) =>
          ((x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.1,
              x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
              {Item.cache
                    { id := x.2.2.2.2.2.2.2.2.2.2.2, state := CacheState.exclusive, ch1 := x.2.1, ch2 := Gnt.inv,
                      ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.1, ptr := x.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.2.2.2}, inv := ∅ }}),
            x.2.2.1, x.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2, x.2.1,
            {Item.cache
                  { id := x.1, state := x.2.2.2.2.1, ch1 := x.2.2.2.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.cmdE, ptr := x.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.1,
                    shr := x.2.2.2.2.2.2.2.2.2.1, inv := {x.1} + x.2.2.2.2.2.2.2.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × Cmd × ℕ × Items × CacheState × Req × Ack × ℕ × Bool × Oids × ℕ × Req) =>
          ((x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.1, ∅, x.2.2.2.2.1, x.2.2.2.2.2.1,
              x.2.2.2.2.2.2.1,
              x.2.2.2.1 +
                  {Item.cache
                      { id := x.2.2.2.2.2.2.2.2.2.2.1, state := CacheState.exclusive, ch1 := x.2.2.2.2.2.2.2.2.2.2.2,
                        ch2 := Gnt.inv, ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.1, ptr := x.2.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.2.2.1}, inv := ∅ }}),
            x.2.1, x.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2,
            x.2.2.2.1 +
                {Item.cache
                    { id := x.1, state := x.2.2.2.2.1, ch1 := x.2.2.2.2.2.1, ch2 := Gnt.noGnt,
                      ch3 := x.2.2.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.cmdE, ptr := x.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.1,
                    shr := x.2.2.2.2.2.2.2.2.2.1, inv := {x.1} }}),
        Unification.Unifier.bind
          fun (x : ℕ × Req × Cmd × ℕ × Items × CacheState × Req × Ack × ℕ × Bool × Oids × Oids × ℕ) =>
          ((x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.1, x.2.2.2.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1,
              x.2.2.2.2.1 +
                  {Item.cache
                      { id := x.2.2.2.2.2.2.2.2.2.2.2.2, state := CacheState.exclusive, ch1 := x.2.1, ch2 := Gnt.inv,
                        ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.1, ptr := x.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.2.2.2.2},
                      inv := ∅ }}),
            x.2.2.1, x.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2, x.2.1,
            x.2.2.2.2.1 +
                {Item.cache
                    { id := x.1, state := x.2.2.2.2.2.1, ch1 := x.2.2.2.2.2.2.1, ch2 := Gnt.noGnt,
                      ch3 := x.2.2.2.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.cmdE, ptr := x.2.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.2.1,
                    shr := x.2.2.2.2.2.2.2.2.2.2.1, inv := {x.1} + x.2.2.2.2.2.2.2.2.2.2.2.1 }})] := by
  sorry

theorem sendInvE_inv.obligation_9 :
    Unification.complete (Narrowing.mayFire sendInvE ownAck)
      [Unification.Unifier.bind fun (x : ℕ × Cmd × ℕ × CacheState × Req × Ack × ℕ × Bool × Oids × ℕ × Req) =>
          ((x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1, x.1, ∅, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
              {Item.cache
                    { id := x.2.2.2.2.2.2.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.2.2.2.2.2.2,
                      ch2 := Gnt.noGnt, ch3 := Ack.invAck }} +
                {Item.dir { cmd := x.2.1, ptr := x.2.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.2.1}, inv := ∅ }}),
            x.2.1, x.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2,
            {Item.cache { id := x.1, state := x.2.2.2.1, ch1 := x.2.2.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.cmdE, ptr := x.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.1, shr := x.2.2.2.2.2.2.2.2.1,
                    inv := {x.1} }}),
        Unification.Unifier.bind fun (x : ℕ × Req × Cmd × ℕ × CacheState × Req × Ack × ℕ × Bool × Oids × Oids × ℕ) =>
          ((x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.1,
              x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
              {Item.cache
                    { id := x.2.2.2.2.2.2.2.2.2.2.2, state := CacheState.invalid, ch1 := x.2.1, ch2 := Gnt.noGnt,
                      ch3 := Ack.invAck }} +
                {Item.dir
                    { cmd := x.2.2.1, ptr := x.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.2.2.2}, inv := ∅ }}),
            x.2.2.1, x.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2, x.2.1,
            {Item.cache
                  { id := x.1, state := x.2.2.2.2.1, ch1 := x.2.2.2.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.cmdE, ptr := x.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.1,
                    shr := x.2.2.2.2.2.2.2.2.2.1, inv := {x.1} + x.2.2.2.2.2.2.2.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × Cmd × ℕ × Items × CacheState × Req × Ack × ℕ × Bool × Oids × ℕ × Req) =>
          ((x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.1, ∅, x.2.2.2.2.1, x.2.2.2.2.2.1,
              x.2.2.2.2.2.2.1,
              x.2.2.2.1 +
                  {Item.cache
                      { id := x.2.2.2.2.2.2.2.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.2.2.2.2.2.2.2,
                        ch2 := Gnt.noGnt, ch3 := Ack.invAck }} +
                {Item.dir
                    { cmd := x.2.1, ptr := x.2.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.2.2.1}, inv := ∅ }}),
            x.2.1, x.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2,
            x.2.2.2.1 +
                {Item.cache
                    { id := x.1, state := x.2.2.2.2.1, ch1 := x.2.2.2.2.2.1, ch2 := Gnt.noGnt,
                      ch3 := x.2.2.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.cmdE, ptr := x.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.1,
                    shr := x.2.2.2.2.2.2.2.2.2.1, inv := {x.1} }}),
        Unification.Unifier.bind
          fun (x : ℕ × Req × Cmd × ℕ × Items × CacheState × Req × Ack × ℕ × Bool × Oids × Oids × ℕ) =>
          ((x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.1, x.2.2.2.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1,
              x.2.2.2.2.1 +
                  {Item.cache
                      { id := x.2.2.2.2.2.2.2.2.2.2.2.2, state := CacheState.invalid, ch1 := x.2.1, ch2 := Gnt.noGnt,
                        ch3 := Ack.invAck }} +
                {Item.dir
                    { cmd := x.2.2.1, ptr := x.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.2.2.2.2},
                      inv := ∅ }}),
            x.2.2.1, x.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2, x.2.1,
            x.2.2.2.2.1 +
                {Item.cache
                    { id := x.1, state := x.2.2.2.2.2.1, ch1 := x.2.2.2.2.2.2.1, ch2 := Gnt.noGnt,
                      ch3 := x.2.2.2.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.cmdE, ptr := x.2.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.2.1,
                    shr := x.2.2.2.2.2.2.2.2.2.2.1, inv := {x.1} + x.2.2.2.2.2.2.2.2.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × Bool × Oids × ℕ × Req × Cmd × ℕ) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1, ∅, CacheState.invalid, x.2.2.2.2.1, Ack.invAck,
              {Item.dir { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2, exGntd := true, shr := {x.2.2.2.1}, inv := ∅ }}),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2, x.2.2.2.1, x.2.2.2.2.1,
            {Item.dir { cmd := Cmd.cmdE, ptr := x.1, exGntd := x.2.1, shr := x.2.2.1, inv := {x.2.2.2.1} }}),
        Unification.Unifier.bind fun (x : ℕ × Bool × Oids × Oids × ℕ × Req × Cmd × ℕ) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.2.1, x.2.2.2.1, CacheState.invalid, x.2.2.2.2.2.1, Ack.invAck,
              {Item.dir
                  { cmd := x.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2, exGntd := true, shr := {x.2.2.2.2.1}, inv := ∅ }}),
            x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2, x.2.2.2.2.1, x.2.2.2.2.2.1,
            {Item.dir
                { cmd := Cmd.cmdE, ptr := x.1, exGntd := x.2.1, shr := x.2.2.1, inv := {x.2.2.2.2.1} + x.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × Bool × Oids × ℕ × Req × Cmd × ℕ × Items) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1, ∅, CacheState.invalid, x.2.2.2.2.1, Ack.invAck,
              x.2.2.2.2.2.2.2 +
                {Item.dir
                    { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.1}, inv := ∅ }}),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
            x.2.2.2.2.2.2.2 +
              {Item.dir { cmd := Cmd.cmdE, ptr := x.1, exGntd := x.2.1, shr := x.2.2.1, inv := {x.2.2.2.1} }}),
        Unification.Unifier.bind fun (x : ℕ × Bool × Oids × Oids × ℕ × Req × Cmd × ℕ × Items) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.2.1, x.2.2.2.1, CacheState.invalid, x.2.2.2.2.2.1, Ack.invAck,
              x.2.2.2.2.2.2.2.2 +
                {Item.dir
                    { cmd := x.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.1},
                      inv := ∅ }}),
            x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
            x.2.2.2.2.2.2.2.2 +
              {Item.dir
                  { cmd := Cmd.cmdE, ptr := x.1, exGntd := x.2.1, shr := x.2.2.1,
                    inv := {x.2.2.2.2.1} + x.2.2.2.1 }})] := by
  maude_certify_comp

theorem sendInvE_inv.obligation_10 :
    Unification.sound (Narrowing.mayFire sendInvE ownAck)
      [Unification.Unifier.bind fun (x : ℕ × Cmd × ℕ × CacheState × Req × Ack × ℕ × Bool × Oids × ℕ × Req) =>
          ((x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1, x.1, ∅, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
              {Item.cache
                    { id := x.2.2.2.2.2.2.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.2.2.2.2.2.2,
                      ch2 := Gnt.noGnt, ch3 := Ack.invAck }} +
                {Item.dir { cmd := x.2.1, ptr := x.2.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.2.1}, inv := ∅ }}),
            x.2.1, x.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2,
            {Item.cache { id := x.1, state := x.2.2.2.1, ch1 := x.2.2.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.cmdE, ptr := x.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.1, shr := x.2.2.2.2.2.2.2.2.1,
                    inv := {x.1} }}),
        Unification.Unifier.bind fun (x : ℕ × Req × Cmd × ℕ × CacheState × Req × Ack × ℕ × Bool × Oids × Oids × ℕ) =>
          ((x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.1,
              x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
              {Item.cache
                    { id := x.2.2.2.2.2.2.2.2.2.2.2, state := CacheState.invalid, ch1 := x.2.1, ch2 := Gnt.noGnt,
                      ch3 := Ack.invAck }} +
                {Item.dir
                    { cmd := x.2.2.1, ptr := x.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.2.2.2}, inv := ∅ }}),
            x.2.2.1, x.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2, x.2.1,
            {Item.cache
                  { id := x.1, state := x.2.2.2.2.1, ch1 := x.2.2.2.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.cmdE, ptr := x.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.1,
                    shr := x.2.2.2.2.2.2.2.2.2.1, inv := {x.1} + x.2.2.2.2.2.2.2.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × Cmd × ℕ × Items × CacheState × Req × Ack × ℕ × Bool × Oids × ℕ × Req) =>
          ((x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.1, ∅, x.2.2.2.2.1, x.2.2.2.2.2.1,
              x.2.2.2.2.2.2.1,
              x.2.2.2.1 +
                  {Item.cache
                      { id := x.2.2.2.2.2.2.2.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.2.2.2.2.2.2.2,
                        ch2 := Gnt.noGnt, ch3 := Ack.invAck }} +
                {Item.dir
                    { cmd := x.2.1, ptr := x.2.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.2.2.1}, inv := ∅ }}),
            x.2.1, x.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2,
            x.2.2.2.1 +
                {Item.cache
                    { id := x.1, state := x.2.2.2.2.1, ch1 := x.2.2.2.2.2.1, ch2 := Gnt.noGnt,
                      ch3 := x.2.2.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.cmdE, ptr := x.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.1,
                    shr := x.2.2.2.2.2.2.2.2.2.1, inv := {x.1} }}),
        Unification.Unifier.bind
          fun (x : ℕ × Req × Cmd × ℕ × Items × CacheState × Req × Ack × ℕ × Bool × Oids × Oids × ℕ) =>
          ((x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.1, x.2.2.2.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1,
              x.2.2.2.2.1 +
                  {Item.cache
                      { id := x.2.2.2.2.2.2.2.2.2.2.2.2, state := CacheState.invalid, ch1 := x.2.1, ch2 := Gnt.noGnt,
                        ch3 := Ack.invAck }} +
                {Item.dir
                    { cmd := x.2.2.1, ptr := x.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.2.2.2.2},
                      inv := ∅ }}),
            x.2.2.1, x.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2, x.2.1,
            x.2.2.2.2.1 +
                {Item.cache
                    { id := x.1, state := x.2.2.2.2.2.1, ch1 := x.2.2.2.2.2.2.1, ch2 := Gnt.noGnt,
                      ch3 := x.2.2.2.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.cmdE, ptr := x.2.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.2.1,
                    shr := x.2.2.2.2.2.2.2.2.2.2.1, inv := {x.1} + x.2.2.2.2.2.2.2.2.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × Bool × Oids × ℕ × Req × Cmd × ℕ) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1, ∅, CacheState.invalid, x.2.2.2.2.1, Ack.invAck,
              {Item.dir { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2, exGntd := true, shr := {x.2.2.2.1}, inv := ∅ }}),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2, x.2.2.2.1, x.2.2.2.2.1,
            {Item.dir { cmd := Cmd.cmdE, ptr := x.1, exGntd := x.2.1, shr := x.2.2.1, inv := {x.2.2.2.1} }}),
        Unification.Unifier.bind fun (x : ℕ × Bool × Oids × Oids × ℕ × Req × Cmd × ℕ) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.2.1, x.2.2.2.1, CacheState.invalid, x.2.2.2.2.2.1, Ack.invAck,
              {Item.dir
                  { cmd := x.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2, exGntd := true, shr := {x.2.2.2.2.1}, inv := ∅ }}),
            x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2, x.2.2.2.2.1, x.2.2.2.2.2.1,
            {Item.dir
                { cmd := Cmd.cmdE, ptr := x.1, exGntd := x.2.1, shr := x.2.2.1, inv := {x.2.2.2.2.1} + x.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × Bool × Oids × ℕ × Req × Cmd × ℕ × Items) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1, ∅, CacheState.invalid, x.2.2.2.2.1, Ack.invAck,
              x.2.2.2.2.2.2.2 +
                {Item.dir
                    { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.1}, inv := ∅ }}),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
            x.2.2.2.2.2.2.2 +
              {Item.dir { cmd := Cmd.cmdE, ptr := x.1, exGntd := x.2.1, shr := x.2.2.1, inv := {x.2.2.2.1} }}),
        Unification.Unifier.bind fun (x : ℕ × Bool × Oids × Oids × ℕ × Req × Cmd × ℕ × Items) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.2.1, x.2.2.2.1, CacheState.invalid, x.2.2.2.2.2.1, Ack.invAck,
              x.2.2.2.2.2.2.2.2 +
                {Item.dir
                    { cmd := x.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.1},
                      inv := ∅ }}),
            x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
            x.2.2.2.2.2.2.2.2 +
              {Item.dir
                  { cmd := Cmd.cmdE, ptr := x.1, exGntd := x.2.1, shr := x.2.2.1,
                    inv := {x.2.2.2.2.1} + x.2.2.2.1 }})] := by
  sorry

theorem sendInvE_inv.obligation_17 :
    ∃ b ∈ inv, Expresso.subsumes [sendInvE_inv.post_10] [b] := by
  sorry

theorem sendInvE_inv.obligation_18 :
    ∃ b ∈ inv, Expresso.subsumes [sendInvE_inv.post_12] [b] := by
  sorry

theorem sendInvS_inv.obligation_1 :
    Unification.complete (Narrowing.mayFire sendInvS freeP)
      [Unification.Unifier.bind fun (x : ℕ × Oids × CacheState × Req × Ack × ℕ × Oids × Cmd × ℕ × Oids) =>
          ((x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.1, ∅, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
              {Item.dir
                  { cmd := x.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.1, exGntd := false, shr := x.2.2.2.2.2.2.2.2.2,
                    inv := x.2.1 }}),
            x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2, x.2.1,
            {Item.cache { id := x.1, state := x.2.2.1, ch1 := x.2.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.cmdS, ptr := x.2.2.2.2.2.1, exGntd := true, shr := x.2.2.2.2.2.2.1, inv := {x.1} }}),
        Unification.Unifier.bind fun (x : ℕ × Oids × Oids × CacheState × Req × Ack × ℕ × Oids × Oids × Cmd × ℕ) =>
          ((x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.1, x.2.2.2.2.2.2.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
              {Item.dir
                  { cmd := x.2.2.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.2.2, exGntd := false, shr := x.2.1,
                    inv := x.2.2.1 }}),
            x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2, x.2.1, x.2.2.1,
            {Item.cache { id := x.1, state := x.2.2.2.1, ch1 := x.2.2.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.cmdS, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := x.2.2.2.2.2.2.2.1,
                    inv := {x.1} + x.2.2.2.2.2.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × Oids × Items × CacheState × Req × Ack × ℕ × Oids × Cmd × ℕ × Oids) =>
          ((x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.1, ∅, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
              x.2.2.1 +
                {Item.dir
                    { cmd := x.2.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.2.1, exGntd := false,
                      shr := x.2.2.2.2.2.2.2.2.2.2, inv := x.2.1 }}),
            x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2, x.2.1,
            x.2.2.1 +
                {Item.cache
                    { id := x.1, state := x.2.2.2.1, ch1 := x.2.2.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.cmdS, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := x.2.2.2.2.2.2.2.1, inv := {x.1} }}),
        Unification.Unifier.bind
          fun (x : ℕ × Oids × Oids × Items × CacheState × Req × Ack × ℕ × Oids × Oids × Cmd × ℕ) =>
          ((x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1, x.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
              x.2.2.2.2.2.2.1,
              x.2.2.2.1 +
                {Item.dir
                    { cmd := x.2.2.2.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.2.2.2, exGntd := false, shr := x.2.1,
                      inv := x.2.2.1 }}),
            x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2, x.2.1, x.2.2.1,
            x.2.2.2.1 +
                {Item.cache
                    { id := x.1, state := x.2.2.2.2.1, ch1 := x.2.2.2.2.2.1, ch2 := Gnt.noGnt,
                      ch3 := x.2.2.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.cmdS, ptr := x.2.2.2.2.2.2.2.1, exGntd := true, shr := x.2.2.2.2.2.2.2.2.1,
                    inv := {x.1} + x.2.2.2.2.2.2.2.2.2.1 }})] := by
  maude_certify_comp

theorem sendInvS_inv.obligation_2 :
    Unification.sound (Narrowing.mayFire sendInvS freeP)
      [Unification.Unifier.bind fun (x : ℕ × Oids × CacheState × Req × Ack × ℕ × Oids × Cmd × ℕ × Oids) =>
          ((x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.1, ∅, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
              {Item.dir
                  { cmd := x.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.1, exGntd := false, shr := x.2.2.2.2.2.2.2.2.2,
                    inv := x.2.1 }}),
            x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2, x.2.1,
            {Item.cache { id := x.1, state := x.2.2.1, ch1 := x.2.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.cmdS, ptr := x.2.2.2.2.2.1, exGntd := true, shr := x.2.2.2.2.2.2.1, inv := {x.1} }}),
        Unification.Unifier.bind fun (x : ℕ × Oids × Oids × CacheState × Req × Ack × ℕ × Oids × Oids × Cmd × ℕ) =>
          ((x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.1, x.2.2.2.2.2.2.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
              {Item.dir
                  { cmd := x.2.2.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.2.2, exGntd := false, shr := x.2.1,
                    inv := x.2.2.1 }}),
            x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2, x.2.1, x.2.2.1,
            {Item.cache { id := x.1, state := x.2.2.2.1, ch1 := x.2.2.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.cmdS, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := x.2.2.2.2.2.2.2.1,
                    inv := {x.1} + x.2.2.2.2.2.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × Oids × Items × CacheState × Req × Ack × ℕ × Oids × Cmd × ℕ × Oids) =>
          ((x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.1, ∅, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
              x.2.2.1 +
                {Item.dir
                    { cmd := x.2.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.2.1, exGntd := false,
                      shr := x.2.2.2.2.2.2.2.2.2.2, inv := x.2.1 }}),
            x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2, x.2.1,
            x.2.2.1 +
                {Item.cache
                    { id := x.1, state := x.2.2.2.1, ch1 := x.2.2.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.cmdS, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := x.2.2.2.2.2.2.2.1, inv := {x.1} }}),
        Unification.Unifier.bind
          fun (x : ℕ × Oids × Oids × Items × CacheState × Req × Ack × ℕ × Oids × Oids × Cmd × ℕ) =>
          ((x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1, x.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
              x.2.2.2.2.2.2.1,
              x.2.2.2.1 +
                {Item.dir
                    { cmd := x.2.2.2.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.2.2.2, exGntd := false, shr := x.2.1,
                      inv := x.2.2.1 }}),
            x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2, x.2.1, x.2.2.1,
            x.2.2.2.1 +
                {Item.cache
                    { id := x.1, state := x.2.2.2.2.1, ch1 := x.2.2.2.2.2.1, ch2 := Gnt.noGnt,
                      ch3 := x.2.2.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.cmdS, ptr := x.2.2.2.2.2.2.2.1, exGntd := true, shr := x.2.2.2.2.2.2.2.2.1,
                    inv := {x.1} + x.2.2.2.2.2.2.2.2.2.1 }})] := by
  sorry

theorem sendInvS_inv.obligation_3 :
    Unification.complete (Narrowing.mayFire sendInvS ownE)
      [Unification.Unifier.bind fun (x : ℕ × ℕ × Oids × CacheState × Req × Ack × ℕ × Oids × ℕ × Req × Cmd) =>
          ((x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.1, ∅, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
              {Item.cache
                    { id := x.2.2.2.2.2.2.2.2.1, state := CacheState.exclusive, ch1 := x.2.2.2.2.2.2.2.2.2.1,
                      ch2 := Gnt.noGnt, ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.2.2.2.2.2, ptr := x.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.1},
                      inv := x.2.2.1 }}),
            x.2.2.2.2.2.2.2.2.2.2, x.2.1, x.2.2.1, x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1,
            {Item.cache { id := x.1, state := x.2.2.2.1, ch1 := x.2.2.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.cmdS, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := x.2.2.2.2.2.2.2.1, inv := {x.1} }}),
        Unification.Unifier.bind fun (x : ℕ × Cmd × ℕ × Oids × CacheState × Req × Ack × ℕ × Oids × Oids × ℕ × Req) =>
          ((x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1, x.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
              x.2.2.2.2.2.2.1,
              {Item.cache
                    { id := x.2.2.2.2.2.2.2.2.2.2.1, state := CacheState.exclusive, ch1 := x.2.2.2.2.2.2.2.2.2.2.2,
                      ch2 := Gnt.noGnt, ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.1, ptr := x.2.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.2.2.1},
                      inv := x.2.2.2.1 }}),
            x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2,
            {Item.cache
                  { id := x.1, state := x.2.2.2.2.1, ch1 := x.2.2.2.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.cmdS, ptr := x.2.2.2.2.2.2.2.1, exGntd := true, shr := x.2.2.2.2.2.2.2.2.1,
                    inv := {x.1} + x.2.2.2.2.2.2.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × ℕ × Oids × Items × CacheState × Req × Ack × ℕ × Oids × ℕ × Req × Cmd) =>
          ((x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1, x.1, ∅, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
              x.2.2.2.1 +
                  {Item.cache
                      { id := x.2.2.2.2.2.2.2.2.2.1, state := CacheState.exclusive, ch1 := x.2.2.2.2.2.2.2.2.2.2.1,
                        ch2 := Gnt.noGnt, ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.2.2.2.2.2.2, ptr := x.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.2.1},
                      inv := x.2.2.1 }}),
            x.2.2.2.2.2.2.2.2.2.2.2, x.2.1, x.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1,
            x.2.2.2.1 +
                {Item.cache
                    { id := x.1, state := x.2.2.2.2.1, ch1 := x.2.2.2.2.2.1, ch2 := Gnt.noGnt,
                      ch3 := x.2.2.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.cmdS, ptr := x.2.2.2.2.2.2.2.1, exGntd := true, shr := x.2.2.2.2.2.2.2.2.1,
                    inv := {x.1} }}),
        Unification.Unifier.bind
          fun (x : ℕ × Cmd × ℕ × Oids × Items × CacheState × Req × Ack × ℕ × Oids × Oids × ℕ × Req) =>
          ((x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.2.1,
              x.2.2.2.2.1 +
                  {Item.cache
                      { id := x.2.2.2.2.2.2.2.2.2.2.2.1, state := CacheState.exclusive,
                        ch1 := x.2.2.2.2.2.2.2.2.2.2.2.2, ch2 := Gnt.noGnt, ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.1, ptr := x.2.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.2.2.2.1},
                      inv := x.2.2.2.1 }}),
            x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2,
            x.2.2.2.2.1 +
                {Item.cache
                    { id := x.1, state := x.2.2.2.2.2.1, ch1 := x.2.2.2.2.2.2.1, ch2 := Gnt.noGnt,
                      ch3 := x.2.2.2.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.cmdS, ptr := x.2.2.2.2.2.2.2.2.1, exGntd := true, shr := x.2.2.2.2.2.2.2.2.2.1,
                    inv := {x.1} + x.2.2.2.2.2.2.2.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × Oids × ℕ × Req × Cmd × ℕ × Oids) =>
          ((x.1, x.2.1, x.2.2.1, ∅, CacheState.exclusive, x.2.2.2.1, Ack.noAck,
              {Item.dir
                  { cmd := x.2.2.2.2.1, ptr := x.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.1},
                    inv := x.2.2.2.2.2.2 }}),
            x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2, x.2.2.1, x.2.2.2.1,
            {Item.dir { cmd := Cmd.cmdS, ptr := x.1, exGntd := true, shr := x.2.1, inv := {x.2.2.1} }}),
        Unification.Unifier.bind fun (x : ℕ × Oids × Oids × ℕ × Req × Cmd × ℕ × Oids) =>
          ((x.1, x.2.1, x.2.2.2.1, x.2.2.1, CacheState.exclusive, x.2.2.2.2.1, Ack.noAck,
              {Item.dir
                  { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.1},
                    inv := x.2.2.2.2.2.2.2 }}),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2, x.2.2.2.1, x.2.2.2.2.1,
            {Item.dir { cmd := Cmd.cmdS, ptr := x.1, exGntd := true, shr := x.2.1, inv := {x.2.2.2.1} + x.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × Oids × ℕ × Req × Cmd × ℕ × Oids × Items) =>
          ((x.1, x.2.1, x.2.2.1, ∅, CacheState.exclusive, x.2.2.2.1, Ack.noAck,
              x.2.2.2.2.2.2.2 +
                {Item.dir
                    { cmd := x.2.2.2.2.1, ptr := x.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.1},
                      inv := x.2.2.2.2.2.2.1 }}),
            x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.1, x.2.2.2.1,
            x.2.2.2.2.2.2.2 +
              {Item.dir { cmd := Cmd.cmdS, ptr := x.1, exGntd := true, shr := x.2.1, inv := {x.2.2.1} }}),
        Unification.Unifier.bind fun (x : ℕ × Oids × Oids × ℕ × Req × Cmd × ℕ × Oids × Items) =>
          ((x.1, x.2.1, x.2.2.2.1, x.2.2.1, CacheState.exclusive, x.2.2.2.2.1, Ack.noAck,
              x.2.2.2.2.2.2.2.2 +
                {Item.dir
                    { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.1},
                      inv := x.2.2.2.2.2.2.2.1 }}),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
            x.2.2.2.2.2.2.2.2 +
              {Item.dir { cmd := Cmd.cmdS, ptr := x.1, exGntd := true, shr := x.2.1, inv := {x.2.2.2.1} + x.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × CacheState × Req × Ack × ℕ × Req × ℕ) =>
          ((x.2.2.2.2.2.2, {x.2.2.2.2.1}, x.1, ∅, x.2.1, x.2.2.1, x.2.2.2.1,
              {Item.cache
                  { id := x.2.2.2.2.1, state := CacheState.exclusive, ch1 := x.2.2.2.2.2.1, ch2 := Gnt.noGnt,
                    ch3 := Ack.noAck }}),
            Cmd.cmdS, x.2.2.2.2.2.2, {x.1}, x.2.2.2.2.1, x.2.2.2.2.2.1,
            {Item.cache { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × CacheState × Req × Ack × Oids × ℕ × Req × ℕ) =>
          ((x.2.2.2.2.2.2.2, {x.2.2.2.2.2.1}, x.1, x.2.2.2.2.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {Item.cache
                  { id := x.2.2.2.2.2.1, state := CacheState.exclusive, ch1 := x.2.2.2.2.2.2.1, ch2 := Gnt.noGnt,
                    ch3 := Ack.noAck }}),
            Cmd.cmdS, x.2.2.2.2.2.2.2, {x.1} + x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
            {Item.cache { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × CacheState × Req × Ack × ℕ × Req × ℕ × Items) =>
          ((x.2.2.2.2.2.2.1, {x.2.2.2.2.1}, x.1, ∅, x.2.1, x.2.2.1, x.2.2.2.1,
              x.2.2.2.2.2.2.2 +
                {Item.cache
                    { id := x.2.2.2.2.1, state := CacheState.exclusive, ch1 := x.2.2.2.2.2.1, ch2 := Gnt.noGnt,
                      ch3 := Ack.noAck }}),
            Cmd.cmdS, x.2.2.2.2.2.2.1, {x.1}, x.2.2.2.2.1, x.2.2.2.2.2.1,
            x.2.2.2.2.2.2.2 +
              {Item.cache { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × CacheState × Req × Ack × Oids × ℕ × Req × ℕ × Items) =>
          ((x.2.2.2.2.2.2.2.1, {x.2.2.2.2.2.1}, x.1, x.2.2.2.2.1, x.2.1, x.2.2.1, x.2.2.2.1,
              x.2.2.2.2.2.2.2.2 +
                {Item.cache
                    { id := x.2.2.2.2.2.1, state := CacheState.exclusive, ch1 := x.2.2.2.2.2.2.1, ch2 := Gnt.noGnt,
                      ch3 := Ack.noAck }}),
            Cmd.cmdS, x.2.2.2.2.2.2.2.1, {x.1} + x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
            x.2.2.2.2.2.2.2.2 +
              {Item.cache { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × Req × ℕ) =>
          ((x.2.2, {x.1}, x.1, ∅, CacheState.exclusive, x.2.1, Ack.noAck, ∅), Cmd.cmdS, x.2.2, {x.1}, x.1, x.2.1, ∅),
        Unification.Unifier.bind fun (x : Oids × ℕ × Req × ℕ) =>
          ((x.2.2.2, {x.2.1}, x.2.1, x.1, CacheState.exclusive, x.2.2.1, Ack.noAck, ∅), Cmd.cmdS, x.2.2.2,
            {x.2.1} + x.1, x.2.1, x.2.2.1, ∅),
        Unification.Unifier.bind fun (x : Items × ℕ × Req × ℕ) =>
          ((x.2.2.2, {x.2.1}, x.2.1, ∅, CacheState.exclusive, x.2.2.1, Ack.noAck, x.1), Cmd.cmdS, x.2.2.2, {x.2.1},
            x.2.1, x.2.2.1, x.1),
        Unification.Unifier.bind fun (x : Oids × Items × ℕ × Req × ℕ) =>
          ((x.2.2.2.2, {x.2.2.1}, x.2.2.1, x.1, CacheState.exclusive, x.2.2.2.1, Ack.noAck, x.2.1), Cmd.cmdS, x.2.2.2.2,
            {x.2.2.1} + x.1, x.2.2.1, x.2.2.2.1, x.2.1)] := by
  maude_certify_comp

theorem sendInvS_inv.obligation_4 :
    Unification.sound (Narrowing.mayFire sendInvS ownE)
      [Unification.Unifier.bind fun (x : ℕ × ℕ × Oids × CacheState × Req × Ack × ℕ × Oids × ℕ × Req × Cmd) =>
          ((x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.1, ∅, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
              {Item.cache
                    { id := x.2.2.2.2.2.2.2.2.1, state := CacheState.exclusive, ch1 := x.2.2.2.2.2.2.2.2.2.1,
                      ch2 := Gnt.noGnt, ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.2.2.2.2.2, ptr := x.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.1},
                      inv := x.2.2.1 }}),
            x.2.2.2.2.2.2.2.2.2.2, x.2.1, x.2.2.1, x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1,
            {Item.cache { id := x.1, state := x.2.2.2.1, ch1 := x.2.2.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.cmdS, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := x.2.2.2.2.2.2.2.1, inv := {x.1} }}),
        Unification.Unifier.bind fun (x : ℕ × Cmd × ℕ × Oids × CacheState × Req × Ack × ℕ × Oids × Oids × ℕ × Req) =>
          ((x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1, x.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
              x.2.2.2.2.2.2.1,
              {Item.cache
                    { id := x.2.2.2.2.2.2.2.2.2.2.1, state := CacheState.exclusive, ch1 := x.2.2.2.2.2.2.2.2.2.2.2,
                      ch2 := Gnt.noGnt, ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.1, ptr := x.2.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.2.2.1},
                      inv := x.2.2.2.1 }}),
            x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2,
            {Item.cache
                  { id := x.1, state := x.2.2.2.2.1, ch1 := x.2.2.2.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.cmdS, ptr := x.2.2.2.2.2.2.2.1, exGntd := true, shr := x.2.2.2.2.2.2.2.2.1,
                    inv := {x.1} + x.2.2.2.2.2.2.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × ℕ × Oids × Items × CacheState × Req × Ack × ℕ × Oids × ℕ × Req × Cmd) =>
          ((x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1, x.1, ∅, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
              x.2.2.2.1 +
                  {Item.cache
                      { id := x.2.2.2.2.2.2.2.2.2.1, state := CacheState.exclusive, ch1 := x.2.2.2.2.2.2.2.2.2.2.1,
                        ch2 := Gnt.noGnt, ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.2.2.2.2.2.2, ptr := x.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.2.1},
                      inv := x.2.2.1 }}),
            x.2.2.2.2.2.2.2.2.2.2.2, x.2.1, x.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1,
            x.2.2.2.1 +
                {Item.cache
                    { id := x.1, state := x.2.2.2.2.1, ch1 := x.2.2.2.2.2.1, ch2 := Gnt.noGnt,
                      ch3 := x.2.2.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.cmdS, ptr := x.2.2.2.2.2.2.2.1, exGntd := true, shr := x.2.2.2.2.2.2.2.2.1,
                    inv := {x.1} }}),
        Unification.Unifier.bind
          fun (x : ℕ × Cmd × ℕ × Oids × Items × CacheState × Req × Ack × ℕ × Oids × Oids × ℕ × Req) =>
          ((x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.2.1,
              x.2.2.2.2.1 +
                  {Item.cache
                      { id := x.2.2.2.2.2.2.2.2.2.2.2.1, state := CacheState.exclusive,
                        ch1 := x.2.2.2.2.2.2.2.2.2.2.2.2, ch2 := Gnt.noGnt, ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.1, ptr := x.2.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.2.2.2.1},
                      inv := x.2.2.2.1 }}),
            x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2,
            x.2.2.2.2.1 +
                {Item.cache
                    { id := x.1, state := x.2.2.2.2.2.1, ch1 := x.2.2.2.2.2.2.1, ch2 := Gnt.noGnt,
                      ch3 := x.2.2.2.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.cmdS, ptr := x.2.2.2.2.2.2.2.2.1, exGntd := true, shr := x.2.2.2.2.2.2.2.2.2.1,
                    inv := {x.1} + x.2.2.2.2.2.2.2.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × Oids × ℕ × Req × Cmd × ℕ × Oids) =>
          ((x.1, x.2.1, x.2.2.1, ∅, CacheState.exclusive, x.2.2.2.1, Ack.noAck,
              {Item.dir
                  { cmd := x.2.2.2.2.1, ptr := x.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.1},
                    inv := x.2.2.2.2.2.2 }}),
            x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2, x.2.2.1, x.2.2.2.1,
            {Item.dir { cmd := Cmd.cmdS, ptr := x.1, exGntd := true, shr := x.2.1, inv := {x.2.2.1} }}),
        Unification.Unifier.bind fun (x : ℕ × Oids × Oids × ℕ × Req × Cmd × ℕ × Oids) =>
          ((x.1, x.2.1, x.2.2.2.1, x.2.2.1, CacheState.exclusive, x.2.2.2.2.1, Ack.noAck,
              {Item.dir
                  { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.1},
                    inv := x.2.2.2.2.2.2.2 }}),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2, x.2.2.2.1, x.2.2.2.2.1,
            {Item.dir { cmd := Cmd.cmdS, ptr := x.1, exGntd := true, shr := x.2.1, inv := {x.2.2.2.1} + x.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × Oids × ℕ × Req × Cmd × ℕ × Oids × Items) =>
          ((x.1, x.2.1, x.2.2.1, ∅, CacheState.exclusive, x.2.2.2.1, Ack.noAck,
              x.2.2.2.2.2.2.2 +
                {Item.dir
                    { cmd := x.2.2.2.2.1, ptr := x.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.1},
                      inv := x.2.2.2.2.2.2.1 }}),
            x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.1, x.2.2.2.1,
            x.2.2.2.2.2.2.2 +
              {Item.dir { cmd := Cmd.cmdS, ptr := x.1, exGntd := true, shr := x.2.1, inv := {x.2.2.1} }}),
        Unification.Unifier.bind fun (x : ℕ × Oids × Oids × ℕ × Req × Cmd × ℕ × Oids × Items) =>
          ((x.1, x.2.1, x.2.2.2.1, x.2.2.1, CacheState.exclusive, x.2.2.2.2.1, Ack.noAck,
              x.2.2.2.2.2.2.2.2 +
                {Item.dir
                    { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.1},
                      inv := x.2.2.2.2.2.2.2.1 }}),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
            x.2.2.2.2.2.2.2.2 +
              {Item.dir { cmd := Cmd.cmdS, ptr := x.1, exGntd := true, shr := x.2.1, inv := {x.2.2.2.1} + x.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × CacheState × Req × Ack × ℕ × Req × ℕ) =>
          ((x.2.2.2.2.2.2, {x.2.2.2.2.1}, x.1, ∅, x.2.1, x.2.2.1, x.2.2.2.1,
              {Item.cache
                  { id := x.2.2.2.2.1, state := CacheState.exclusive, ch1 := x.2.2.2.2.2.1, ch2 := Gnt.noGnt,
                    ch3 := Ack.noAck }}),
            Cmd.cmdS, x.2.2.2.2.2.2, {x.1}, x.2.2.2.2.1, x.2.2.2.2.2.1,
            {Item.cache { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × CacheState × Req × Ack × Oids × ℕ × Req × ℕ) =>
          ((x.2.2.2.2.2.2.2, {x.2.2.2.2.2.1}, x.1, x.2.2.2.2.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {Item.cache
                  { id := x.2.2.2.2.2.1, state := CacheState.exclusive, ch1 := x.2.2.2.2.2.2.1, ch2 := Gnt.noGnt,
                    ch3 := Ack.noAck }}),
            Cmd.cmdS, x.2.2.2.2.2.2.2, {x.1} + x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
            {Item.cache { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × CacheState × Req × Ack × ℕ × Req × ℕ × Items) =>
          ((x.2.2.2.2.2.2.1, {x.2.2.2.2.1}, x.1, ∅, x.2.1, x.2.2.1, x.2.2.2.1,
              x.2.2.2.2.2.2.2 +
                {Item.cache
                    { id := x.2.2.2.2.1, state := CacheState.exclusive, ch1 := x.2.2.2.2.2.1, ch2 := Gnt.noGnt,
                      ch3 := Ack.noAck }}),
            Cmd.cmdS, x.2.2.2.2.2.2.1, {x.1}, x.2.2.2.2.1, x.2.2.2.2.2.1,
            x.2.2.2.2.2.2.2 +
              {Item.cache { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × CacheState × Req × Ack × Oids × ℕ × Req × ℕ × Items) =>
          ((x.2.2.2.2.2.2.2.1, {x.2.2.2.2.2.1}, x.1, x.2.2.2.2.1, x.2.1, x.2.2.1, x.2.2.2.1,
              x.2.2.2.2.2.2.2.2 +
                {Item.cache
                    { id := x.2.2.2.2.2.1, state := CacheState.exclusive, ch1 := x.2.2.2.2.2.2.1, ch2 := Gnt.noGnt,
                      ch3 := Ack.noAck }}),
            Cmd.cmdS, x.2.2.2.2.2.2.2.1, {x.1} + x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
            x.2.2.2.2.2.2.2.2 +
              {Item.cache { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × Req × ℕ) =>
          ((x.2.2, {x.1}, x.1, ∅, CacheState.exclusive, x.2.1, Ack.noAck, ∅), Cmd.cmdS, x.2.2, {x.1}, x.1, x.2.1, ∅),
        Unification.Unifier.bind fun (x : Oids × ℕ × Req × ℕ) =>
          ((x.2.2.2, {x.2.1}, x.2.1, x.1, CacheState.exclusive, x.2.2.1, Ack.noAck, ∅), Cmd.cmdS, x.2.2.2,
            {x.2.1} + x.1, x.2.1, x.2.2.1, ∅),
        Unification.Unifier.bind fun (x : Items × ℕ × Req × ℕ) =>
          ((x.2.2.2, {x.2.1}, x.2.1, ∅, CacheState.exclusive, x.2.2.1, Ack.noAck, x.1), Cmd.cmdS, x.2.2.2, {x.2.1},
            x.2.1, x.2.2.1, x.1),
        Unification.Unifier.bind fun (x : Oids × Items × ℕ × Req × ℕ) =>
          ((x.2.2.2.2, {x.2.2.1}, x.2.2.1, x.1, CacheState.exclusive, x.2.2.2.1, Ack.noAck, x.2.1), Cmd.cmdS, x.2.2.2.2,
            {x.2.2.1} + x.1, x.2.2.1, x.2.2.2.1, x.2.1)] := by
  sorry

theorem sendInvS_inv.obligation_5 :
    Unification.complete (Narrowing.mayFire sendInvS ownG)
      [Unification.Unifier.bind fun (x : ℕ × ℕ × Oids × CacheState × Req × Ack × ℕ × Oids × ℕ × Req × Cmd) =>
          ((x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.1, ∅, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
              {Item.cache
                    { id := x.2.2.2.2.2.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.2.2.2.2.2.1,
                      ch2 := Gnt.gntE, ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.2.2.2.2.2, ptr := x.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.1},
                      inv := x.2.2.1 }}),
            x.2.2.2.2.2.2.2.2.2.2, x.2.1, x.2.2.1, x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1,
            {Item.cache { id := x.1, state := x.2.2.2.1, ch1 := x.2.2.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.cmdS, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := x.2.2.2.2.2.2.2.1, inv := {x.1} }}),
        Unification.Unifier.bind fun (x : ℕ × Cmd × ℕ × Oids × CacheState × Req × Ack × ℕ × Oids × Oids × ℕ × Req) =>
          ((x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1, x.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
              x.2.2.2.2.2.2.1,
              {Item.cache
                    { id := x.2.2.2.2.2.2.2.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.2.2.2.2.2.2.2,
                      ch2 := Gnt.gntE, ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.1, ptr := x.2.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.2.2.1},
                      inv := x.2.2.2.1 }}),
            x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2,
            {Item.cache
                  { id := x.1, state := x.2.2.2.2.1, ch1 := x.2.2.2.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.cmdS, ptr := x.2.2.2.2.2.2.2.1, exGntd := true, shr := x.2.2.2.2.2.2.2.2.1,
                    inv := {x.1} + x.2.2.2.2.2.2.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × ℕ × Oids × Items × CacheState × Req × Ack × ℕ × Oids × ℕ × Req × Cmd) =>
          ((x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1, x.1, ∅, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
              x.2.2.2.1 +
                  {Item.cache
                      { id := x.2.2.2.2.2.2.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.2.2.2.2.2.2.1,
                        ch2 := Gnt.gntE, ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.2.2.2.2.2.2, ptr := x.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.2.1},
                      inv := x.2.2.1 }}),
            x.2.2.2.2.2.2.2.2.2.2.2, x.2.1, x.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1,
            x.2.2.2.1 +
                {Item.cache
                    { id := x.1, state := x.2.2.2.2.1, ch1 := x.2.2.2.2.2.1, ch2 := Gnt.noGnt,
                      ch3 := x.2.2.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.cmdS, ptr := x.2.2.2.2.2.2.2.1, exGntd := true, shr := x.2.2.2.2.2.2.2.2.1,
                    inv := {x.1} }}),
        Unification.Unifier.bind
          fun (x : ℕ × Cmd × ℕ × Oids × Items × CacheState × Req × Ack × ℕ × Oids × Oids × ℕ × Req) =>
          ((x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.2.1,
              x.2.2.2.2.1 +
                  {Item.cache
                      { id := x.2.2.2.2.2.2.2.2.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.2.2.2.2.2.2.2.2,
                        ch2 := Gnt.gntE, ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.1, ptr := x.2.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.2.2.2.1},
                      inv := x.2.2.2.1 }}),
            x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2,
            x.2.2.2.2.1 +
                {Item.cache
                    { id := x.1, state := x.2.2.2.2.2.1, ch1 := x.2.2.2.2.2.2.1, ch2 := Gnt.noGnt,
                      ch3 := x.2.2.2.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.cmdS, ptr := x.2.2.2.2.2.2.2.2.1, exGntd := true, shr := x.2.2.2.2.2.2.2.2.2.1,
                    inv := {x.1} + x.2.2.2.2.2.2.2.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × CacheState × Req × Ack × ℕ × Req × ℕ) =>
          ((x.2.2.2.2.2.2, {x.2.2.2.2.1}, x.1, ∅, x.2.1, x.2.2.1, x.2.2.2.1,
              {Item.cache
                  { id := x.2.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.2.1, ch2 := Gnt.gntE,
                    ch3 := Ack.noAck }}),
            Cmd.cmdS, x.2.2.2.2.2.2, {x.1}, x.2.2.2.2.1, x.2.2.2.2.2.1,
            {Item.cache { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × CacheState × Req × Ack × Oids × ℕ × Req × ℕ) =>
          ((x.2.2.2.2.2.2.2, {x.2.2.2.2.2.1}, x.1, x.2.2.2.2.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {Item.cache
                  { id := x.2.2.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.2.2.1, ch2 := Gnt.gntE,
                    ch3 := Ack.noAck }}),
            Cmd.cmdS, x.2.2.2.2.2.2.2, {x.1} + x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
            {Item.cache { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × CacheState × Req × Ack × ℕ × Req × ℕ × Items) =>
          ((x.2.2.2.2.2.2.1, {x.2.2.2.2.1}, x.1, ∅, x.2.1, x.2.2.1, x.2.2.2.1,
              x.2.2.2.2.2.2.2 +
                {Item.cache
                    { id := x.2.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.2.1, ch2 := Gnt.gntE,
                      ch3 := Ack.noAck }}),
            Cmd.cmdS, x.2.2.2.2.2.2.1, {x.1}, x.2.2.2.2.1, x.2.2.2.2.2.1,
            x.2.2.2.2.2.2.2 +
              {Item.cache { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × CacheState × Req × Ack × Oids × ℕ × Req × ℕ × Items) =>
          ((x.2.2.2.2.2.2.2.1, {x.2.2.2.2.2.1}, x.1, x.2.2.2.2.1, x.2.1, x.2.2.1, x.2.2.2.1,
              x.2.2.2.2.2.2.2.2 +
                {Item.cache
                    { id := x.2.2.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.2.2.1, ch2 := Gnt.gntE,
                      ch3 := Ack.noAck }}),
            Cmd.cmdS, x.2.2.2.2.2.2.2.1, {x.1} + x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
            x.2.2.2.2.2.2.2.2 +
              {Item.cache { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.1 }})] := by
  maude_certify_comp

theorem sendInvS_inv.obligation_6 :
    Unification.sound (Narrowing.mayFire sendInvS ownG)
      [Unification.Unifier.bind fun (x : ℕ × ℕ × Oids × CacheState × Req × Ack × ℕ × Oids × ℕ × Req × Cmd) =>
          ((x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.1, ∅, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
              {Item.cache
                    { id := x.2.2.2.2.2.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.2.2.2.2.2.1,
                      ch2 := Gnt.gntE, ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.2.2.2.2.2, ptr := x.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.1},
                      inv := x.2.2.1 }}),
            x.2.2.2.2.2.2.2.2.2.2, x.2.1, x.2.2.1, x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1,
            {Item.cache { id := x.1, state := x.2.2.2.1, ch1 := x.2.2.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.cmdS, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := x.2.2.2.2.2.2.2.1, inv := {x.1} }}),
        Unification.Unifier.bind fun (x : ℕ × Cmd × ℕ × Oids × CacheState × Req × Ack × ℕ × Oids × Oids × ℕ × Req) =>
          ((x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1, x.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
              x.2.2.2.2.2.2.1,
              {Item.cache
                    { id := x.2.2.2.2.2.2.2.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.2.2.2.2.2.2.2,
                      ch2 := Gnt.gntE, ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.1, ptr := x.2.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.2.2.1},
                      inv := x.2.2.2.1 }}),
            x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2,
            {Item.cache
                  { id := x.1, state := x.2.2.2.2.1, ch1 := x.2.2.2.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.cmdS, ptr := x.2.2.2.2.2.2.2.1, exGntd := true, shr := x.2.2.2.2.2.2.2.2.1,
                    inv := {x.1} + x.2.2.2.2.2.2.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × ℕ × Oids × Items × CacheState × Req × Ack × ℕ × Oids × ℕ × Req × Cmd) =>
          ((x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1, x.1, ∅, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
              x.2.2.2.1 +
                  {Item.cache
                      { id := x.2.2.2.2.2.2.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.2.2.2.2.2.2.1,
                        ch2 := Gnt.gntE, ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.2.2.2.2.2.2, ptr := x.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.2.1},
                      inv := x.2.2.1 }}),
            x.2.2.2.2.2.2.2.2.2.2.2, x.2.1, x.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1,
            x.2.2.2.1 +
                {Item.cache
                    { id := x.1, state := x.2.2.2.2.1, ch1 := x.2.2.2.2.2.1, ch2 := Gnt.noGnt,
                      ch3 := x.2.2.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.cmdS, ptr := x.2.2.2.2.2.2.2.1, exGntd := true, shr := x.2.2.2.2.2.2.2.2.1,
                    inv := {x.1} }}),
        Unification.Unifier.bind
          fun (x : ℕ × Cmd × ℕ × Oids × Items × CacheState × Req × Ack × ℕ × Oids × Oids × ℕ × Req) =>
          ((x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.2.1,
              x.2.2.2.2.1 +
                  {Item.cache
                      { id := x.2.2.2.2.2.2.2.2.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.2.2.2.2.2.2.2.2,
                        ch2 := Gnt.gntE, ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.1, ptr := x.2.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.2.2.2.1},
                      inv := x.2.2.2.1 }}),
            x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2,
            x.2.2.2.2.1 +
                {Item.cache
                    { id := x.1, state := x.2.2.2.2.2.1, ch1 := x.2.2.2.2.2.2.1, ch2 := Gnt.noGnt,
                      ch3 := x.2.2.2.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.cmdS, ptr := x.2.2.2.2.2.2.2.2.1, exGntd := true, shr := x.2.2.2.2.2.2.2.2.2.1,
                    inv := {x.1} + x.2.2.2.2.2.2.2.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × CacheState × Req × Ack × ℕ × Req × ℕ) =>
          ((x.2.2.2.2.2.2, {x.2.2.2.2.1}, x.1, ∅, x.2.1, x.2.2.1, x.2.2.2.1,
              {Item.cache
                  { id := x.2.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.2.1, ch2 := Gnt.gntE,
                    ch3 := Ack.noAck }}),
            Cmd.cmdS, x.2.2.2.2.2.2, {x.1}, x.2.2.2.2.1, x.2.2.2.2.2.1,
            {Item.cache { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × CacheState × Req × Ack × Oids × ℕ × Req × ℕ) =>
          ((x.2.2.2.2.2.2.2, {x.2.2.2.2.2.1}, x.1, x.2.2.2.2.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {Item.cache
                  { id := x.2.2.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.2.2.1, ch2 := Gnt.gntE,
                    ch3 := Ack.noAck }}),
            Cmd.cmdS, x.2.2.2.2.2.2.2, {x.1} + x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
            {Item.cache { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × CacheState × Req × Ack × ℕ × Req × ℕ × Items) =>
          ((x.2.2.2.2.2.2.1, {x.2.2.2.2.1}, x.1, ∅, x.2.1, x.2.2.1, x.2.2.2.1,
              x.2.2.2.2.2.2.2 +
                {Item.cache
                    { id := x.2.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.2.1, ch2 := Gnt.gntE,
                      ch3 := Ack.noAck }}),
            Cmd.cmdS, x.2.2.2.2.2.2.1, {x.1}, x.2.2.2.2.1, x.2.2.2.2.2.1,
            x.2.2.2.2.2.2.2 +
              {Item.cache { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × CacheState × Req × Ack × Oids × ℕ × Req × ℕ × Items) =>
          ((x.2.2.2.2.2.2.2.1, {x.2.2.2.2.2.1}, x.1, x.2.2.2.2.1, x.2.1, x.2.2.1, x.2.2.2.1,
              x.2.2.2.2.2.2.2.2 +
                {Item.cache
                    { id := x.2.2.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.2.2.1, ch2 := Gnt.gntE,
                      ch3 := Ack.noAck }}),
            Cmd.cmdS, x.2.2.2.2.2.2.2.1, {x.1} + x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
            x.2.2.2.2.2.2.2.2 +
              {Item.cache { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.1 }})] := by
  sorry

theorem sendInvS_inv.obligation_7 :
    Unification.complete (Narrowing.mayFire sendInvS ownInv)
      [Unification.Unifier.bind fun (x : ℕ × ℕ × CacheState × Req × Ack × ℕ × Oids × ℕ × Req × Cmd) =>
          ((x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.1, ∅, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
              {Item.cache
                    { id := x.2.2.2.2.2.2.2.1, state := CacheState.exclusive, ch1 := x.2.2.2.2.2.2.2.2.1,
                      ch2 := Gnt.inv, ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.2.2.2.2, ptr := x.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.1},
                      inv := ∅ }}),
            x.2.2.2.2.2.2.2.2.2, x.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1,
            {Item.cache { id := x.1, state := x.2.2.1, ch1 := x.2.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.cmdS, ptr := x.2.2.2.2.2.1, exGntd := true, shr := x.2.2.2.2.2.2.1, inv := {x.1} }}),
        Unification.Unifier.bind fun (x : ℕ × Cmd × ℕ × CacheState × Req × Ack × ℕ × Oids × Oids × ℕ × Req) =>
          ((x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.1, x.2.2.2.2.2.2.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
              {Item.cache
                    { id := x.2.2.2.2.2.2.2.2.2.1, state := CacheState.exclusive, ch1 := x.2.2.2.2.2.2.2.2.2.2,
                      ch2 := Gnt.inv, ch3 := Ack.noAck }} +
                {Item.dir { cmd := x.2.1, ptr := x.2.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.2.1}, inv := ∅ }}),
            x.2.1, x.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2,
            {Item.cache { id := x.1, state := x.2.2.2.1, ch1 := x.2.2.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.cmdS, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := x.2.2.2.2.2.2.2.1,
                    inv := {x.1} + x.2.2.2.2.2.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × ℕ × Items × CacheState × Req × Ack × ℕ × Oids × ℕ × Req × Cmd) =>
          ((x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.1, ∅, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
              x.2.2.1 +
                  {Item.cache
                      { id := x.2.2.2.2.2.2.2.2.1, state := CacheState.exclusive, ch1 := x.2.2.2.2.2.2.2.2.2.1,
                        ch2 := Gnt.inv, ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.2.2.2.2.2, ptr := x.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.1},
                      inv := ∅ }}),
            x.2.2.2.2.2.2.2.2.2.2, x.2.1, x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1,
            x.2.2.1 +
                {Item.cache
                    { id := x.1, state := x.2.2.2.1, ch1 := x.2.2.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.cmdS, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := x.2.2.2.2.2.2.2.1, inv := {x.1} }}),
        Unification.Unifier.bind fun (x : ℕ × Cmd × ℕ × Items × CacheState × Req × Ack × ℕ × Oids × Oids × ℕ × Req) =>
          ((x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1, x.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
              x.2.2.2.2.2.2.1,
              x.2.2.2.1 +
                  {Item.cache
                      { id := x.2.2.2.2.2.2.2.2.2.2.1, state := CacheState.exclusive, ch1 := x.2.2.2.2.2.2.2.2.2.2.2,
                        ch2 := Gnt.inv, ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.1, ptr := x.2.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.2.2.1}, inv := ∅ }}),
            x.2.1, x.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2,
            x.2.2.2.1 +
                {Item.cache
                    { id := x.1, state := x.2.2.2.2.1, ch1 := x.2.2.2.2.2.1, ch2 := Gnt.noGnt,
                      ch3 := x.2.2.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.cmdS, ptr := x.2.2.2.2.2.2.2.1, exGntd := true, shr := x.2.2.2.2.2.2.2.2.1,
                    inv := {x.1} + x.2.2.2.2.2.2.2.2.2.1 }})] := by
  maude_certify_comp

theorem sendInvS_inv.obligation_8 :
    Unification.sound (Narrowing.mayFire sendInvS ownInv)
      [Unification.Unifier.bind fun (x : ℕ × ℕ × CacheState × Req × Ack × ℕ × Oids × ℕ × Req × Cmd) =>
          ((x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.1, ∅, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
              {Item.cache
                    { id := x.2.2.2.2.2.2.2.1, state := CacheState.exclusive, ch1 := x.2.2.2.2.2.2.2.2.1,
                      ch2 := Gnt.inv, ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.2.2.2.2, ptr := x.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.1},
                      inv := ∅ }}),
            x.2.2.2.2.2.2.2.2.2, x.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1,
            {Item.cache { id := x.1, state := x.2.2.1, ch1 := x.2.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.cmdS, ptr := x.2.2.2.2.2.1, exGntd := true, shr := x.2.2.2.2.2.2.1, inv := {x.1} }}),
        Unification.Unifier.bind fun (x : ℕ × Cmd × ℕ × CacheState × Req × Ack × ℕ × Oids × Oids × ℕ × Req) =>
          ((x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.1, x.2.2.2.2.2.2.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
              {Item.cache
                    { id := x.2.2.2.2.2.2.2.2.2.1, state := CacheState.exclusive, ch1 := x.2.2.2.2.2.2.2.2.2.2,
                      ch2 := Gnt.inv, ch3 := Ack.noAck }} +
                {Item.dir { cmd := x.2.1, ptr := x.2.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.2.1}, inv := ∅ }}),
            x.2.1, x.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2,
            {Item.cache { id := x.1, state := x.2.2.2.1, ch1 := x.2.2.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.cmdS, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := x.2.2.2.2.2.2.2.1,
                    inv := {x.1} + x.2.2.2.2.2.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × ℕ × Items × CacheState × Req × Ack × ℕ × Oids × ℕ × Req × Cmd) =>
          ((x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.1, ∅, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
              x.2.2.1 +
                  {Item.cache
                      { id := x.2.2.2.2.2.2.2.2.1, state := CacheState.exclusive, ch1 := x.2.2.2.2.2.2.2.2.2.1,
                        ch2 := Gnt.inv, ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.2.2.2.2.2, ptr := x.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.1},
                      inv := ∅ }}),
            x.2.2.2.2.2.2.2.2.2.2, x.2.1, x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1,
            x.2.2.1 +
                {Item.cache
                    { id := x.1, state := x.2.2.2.1, ch1 := x.2.2.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.cmdS, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := x.2.2.2.2.2.2.2.1, inv := {x.1} }}),
        Unification.Unifier.bind fun (x : ℕ × Cmd × ℕ × Items × CacheState × Req × Ack × ℕ × Oids × Oids × ℕ × Req) =>
          ((x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1, x.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
              x.2.2.2.2.2.2.1,
              x.2.2.2.1 +
                  {Item.cache
                      { id := x.2.2.2.2.2.2.2.2.2.2.1, state := CacheState.exclusive, ch1 := x.2.2.2.2.2.2.2.2.2.2.2,
                        ch2 := Gnt.inv, ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.1, ptr := x.2.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.2.2.1}, inv := ∅ }}),
            x.2.1, x.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2,
            x.2.2.2.1 +
                {Item.cache
                    { id := x.1, state := x.2.2.2.2.1, ch1 := x.2.2.2.2.2.1, ch2 := Gnt.noGnt,
                      ch3 := x.2.2.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.cmdS, ptr := x.2.2.2.2.2.2.2.1, exGntd := true, shr := x.2.2.2.2.2.2.2.2.1,
                    inv := {x.1} + x.2.2.2.2.2.2.2.2.2.1 }})] := by
  sorry

theorem sendInvS_inv.obligation_9 :
    Unification.complete (Narrowing.mayFire sendInvS ownAck)
      [Unification.Unifier.bind fun (x : ℕ × ℕ × CacheState × Req × Ack × ℕ × Oids × ℕ × Req × Cmd) =>
          ((x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.1, ∅, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
              {Item.cache
                    { id := x.2.2.2.2.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.2.2.2.2.1,
                      ch2 := Gnt.noGnt, ch3 := Ack.invAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.2.2.2.2, ptr := x.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.1},
                      inv := ∅ }}),
            x.2.2.2.2.2.2.2.2.2, x.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1,
            {Item.cache { id := x.1, state := x.2.2.1, ch1 := x.2.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.cmdS, ptr := x.2.2.2.2.2.1, exGntd := true, shr := x.2.2.2.2.2.2.1, inv := {x.1} }}),
        Unification.Unifier.bind fun (x : ℕ × Cmd × ℕ × CacheState × Req × Ack × ℕ × Oids × Oids × ℕ × Req) =>
          ((x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.1, x.2.2.2.2.2.2.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
              {Item.cache
                    { id := x.2.2.2.2.2.2.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.2.2.2.2.2.2,
                      ch2 := Gnt.noGnt, ch3 := Ack.invAck }} +
                {Item.dir { cmd := x.2.1, ptr := x.2.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.2.1}, inv := ∅ }}),
            x.2.1, x.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2,
            {Item.cache { id := x.1, state := x.2.2.2.1, ch1 := x.2.2.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.cmdS, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := x.2.2.2.2.2.2.2.1,
                    inv := {x.1} + x.2.2.2.2.2.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × ℕ × Items × CacheState × Req × Ack × ℕ × Oids × ℕ × Req × Cmd) =>
          ((x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.1, ∅, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
              x.2.2.1 +
                  {Item.cache
                      { id := x.2.2.2.2.2.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.2.2.2.2.2.1,
                        ch2 := Gnt.noGnt, ch3 := Ack.invAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.2.2.2.2.2, ptr := x.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.1},
                      inv := ∅ }}),
            x.2.2.2.2.2.2.2.2.2.2, x.2.1, x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1,
            x.2.2.1 +
                {Item.cache
                    { id := x.1, state := x.2.2.2.1, ch1 := x.2.2.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.cmdS, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := x.2.2.2.2.2.2.2.1, inv := {x.1} }}),
        Unification.Unifier.bind fun (x : ℕ × Cmd × ℕ × Items × CacheState × Req × Ack × ℕ × Oids × Oids × ℕ × Req) =>
          ((x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1, x.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
              x.2.2.2.2.2.2.1,
              x.2.2.2.1 +
                  {Item.cache
                      { id := x.2.2.2.2.2.2.2.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.2.2.2.2.2.2.2,
                        ch2 := Gnt.noGnt, ch3 := Ack.invAck }} +
                {Item.dir
                    { cmd := x.2.1, ptr := x.2.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.2.2.1}, inv := ∅ }}),
            x.2.1, x.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2,
            x.2.2.2.1 +
                {Item.cache
                    { id := x.1, state := x.2.2.2.2.1, ch1 := x.2.2.2.2.2.1, ch2 := Gnt.noGnt,
                      ch3 := x.2.2.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.cmdS, ptr := x.2.2.2.2.2.2.2.1, exGntd := true, shr := x.2.2.2.2.2.2.2.2.1,
                    inv := {x.1} + x.2.2.2.2.2.2.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × Oids × ℕ × Req × Cmd × ℕ) =>
          ((x.1, x.2.1, x.2.2.1, ∅, CacheState.invalid, x.2.2.2.1, Ack.invAck,
              {Item.dir { cmd := x.2.2.2.2.1, ptr := x.2.2.2.2.2, exGntd := true, shr := {x.2.2.1}, inv := ∅ }}),
            x.2.2.2.2.1, x.2.2.2.2.2, x.2.2.1, x.2.2.2.1,
            {Item.dir { cmd := Cmd.cmdS, ptr := x.1, exGntd := true, shr := x.2.1, inv := {x.2.2.1} }}),
        Unification.Unifier.bind fun (x : ℕ × Oids × Oids × ℕ × Req × Cmd × ℕ) =>
          ((x.1, x.2.1, x.2.2.2.1, x.2.2.1, CacheState.invalid, x.2.2.2.2.1, Ack.invAck,
              {Item.dir { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2, exGntd := true, shr := {x.2.2.2.1}, inv := ∅ }}),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2, x.2.2.2.1, x.2.2.2.2.1,
            {Item.dir { cmd := Cmd.cmdS, ptr := x.1, exGntd := true, shr := x.2.1, inv := {x.2.2.2.1} + x.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × Oids × ℕ × Req × Cmd × ℕ × Items) =>
          ((x.1, x.2.1, x.2.2.1, ∅, CacheState.invalid, x.2.2.2.1, Ack.invAck,
              x.2.2.2.2.2.2 +
                {Item.dir { cmd := x.2.2.2.2.1, ptr := x.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.1}, inv := ∅ }}),
            x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.1, x.2.2.2.1,
            x.2.2.2.2.2.2 + {Item.dir { cmd := Cmd.cmdS, ptr := x.1, exGntd := true, shr := x.2.1, inv := {x.2.2.1} }}),
        Unification.Unifier.bind fun (x : ℕ × Oids × Oids × ℕ × Req × Cmd × ℕ × Items) =>
          ((x.1, x.2.1, x.2.2.2.1, x.2.2.1, CacheState.invalid, x.2.2.2.2.1, Ack.invAck,
              x.2.2.2.2.2.2.2 +
                {Item.dir
                    { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.1}, inv := ∅ }}),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
            x.2.2.2.2.2.2.2 +
              {Item.dir
                  { cmd := Cmd.cmdS, ptr := x.1, exGntd := true, shr := x.2.1, inv := {x.2.2.2.1} + x.2.2.1 }})] := by
  maude_certify_comp

theorem sendInvS_inv.obligation_10 :
    Unification.sound (Narrowing.mayFire sendInvS ownAck)
      [Unification.Unifier.bind fun (x : ℕ × ℕ × CacheState × Req × Ack × ℕ × Oids × ℕ × Req × Cmd) =>
          ((x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.1, ∅, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
              {Item.cache
                    { id := x.2.2.2.2.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.2.2.2.2.1,
                      ch2 := Gnt.noGnt, ch3 := Ack.invAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.2.2.2.2, ptr := x.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.1},
                      inv := ∅ }}),
            x.2.2.2.2.2.2.2.2.2, x.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1,
            {Item.cache { id := x.1, state := x.2.2.1, ch1 := x.2.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.cmdS, ptr := x.2.2.2.2.2.1, exGntd := true, shr := x.2.2.2.2.2.2.1, inv := {x.1} }}),
        Unification.Unifier.bind fun (x : ℕ × Cmd × ℕ × CacheState × Req × Ack × ℕ × Oids × Oids × ℕ × Req) =>
          ((x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.1, x.2.2.2.2.2.2.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
              {Item.cache
                    { id := x.2.2.2.2.2.2.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.2.2.2.2.2.2,
                      ch2 := Gnt.noGnt, ch3 := Ack.invAck }} +
                {Item.dir { cmd := x.2.1, ptr := x.2.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.2.1}, inv := ∅ }}),
            x.2.1, x.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2,
            {Item.cache { id := x.1, state := x.2.2.2.1, ch1 := x.2.2.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.cmdS, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := x.2.2.2.2.2.2.2.1,
                    inv := {x.1} + x.2.2.2.2.2.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × ℕ × Items × CacheState × Req × Ack × ℕ × Oids × ℕ × Req × Cmd) =>
          ((x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.1, ∅, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
              x.2.2.1 +
                  {Item.cache
                      { id := x.2.2.2.2.2.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.2.2.2.2.2.1,
                        ch2 := Gnt.noGnt, ch3 := Ack.invAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.2.2.2.2.2, ptr := x.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.1},
                      inv := ∅ }}),
            x.2.2.2.2.2.2.2.2.2.2, x.2.1, x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1,
            x.2.2.1 +
                {Item.cache
                    { id := x.1, state := x.2.2.2.1, ch1 := x.2.2.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.cmdS, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := x.2.2.2.2.2.2.2.1, inv := {x.1} }}),
        Unification.Unifier.bind fun (x : ℕ × Cmd × ℕ × Items × CacheState × Req × Ack × ℕ × Oids × Oids × ℕ × Req) =>
          ((x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1, x.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
              x.2.2.2.2.2.2.1,
              x.2.2.2.1 +
                  {Item.cache
                      { id := x.2.2.2.2.2.2.2.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.2.2.2.2.2.2.2,
                        ch2 := Gnt.noGnt, ch3 := Ack.invAck }} +
                {Item.dir
                    { cmd := x.2.1, ptr := x.2.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.2.2.1}, inv := ∅ }}),
            x.2.1, x.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2,
            x.2.2.2.1 +
                {Item.cache
                    { id := x.1, state := x.2.2.2.2.1, ch1 := x.2.2.2.2.2.1, ch2 := Gnt.noGnt,
                      ch3 := x.2.2.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.cmdS, ptr := x.2.2.2.2.2.2.2.1, exGntd := true, shr := x.2.2.2.2.2.2.2.2.1,
                    inv := {x.1} + x.2.2.2.2.2.2.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × Oids × ℕ × Req × Cmd × ℕ) =>
          ((x.1, x.2.1, x.2.2.1, ∅, CacheState.invalid, x.2.2.2.1, Ack.invAck,
              {Item.dir { cmd := x.2.2.2.2.1, ptr := x.2.2.2.2.2, exGntd := true, shr := {x.2.2.1}, inv := ∅ }}),
            x.2.2.2.2.1, x.2.2.2.2.2, x.2.2.1, x.2.2.2.1,
            {Item.dir { cmd := Cmd.cmdS, ptr := x.1, exGntd := true, shr := x.2.1, inv := {x.2.2.1} }}),
        Unification.Unifier.bind fun (x : ℕ × Oids × Oids × ℕ × Req × Cmd × ℕ) =>
          ((x.1, x.2.1, x.2.2.2.1, x.2.2.1, CacheState.invalid, x.2.2.2.2.1, Ack.invAck,
              {Item.dir { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2, exGntd := true, shr := {x.2.2.2.1}, inv := ∅ }}),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2, x.2.2.2.1, x.2.2.2.2.1,
            {Item.dir { cmd := Cmd.cmdS, ptr := x.1, exGntd := true, shr := x.2.1, inv := {x.2.2.2.1} + x.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × Oids × ℕ × Req × Cmd × ℕ × Items) =>
          ((x.1, x.2.1, x.2.2.1, ∅, CacheState.invalid, x.2.2.2.1, Ack.invAck,
              x.2.2.2.2.2.2 +
                {Item.dir { cmd := x.2.2.2.2.1, ptr := x.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.1}, inv := ∅ }}),
            x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.1, x.2.2.2.1,
            x.2.2.2.2.2.2 + {Item.dir { cmd := Cmd.cmdS, ptr := x.1, exGntd := true, shr := x.2.1, inv := {x.2.2.1} }}),
        Unification.Unifier.bind fun (x : ℕ × Oids × Oids × ℕ × Req × Cmd × ℕ × Items) =>
          ((x.1, x.2.1, x.2.2.2.1, x.2.2.1, CacheState.invalid, x.2.2.2.2.1, Ack.invAck,
              x.2.2.2.2.2.2.2 +
                {Item.dir
                    { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.1}, inv := ∅ }}),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
            x.2.2.2.2.2.2.2 +
              {Item.dir
                  { cmd := Cmd.cmdS, ptr := x.1, exGntd := true, shr := x.2.1, inv := {x.2.2.2.1} + x.2.2.1 }})] := by
  sorry

theorem sendInvS_inv.obligation_13 :
    ∃ b ∈ inv, Expresso.subsumes [sendInvS_inv.post_6] [b] := by
  sorry

theorem sendInvS_inv.obligation_14 :
    ∃ b ∈ inv, Expresso.subsumes [sendInvS_inv.post_8] [b] := by
  sorry

theorem sendInvAck_inv.obligation_1 :
    Unification.complete (Narrowing.mayFire sendInvAck freeP)
      [Unification.Unifier.bind fun (x : ℕ × CacheState × Req × Cmd × ℕ × Oids × Oids) =>
          ((x.1, x.2.1, x.2.2.1,
              {Item.dir
                  { cmd := x.2.2.2.1, ptr := x.2.2.2.2.1, exGntd := false, shr := x.2.2.2.2.2.1,
                    inv := x.2.2.2.2.2.2 }}),
            x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2,
            {Item.cache { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := Gnt.inv, ch3 := Ack.noAck }}),
        Unification.Unifier.bind fun (x : ℕ × CacheState × Req × Cmd × ℕ × Oids × Oids × Items) =>
          ((x.1, x.2.1, x.2.2.1,
              x.2.2.2.2.2.2.2 +
                {Item.dir
                    { cmd := x.2.2.2.1, ptr := x.2.2.2.2.1, exGntd := false, shr := x.2.2.2.2.2.1,
                      inv := x.2.2.2.2.2.2.1 }}),
            x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
            x.2.2.2.2.2.2.2 +
              {Item.cache { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := Gnt.inv, ch3 := Ack.noAck }})] := by
  maude_certify_comp

theorem sendInvAck_inv.obligation_2 :
    Unification.sound (Narrowing.mayFire sendInvAck freeP)
      [Unification.Unifier.bind fun (x : ℕ × CacheState × Req × Cmd × ℕ × Oids × Oids) =>
          ((x.1, x.2.1, x.2.2.1,
              {Item.dir
                  { cmd := x.2.2.2.1, ptr := x.2.2.2.2.1, exGntd := false, shr := x.2.2.2.2.2.1,
                    inv := x.2.2.2.2.2.2 }}),
            x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2,
            {Item.cache { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := Gnt.inv, ch3 := Ack.noAck }}),
        Unification.Unifier.bind fun (x : ℕ × CacheState × Req × Cmd × ℕ × Oids × Oids × Items) =>
          ((x.1, x.2.1, x.2.2.1,
              x.2.2.2.2.2.2.2 +
                {Item.dir
                    { cmd := x.2.2.2.1, ptr := x.2.2.2.2.1, exGntd := false, shr := x.2.2.2.2.2.1,
                      inv := x.2.2.2.2.2.2.1 }}),
            x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
            x.2.2.2.2.2.2.2 +
              {Item.cache { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := Gnt.inv, ch3 := Ack.noAck }})] := by
  sorry

theorem sendInvAck_inv.obligation_3 :
    Unification.complete (Narrowing.mayFire sendInvAck ownE)
      [Unification.Unifier.bind fun (x : ℕ × CacheState × Req × ℕ × Req × Cmd × ℕ × Oids) =>
          ((x.1, x.2.1, x.2.2.1,
              {Item.cache
                    { id := x.2.2.2.1, state := CacheState.exclusive, ch1 := x.2.2.2.2.1, ch2 := Gnt.noGnt,
                      ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.1},
                      inv := x.2.2.2.2.2.2.2 }}),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2, x.2.2.2.1, x.2.2.2.2.1,
            {Item.cache { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := Gnt.inv, ch3 := Ack.noAck }}),
        Unification.Unifier.bind fun (x : ℕ × CacheState × Req × ℕ × Req × Cmd × ℕ × Oids × Items) =>
          ((x.1, x.2.1, x.2.2.1,
              x.2.2.2.2.2.2.2.2 +
                  {Item.cache
                      { id := x.2.2.2.1, state := CacheState.exclusive, ch1 := x.2.2.2.2.1, ch2 := Gnt.noGnt,
                        ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.1},
                      inv := x.2.2.2.2.2.2.2.1 }}),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
            x.2.2.2.2.2.2.2.2 +
              {Item.cache { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := Gnt.inv, ch3 := Ack.noAck }})] := by
  maude_certify_comp

theorem sendInvAck_inv.obligation_4 :
    Unification.sound (Narrowing.mayFire sendInvAck ownE)
      [Unification.Unifier.bind fun (x : ℕ × CacheState × Req × ℕ × Req × Cmd × ℕ × Oids) =>
          ((x.1, x.2.1, x.2.2.1,
              {Item.cache
                    { id := x.2.2.2.1, state := CacheState.exclusive, ch1 := x.2.2.2.2.1, ch2 := Gnt.noGnt,
                      ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.1},
                      inv := x.2.2.2.2.2.2.2 }}),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2, x.2.2.2.1, x.2.2.2.2.1,
            {Item.cache { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := Gnt.inv, ch3 := Ack.noAck }}),
        Unification.Unifier.bind fun (x : ℕ × CacheState × Req × ℕ × Req × Cmd × ℕ × Oids × Items) =>
          ((x.1, x.2.1, x.2.2.1,
              x.2.2.2.2.2.2.2.2 +
                  {Item.cache
                      { id := x.2.2.2.1, state := CacheState.exclusive, ch1 := x.2.2.2.2.1, ch2 := Gnt.noGnt,
                        ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.1},
                      inv := x.2.2.2.2.2.2.2.1 }}),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
            x.2.2.2.2.2.2.2.2 +
              {Item.cache { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := Gnt.inv, ch3 := Ack.noAck }})] := by
  sorry

theorem sendInvAck_inv.obligation_5 :
    Unification.complete (Narrowing.mayFire sendInvAck ownG)
      [Unification.Unifier.bind fun (x : ℕ × CacheState × Req × ℕ × Req × Cmd × ℕ × Oids) =>
          ((x.1, x.2.1, x.2.2.1,
              {Item.cache
                    { id := x.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.1, ch2 := Gnt.gntE,
                      ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.1},
                      inv := x.2.2.2.2.2.2.2 }}),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2, x.2.2.2.1, x.2.2.2.2.1,
            {Item.cache { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := Gnt.inv, ch3 := Ack.noAck }}),
        Unification.Unifier.bind fun (x : ℕ × CacheState × Req × ℕ × Req × Cmd × ℕ × Oids × Items) =>
          ((x.1, x.2.1, x.2.2.1,
              x.2.2.2.2.2.2.2.2 +
                  {Item.cache
                      { id := x.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.1, ch2 := Gnt.gntE,
                        ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.1},
                      inv := x.2.2.2.2.2.2.2.1 }}),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
            x.2.2.2.2.2.2.2.2 +
              {Item.cache { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := Gnt.inv, ch3 := Ack.noAck }})] := by
  maude_certify_comp

theorem sendInvAck_inv.obligation_6 :
    Unification.sound (Narrowing.mayFire sendInvAck ownG)
      [Unification.Unifier.bind fun (x : ℕ × CacheState × Req × ℕ × Req × Cmd × ℕ × Oids) =>
          ((x.1, x.2.1, x.2.2.1,
              {Item.cache
                    { id := x.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.1, ch2 := Gnt.gntE,
                      ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.1},
                      inv := x.2.2.2.2.2.2.2 }}),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2, x.2.2.2.1, x.2.2.2.2.1,
            {Item.cache { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := Gnt.inv, ch3 := Ack.noAck }}),
        Unification.Unifier.bind fun (x : ℕ × CacheState × Req × ℕ × Req × Cmd × ℕ × Oids × Items) =>
          ((x.1, x.2.1, x.2.2.1,
              x.2.2.2.2.2.2.2.2 +
                  {Item.cache
                      { id := x.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.1, ch2 := Gnt.gntE,
                        ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.1},
                      inv := x.2.2.2.2.2.2.2.1 }}),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
            x.2.2.2.2.2.2.2.2 +
              {Item.cache { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := Gnt.inv, ch3 := Ack.noAck }})] := by
  sorry

theorem sendInvAck_inv.obligation_7 :
    Unification.complete (Narrowing.mayFire sendInvAck ownInv)
      [Unification.Unifier.bind fun (x : ℕ × CacheState × Req × ℕ × Req × Cmd × ℕ) =>
          ((x.1, x.2.1, x.2.2.1,
              {Item.cache
                    { id := x.2.2.2.1, state := CacheState.exclusive, ch1 := x.2.2.2.2.1, ch2 := Gnt.inv,
                      ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2, exGntd := true, shr := {x.2.2.2.1}, inv := ∅ }}),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2, x.2.2.2.1, x.2.2.2.2.1,
            {Item.cache { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := Gnt.inv, ch3 := Ack.noAck }}),
        Unification.Unifier.bind fun (x : ℕ × CacheState × Req × ℕ × Req × Cmd × ℕ × Items) =>
          ((x.1, x.2.1, x.2.2.1,
              x.2.2.2.2.2.2.2 +
                  {Item.cache
                      { id := x.2.2.2.1, state := CacheState.exclusive, ch1 := x.2.2.2.2.1, ch2 := Gnt.inv,
                        ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.1}, inv := ∅ }}),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
            x.2.2.2.2.2.2.2 +
              {Item.cache { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := Gnt.inv, ch3 := Ack.noAck }}),
        Unification.Unifier.bind fun (x : ℕ × Req × Cmd × ℕ) =>
          ((x.1, CacheState.exclusive, x.2.1,
              {Item.dir { cmd := x.2.2.1, ptr := x.2.2.2, exGntd := true, shr := {x.1}, inv := ∅ }}),
            x.2.2.1, x.2.2.2, x.1, x.2.1, ∅),
        Unification.Unifier.bind fun (x : Items × ℕ × Req × Cmd × ℕ) =>
          ((x.2.1, CacheState.exclusive, x.2.2.1,
              x.1 + {Item.dir { cmd := x.2.2.2.1, ptr := x.2.2.2.2, exGntd := true, shr := {x.2.1}, inv := ∅ }}),
            x.2.2.2.1, x.2.2.2.2, x.2.1, x.2.2.1, x.1)] := by
  maude_certify_comp

theorem sendInvAck_inv.obligation_8 :
    Unification.sound (Narrowing.mayFire sendInvAck ownInv)
      [Unification.Unifier.bind fun (x : ℕ × CacheState × Req × ℕ × Req × Cmd × ℕ) =>
          ((x.1, x.2.1, x.2.2.1,
              {Item.cache
                    { id := x.2.2.2.1, state := CacheState.exclusive, ch1 := x.2.2.2.2.1, ch2 := Gnt.inv,
                      ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2, exGntd := true, shr := {x.2.2.2.1}, inv := ∅ }}),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2, x.2.2.2.1, x.2.2.2.2.1,
            {Item.cache { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := Gnt.inv, ch3 := Ack.noAck }}),
        Unification.Unifier.bind fun (x : ℕ × CacheState × Req × ℕ × Req × Cmd × ℕ × Items) =>
          ((x.1, x.2.1, x.2.2.1,
              x.2.2.2.2.2.2.2 +
                  {Item.cache
                      { id := x.2.2.2.1, state := CacheState.exclusive, ch1 := x.2.2.2.2.1, ch2 := Gnt.inv,
                        ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.1}, inv := ∅ }}),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
            x.2.2.2.2.2.2.2 +
              {Item.cache { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := Gnt.inv, ch3 := Ack.noAck }}),
        Unification.Unifier.bind fun (x : ℕ × Req × Cmd × ℕ) =>
          ((x.1, CacheState.exclusive, x.2.1,
              {Item.dir { cmd := x.2.2.1, ptr := x.2.2.2, exGntd := true, shr := {x.1}, inv := ∅ }}),
            x.2.2.1, x.2.2.2, x.1, x.2.1, ∅),
        Unification.Unifier.bind fun (x : Items × ℕ × Req × Cmd × ℕ) =>
          ((x.2.1, CacheState.exclusive, x.2.2.1,
              x.1 + {Item.dir { cmd := x.2.2.2.1, ptr := x.2.2.2.2, exGntd := true, shr := {x.2.1}, inv := ∅ }}),
            x.2.2.2.1, x.2.2.2.2, x.2.1, x.2.2.1, x.1)] := by
  sorry

theorem sendInvAck_inv.obligation_9 :
    Unification.complete (Narrowing.mayFire sendInvAck ownAck)
      [Unification.Unifier.bind fun (x : ℕ × CacheState × Req × ℕ × Req × Cmd × ℕ) =>
          ((x.1, x.2.1, x.2.2.1,
              {Item.cache
                    { id := x.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.1, ch2 := Gnt.noGnt,
                      ch3 := Ack.invAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2, exGntd := true, shr := {x.2.2.2.1}, inv := ∅ }}),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2, x.2.2.2.1, x.2.2.2.2.1,
            {Item.cache { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := Gnt.inv, ch3 := Ack.noAck }}),
        Unification.Unifier.bind fun (x : ℕ × CacheState × Req × ℕ × Req × Cmd × ℕ × Items) =>
          ((x.1, x.2.1, x.2.2.1,
              x.2.2.2.2.2.2.2 +
                  {Item.cache
                      { id := x.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.1, ch2 := Gnt.noGnt,
                        ch3 := Ack.invAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.1}, inv := ∅ }}),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
            x.2.2.2.2.2.2.2 +
              {Item.cache { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := Gnt.inv, ch3 := Ack.noAck }})] := by
  maude_certify_comp

theorem sendInvAck_inv.obligation_10 :
    Unification.sound (Narrowing.mayFire sendInvAck ownAck)
      [Unification.Unifier.bind fun (x : ℕ × CacheState × Req × ℕ × Req × Cmd × ℕ) =>
          ((x.1, x.2.1, x.2.2.1,
              {Item.cache
                    { id := x.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.1, ch2 := Gnt.noGnt,
                      ch3 := Ack.invAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2, exGntd := true, shr := {x.2.2.2.1}, inv := ∅ }}),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2, x.2.2.2.1, x.2.2.2.2.1,
            {Item.cache { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := Gnt.inv, ch3 := Ack.noAck }}),
        Unification.Unifier.bind fun (x : ℕ × CacheState × Req × ℕ × Req × Cmd × ℕ × Items) =>
          ((x.1, x.2.1, x.2.2.1,
              x.2.2.2.2.2.2.2 +
                  {Item.cache
                      { id := x.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.1, ch2 := Gnt.noGnt,
                        ch3 := Ack.invAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.1}, inv := ∅ }}),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
            x.2.2.2.2.2.2.2 +
              {Item.cache { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := Gnt.inv, ch3 := Ack.noAck }})] := by
  sorry

theorem recvInvAckS_inv.obligation_1 :
    Unification.complete (Narrowing.mayFire recvInvAckS freeP)
      [Unification.Unifier.bind fun (x : ℕ × ℕ × Oids × Oids × CacheState × Req × Gnt × Cmd × ℕ × Bool × Oids × Cmd) =>
          ((x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.1, ∅, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.1,
              x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
              {Item.dir
                  { cmd := x.2.2.2.2.2.2.2.2.2.2.2, ptr := x.2.1, exGntd := false, shr := x.2.2.1, inv := x.2.2.2.1 }}),
            x.2.2.2.2.2.2.2.2.2.2.2, x.2.1, x.2.2.1, x.2.2.2.1,
            {Item.cache
                  { id := x.1, state := x.2.2.2.2.1, ch1 := x.2.2.2.2.2.1, ch2 := x.2.2.2.2.2.2.1,
                    ch3 := Ack.invAck }} +
              {Item.dir
                  { cmd := x.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.2.1, shr := {x.1},
                    inv := x.2.2.2.2.2.2.2.2.2.2.1 }}),
        Unification.Unifier.bind
          fun (x : ℕ × Cmd × ℕ × Oids × Oids × CacheState × Req × Gnt × Cmd × ℕ × Bool × Oids × Oids) =>
          ((x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.1, x.2.2.2.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.2.2.2.2.2.2, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1,
              {Item.dir { cmd := x.2.1, ptr := x.2.2.1, exGntd := false, shr := x.2.2.2.1, inv := x.2.2.2.2.1 }}),
            x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
            {Item.cache
                  { id := x.1, state := x.2.2.2.2.2.1, ch1 := x.2.2.2.2.2.2.1, ch2 := x.2.2.2.2.2.2.2.1,
                    ch3 := Ack.invAck }} +
              {Item.dir
                  { cmd := x.2.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.2.2.1,
                    shr := {x.1} + x.2.2.2.2.2.2.2.2.2.2.2.1, inv := x.2.2.2.2.2.2.2.2.2.2.2.2 }}),
        Unification.Unifier.bind
          fun (x : ℕ × ℕ × Oids × Oids × Items × CacheState × Req × Gnt × Cmd × ℕ × Bool × Oids × Cmd) =>
          ((x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.1, ∅, x.2.2.2.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1,
              x.2.2.2.2.1 +
                {Item.dir
                    { cmd := x.2.2.2.2.2.2.2.2.2.2.2.2, ptr := x.2.1, exGntd := false, shr := x.2.2.1,
                      inv := x.2.2.2.1 }}),
            x.2.2.2.2.2.2.2.2.2.2.2.2, x.2.1, x.2.2.1, x.2.2.2.1,
            x.2.2.2.2.1 +
                {Item.cache
                    { id := x.1, state := x.2.2.2.2.2.1, ch1 := x.2.2.2.2.2.2.1, ch2 := x.2.2.2.2.2.2.2.1,
                      ch3 := Ack.invAck }} +
              {Item.dir
                  { cmd := x.2.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.2.2.1,
                    shr := {x.1}, inv := x.2.2.2.2.2.2.2.2.2.2.2.1 }}),
        Unification.Unifier.bind
          fun (x : ℕ × Cmd × ℕ × Oids × Oids × Items × CacheState × Req × Gnt × Cmd × ℕ × Bool × Oids × Oids) =>
          ((x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.1, x.1, x.2.2.2.2.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.2.2.2.2.2.2.2, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.1 +
                {Item.dir { cmd := x.2.1, ptr := x.2.2.1, exGntd := false, shr := x.2.2.2.1, inv := x.2.2.2.2.1 }}),
            x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
            x.2.2.2.2.2.1 +
                {Item.cache
                    { id := x.1, state := x.2.2.2.2.2.2.1, ch1 := x.2.2.2.2.2.2.2.1, ch2 := x.2.2.2.2.2.2.2.2.1,
                      ch3 := Ack.invAck }} +
              {Item.dir
                  { cmd := x.2.2.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.2.2.2.1,
                    shr := {x.1} + x.2.2.2.2.2.2.2.2.2.2.2.2.1, inv := x.2.2.2.2.2.2.2.2.2.2.2.2.2 }}),
        Unification.Unifier.bind fun (x : ℕ × CacheState × Req × Gnt × Cmd × ℕ × Oids) =>
          ((x.2.2.2.2.1, x.2.2.2.2.2.1, false, x.1, ∅, x.2.2.2.2.2.2, x.2.1, x.2.2.1, x.2.2.2.1, ∅), x.2.2.2.2.1,
            x.2.2.2.2.2.1, {x.1}, x.2.2.2.2.2.2,
            {Item.cache { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := x.2.2.2.1, ch3 := Ack.invAck }}),
        Unification.Unifier.bind fun (x : ℕ × CacheState × Req × Gnt × Oids × Cmd × ℕ × Oids) =>
          ((x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, false, x.1, x.2.2.2.2.1, x.2.2.2.2.2.2.2, x.2.1, x.2.2.1, x.2.2.2.1, ∅),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, {x.1} + x.2.2.2.2.1, x.2.2.2.2.2.2.2,
            {Item.cache { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := x.2.2.2.1, ch3 := Ack.invAck }}),
        Unification.Unifier.bind fun (x : Items × ℕ × CacheState × Req × Gnt × Cmd × ℕ × Oids) =>
          ((x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, false, x.2.1, ∅, x.2.2.2.2.2.2.2, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.1),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, {x.2.1}, x.2.2.2.2.2.2.2,
            x.1 +
              {Item.cache { id := x.2.1, state := x.2.2.1, ch1 := x.2.2.2.1, ch2 := x.2.2.2.2.1, ch3 := Ack.invAck }}),
        Unification.Unifier.bind fun (x : Items × ℕ × CacheState × Req × Gnt × Oids × Cmd × ℕ × Oids) =>
          ((x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, false, x.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2, x.2.2.1, x.2.2.2.1,
              x.2.2.2.2.1, x.1),
            x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, {x.2.1} + x.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2,
            x.1 +
              {Item.cache
                  { id := x.2.1, state := x.2.2.1, ch1 := x.2.2.2.1, ch2 := x.2.2.2.2.1, ch3 := Ack.invAck }})] := by
  maude_certify_comp

theorem recvInvAckS_inv.obligation_2 :
    Unification.sound (Narrowing.mayFire recvInvAckS freeP)
      [Unification.Unifier.bind fun (x : ℕ × ℕ × Oids × Oids × CacheState × Req × Gnt × Cmd × ℕ × Bool × Oids × Cmd) =>
          ((x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.1, ∅, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.1,
              x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
              {Item.dir
                  { cmd := x.2.2.2.2.2.2.2.2.2.2.2, ptr := x.2.1, exGntd := false, shr := x.2.2.1, inv := x.2.2.2.1 }}),
            x.2.2.2.2.2.2.2.2.2.2.2, x.2.1, x.2.2.1, x.2.2.2.1,
            {Item.cache
                  { id := x.1, state := x.2.2.2.2.1, ch1 := x.2.2.2.2.2.1, ch2 := x.2.2.2.2.2.2.1,
                    ch3 := Ack.invAck }} +
              {Item.dir
                  { cmd := x.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.2.1, shr := {x.1},
                    inv := x.2.2.2.2.2.2.2.2.2.2.1 }}),
        Unification.Unifier.bind
          fun (x : ℕ × Cmd × ℕ × Oids × Oids × CacheState × Req × Gnt × Cmd × ℕ × Bool × Oids × Oids) =>
          ((x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.1, x.2.2.2.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.2.2.2.2.2.2, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1,
              {Item.dir { cmd := x.2.1, ptr := x.2.2.1, exGntd := false, shr := x.2.2.2.1, inv := x.2.2.2.2.1 }}),
            x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
            {Item.cache
                  { id := x.1, state := x.2.2.2.2.2.1, ch1 := x.2.2.2.2.2.2.1, ch2 := x.2.2.2.2.2.2.2.1,
                    ch3 := Ack.invAck }} +
              {Item.dir
                  { cmd := x.2.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.2.2.1,
                    shr := {x.1} + x.2.2.2.2.2.2.2.2.2.2.2.1, inv := x.2.2.2.2.2.2.2.2.2.2.2.2 }}),
        Unification.Unifier.bind
          fun (x : ℕ × ℕ × Oids × Oids × Items × CacheState × Req × Gnt × Cmd × ℕ × Bool × Oids × Cmd) =>
          ((x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.1, ∅, x.2.2.2.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1,
              x.2.2.2.2.1 +
                {Item.dir
                    { cmd := x.2.2.2.2.2.2.2.2.2.2.2.2, ptr := x.2.1, exGntd := false, shr := x.2.2.1,
                      inv := x.2.2.2.1 }}),
            x.2.2.2.2.2.2.2.2.2.2.2.2, x.2.1, x.2.2.1, x.2.2.2.1,
            x.2.2.2.2.1 +
                {Item.cache
                    { id := x.1, state := x.2.2.2.2.2.1, ch1 := x.2.2.2.2.2.2.1, ch2 := x.2.2.2.2.2.2.2.1,
                      ch3 := Ack.invAck }} +
              {Item.dir
                  { cmd := x.2.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.2.2.1,
                    shr := {x.1}, inv := x.2.2.2.2.2.2.2.2.2.2.2.1 }}),
        Unification.Unifier.bind
          fun (x : ℕ × Cmd × ℕ × Oids × Oids × Items × CacheState × Req × Gnt × Cmd × ℕ × Bool × Oids × Oids) =>
          ((x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.1, x.1, x.2.2.2.2.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.2.2.2.2.2.2.2, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.1 +
                {Item.dir { cmd := x.2.1, ptr := x.2.2.1, exGntd := false, shr := x.2.2.2.1, inv := x.2.2.2.2.1 }}),
            x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
            x.2.2.2.2.2.1 +
                {Item.cache
                    { id := x.1, state := x.2.2.2.2.2.2.1, ch1 := x.2.2.2.2.2.2.2.1, ch2 := x.2.2.2.2.2.2.2.2.1,
                      ch3 := Ack.invAck }} +
              {Item.dir
                  { cmd := x.2.2.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.2.2.2.1,
                    shr := {x.1} + x.2.2.2.2.2.2.2.2.2.2.2.2.1, inv := x.2.2.2.2.2.2.2.2.2.2.2.2.2 }}),
        Unification.Unifier.bind fun (x : ℕ × CacheState × Req × Gnt × Cmd × ℕ × Oids) =>
          ((x.2.2.2.2.1, x.2.2.2.2.2.1, false, x.1, ∅, x.2.2.2.2.2.2, x.2.1, x.2.2.1, x.2.2.2.1, ∅), x.2.2.2.2.1,
            x.2.2.2.2.2.1, {x.1}, x.2.2.2.2.2.2,
            {Item.cache { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := x.2.2.2.1, ch3 := Ack.invAck }}),
        Unification.Unifier.bind fun (x : ℕ × CacheState × Req × Gnt × Oids × Cmd × ℕ × Oids) =>
          ((x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, false, x.1, x.2.2.2.2.1, x.2.2.2.2.2.2.2, x.2.1, x.2.2.1, x.2.2.2.1, ∅),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, {x.1} + x.2.2.2.2.1, x.2.2.2.2.2.2.2,
            {Item.cache { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := x.2.2.2.1, ch3 := Ack.invAck }}),
        Unification.Unifier.bind fun (x : Items × ℕ × CacheState × Req × Gnt × Cmd × ℕ × Oids) =>
          ((x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, false, x.2.1, ∅, x.2.2.2.2.2.2.2, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.1),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, {x.2.1}, x.2.2.2.2.2.2.2,
            x.1 +
              {Item.cache { id := x.2.1, state := x.2.2.1, ch1 := x.2.2.2.1, ch2 := x.2.2.2.2.1, ch3 := Ack.invAck }}),
        Unification.Unifier.bind fun (x : Items × ℕ × CacheState × Req × Gnt × Oids × Cmd × ℕ × Oids) =>
          ((x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, false, x.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2, x.2.2.1, x.2.2.2.1,
              x.2.2.2.2.1, x.1),
            x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, {x.2.1} + x.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2,
            x.1 +
              {Item.cache
                  { id := x.2.1, state := x.2.2.1, ch1 := x.2.2.2.1, ch2 := x.2.2.2.2.1, ch3 := Ack.invAck }})] := by
  sorry

theorem recvInvAckS_inv.obligation_3 :
    Unification.complete (Narrowing.mayFire recvInvAckS ownE)
      [Unification.Unifier.bind
          fun (x : ℕ × Req × Cmd × ℕ × Oids × CacheState × Req × Gnt × Cmd × ℕ × Bool × Oids × ℕ) =>
          ((x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.1, ∅, x.2.2.2.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1,
              {Item.cache
                    { id := x.2.2.2.2.2.2.2.2.2.2.2.2, state := CacheState.exclusive, ch1 := x.2.1, ch2 := Gnt.noGnt,
                      ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.1, ptr := x.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.2.2.2.2},
                      inv := x.2.2.2.2.1 }}),
            x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2, x.2.1,
            {Item.cache
                  { id := x.1, state := x.2.2.2.2.2.1, ch1 := x.2.2.2.2.2.2.1, ch2 := x.2.2.2.2.2.2.2.1,
                    ch3 := Ack.invAck }} +
              {Item.dir
                  { cmd := x.2.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.2.2.1,
                    shr := {x.1}, inv := x.2.2.2.2.2.2.2.2.2.2.2.1 }}),
        Unification.Unifier.bind
          fun (x : ℕ × ℕ × Req × Cmd × ℕ × Oids × CacheState × Req × Gnt × Cmd × ℕ × Bool × Oids × Oids) =>
          ((x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.1, x.1, x.2.2.2.2.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.2.2.2.2.2.2.2, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1,
              {Item.cache
                    { id := x.2.1, state := CacheState.exclusive, ch1 := x.2.2.1, ch2 := Gnt.noGnt,
                      ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.2.1, ptr := x.2.2.2.2.1, exGntd := true, shr := {x.2.1}, inv := x.2.2.2.2.2.1 }}),
            x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.1, x.2.2.1,
            {Item.cache
                  { id := x.1, state := x.2.2.2.2.2.2.1, ch1 := x.2.2.2.2.2.2.2.1, ch2 := x.2.2.2.2.2.2.2.2.1,
                    ch3 := Ack.invAck }} +
              {Item.dir
                  { cmd := x.2.2.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.2.2.2.1,
                    shr := {x.1} + x.2.2.2.2.2.2.2.2.2.2.2.2.1, inv := x.2.2.2.2.2.2.2.2.2.2.2.2.2 }}),
        Unification.Unifier.bind
          fun (x : ℕ × Req × Cmd × ℕ × Oids × Items × CacheState × Req × Gnt × Cmd × ℕ × Bool × Oids × ℕ) =>
          ((x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.1, x.1, ∅,
              x.2.2.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.1 +
                  {Item.cache
                      { id := x.2.2.2.2.2.2.2.2.2.2.2.2.2, state := CacheState.exclusive, ch1 := x.2.1,
                        ch2 := Gnt.noGnt, ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.1, ptr := x.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.2.2.2.2.2},
                      inv := x.2.2.2.2.1 }}),
            x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2.2, x.2.1,
            x.2.2.2.2.2.1 +
                {Item.cache
                    { id := x.1, state := x.2.2.2.2.2.2.1, ch1 := x.2.2.2.2.2.2.2.1, ch2 := x.2.2.2.2.2.2.2.2.1,
                      ch3 := Ack.invAck }} +
              {Item.dir
                  { cmd := x.2.2.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.2.2.2.1,
                    shr := {x.1}, inv := x.2.2.2.2.2.2.2.2.2.2.2.2.1 }}),
        Unification.Unifier.bind
          fun (x : ℕ × ℕ × Req × Cmd × ℕ × Oids × Items × CacheState × Req × Gnt × Cmd × ℕ × Bool × Oids × Oids) =>
          ((x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2.1, x.1,
              x.2.2.2.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2.2.2, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.1 +
                  {Item.cache
                      { id := x.2.1, state := CacheState.exclusive, ch1 := x.2.2.1, ch2 := Gnt.noGnt,
                        ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.2.1, ptr := x.2.2.2.2.1, exGntd := true, shr := {x.2.1}, inv := x.2.2.2.2.2.1 }}),
            x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.1, x.2.2.1,
            x.2.2.2.2.2.2.1 +
                {Item.cache
                    { id := x.1, state := x.2.2.2.2.2.2.2.1, ch1 := x.2.2.2.2.2.2.2.2.1, ch2 := x.2.2.2.2.2.2.2.2.2.1,
                      ch3 := Ack.invAck }} +
              {Item.dir
                  { cmd := x.2.2.2.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.2.2.2.1,
                    exGntd := x.2.2.2.2.2.2.2.2.2.2.2.2.1, shr := {x.1} + x.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
                    inv := x.2.2.2.2.2.2.2.2.2.2.2.2.2.2 }}),
        Unification.Unifier.bind fun (x : CacheState × Req × Gnt × ℕ × Req × Cmd × ℕ × Oids) =>
          ((x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, true, x.2.2.2.1, ∅, x.2.2.2.2.2.2.2, x.1, x.2.1, x.2.2.1,
              {Item.cache
                  { id := x.2.2.2.1, state := CacheState.exclusive, ch1 := x.2.2.2.2.1, ch2 := Gnt.noGnt,
                    ch3 := Ack.noAck }}),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2, x.2.2.2.1, x.2.2.2.2.1,
            {Item.cache { id := x.2.2.2.1, state := x.1, ch1 := x.2.1, ch2 := x.2.2.1, ch3 := Ack.invAck }}),
        Unification.Unifier.bind fun (x : CacheState × Req × Gnt × ℕ × Req × Cmd × ℕ × Oids × Items) =>
          ((x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, true, x.2.2.2.1, ∅, x.2.2.2.2.2.2.2.1, x.1, x.2.1, x.2.2.1,
              x.2.2.2.2.2.2.2.2 +
                {Item.cache
                    { id := x.2.2.2.1, state := CacheState.exclusive, ch1 := x.2.2.2.2.1, ch2 := Gnt.noGnt,
                      ch3 := Ack.noAck }}),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
            x.2.2.2.2.2.2.2.2 +
              {Item.cache { id := x.2.2.2.1, state := x.1, ch1 := x.2.1, ch2 := x.2.2.1, ch3 := Ack.invAck }})] := by
  maude_certify_comp

theorem recvInvAckS_inv.obligation_4 :
    Unification.sound (Narrowing.mayFire recvInvAckS ownE)
      [Unification.Unifier.bind
          fun (x : ℕ × Req × Cmd × ℕ × Oids × CacheState × Req × Gnt × Cmd × ℕ × Bool × Oids × ℕ) =>
          ((x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.1, ∅, x.2.2.2.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1,
              {Item.cache
                    { id := x.2.2.2.2.2.2.2.2.2.2.2.2, state := CacheState.exclusive, ch1 := x.2.1, ch2 := Gnt.noGnt,
                      ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.1, ptr := x.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.2.2.2.2},
                      inv := x.2.2.2.2.1 }}),
            x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2, x.2.1,
            {Item.cache
                  { id := x.1, state := x.2.2.2.2.2.1, ch1 := x.2.2.2.2.2.2.1, ch2 := x.2.2.2.2.2.2.2.1,
                    ch3 := Ack.invAck }} +
              {Item.dir
                  { cmd := x.2.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.2.2.1,
                    shr := {x.1}, inv := x.2.2.2.2.2.2.2.2.2.2.2.1 }}),
        Unification.Unifier.bind
          fun (x : ℕ × ℕ × Req × Cmd × ℕ × Oids × CacheState × Req × Gnt × Cmd × ℕ × Bool × Oids × Oids) =>
          ((x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.1, x.1, x.2.2.2.2.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.2.2.2.2.2.2.2, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1,
              {Item.cache
                    { id := x.2.1, state := CacheState.exclusive, ch1 := x.2.2.1, ch2 := Gnt.noGnt,
                      ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.2.1, ptr := x.2.2.2.2.1, exGntd := true, shr := {x.2.1}, inv := x.2.2.2.2.2.1 }}),
            x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.1, x.2.2.1,
            {Item.cache
                  { id := x.1, state := x.2.2.2.2.2.2.1, ch1 := x.2.2.2.2.2.2.2.1, ch2 := x.2.2.2.2.2.2.2.2.1,
                    ch3 := Ack.invAck }} +
              {Item.dir
                  { cmd := x.2.2.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.2.2.2.1,
                    shr := {x.1} + x.2.2.2.2.2.2.2.2.2.2.2.2.1, inv := x.2.2.2.2.2.2.2.2.2.2.2.2.2 }}),
        Unification.Unifier.bind
          fun (x : ℕ × Req × Cmd × ℕ × Oids × Items × CacheState × Req × Gnt × Cmd × ℕ × Bool × Oids × ℕ) =>
          ((x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.1, x.1, ∅,
              x.2.2.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.1 +
                  {Item.cache
                      { id := x.2.2.2.2.2.2.2.2.2.2.2.2.2, state := CacheState.exclusive, ch1 := x.2.1,
                        ch2 := Gnt.noGnt, ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.1, ptr := x.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.2.2.2.2.2},
                      inv := x.2.2.2.2.1 }}),
            x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2.2, x.2.1,
            x.2.2.2.2.2.1 +
                {Item.cache
                    { id := x.1, state := x.2.2.2.2.2.2.1, ch1 := x.2.2.2.2.2.2.2.1, ch2 := x.2.2.2.2.2.2.2.2.1,
                      ch3 := Ack.invAck }} +
              {Item.dir
                  { cmd := x.2.2.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.2.2.2.1,
                    shr := {x.1}, inv := x.2.2.2.2.2.2.2.2.2.2.2.2.1 }}),
        Unification.Unifier.bind
          fun (x : ℕ × ℕ × Req × Cmd × ℕ × Oids × Items × CacheState × Req × Gnt × Cmd × ℕ × Bool × Oids × Oids) =>
          ((x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2.1, x.1,
              x.2.2.2.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2.2.2, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.1 +
                  {Item.cache
                      { id := x.2.1, state := CacheState.exclusive, ch1 := x.2.2.1, ch2 := Gnt.noGnt,
                        ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.2.1, ptr := x.2.2.2.2.1, exGntd := true, shr := {x.2.1}, inv := x.2.2.2.2.2.1 }}),
            x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.1, x.2.2.1,
            x.2.2.2.2.2.2.1 +
                {Item.cache
                    { id := x.1, state := x.2.2.2.2.2.2.2.1, ch1 := x.2.2.2.2.2.2.2.2.1, ch2 := x.2.2.2.2.2.2.2.2.2.1,
                      ch3 := Ack.invAck }} +
              {Item.dir
                  { cmd := x.2.2.2.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.2.2.2.1,
                    exGntd := x.2.2.2.2.2.2.2.2.2.2.2.2.1, shr := {x.1} + x.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
                    inv := x.2.2.2.2.2.2.2.2.2.2.2.2.2.2 }}),
        Unification.Unifier.bind fun (x : CacheState × Req × Gnt × ℕ × Req × Cmd × ℕ × Oids) =>
          ((x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, true, x.2.2.2.1, ∅, x.2.2.2.2.2.2.2, x.1, x.2.1, x.2.2.1,
              {Item.cache
                  { id := x.2.2.2.1, state := CacheState.exclusive, ch1 := x.2.2.2.2.1, ch2 := Gnt.noGnt,
                    ch3 := Ack.noAck }}),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2, x.2.2.2.1, x.2.2.2.2.1,
            {Item.cache { id := x.2.2.2.1, state := x.1, ch1 := x.2.1, ch2 := x.2.2.1, ch3 := Ack.invAck }}),
        Unification.Unifier.bind fun (x : CacheState × Req × Gnt × ℕ × Req × Cmd × ℕ × Oids × Items) =>
          ((x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, true, x.2.2.2.1, ∅, x.2.2.2.2.2.2.2.1, x.1, x.2.1, x.2.2.1,
              x.2.2.2.2.2.2.2.2 +
                {Item.cache
                    { id := x.2.2.2.1, state := CacheState.exclusive, ch1 := x.2.2.2.2.1, ch2 := Gnt.noGnt,
                      ch3 := Ack.noAck }}),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
            x.2.2.2.2.2.2.2.2 +
              {Item.cache { id := x.2.2.2.1, state := x.1, ch1 := x.2.1, ch2 := x.2.2.1, ch3 := Ack.invAck }})] := by
  sorry

theorem recvInvAckS_inv.obligation_5 :
    Unification.complete (Narrowing.mayFire recvInvAckS ownG)
      [Unification.Unifier.bind
          fun (x : ℕ × Req × Cmd × ℕ × Oids × CacheState × Req × Gnt × Cmd × ℕ × Bool × Oids × ℕ) =>
          ((x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.1, ∅, x.2.2.2.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1,
              {Item.cache
                    { id := x.2.2.2.2.2.2.2.2.2.2.2.2, state := CacheState.invalid, ch1 := x.2.1, ch2 := Gnt.gntE,
                      ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.1, ptr := x.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.2.2.2.2},
                      inv := x.2.2.2.2.1 }}),
            x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2, x.2.1,
            {Item.cache
                  { id := x.1, state := x.2.2.2.2.2.1, ch1 := x.2.2.2.2.2.2.1, ch2 := x.2.2.2.2.2.2.2.1,
                    ch3 := Ack.invAck }} +
              {Item.dir
                  { cmd := x.2.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.2.2.1,
                    shr := {x.1}, inv := x.2.2.2.2.2.2.2.2.2.2.2.1 }}),
        Unification.Unifier.bind
          fun (x : ℕ × ℕ × Req × Cmd × ℕ × Oids × CacheState × Req × Gnt × Cmd × ℕ × Bool × Oids × Oids) =>
          ((x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.1, x.1, x.2.2.2.2.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.2.2.2.2.2.2.2, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1,
              {Item.cache
                    { id := x.2.1, state := CacheState.invalid, ch1 := x.2.2.1, ch2 := Gnt.gntE, ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.2.1, ptr := x.2.2.2.2.1, exGntd := true, shr := {x.2.1}, inv := x.2.2.2.2.2.1 }}),
            x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.1, x.2.2.1,
            {Item.cache
                  { id := x.1, state := x.2.2.2.2.2.2.1, ch1 := x.2.2.2.2.2.2.2.1, ch2 := x.2.2.2.2.2.2.2.2.1,
                    ch3 := Ack.invAck }} +
              {Item.dir
                  { cmd := x.2.2.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.2.2.2.1,
                    shr := {x.1} + x.2.2.2.2.2.2.2.2.2.2.2.2.1, inv := x.2.2.2.2.2.2.2.2.2.2.2.2.2 }}),
        Unification.Unifier.bind
          fun (x : ℕ × Req × Cmd × ℕ × Oids × Items × CacheState × Req × Gnt × Cmd × ℕ × Bool × Oids × ℕ) =>
          ((x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.1, x.1, ∅,
              x.2.2.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.1 +
                  {Item.cache
                      { id := x.2.2.2.2.2.2.2.2.2.2.2.2.2, state := CacheState.invalid, ch1 := x.2.1, ch2 := Gnt.gntE,
                        ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.1, ptr := x.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.2.2.2.2.2},
                      inv := x.2.2.2.2.1 }}),
            x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2.2, x.2.1,
            x.2.2.2.2.2.1 +
                {Item.cache
                    { id := x.1, state := x.2.2.2.2.2.2.1, ch1 := x.2.2.2.2.2.2.2.1, ch2 := x.2.2.2.2.2.2.2.2.1,
                      ch3 := Ack.invAck }} +
              {Item.dir
                  { cmd := x.2.2.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.2.2.2.1,
                    shr := {x.1}, inv := x.2.2.2.2.2.2.2.2.2.2.2.2.1 }}),
        Unification.Unifier.bind
          fun (x : ℕ × ℕ × Req × Cmd × ℕ × Oids × Items × CacheState × Req × Gnt × Cmd × ℕ × Bool × Oids × Oids) =>
          ((x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2.1, x.1,
              x.2.2.2.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2.2.2, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.1 +
                  {Item.cache
                      { id := x.2.1, state := CacheState.invalid, ch1 := x.2.2.1, ch2 := Gnt.gntE, ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.2.1, ptr := x.2.2.2.2.1, exGntd := true, shr := {x.2.1}, inv := x.2.2.2.2.2.1 }}),
            x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.1, x.2.2.1,
            x.2.2.2.2.2.2.1 +
                {Item.cache
                    { id := x.1, state := x.2.2.2.2.2.2.2.1, ch1 := x.2.2.2.2.2.2.2.2.1, ch2 := x.2.2.2.2.2.2.2.2.2.1,
                      ch3 := Ack.invAck }} +
              {Item.dir
                  { cmd := x.2.2.2.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.2.2.2.1,
                    exGntd := x.2.2.2.2.2.2.2.2.2.2.2.2.1, shr := {x.1} + x.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
                    inv := x.2.2.2.2.2.2.2.2.2.2.2.2.2.2 }}),
        Unification.Unifier.bind fun (x : CacheState × Req × Gnt × ℕ × Req × Cmd × ℕ × Oids) =>
          ((x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, true, x.2.2.2.1, ∅, x.2.2.2.2.2.2.2, x.1, x.2.1, x.2.2.1,
              {Item.cache
                  { id := x.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.1, ch2 := Gnt.gntE,
                    ch3 := Ack.noAck }}),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2, x.2.2.2.1, x.2.2.2.2.1,
            {Item.cache { id := x.2.2.2.1, state := x.1, ch1 := x.2.1, ch2 := x.2.2.1, ch3 := Ack.invAck }}),
        Unification.Unifier.bind fun (x : CacheState × Req × Gnt × ℕ × Req × Cmd × ℕ × Oids × Items) =>
          ((x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, true, x.2.2.2.1, ∅, x.2.2.2.2.2.2.2.1, x.1, x.2.1, x.2.2.1,
              x.2.2.2.2.2.2.2.2 +
                {Item.cache
                    { id := x.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.1, ch2 := Gnt.gntE,
                      ch3 := Ack.noAck }}),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
            x.2.2.2.2.2.2.2.2 +
              {Item.cache { id := x.2.2.2.1, state := x.1, ch1 := x.2.1, ch2 := x.2.2.1, ch3 := Ack.invAck }})] := by
  maude_certify_comp

theorem recvInvAckS_inv.obligation_6 :
    Unification.sound (Narrowing.mayFire recvInvAckS ownG)
      [Unification.Unifier.bind
          fun (x : ℕ × Req × Cmd × ℕ × Oids × CacheState × Req × Gnt × Cmd × ℕ × Bool × Oids × ℕ) =>
          ((x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.1, ∅, x.2.2.2.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1,
              {Item.cache
                    { id := x.2.2.2.2.2.2.2.2.2.2.2.2, state := CacheState.invalid, ch1 := x.2.1, ch2 := Gnt.gntE,
                      ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.1, ptr := x.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.2.2.2.2},
                      inv := x.2.2.2.2.1 }}),
            x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2, x.2.1,
            {Item.cache
                  { id := x.1, state := x.2.2.2.2.2.1, ch1 := x.2.2.2.2.2.2.1, ch2 := x.2.2.2.2.2.2.2.1,
                    ch3 := Ack.invAck }} +
              {Item.dir
                  { cmd := x.2.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.2.2.1,
                    shr := {x.1}, inv := x.2.2.2.2.2.2.2.2.2.2.2.1 }}),
        Unification.Unifier.bind
          fun (x : ℕ × ℕ × Req × Cmd × ℕ × Oids × CacheState × Req × Gnt × Cmd × ℕ × Bool × Oids × Oids) =>
          ((x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.1, x.1, x.2.2.2.2.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.2.2.2.2.2.2.2, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1,
              {Item.cache
                    { id := x.2.1, state := CacheState.invalid, ch1 := x.2.2.1, ch2 := Gnt.gntE, ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.2.1, ptr := x.2.2.2.2.1, exGntd := true, shr := {x.2.1}, inv := x.2.2.2.2.2.1 }}),
            x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.1, x.2.2.1,
            {Item.cache
                  { id := x.1, state := x.2.2.2.2.2.2.1, ch1 := x.2.2.2.2.2.2.2.1, ch2 := x.2.2.2.2.2.2.2.2.1,
                    ch3 := Ack.invAck }} +
              {Item.dir
                  { cmd := x.2.2.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.2.2.2.1,
                    shr := {x.1} + x.2.2.2.2.2.2.2.2.2.2.2.2.1, inv := x.2.2.2.2.2.2.2.2.2.2.2.2.2 }}),
        Unification.Unifier.bind
          fun (x : ℕ × Req × Cmd × ℕ × Oids × Items × CacheState × Req × Gnt × Cmd × ℕ × Bool × Oids × ℕ) =>
          ((x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.1, x.1, ∅,
              x.2.2.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.1 +
                  {Item.cache
                      { id := x.2.2.2.2.2.2.2.2.2.2.2.2.2, state := CacheState.invalid, ch1 := x.2.1, ch2 := Gnt.gntE,
                        ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.1, ptr := x.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.2.2.2.2.2},
                      inv := x.2.2.2.2.1 }}),
            x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2.2, x.2.1,
            x.2.2.2.2.2.1 +
                {Item.cache
                    { id := x.1, state := x.2.2.2.2.2.2.1, ch1 := x.2.2.2.2.2.2.2.1, ch2 := x.2.2.2.2.2.2.2.2.1,
                      ch3 := Ack.invAck }} +
              {Item.dir
                  { cmd := x.2.2.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.2.2.2.1,
                    shr := {x.1}, inv := x.2.2.2.2.2.2.2.2.2.2.2.2.1 }}),
        Unification.Unifier.bind
          fun (x : ℕ × ℕ × Req × Cmd × ℕ × Oids × Items × CacheState × Req × Gnt × Cmd × ℕ × Bool × Oids × Oids) =>
          ((x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2.1, x.1,
              x.2.2.2.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2.2.2, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.1 +
                  {Item.cache
                      { id := x.2.1, state := CacheState.invalid, ch1 := x.2.2.1, ch2 := Gnt.gntE, ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.2.1, ptr := x.2.2.2.2.1, exGntd := true, shr := {x.2.1}, inv := x.2.2.2.2.2.1 }}),
            x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.1, x.2.2.1,
            x.2.2.2.2.2.2.1 +
                {Item.cache
                    { id := x.1, state := x.2.2.2.2.2.2.2.1, ch1 := x.2.2.2.2.2.2.2.2.1, ch2 := x.2.2.2.2.2.2.2.2.2.1,
                      ch3 := Ack.invAck }} +
              {Item.dir
                  { cmd := x.2.2.2.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.2.2.2.1,
                    exGntd := x.2.2.2.2.2.2.2.2.2.2.2.2.1, shr := {x.1} + x.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
                    inv := x.2.2.2.2.2.2.2.2.2.2.2.2.2.2 }}),
        Unification.Unifier.bind fun (x : CacheState × Req × Gnt × ℕ × Req × Cmd × ℕ × Oids) =>
          ((x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, true, x.2.2.2.1, ∅, x.2.2.2.2.2.2.2, x.1, x.2.1, x.2.2.1,
              {Item.cache
                  { id := x.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.1, ch2 := Gnt.gntE,
                    ch3 := Ack.noAck }}),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2, x.2.2.2.1, x.2.2.2.2.1,
            {Item.cache { id := x.2.2.2.1, state := x.1, ch1 := x.2.1, ch2 := x.2.2.1, ch3 := Ack.invAck }}),
        Unification.Unifier.bind fun (x : CacheState × Req × Gnt × ℕ × Req × Cmd × ℕ × Oids × Items) =>
          ((x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, true, x.2.2.2.1, ∅, x.2.2.2.2.2.2.2.1, x.1, x.2.1, x.2.2.1,
              x.2.2.2.2.2.2.2.2 +
                {Item.cache
                    { id := x.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.1, ch2 := Gnt.gntE,
                      ch3 := Ack.noAck }}),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
            x.2.2.2.2.2.2.2.2 +
              {Item.cache { id := x.2.2.2.1, state := x.1, ch1 := x.2.1, ch2 := x.2.2.1, ch3 := Ack.invAck }})] := by
  sorry

theorem recvInvAckS_inv.obligation_7 :
    Unification.complete (Narrowing.mayFire recvInvAckS ownInv)
      [Unification.Unifier.bind fun (x : ℕ × Req × Cmd × ℕ × CacheState × Req × Gnt × Cmd × ℕ × Bool × Oids × ℕ) =>
          ((x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.1, ∅, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.1,
              x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
              {Item.cache
                    { id := x.2.2.2.2.2.2.2.2.2.2.2, state := CacheState.exclusive, ch1 := x.2.1, ch2 := Gnt.inv,
                      ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.1, ptr := x.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.2.2.2}, inv := ∅ }}),
            x.2.2.1, x.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2, x.2.1,
            {Item.cache
                  { id := x.1, state := x.2.2.2.2.1, ch1 := x.2.2.2.2.2.1, ch2 := x.2.2.2.2.2.2.1,
                    ch3 := Ack.invAck }} +
              {Item.dir
                  { cmd := x.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.2.1, shr := {x.1},
                    inv := x.2.2.2.2.2.2.2.2.2.2.1 }}),
        Unification.Unifier.bind
          fun (x : ℕ × ℕ × Req × Cmd × ℕ × CacheState × Req × Gnt × Cmd × ℕ × Bool × Oids × Oids) =>
          ((x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.1, x.2.2.2.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.2.2.2.2.2.2, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1,
              {Item.cache
                    { id := x.2.1, state := CacheState.exclusive, ch1 := x.2.2.1, ch2 := Gnt.inv, ch3 := Ack.noAck }} +
                {Item.dir { cmd := x.2.2.2.1, ptr := x.2.2.2.2.1, exGntd := true, shr := {x.2.1}, inv := ∅ }}),
            x.2.2.2.1, x.2.2.2.2.1, x.2.1, x.2.2.1,
            {Item.cache
                  { id := x.1, state := x.2.2.2.2.2.1, ch1 := x.2.2.2.2.2.2.1, ch2 := x.2.2.2.2.2.2.2.1,
                    ch3 := Ack.invAck }} +
              {Item.dir
                  { cmd := x.2.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.2.2.1,
                    shr := {x.1} + x.2.2.2.2.2.2.2.2.2.2.2.1, inv := x.2.2.2.2.2.2.2.2.2.2.2.2 }}),
        Unification.Unifier.bind
          fun (x : ℕ × Req × Cmd × ℕ × Items × CacheState × Req × Gnt × Cmd × ℕ × Bool × Oids × ℕ) =>
          ((x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.1, ∅, x.2.2.2.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1,
              x.2.2.2.2.1 +
                  {Item.cache
                      { id := x.2.2.2.2.2.2.2.2.2.2.2.2, state := CacheState.exclusive, ch1 := x.2.1, ch2 := Gnt.inv,
                        ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.1, ptr := x.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.2.2.2.2},
                      inv := ∅ }}),
            x.2.2.1, x.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2, x.2.1,
            x.2.2.2.2.1 +
                {Item.cache
                    { id := x.1, state := x.2.2.2.2.2.1, ch1 := x.2.2.2.2.2.2.1, ch2 := x.2.2.2.2.2.2.2.1,
                      ch3 := Ack.invAck }} +
              {Item.dir
                  { cmd := x.2.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.2.2.1,
                    shr := {x.1}, inv := x.2.2.2.2.2.2.2.2.2.2.2.1 }}),
        Unification.Unifier.bind
          fun (x : ℕ × ℕ × Req × Cmd × ℕ × Items × CacheState × Req × Gnt × Cmd × ℕ × Bool × Oids × Oids) =>
          ((x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.1, x.1, x.2.2.2.2.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.2.2.2.2.2.2.2, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.1 +
                  {Item.cache
                      { id := x.2.1, state := CacheState.exclusive, ch1 := x.2.2.1, ch2 := Gnt.inv,
                        ch3 := Ack.noAck }} +
                {Item.dir { cmd := x.2.2.2.1, ptr := x.2.2.2.2.1, exGntd := true, shr := {x.2.1}, inv := ∅ }}),
            x.2.2.2.1, x.2.2.2.2.1, x.2.1, x.2.2.1,
            x.2.2.2.2.2.1 +
                {Item.cache
                    { id := x.1, state := x.2.2.2.2.2.2.1, ch1 := x.2.2.2.2.2.2.2.1, ch2 := x.2.2.2.2.2.2.2.2.1,
                      ch3 := Ack.invAck }} +
              {Item.dir
                  { cmd := x.2.2.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.2.2.2.1,
                    shr := {x.1} + x.2.2.2.2.2.2.2.2.2.2.2.2.1, inv := x.2.2.2.2.2.2.2.2.2.2.2.2.2 }}),
        Unification.Unifier.bind fun (x : CacheState × Req × Gnt × ℕ × Req × Cmd × ℕ) =>
          ((x.2.2.2.2.2.1, x.2.2.2.2.2.2, true, x.2.2.2.1, ∅, ∅, x.1, x.2.1, x.2.2.1,
              {Item.cache
                  { id := x.2.2.2.1, state := CacheState.exclusive, ch1 := x.2.2.2.2.1, ch2 := Gnt.inv,
                    ch3 := Ack.noAck }}),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2, x.2.2.2.1, x.2.2.2.2.1,
            {Item.cache { id := x.2.2.2.1, state := x.1, ch1 := x.2.1, ch2 := x.2.2.1, ch3 := Ack.invAck }}),
        Unification.Unifier.bind fun (x : CacheState × Req × Gnt × ℕ × Req × Cmd × ℕ × Items) =>
          ((x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, true, x.2.2.2.1, ∅, ∅, x.1, x.2.1, x.2.2.1,
              x.2.2.2.2.2.2.2 +
                {Item.cache
                    { id := x.2.2.2.1, state := CacheState.exclusive, ch1 := x.2.2.2.2.1, ch2 := Gnt.inv,
                      ch3 := Ack.noAck }}),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
            x.2.2.2.2.2.2.2 +
              {Item.cache { id := x.2.2.2.1, state := x.1, ch1 := x.2.1, ch2 := x.2.2.1, ch3 := Ack.invAck }})] := by
  maude_certify_comp

theorem recvInvAckS_inv.obligation_8 :
    Unification.sound (Narrowing.mayFire recvInvAckS ownInv)
      [Unification.Unifier.bind fun (x : ℕ × Req × Cmd × ℕ × CacheState × Req × Gnt × Cmd × ℕ × Bool × Oids × ℕ) =>
          ((x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.1, ∅, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.1,
              x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
              {Item.cache
                    { id := x.2.2.2.2.2.2.2.2.2.2.2, state := CacheState.exclusive, ch1 := x.2.1, ch2 := Gnt.inv,
                      ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.1, ptr := x.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.2.2.2}, inv := ∅ }}),
            x.2.2.1, x.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2, x.2.1,
            {Item.cache
                  { id := x.1, state := x.2.2.2.2.1, ch1 := x.2.2.2.2.2.1, ch2 := x.2.2.2.2.2.2.1,
                    ch3 := Ack.invAck }} +
              {Item.dir
                  { cmd := x.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.2.1, shr := {x.1},
                    inv := x.2.2.2.2.2.2.2.2.2.2.1 }}),
        Unification.Unifier.bind
          fun (x : ℕ × ℕ × Req × Cmd × ℕ × CacheState × Req × Gnt × Cmd × ℕ × Bool × Oids × Oids) =>
          ((x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.1, x.2.2.2.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.2.2.2.2.2.2, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1,
              {Item.cache
                    { id := x.2.1, state := CacheState.exclusive, ch1 := x.2.2.1, ch2 := Gnt.inv, ch3 := Ack.noAck }} +
                {Item.dir { cmd := x.2.2.2.1, ptr := x.2.2.2.2.1, exGntd := true, shr := {x.2.1}, inv := ∅ }}),
            x.2.2.2.1, x.2.2.2.2.1, x.2.1, x.2.2.1,
            {Item.cache
                  { id := x.1, state := x.2.2.2.2.2.1, ch1 := x.2.2.2.2.2.2.1, ch2 := x.2.2.2.2.2.2.2.1,
                    ch3 := Ack.invAck }} +
              {Item.dir
                  { cmd := x.2.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.2.2.1,
                    shr := {x.1} + x.2.2.2.2.2.2.2.2.2.2.2.1, inv := x.2.2.2.2.2.2.2.2.2.2.2.2 }}),
        Unification.Unifier.bind
          fun (x : ℕ × Req × Cmd × ℕ × Items × CacheState × Req × Gnt × Cmd × ℕ × Bool × Oids × ℕ) =>
          ((x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.1, ∅, x.2.2.2.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1,
              x.2.2.2.2.1 +
                  {Item.cache
                      { id := x.2.2.2.2.2.2.2.2.2.2.2.2, state := CacheState.exclusive, ch1 := x.2.1, ch2 := Gnt.inv,
                        ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.1, ptr := x.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.2.2.2.2},
                      inv := ∅ }}),
            x.2.2.1, x.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2, x.2.1,
            x.2.2.2.2.1 +
                {Item.cache
                    { id := x.1, state := x.2.2.2.2.2.1, ch1 := x.2.2.2.2.2.2.1, ch2 := x.2.2.2.2.2.2.2.1,
                      ch3 := Ack.invAck }} +
              {Item.dir
                  { cmd := x.2.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.2.2.1,
                    shr := {x.1}, inv := x.2.2.2.2.2.2.2.2.2.2.2.1 }}),
        Unification.Unifier.bind
          fun (x : ℕ × ℕ × Req × Cmd × ℕ × Items × CacheState × Req × Gnt × Cmd × ℕ × Bool × Oids × Oids) =>
          ((x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.1, x.1, x.2.2.2.2.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.2.2.2.2.2.2.2, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.1 +
                  {Item.cache
                      { id := x.2.1, state := CacheState.exclusive, ch1 := x.2.2.1, ch2 := Gnt.inv,
                        ch3 := Ack.noAck }} +
                {Item.dir { cmd := x.2.2.2.1, ptr := x.2.2.2.2.1, exGntd := true, shr := {x.2.1}, inv := ∅ }}),
            x.2.2.2.1, x.2.2.2.2.1, x.2.1, x.2.2.1,
            x.2.2.2.2.2.1 +
                {Item.cache
                    { id := x.1, state := x.2.2.2.2.2.2.1, ch1 := x.2.2.2.2.2.2.2.1, ch2 := x.2.2.2.2.2.2.2.2.1,
                      ch3 := Ack.invAck }} +
              {Item.dir
                  { cmd := x.2.2.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.2.2.2.1,
                    shr := {x.1} + x.2.2.2.2.2.2.2.2.2.2.2.2.1, inv := x.2.2.2.2.2.2.2.2.2.2.2.2.2 }}),
        Unification.Unifier.bind fun (x : CacheState × Req × Gnt × ℕ × Req × Cmd × ℕ) =>
          ((x.2.2.2.2.2.1, x.2.2.2.2.2.2, true, x.2.2.2.1, ∅, ∅, x.1, x.2.1, x.2.2.1,
              {Item.cache
                  { id := x.2.2.2.1, state := CacheState.exclusive, ch1 := x.2.2.2.2.1, ch2 := Gnt.inv,
                    ch3 := Ack.noAck }}),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2, x.2.2.2.1, x.2.2.2.2.1,
            {Item.cache { id := x.2.2.2.1, state := x.1, ch1 := x.2.1, ch2 := x.2.2.1, ch3 := Ack.invAck }}),
        Unification.Unifier.bind fun (x : CacheState × Req × Gnt × ℕ × Req × Cmd × ℕ × Items) =>
          ((x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, true, x.2.2.2.1, ∅, ∅, x.1, x.2.1, x.2.2.1,
              x.2.2.2.2.2.2.2 +
                {Item.cache
                    { id := x.2.2.2.1, state := CacheState.exclusive, ch1 := x.2.2.2.2.1, ch2 := Gnt.inv,
                      ch3 := Ack.noAck }}),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
            x.2.2.2.2.2.2.2 +
              {Item.cache { id := x.2.2.2.1, state := x.1, ch1 := x.2.1, ch2 := x.2.2.1, ch3 := Ack.invAck }})] := by
  sorry

theorem recvInvAckS_inv.obligation_9 :
    Unification.complete (Narrowing.mayFire recvInvAckS ownAck)
      [Unification.Unifier.bind fun (x : ℕ × Req × Cmd × ℕ × CacheState × Req × Gnt × Cmd × ℕ × Bool × Oids × ℕ) =>
          ((x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.1, ∅, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.1,
              x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
              {Item.cache
                    { id := x.2.2.2.2.2.2.2.2.2.2.2, state := CacheState.invalid, ch1 := x.2.1, ch2 := Gnt.noGnt,
                      ch3 := Ack.invAck }} +
                {Item.dir
                    { cmd := x.2.2.1, ptr := x.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.2.2.2}, inv := ∅ }}),
            x.2.2.1, x.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2, x.2.1,
            {Item.cache
                  { id := x.1, state := x.2.2.2.2.1, ch1 := x.2.2.2.2.2.1, ch2 := x.2.2.2.2.2.2.1,
                    ch3 := Ack.invAck }} +
              {Item.dir
                  { cmd := x.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.2.1, shr := {x.1},
                    inv := x.2.2.2.2.2.2.2.2.2.2.1 }}),
        Unification.Unifier.bind
          fun (x : ℕ × ℕ × Req × Cmd × ℕ × CacheState × Req × Gnt × Cmd × ℕ × Bool × Oids × Oids) =>
          ((x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.1, x.2.2.2.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.2.2.2.2.2.2, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1,
              {Item.cache
                    { id := x.2.1, state := CacheState.invalid, ch1 := x.2.2.1, ch2 := Gnt.noGnt, ch3 := Ack.invAck }} +
                {Item.dir { cmd := x.2.2.2.1, ptr := x.2.2.2.2.1, exGntd := true, shr := {x.2.1}, inv := ∅ }}),
            x.2.2.2.1, x.2.2.2.2.1, x.2.1, x.2.2.1,
            {Item.cache
                  { id := x.1, state := x.2.2.2.2.2.1, ch1 := x.2.2.2.2.2.2.1, ch2 := x.2.2.2.2.2.2.2.1,
                    ch3 := Ack.invAck }} +
              {Item.dir
                  { cmd := x.2.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.2.2.1,
                    shr := {x.1} + x.2.2.2.2.2.2.2.2.2.2.2.1, inv := x.2.2.2.2.2.2.2.2.2.2.2.2 }}),
        Unification.Unifier.bind
          fun (x : ℕ × Req × Cmd × ℕ × Items × CacheState × Req × Gnt × Cmd × ℕ × Bool × Oids × ℕ) =>
          ((x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.1, ∅, x.2.2.2.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1,
              x.2.2.2.2.1 +
                  {Item.cache
                      { id := x.2.2.2.2.2.2.2.2.2.2.2.2, state := CacheState.invalid, ch1 := x.2.1, ch2 := Gnt.noGnt,
                        ch3 := Ack.invAck }} +
                {Item.dir
                    { cmd := x.2.2.1, ptr := x.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.2.2.2.2},
                      inv := ∅ }}),
            x.2.2.1, x.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2, x.2.1,
            x.2.2.2.2.1 +
                {Item.cache
                    { id := x.1, state := x.2.2.2.2.2.1, ch1 := x.2.2.2.2.2.2.1, ch2 := x.2.2.2.2.2.2.2.1,
                      ch3 := Ack.invAck }} +
              {Item.dir
                  { cmd := x.2.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.2.2.1,
                    shr := {x.1}, inv := x.2.2.2.2.2.2.2.2.2.2.2.1 }}),
        Unification.Unifier.bind
          fun (x : ℕ × ℕ × Req × Cmd × ℕ × Items × CacheState × Req × Gnt × Cmd × ℕ × Bool × Oids × Oids) =>
          ((x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.1, x.1, x.2.2.2.2.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.2.2.2.2.2.2.2, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.1 +
                  {Item.cache
                      { id := x.2.1, state := CacheState.invalid, ch1 := x.2.2.1, ch2 := Gnt.noGnt,
                        ch3 := Ack.invAck }} +
                {Item.dir { cmd := x.2.2.2.1, ptr := x.2.2.2.2.1, exGntd := true, shr := {x.2.1}, inv := ∅ }}),
            x.2.2.2.1, x.2.2.2.2.1, x.2.1, x.2.2.1,
            x.2.2.2.2.2.1 +
                {Item.cache
                    { id := x.1, state := x.2.2.2.2.2.2.1, ch1 := x.2.2.2.2.2.2.2.1, ch2 := x.2.2.2.2.2.2.2.2.1,
                      ch3 := Ack.invAck }} +
              {Item.dir
                  { cmd := x.2.2.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.2.2.2.1,
                    shr := {x.1} + x.2.2.2.2.2.2.2.2.2.2.2.2.1, inv := x.2.2.2.2.2.2.2.2.2.2.2.2.2 }}),
        Unification.Unifier.bind fun (x : Cmd × ℕ × Bool × Oids × ℕ × Req × Cmd × ℕ) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.2.1, ∅, x.2.2.2.1, CacheState.invalid, x.2.2.2.2.2.1, Gnt.noGnt,
              {Item.dir
                  { cmd := x.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2, exGntd := true, shr := {x.2.2.2.2.1}, inv := ∅ }}),
            x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2, x.2.2.2.2.1, x.2.2.2.2.2.1,
            {Item.dir { cmd := x.1, ptr := x.2.1, exGntd := x.2.2.1, shr := {x.2.2.2.2.1}, inv := x.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : Cmd × ℕ × Bool × Oids × Oids × ℕ × Req × Cmd × ℕ) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.2.2.1, x.2.2.2.1, x.2.2.2.2.1, CacheState.invalid, x.2.2.2.2.2.2.1, Gnt.noGnt,
              {Item.dir
                  { cmd := x.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2, exGntd := true, shr := {x.2.2.2.2.2.1},
                    inv := ∅ }}),
            x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
            {Item.dir
                { cmd := x.1, ptr := x.2.1, exGntd := x.2.2.1, shr := {x.2.2.2.2.2.1} + x.2.2.2.1,
                  inv := x.2.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : Cmd × ℕ × Bool × Oids × ℕ × Req × Cmd × ℕ × Items) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.2.1, ∅, x.2.2.2.1, CacheState.invalid, x.2.2.2.2.2.1, Gnt.noGnt,
              x.2.2.2.2.2.2.2.2 +
                {Item.dir
                    { cmd := x.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.1},
                      inv := ∅ }}),
            x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
            x.2.2.2.2.2.2.2.2 +
              {Item.dir { cmd := x.1, ptr := x.2.1, exGntd := x.2.2.1, shr := {x.2.2.2.2.1}, inv := x.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : Cmd × Items × ℕ × Bool × Oids × Oids × ℕ × Req × Cmd × ℕ) =>
          ((x.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, CacheState.invalid, x.2.2.2.2.2.2.2.1,
              Gnt.noGnt,
              x.2.1 +
                {Item.dir
                    { cmd := x.2.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.2, exGntd := true, shr := {x.2.2.2.2.2.2.1},
                      inv := ∅ }}),
            x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1,
            x.2.1 +
              {Item.dir
                  { cmd := x.1, ptr := x.2.2.1, exGntd := x.2.2.2.1, shr := {x.2.2.2.2.2.2.1} + x.2.2.2.2.1,
                    inv := x.2.2.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : CacheState × Req × Gnt × ℕ × Req × Cmd × ℕ) =>
          ((x.2.2.2.2.2.1, x.2.2.2.2.2.2, true, x.2.2.2.1, ∅, ∅, x.1, x.2.1, x.2.2.1,
              {Item.cache
                  { id := x.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.1, ch2 := Gnt.noGnt,
                    ch3 := Ack.invAck }}),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2, x.2.2.2.1, x.2.2.2.2.1,
            {Item.cache { id := x.2.2.2.1, state := x.1, ch1 := x.2.1, ch2 := x.2.2.1, ch3 := Ack.invAck }}),
        Unification.Unifier.bind fun (x : CacheState × Req × Gnt × ℕ × Req × Cmd × ℕ × Items) =>
          ((x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, true, x.2.2.2.1, ∅, ∅, x.1, x.2.1, x.2.2.1,
              x.2.2.2.2.2.2.2 +
                {Item.cache
                    { id := x.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.1, ch2 := Gnt.noGnt,
                      ch3 := Ack.invAck }}),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
            x.2.2.2.2.2.2.2 +
              {Item.cache { id := x.2.2.2.1, state := x.1, ch1 := x.2.1, ch2 := x.2.2.1, ch3 := Ack.invAck }}),
        Unification.Unifier.bind fun (x : ℕ × Req × Cmd × ℕ) =>
          ((x.2.2.1, x.2.2.2, true, x.1, ∅, ∅, CacheState.invalid, x.2.1, Gnt.noGnt, ∅), x.2.2.1, x.2.2.2, x.1, x.2.1,
            ∅),
        Unification.Unifier.bind fun (x : Items × ℕ × Req × Cmd × ℕ) =>
          ((x.2.2.2.1, x.2.2.2.2, true, x.2.1, ∅, ∅, CacheState.invalid, x.2.2.1, Gnt.noGnt, x.1), x.2.2.2.1, x.2.2.2.2,
            x.2.1, x.2.2.1, x.1)] := by
  maude_certify_comp

theorem recvInvAckS_inv.obligation_10 :
    Unification.sound (Narrowing.mayFire recvInvAckS ownAck)
      [Unification.Unifier.bind fun (x : ℕ × Req × Cmd × ℕ × CacheState × Req × Gnt × Cmd × ℕ × Bool × Oids × ℕ) =>
          ((x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.1, ∅, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.1,
              x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
              {Item.cache
                    { id := x.2.2.2.2.2.2.2.2.2.2.2, state := CacheState.invalid, ch1 := x.2.1, ch2 := Gnt.noGnt,
                      ch3 := Ack.invAck }} +
                {Item.dir
                    { cmd := x.2.2.1, ptr := x.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.2.2.2}, inv := ∅ }}),
            x.2.2.1, x.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2, x.2.1,
            {Item.cache
                  { id := x.1, state := x.2.2.2.2.1, ch1 := x.2.2.2.2.2.1, ch2 := x.2.2.2.2.2.2.1,
                    ch3 := Ack.invAck }} +
              {Item.dir
                  { cmd := x.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.2.1, shr := {x.1},
                    inv := x.2.2.2.2.2.2.2.2.2.2.1 }}),
        Unification.Unifier.bind
          fun (x : ℕ × ℕ × Req × Cmd × ℕ × CacheState × Req × Gnt × Cmd × ℕ × Bool × Oids × Oids) =>
          ((x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.1, x.2.2.2.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.2.2.2.2.2.2, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1,
              {Item.cache
                    { id := x.2.1, state := CacheState.invalid, ch1 := x.2.2.1, ch2 := Gnt.noGnt, ch3 := Ack.invAck }} +
                {Item.dir { cmd := x.2.2.2.1, ptr := x.2.2.2.2.1, exGntd := true, shr := {x.2.1}, inv := ∅ }}),
            x.2.2.2.1, x.2.2.2.2.1, x.2.1, x.2.2.1,
            {Item.cache
                  { id := x.1, state := x.2.2.2.2.2.1, ch1 := x.2.2.2.2.2.2.1, ch2 := x.2.2.2.2.2.2.2.1,
                    ch3 := Ack.invAck }} +
              {Item.dir
                  { cmd := x.2.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.2.2.1,
                    shr := {x.1} + x.2.2.2.2.2.2.2.2.2.2.2.1, inv := x.2.2.2.2.2.2.2.2.2.2.2.2 }}),
        Unification.Unifier.bind
          fun (x : ℕ × Req × Cmd × ℕ × Items × CacheState × Req × Gnt × Cmd × ℕ × Bool × Oids × ℕ) =>
          ((x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.1, ∅, x.2.2.2.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1,
              x.2.2.2.2.1 +
                  {Item.cache
                      { id := x.2.2.2.2.2.2.2.2.2.2.2.2, state := CacheState.invalid, ch1 := x.2.1, ch2 := Gnt.noGnt,
                        ch3 := Ack.invAck }} +
                {Item.dir
                    { cmd := x.2.2.1, ptr := x.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.2.2.2.2},
                      inv := ∅ }}),
            x.2.2.1, x.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2, x.2.1,
            x.2.2.2.2.1 +
                {Item.cache
                    { id := x.1, state := x.2.2.2.2.2.1, ch1 := x.2.2.2.2.2.2.1, ch2 := x.2.2.2.2.2.2.2.1,
                      ch3 := Ack.invAck }} +
              {Item.dir
                  { cmd := x.2.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.2.2.1,
                    shr := {x.1}, inv := x.2.2.2.2.2.2.2.2.2.2.2.1 }}),
        Unification.Unifier.bind
          fun (x : ℕ × ℕ × Req × Cmd × ℕ × Items × CacheState × Req × Gnt × Cmd × ℕ × Bool × Oids × Oids) =>
          ((x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.1, x.1, x.2.2.2.2.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.2.2.2.2.2.2.2, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.1 +
                  {Item.cache
                      { id := x.2.1, state := CacheState.invalid, ch1 := x.2.2.1, ch2 := Gnt.noGnt,
                        ch3 := Ack.invAck }} +
                {Item.dir { cmd := x.2.2.2.1, ptr := x.2.2.2.2.1, exGntd := true, shr := {x.2.1}, inv := ∅ }}),
            x.2.2.2.1, x.2.2.2.2.1, x.2.1, x.2.2.1,
            x.2.2.2.2.2.1 +
                {Item.cache
                    { id := x.1, state := x.2.2.2.2.2.2.1, ch1 := x.2.2.2.2.2.2.2.1, ch2 := x.2.2.2.2.2.2.2.2.1,
                      ch3 := Ack.invAck }} +
              {Item.dir
                  { cmd := x.2.2.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.2.2.2.1,
                    shr := {x.1} + x.2.2.2.2.2.2.2.2.2.2.2.2.1, inv := x.2.2.2.2.2.2.2.2.2.2.2.2.2 }}),
        Unification.Unifier.bind fun (x : Cmd × ℕ × Bool × Oids × ℕ × Req × Cmd × ℕ) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.2.1, ∅, x.2.2.2.1, CacheState.invalid, x.2.2.2.2.2.1, Gnt.noGnt,
              {Item.dir
                  { cmd := x.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2, exGntd := true, shr := {x.2.2.2.2.1}, inv := ∅ }}),
            x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2, x.2.2.2.2.1, x.2.2.2.2.2.1,
            {Item.dir { cmd := x.1, ptr := x.2.1, exGntd := x.2.2.1, shr := {x.2.2.2.2.1}, inv := x.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : Cmd × ℕ × Bool × Oids × Oids × ℕ × Req × Cmd × ℕ) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.2.2.1, x.2.2.2.1, x.2.2.2.2.1, CacheState.invalid, x.2.2.2.2.2.2.1, Gnt.noGnt,
              {Item.dir
                  { cmd := x.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2, exGntd := true, shr := {x.2.2.2.2.2.1},
                    inv := ∅ }}),
            x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
            {Item.dir
                { cmd := x.1, ptr := x.2.1, exGntd := x.2.2.1, shr := {x.2.2.2.2.2.1} + x.2.2.2.1,
                  inv := x.2.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : Cmd × ℕ × Bool × Oids × ℕ × Req × Cmd × ℕ × Items) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.2.1, ∅, x.2.2.2.1, CacheState.invalid, x.2.2.2.2.2.1, Gnt.noGnt,
              x.2.2.2.2.2.2.2.2 +
                {Item.dir
                    { cmd := x.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.1},
                      inv := ∅ }}),
            x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
            x.2.2.2.2.2.2.2.2 +
              {Item.dir { cmd := x.1, ptr := x.2.1, exGntd := x.2.2.1, shr := {x.2.2.2.2.1}, inv := x.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : Cmd × Items × ℕ × Bool × Oids × Oids × ℕ × Req × Cmd × ℕ) =>
          ((x.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, CacheState.invalid, x.2.2.2.2.2.2.2.1,
              Gnt.noGnt,
              x.2.1 +
                {Item.dir
                    { cmd := x.2.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.2, exGntd := true, shr := {x.2.2.2.2.2.2.1},
                      inv := ∅ }}),
            x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1,
            x.2.1 +
              {Item.dir
                  { cmd := x.1, ptr := x.2.2.1, exGntd := x.2.2.2.1, shr := {x.2.2.2.2.2.2.1} + x.2.2.2.2.1,
                    inv := x.2.2.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : CacheState × Req × Gnt × ℕ × Req × Cmd × ℕ) =>
          ((x.2.2.2.2.2.1, x.2.2.2.2.2.2, true, x.2.2.2.1, ∅, ∅, x.1, x.2.1, x.2.2.1,
              {Item.cache
                  { id := x.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.1, ch2 := Gnt.noGnt,
                    ch3 := Ack.invAck }}),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2, x.2.2.2.1, x.2.2.2.2.1,
            {Item.cache { id := x.2.2.2.1, state := x.1, ch1 := x.2.1, ch2 := x.2.2.1, ch3 := Ack.invAck }}),
        Unification.Unifier.bind fun (x : CacheState × Req × Gnt × ℕ × Req × Cmd × ℕ × Items) =>
          ((x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, true, x.2.2.2.1, ∅, ∅, x.1, x.2.1, x.2.2.1,
              x.2.2.2.2.2.2.2 +
                {Item.cache
                    { id := x.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.1, ch2 := Gnt.noGnt,
                      ch3 := Ack.invAck }}),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
            x.2.2.2.2.2.2.2 +
              {Item.cache { id := x.2.2.2.1, state := x.1, ch1 := x.2.1, ch2 := x.2.2.1, ch3 := Ack.invAck }}),
        Unification.Unifier.bind fun (x : ℕ × Req × Cmd × ℕ) =>
          ((x.2.2.1, x.2.2.2, true, x.1, ∅, ∅, CacheState.invalid, x.2.1, Gnt.noGnt, ∅), x.2.2.1, x.2.2.2, x.1, x.2.1,
            ∅),
        Unification.Unifier.bind fun (x : Items × ℕ × Req × Cmd × ℕ) =>
          ((x.2.2.2.1, x.2.2.2.2, true, x.2.1, ∅, ∅, CacheState.invalid, x.2.2.1, Gnt.noGnt, x.1), x.2.2.2.1, x.2.2.2.2,
            x.2.1, x.2.2.1, x.1)] := by
  sorry

theorem recvInvAckN_inv.obligation_1 :
    Unification.complete (Narrowing.mayFire recvInvAckN freeP)
      [Unification.Unifier.bind
          fun (x : ℕ × Cmd × ℕ × Oids × Oids × CacheState × Req × Gnt × Cmd × ℕ × Bool × Oids × Oids) =>
          ((x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.2.2.2.2.2.2, x.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1,
              {Item.dir { cmd := x.2.1, ptr := x.2.2.1, exGntd := false, shr := x.2.2.2.1, inv := x.2.2.2.2.1 }}),
            x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
            {Item.cache
                  { id := x.1, state := x.2.2.2.2.2.1, ch1 := x.2.2.2.2.2.2.1, ch2 := x.2.2.2.2.2.2.2.1,
                    ch3 := Ack.invAck }} +
              {Item.dir
                  { cmd := x.2.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.2.2.1,
                    shr := x.2.2.2.2.2.2.2.2.2.2.2.1, inv := x.2.2.2.2.2.2.2.2.2.2.2.2 }}),
        Unification.Unifier.bind
          fun (x : ℕ × Cmd × ℕ × Oids × Oids × Items × CacheState × Req × Gnt × Cmd × ℕ × Bool × Oids × Oids) =>
          ((x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.2.2.2.2.2.2.2, x.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.1 +
                {Item.dir { cmd := x.2.1, ptr := x.2.2.1, exGntd := false, shr := x.2.2.2.1, inv := x.2.2.2.2.1 }}),
            x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
            x.2.2.2.2.2.1 +
                {Item.cache
                    { id := x.1, state := x.2.2.2.2.2.2.1, ch1 := x.2.2.2.2.2.2.2.1, ch2 := x.2.2.2.2.2.2.2.2.1,
                      ch3 := Ack.invAck }} +
              {Item.dir
                  { cmd := x.2.2.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.2.2.2.1,
                    shr := x.2.2.2.2.2.2.2.2.2.2.2.2.1, inv := x.2.2.2.2.2.2.2.2.2.2.2.2.2 }}),
        Unification.Unifier.bind fun (x : ℕ × CacheState × Req × Gnt × Cmd × ℕ × Oids × Oids) =>
          ((x.2.2.2.2.1, x.2.2.2.2.2.1, false, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2, x.1, x.2.1, x.2.2.1, x.2.2.2.1, ∅),
            x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2,
            {Item.cache { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := x.2.2.2.1, ch3 := Ack.invAck }}),
        Unification.Unifier.bind fun (x : Items × ℕ × CacheState × Req × Gnt × Cmd × ℕ × Oids × Oids) =>
          ((x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, false, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2, x.2.1, x.2.2.1, x.2.2.2.1,
              x.2.2.2.2.1, x.1),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2,
            x.1 +
              {Item.cache
                  { id := x.2.1, state := x.2.2.1, ch1 := x.2.2.2.1, ch2 := x.2.2.2.2.1, ch3 := Ack.invAck }})] := by
  maude_certify_comp

theorem recvInvAckN_inv.obligation_2 :
    Unification.sound (Narrowing.mayFire recvInvAckN freeP)
      [Unification.Unifier.bind
          fun (x : ℕ × Cmd × ℕ × Oids × Oids × CacheState × Req × Gnt × Cmd × ℕ × Bool × Oids × Oids) =>
          ((x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.2.2.2.2.2.2, x.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1,
              {Item.dir { cmd := x.2.1, ptr := x.2.2.1, exGntd := false, shr := x.2.2.2.1, inv := x.2.2.2.2.1 }}),
            x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
            {Item.cache
                  { id := x.1, state := x.2.2.2.2.2.1, ch1 := x.2.2.2.2.2.2.1, ch2 := x.2.2.2.2.2.2.2.1,
                    ch3 := Ack.invAck }} +
              {Item.dir
                  { cmd := x.2.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.2.2.1,
                    shr := x.2.2.2.2.2.2.2.2.2.2.2.1, inv := x.2.2.2.2.2.2.2.2.2.2.2.2 }}),
        Unification.Unifier.bind
          fun (x : ℕ × Cmd × ℕ × Oids × Oids × Items × CacheState × Req × Gnt × Cmd × ℕ × Bool × Oids × Oids) =>
          ((x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.2.2.2.2.2.2.2, x.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.1 +
                {Item.dir { cmd := x.2.1, ptr := x.2.2.1, exGntd := false, shr := x.2.2.2.1, inv := x.2.2.2.2.1 }}),
            x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
            x.2.2.2.2.2.1 +
                {Item.cache
                    { id := x.1, state := x.2.2.2.2.2.2.1, ch1 := x.2.2.2.2.2.2.2.1, ch2 := x.2.2.2.2.2.2.2.2.1,
                      ch3 := Ack.invAck }} +
              {Item.dir
                  { cmd := x.2.2.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.2.2.2.1,
                    shr := x.2.2.2.2.2.2.2.2.2.2.2.2.1, inv := x.2.2.2.2.2.2.2.2.2.2.2.2.2 }}),
        Unification.Unifier.bind fun (x : ℕ × CacheState × Req × Gnt × Cmd × ℕ × Oids × Oids) =>
          ((x.2.2.2.2.1, x.2.2.2.2.2.1, false, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2, x.1, x.2.1, x.2.2.1, x.2.2.2.1, ∅),
            x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2,
            {Item.cache { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := x.2.2.2.1, ch3 := Ack.invAck }}),
        Unification.Unifier.bind fun (x : Items × ℕ × CacheState × Req × Gnt × Cmd × ℕ × Oids × Oids) =>
          ((x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, false, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2, x.2.1, x.2.2.1, x.2.2.2.1,
              x.2.2.2.2.1, x.1),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2,
            x.1 +
              {Item.cache
                  { id := x.2.1, state := x.2.2.1, ch1 := x.2.2.2.1, ch2 := x.2.2.2.2.1, ch3 := Ack.invAck }})] := by
  sorry

theorem recvInvAckN_inv.obligation_3 :
    Unification.complete (Narrowing.mayFire recvInvAckN ownE)
      [Unification.Unifier.bind
          fun (x : ℕ × ℕ × Req × Cmd × ℕ × Oids × CacheState × Req × Gnt × Cmd × ℕ × Bool × Oids × Oids) =>
          ((x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.2.2.2.2.2.2.2, x.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1,
              {Item.cache
                    { id := x.2.1, state := CacheState.exclusive, ch1 := x.2.2.1, ch2 := Gnt.noGnt,
                      ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.2.1, ptr := x.2.2.2.2.1, exGntd := true, shr := {x.2.1}, inv := x.2.2.2.2.2.1 }}),
            x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.1, x.2.2.1,
            {Item.cache
                  { id := x.1, state := x.2.2.2.2.2.2.1, ch1 := x.2.2.2.2.2.2.2.1, ch2 := x.2.2.2.2.2.2.2.2.1,
                    ch3 := Ack.invAck }} +
              {Item.dir
                  { cmd := x.2.2.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.2.2.2.1,
                    shr := x.2.2.2.2.2.2.2.2.2.2.2.2.1, inv := x.2.2.2.2.2.2.2.2.2.2.2.2.2 }}),
        Unification.Unifier.bind
          fun (x : ℕ × ℕ × Req × Cmd × ℕ × Oids × Items × CacheState × Req × Gnt × Cmd × ℕ × Bool × Oids × Oids) =>
          ((x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2.2.2, x.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.1 +
                  {Item.cache
                      { id := x.2.1, state := CacheState.exclusive, ch1 := x.2.2.1, ch2 := Gnt.noGnt,
                        ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.2.1, ptr := x.2.2.2.2.1, exGntd := true, shr := {x.2.1}, inv := x.2.2.2.2.2.1 }}),
            x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.1, x.2.2.1,
            x.2.2.2.2.2.2.1 +
                {Item.cache
                    { id := x.1, state := x.2.2.2.2.2.2.2.1, ch1 := x.2.2.2.2.2.2.2.2.1, ch2 := x.2.2.2.2.2.2.2.2.2.1,
                      ch3 := Ack.invAck }} +
              {Item.dir
                  { cmd := x.2.2.2.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.2.2.2.1,
                    exGntd := x.2.2.2.2.2.2.2.2.2.2.2.2.1, shr := x.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
                    inv := x.2.2.2.2.2.2.2.2.2.2.2.2.2.2 }}),
        Unification.Unifier.bind fun (x : ℕ × CacheState × Req × Gnt × ℕ × Req × Cmd × ℕ × Oids) =>
          ((x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, true, {x.2.2.2.2.1}, x.2.2.2.2.2.2.2.2, x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {Item.cache
                  { id := x.2.2.2.2.1, state := CacheState.exclusive, ch1 := x.2.2.2.2.2.1, ch2 := Gnt.noGnt,
                    ch3 := Ack.noAck }}),
            x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2, x.2.2.2.2.1, x.2.2.2.2.2.1,
            {Item.cache { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := x.2.2.2.1, ch3 := Ack.invAck }}),
        Unification.Unifier.bind fun (x : ℕ × Items × CacheState × Req × Gnt × ℕ × Req × Cmd × ℕ × Oids) =>
          ((x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1, true, {x.2.2.2.2.2.1}, x.2.2.2.2.2.2.2.2.2, x.1, x.2.2.1, x.2.2.2.1,
              x.2.2.2.2.1,
              x.2.1 +
                {Item.cache
                    { id := x.2.2.2.2.2.1, state := CacheState.exclusive, ch1 := x.2.2.2.2.2.2.1, ch2 := Gnt.noGnt,
                      ch3 := Ack.noAck }}),
            x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
            x.2.1 +
              {Item.cache
                  { id := x.1, state := x.2.2.1, ch1 := x.2.2.2.1, ch2 := x.2.2.2.2.1, ch3 := Ack.invAck }})] := by
  maude_certify_comp

theorem recvInvAckN_inv.obligation_4 :
    Unification.sound (Narrowing.mayFire recvInvAckN ownE)
      [Unification.Unifier.bind
          fun (x : ℕ × ℕ × Req × Cmd × ℕ × Oids × CacheState × Req × Gnt × Cmd × ℕ × Bool × Oids × Oids) =>
          ((x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.2.2.2.2.2.2.2, x.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1,
              {Item.cache
                    { id := x.2.1, state := CacheState.exclusive, ch1 := x.2.2.1, ch2 := Gnt.noGnt,
                      ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.2.1, ptr := x.2.2.2.2.1, exGntd := true, shr := {x.2.1}, inv := x.2.2.2.2.2.1 }}),
            x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.1, x.2.2.1,
            {Item.cache
                  { id := x.1, state := x.2.2.2.2.2.2.1, ch1 := x.2.2.2.2.2.2.2.1, ch2 := x.2.2.2.2.2.2.2.2.1,
                    ch3 := Ack.invAck }} +
              {Item.dir
                  { cmd := x.2.2.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.2.2.2.1,
                    shr := x.2.2.2.2.2.2.2.2.2.2.2.2.1, inv := x.2.2.2.2.2.2.2.2.2.2.2.2.2 }}),
        Unification.Unifier.bind
          fun (x : ℕ × ℕ × Req × Cmd × ℕ × Oids × Items × CacheState × Req × Gnt × Cmd × ℕ × Bool × Oids × Oids) =>
          ((x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2.2.2, x.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.1 +
                  {Item.cache
                      { id := x.2.1, state := CacheState.exclusive, ch1 := x.2.2.1, ch2 := Gnt.noGnt,
                        ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.2.1, ptr := x.2.2.2.2.1, exGntd := true, shr := {x.2.1}, inv := x.2.2.2.2.2.1 }}),
            x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.1, x.2.2.1,
            x.2.2.2.2.2.2.1 +
                {Item.cache
                    { id := x.1, state := x.2.2.2.2.2.2.2.1, ch1 := x.2.2.2.2.2.2.2.2.1, ch2 := x.2.2.2.2.2.2.2.2.2.1,
                      ch3 := Ack.invAck }} +
              {Item.dir
                  { cmd := x.2.2.2.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.2.2.2.1,
                    exGntd := x.2.2.2.2.2.2.2.2.2.2.2.2.1, shr := x.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
                    inv := x.2.2.2.2.2.2.2.2.2.2.2.2.2.2 }}),
        Unification.Unifier.bind fun (x : ℕ × CacheState × Req × Gnt × ℕ × Req × Cmd × ℕ × Oids) =>
          ((x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, true, {x.2.2.2.2.1}, x.2.2.2.2.2.2.2.2, x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {Item.cache
                  { id := x.2.2.2.2.1, state := CacheState.exclusive, ch1 := x.2.2.2.2.2.1, ch2 := Gnt.noGnt,
                    ch3 := Ack.noAck }}),
            x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2, x.2.2.2.2.1, x.2.2.2.2.2.1,
            {Item.cache { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := x.2.2.2.1, ch3 := Ack.invAck }}),
        Unification.Unifier.bind fun (x : ℕ × Items × CacheState × Req × Gnt × ℕ × Req × Cmd × ℕ × Oids) =>
          ((x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1, true, {x.2.2.2.2.2.1}, x.2.2.2.2.2.2.2.2.2, x.1, x.2.2.1, x.2.2.2.1,
              x.2.2.2.2.1,
              x.2.1 +
                {Item.cache
                    { id := x.2.2.2.2.2.1, state := CacheState.exclusive, ch1 := x.2.2.2.2.2.2.1, ch2 := Gnt.noGnt,
                      ch3 := Ack.noAck }}),
            x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
            x.2.1 +
              {Item.cache
                  { id := x.1, state := x.2.2.1, ch1 := x.2.2.2.1, ch2 := x.2.2.2.2.1, ch3 := Ack.invAck }})] := by
  sorry

theorem recvInvAckN_inv.obligation_5 :
    Unification.complete (Narrowing.mayFire recvInvAckN ownG)
      [Unification.Unifier.bind
          fun (x : ℕ × ℕ × Req × Cmd × ℕ × Oids × CacheState × Req × Gnt × Cmd × ℕ × Bool × Oids × Oids) =>
          ((x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.2.2.2.2.2.2.2, x.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1,
              {Item.cache
                    { id := x.2.1, state := CacheState.invalid, ch1 := x.2.2.1, ch2 := Gnt.gntE, ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.2.1, ptr := x.2.2.2.2.1, exGntd := true, shr := {x.2.1}, inv := x.2.2.2.2.2.1 }}),
            x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.1, x.2.2.1,
            {Item.cache
                  { id := x.1, state := x.2.2.2.2.2.2.1, ch1 := x.2.2.2.2.2.2.2.1, ch2 := x.2.2.2.2.2.2.2.2.1,
                    ch3 := Ack.invAck }} +
              {Item.dir
                  { cmd := x.2.2.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.2.2.2.1,
                    shr := x.2.2.2.2.2.2.2.2.2.2.2.2.1, inv := x.2.2.2.2.2.2.2.2.2.2.2.2.2 }}),
        Unification.Unifier.bind
          fun (x : ℕ × ℕ × Req × Cmd × ℕ × Oids × Items × CacheState × Req × Gnt × Cmd × ℕ × Bool × Oids × Oids) =>
          ((x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2.2.2, x.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.1 +
                  {Item.cache
                      { id := x.2.1, state := CacheState.invalid, ch1 := x.2.2.1, ch2 := Gnt.gntE, ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.2.1, ptr := x.2.2.2.2.1, exGntd := true, shr := {x.2.1}, inv := x.2.2.2.2.2.1 }}),
            x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.1, x.2.2.1,
            x.2.2.2.2.2.2.1 +
                {Item.cache
                    { id := x.1, state := x.2.2.2.2.2.2.2.1, ch1 := x.2.2.2.2.2.2.2.2.1, ch2 := x.2.2.2.2.2.2.2.2.2.1,
                      ch3 := Ack.invAck }} +
              {Item.dir
                  { cmd := x.2.2.2.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.2.2.2.1,
                    exGntd := x.2.2.2.2.2.2.2.2.2.2.2.2.1, shr := x.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
                    inv := x.2.2.2.2.2.2.2.2.2.2.2.2.2.2 }}),
        Unification.Unifier.bind fun (x : ℕ × CacheState × Req × Gnt × ℕ × Req × Cmd × ℕ × Oids) =>
          ((x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, true, {x.2.2.2.2.1}, x.2.2.2.2.2.2.2.2, x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {Item.cache
                  { id := x.2.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.2.1, ch2 := Gnt.gntE,
                    ch3 := Ack.noAck }}),
            x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2, x.2.2.2.2.1, x.2.2.2.2.2.1,
            {Item.cache { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := x.2.2.2.1, ch3 := Ack.invAck }}),
        Unification.Unifier.bind fun (x : ℕ × Items × CacheState × Req × Gnt × ℕ × Req × Cmd × ℕ × Oids) =>
          ((x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1, true, {x.2.2.2.2.2.1}, x.2.2.2.2.2.2.2.2.2, x.1, x.2.2.1, x.2.2.2.1,
              x.2.2.2.2.1,
              x.2.1 +
                {Item.cache
                    { id := x.2.2.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.2.2.1, ch2 := Gnt.gntE,
                      ch3 := Ack.noAck }}),
            x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
            x.2.1 +
              {Item.cache
                  { id := x.1, state := x.2.2.1, ch1 := x.2.2.2.1, ch2 := x.2.2.2.2.1, ch3 := Ack.invAck }})] := by
  maude_certify_comp

theorem recvInvAckN_inv.obligation_6 :
    Unification.sound (Narrowing.mayFire recvInvAckN ownG)
      [Unification.Unifier.bind
          fun (x : ℕ × ℕ × Req × Cmd × ℕ × Oids × CacheState × Req × Gnt × Cmd × ℕ × Bool × Oids × Oids) =>
          ((x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.2.2.2.2.2.2.2, x.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1,
              {Item.cache
                    { id := x.2.1, state := CacheState.invalid, ch1 := x.2.2.1, ch2 := Gnt.gntE, ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.2.1, ptr := x.2.2.2.2.1, exGntd := true, shr := {x.2.1}, inv := x.2.2.2.2.2.1 }}),
            x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.1, x.2.2.1,
            {Item.cache
                  { id := x.1, state := x.2.2.2.2.2.2.1, ch1 := x.2.2.2.2.2.2.2.1, ch2 := x.2.2.2.2.2.2.2.2.1,
                    ch3 := Ack.invAck }} +
              {Item.dir
                  { cmd := x.2.2.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.2.2.2.1,
                    shr := x.2.2.2.2.2.2.2.2.2.2.2.2.1, inv := x.2.2.2.2.2.2.2.2.2.2.2.2.2 }}),
        Unification.Unifier.bind
          fun (x : ℕ × ℕ × Req × Cmd × ℕ × Oids × Items × CacheState × Req × Gnt × Cmd × ℕ × Bool × Oids × Oids) =>
          ((x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2.2.2, x.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.1 +
                  {Item.cache
                      { id := x.2.1, state := CacheState.invalid, ch1 := x.2.2.1, ch2 := Gnt.gntE, ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.2.1, ptr := x.2.2.2.2.1, exGntd := true, shr := {x.2.1}, inv := x.2.2.2.2.2.1 }}),
            x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.1, x.2.2.1,
            x.2.2.2.2.2.2.1 +
                {Item.cache
                    { id := x.1, state := x.2.2.2.2.2.2.2.1, ch1 := x.2.2.2.2.2.2.2.2.1, ch2 := x.2.2.2.2.2.2.2.2.2.1,
                      ch3 := Ack.invAck }} +
              {Item.dir
                  { cmd := x.2.2.2.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.2.2.2.1,
                    exGntd := x.2.2.2.2.2.2.2.2.2.2.2.2.1, shr := x.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
                    inv := x.2.2.2.2.2.2.2.2.2.2.2.2.2.2 }}),
        Unification.Unifier.bind fun (x : ℕ × CacheState × Req × Gnt × ℕ × Req × Cmd × ℕ × Oids) =>
          ((x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, true, {x.2.2.2.2.1}, x.2.2.2.2.2.2.2.2, x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {Item.cache
                  { id := x.2.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.2.1, ch2 := Gnt.gntE,
                    ch3 := Ack.noAck }}),
            x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2, x.2.2.2.2.1, x.2.2.2.2.2.1,
            {Item.cache { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := x.2.2.2.1, ch3 := Ack.invAck }}),
        Unification.Unifier.bind fun (x : ℕ × Items × CacheState × Req × Gnt × ℕ × Req × Cmd × ℕ × Oids) =>
          ((x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1, true, {x.2.2.2.2.2.1}, x.2.2.2.2.2.2.2.2.2, x.1, x.2.2.1, x.2.2.2.1,
              x.2.2.2.2.1,
              x.2.1 +
                {Item.cache
                    { id := x.2.2.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.2.2.1, ch2 := Gnt.gntE,
                      ch3 := Ack.noAck }}),
            x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
            x.2.1 +
              {Item.cache
                  { id := x.1, state := x.2.2.1, ch1 := x.2.2.2.1, ch2 := x.2.2.2.2.1, ch3 := Ack.invAck }})] := by
  sorry

theorem recvInvAckN_inv.obligation_7 :
    Unification.complete (Narrowing.mayFire recvInvAckN ownInv)
      [Unification.Unifier.bind
          fun (x : ℕ × ℕ × Req × Cmd × ℕ × CacheState × Req × Gnt × Cmd × ℕ × Bool × Oids × Oids) =>
          ((x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.2.2.2.2.2.2, x.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1,
              {Item.cache
                    { id := x.2.1, state := CacheState.exclusive, ch1 := x.2.2.1, ch2 := Gnt.inv, ch3 := Ack.noAck }} +
                {Item.dir { cmd := x.2.2.2.1, ptr := x.2.2.2.2.1, exGntd := true, shr := {x.2.1}, inv := ∅ }}),
            x.2.2.2.1, x.2.2.2.2.1, x.2.1, x.2.2.1,
            {Item.cache
                  { id := x.1, state := x.2.2.2.2.2.1, ch1 := x.2.2.2.2.2.2.1, ch2 := x.2.2.2.2.2.2.2.1,
                    ch3 := Ack.invAck }} +
              {Item.dir
                  { cmd := x.2.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.2.2.1,
                    shr := x.2.2.2.2.2.2.2.2.2.2.2.1, inv := x.2.2.2.2.2.2.2.2.2.2.2.2 }}),
        Unification.Unifier.bind
          fun (x : ℕ × ℕ × Req × Cmd × ℕ × Items × CacheState × Req × Gnt × Cmd × ℕ × Bool × Oids × Oids) =>
          ((x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.2.2.2.2.2.2.2, x.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.1 +
                  {Item.cache
                      { id := x.2.1, state := CacheState.exclusive, ch1 := x.2.2.1, ch2 := Gnt.inv,
                        ch3 := Ack.noAck }} +
                {Item.dir { cmd := x.2.2.2.1, ptr := x.2.2.2.2.1, exGntd := true, shr := {x.2.1}, inv := ∅ }}),
            x.2.2.2.1, x.2.2.2.2.1, x.2.1, x.2.2.1,
            x.2.2.2.2.2.1 +
                {Item.cache
                    { id := x.1, state := x.2.2.2.2.2.2.1, ch1 := x.2.2.2.2.2.2.2.1, ch2 := x.2.2.2.2.2.2.2.2.1,
                      ch3 := Ack.invAck }} +
              {Item.dir
                  { cmd := x.2.2.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.2.2.2.1,
                    shr := x.2.2.2.2.2.2.2.2.2.2.2.2.1, inv := x.2.2.2.2.2.2.2.2.2.2.2.2.2 }}),
        Unification.Unifier.bind fun (x : ℕ × CacheState × Req × Gnt × ℕ × Req × Cmd × ℕ) =>
          ((x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2, true, {x.2.2.2.2.1}, ∅, x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {Item.cache
                  { id := x.2.2.2.2.1, state := CacheState.exclusive, ch1 := x.2.2.2.2.2.1, ch2 := Gnt.inv,
                    ch3 := Ack.noAck }}),
            x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2, x.2.2.2.2.1, x.2.2.2.2.2.1,
            {Item.cache { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := x.2.2.2.1, ch3 := Ack.invAck }}),
        Unification.Unifier.bind fun (x : ℕ × CacheState × Req × Gnt × ℕ × Req × Cmd × ℕ × Items) =>
          ((x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, true, {x.2.2.2.2.1}, ∅, x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              x.2.2.2.2.2.2.2.2 +
                {Item.cache
                    { id := x.2.2.2.2.1, state := CacheState.exclusive, ch1 := x.2.2.2.2.2.1, ch2 := Gnt.inv,
                      ch3 := Ack.noAck }}),
            x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
            x.2.2.2.2.2.2.2.2 +
              {Item.cache { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := x.2.2.2.1, ch3 := Ack.invAck }})] := by
  maude_certify_comp

theorem recvInvAckN_inv.obligation_8 :
    Unification.sound (Narrowing.mayFire recvInvAckN ownInv)
      [Unification.Unifier.bind
          fun (x : ℕ × ℕ × Req × Cmd × ℕ × CacheState × Req × Gnt × Cmd × ℕ × Bool × Oids × Oids) =>
          ((x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.2.2.2.2.2.2, x.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1,
              {Item.cache
                    { id := x.2.1, state := CacheState.exclusive, ch1 := x.2.2.1, ch2 := Gnt.inv, ch3 := Ack.noAck }} +
                {Item.dir { cmd := x.2.2.2.1, ptr := x.2.2.2.2.1, exGntd := true, shr := {x.2.1}, inv := ∅ }}),
            x.2.2.2.1, x.2.2.2.2.1, x.2.1, x.2.2.1,
            {Item.cache
                  { id := x.1, state := x.2.2.2.2.2.1, ch1 := x.2.2.2.2.2.2.1, ch2 := x.2.2.2.2.2.2.2.1,
                    ch3 := Ack.invAck }} +
              {Item.dir
                  { cmd := x.2.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.2.2.1,
                    shr := x.2.2.2.2.2.2.2.2.2.2.2.1, inv := x.2.2.2.2.2.2.2.2.2.2.2.2 }}),
        Unification.Unifier.bind
          fun (x : ℕ × ℕ × Req × Cmd × ℕ × Items × CacheState × Req × Gnt × Cmd × ℕ × Bool × Oids × Oids) =>
          ((x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.2.2.2.2.2.2.2, x.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.1 +
                  {Item.cache
                      { id := x.2.1, state := CacheState.exclusive, ch1 := x.2.2.1, ch2 := Gnt.inv,
                        ch3 := Ack.noAck }} +
                {Item.dir { cmd := x.2.2.2.1, ptr := x.2.2.2.2.1, exGntd := true, shr := {x.2.1}, inv := ∅ }}),
            x.2.2.2.1, x.2.2.2.2.1, x.2.1, x.2.2.1,
            x.2.2.2.2.2.1 +
                {Item.cache
                    { id := x.1, state := x.2.2.2.2.2.2.1, ch1 := x.2.2.2.2.2.2.2.1, ch2 := x.2.2.2.2.2.2.2.2.1,
                      ch3 := Ack.invAck }} +
              {Item.dir
                  { cmd := x.2.2.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.2.2.2.1,
                    shr := x.2.2.2.2.2.2.2.2.2.2.2.2.1, inv := x.2.2.2.2.2.2.2.2.2.2.2.2.2 }}),
        Unification.Unifier.bind fun (x : ℕ × CacheState × Req × Gnt × ℕ × Req × Cmd × ℕ) =>
          ((x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2, true, {x.2.2.2.2.1}, ∅, x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {Item.cache
                  { id := x.2.2.2.2.1, state := CacheState.exclusive, ch1 := x.2.2.2.2.2.1, ch2 := Gnt.inv,
                    ch3 := Ack.noAck }}),
            x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2, x.2.2.2.2.1, x.2.2.2.2.2.1,
            {Item.cache { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := x.2.2.2.1, ch3 := Ack.invAck }}),
        Unification.Unifier.bind fun (x : ℕ × CacheState × Req × Gnt × ℕ × Req × Cmd × ℕ × Items) =>
          ((x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, true, {x.2.2.2.2.1}, ∅, x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              x.2.2.2.2.2.2.2.2 +
                {Item.cache
                    { id := x.2.2.2.2.1, state := CacheState.exclusive, ch1 := x.2.2.2.2.2.1, ch2 := Gnt.inv,
                      ch3 := Ack.noAck }}),
            x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
            x.2.2.2.2.2.2.2.2 +
              {Item.cache { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := x.2.2.2.1, ch3 := Ack.invAck }})] := by
  sorry

theorem recvInvAckN_inv.obligation_9 :
    Unification.complete (Narrowing.mayFire recvInvAckN ownAck)
      [Unification.Unifier.bind
          fun (x : ℕ × ℕ × Req × Cmd × ℕ × CacheState × Req × Gnt × Cmd × ℕ × Bool × Oids × Oids) =>
          ((x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.2.2.2.2.2.2, x.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1,
              {Item.cache
                    { id := x.2.1, state := CacheState.invalid, ch1 := x.2.2.1, ch2 := Gnt.noGnt, ch3 := Ack.invAck }} +
                {Item.dir { cmd := x.2.2.2.1, ptr := x.2.2.2.2.1, exGntd := true, shr := {x.2.1}, inv := ∅ }}),
            x.2.2.2.1, x.2.2.2.2.1, x.2.1, x.2.2.1,
            {Item.cache
                  { id := x.1, state := x.2.2.2.2.2.1, ch1 := x.2.2.2.2.2.2.1, ch2 := x.2.2.2.2.2.2.2.1,
                    ch3 := Ack.invAck }} +
              {Item.dir
                  { cmd := x.2.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.2.2.1,
                    shr := x.2.2.2.2.2.2.2.2.2.2.2.1, inv := x.2.2.2.2.2.2.2.2.2.2.2.2 }}),
        Unification.Unifier.bind
          fun (x : ℕ × ℕ × Req × Cmd × ℕ × Items × CacheState × Req × Gnt × Cmd × ℕ × Bool × Oids × Oids) =>
          ((x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.2.2.2.2.2.2.2, x.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.1 +
                  {Item.cache
                      { id := x.2.1, state := CacheState.invalid, ch1 := x.2.2.1, ch2 := Gnt.noGnt,
                        ch3 := Ack.invAck }} +
                {Item.dir { cmd := x.2.2.2.1, ptr := x.2.2.2.2.1, exGntd := true, shr := {x.2.1}, inv := ∅ }}),
            x.2.2.2.1, x.2.2.2.2.1, x.2.1, x.2.2.1,
            x.2.2.2.2.2.1 +
                {Item.cache
                    { id := x.1, state := x.2.2.2.2.2.2.1, ch1 := x.2.2.2.2.2.2.2.1, ch2 := x.2.2.2.2.2.2.2.2.1,
                      ch3 := Ack.invAck }} +
              {Item.dir
                  { cmd := x.2.2.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.2.2.2.1,
                    shr := x.2.2.2.2.2.2.2.2.2.2.2.2.1, inv := x.2.2.2.2.2.2.2.2.2.2.2.2.2 }}),
        Unification.Unifier.bind fun (x : Cmd × ℕ × Bool × Oids × Oids × ℕ × Req × Cmd × ℕ) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, CacheState.invalid, x.2.2.2.2.2.2.1, Gnt.noGnt,
              {Item.dir
                  { cmd := x.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2, exGntd := true, shr := {x.2.2.2.2.2.1},
                    inv := ∅ }}),
            x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
            {Item.dir { cmd := x.1, ptr := x.2.1, exGntd := x.2.2.1, shr := x.2.2.2.1, inv := x.2.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : Cmd × Items × ℕ × Bool × Oids × Oids × ℕ × Req × Cmd × ℕ) =>
          ((x.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, CacheState.invalid, x.2.2.2.2.2.2.2.1,
              Gnt.noGnt,
              x.2.1 +
                {Item.dir
                    { cmd := x.2.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.2, exGntd := true, shr := {x.2.2.2.2.2.2.1},
                      inv := ∅ }}),
            x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1,
            x.2.1 +
              {Item.dir { cmd := x.1, ptr := x.2.2.1, exGntd := x.2.2.2.1, shr := x.2.2.2.2.1, inv := x.2.2.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × CacheState × Req × Gnt × ℕ × Req × Cmd × ℕ) =>
          ((x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2, true, {x.2.2.2.2.1}, ∅, x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {Item.cache
                  { id := x.2.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.2.1, ch2 := Gnt.noGnt,
                    ch3 := Ack.invAck }}),
            x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2, x.2.2.2.2.1, x.2.2.2.2.2.1,
            {Item.cache { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := x.2.2.2.1, ch3 := Ack.invAck }}),
        Unification.Unifier.bind fun (x : ℕ × CacheState × Req × Gnt × ℕ × Req × Cmd × ℕ × Items) =>
          ((x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, true, {x.2.2.2.2.1}, ∅, x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              x.2.2.2.2.2.2.2.2 +
                {Item.cache
                    { id := x.2.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.2.1, ch2 := Gnt.noGnt,
                      ch3 := Ack.invAck }}),
            x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
            x.2.2.2.2.2.2.2.2 +
              {Item.cache { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := x.2.2.2.1, ch3 := Ack.invAck }}),
        Unification.Unifier.bind fun (x : ℕ × Req × Cmd × ℕ) =>
          ((x.2.2.1, x.2.2.2, true, {x.1}, ∅, x.1, CacheState.invalid, x.2.1, Gnt.noGnt, ∅), x.2.2.1, x.2.2.2, x.1,
            x.2.1, ∅),
        Unification.Unifier.bind fun (x : Items × ℕ × Req × Cmd × ℕ) =>
          ((x.2.2.2.1, x.2.2.2.2, true, {x.2.1}, ∅, x.2.1, CacheState.invalid, x.2.2.1, Gnt.noGnt, x.1), x.2.2.2.1,
            x.2.2.2.2, x.2.1, x.2.2.1, x.1)] := by
  maude_certify_comp

theorem recvInvAckN_inv.obligation_10 :
    Unification.sound (Narrowing.mayFire recvInvAckN ownAck)
      [Unification.Unifier.bind
          fun (x : ℕ × ℕ × Req × Cmd × ℕ × CacheState × Req × Gnt × Cmd × ℕ × Bool × Oids × Oids) =>
          ((x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.2.2.2.2.2.2, x.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1,
              {Item.cache
                    { id := x.2.1, state := CacheState.invalid, ch1 := x.2.2.1, ch2 := Gnt.noGnt, ch3 := Ack.invAck }} +
                {Item.dir { cmd := x.2.2.2.1, ptr := x.2.2.2.2.1, exGntd := true, shr := {x.2.1}, inv := ∅ }}),
            x.2.2.2.1, x.2.2.2.2.1, x.2.1, x.2.2.1,
            {Item.cache
                  { id := x.1, state := x.2.2.2.2.2.1, ch1 := x.2.2.2.2.2.2.1, ch2 := x.2.2.2.2.2.2.2.1,
                    ch3 := Ack.invAck }} +
              {Item.dir
                  { cmd := x.2.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.2.2.1,
                    shr := x.2.2.2.2.2.2.2.2.2.2.2.1, inv := x.2.2.2.2.2.2.2.2.2.2.2.2 }}),
        Unification.Unifier.bind
          fun (x : ℕ × ℕ × Req × Cmd × ℕ × Items × CacheState × Req × Gnt × Cmd × ℕ × Bool × Oids × Oids) =>
          ((x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.2.2.2.2.2.2.2, x.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.1 +
                  {Item.cache
                      { id := x.2.1, state := CacheState.invalid, ch1 := x.2.2.1, ch2 := Gnt.noGnt,
                        ch3 := Ack.invAck }} +
                {Item.dir { cmd := x.2.2.2.1, ptr := x.2.2.2.2.1, exGntd := true, shr := {x.2.1}, inv := ∅ }}),
            x.2.2.2.1, x.2.2.2.2.1, x.2.1, x.2.2.1,
            x.2.2.2.2.2.1 +
                {Item.cache
                    { id := x.1, state := x.2.2.2.2.2.2.1, ch1 := x.2.2.2.2.2.2.2.1, ch2 := x.2.2.2.2.2.2.2.2.1,
                      ch3 := Ack.invAck }} +
              {Item.dir
                  { cmd := x.2.2.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.2.2.1, exGntd := x.2.2.2.2.2.2.2.2.2.2.2.1,
                    shr := x.2.2.2.2.2.2.2.2.2.2.2.2.1, inv := x.2.2.2.2.2.2.2.2.2.2.2.2.2 }}),
        Unification.Unifier.bind fun (x : Cmd × ℕ × Bool × Oids × Oids × ℕ × Req × Cmd × ℕ) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, CacheState.invalid, x.2.2.2.2.2.2.1, Gnt.noGnt,
              {Item.dir
                  { cmd := x.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2, exGntd := true, shr := {x.2.2.2.2.2.1},
                    inv := ∅ }}),
            x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
            {Item.dir { cmd := x.1, ptr := x.2.1, exGntd := x.2.2.1, shr := x.2.2.2.1, inv := x.2.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : Cmd × Items × ℕ × Bool × Oids × Oids × ℕ × Req × Cmd × ℕ) =>
          ((x.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, CacheState.invalid, x.2.2.2.2.2.2.2.1,
              Gnt.noGnt,
              x.2.1 +
                {Item.dir
                    { cmd := x.2.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.2, exGntd := true, shr := {x.2.2.2.2.2.2.1},
                      inv := ∅ }}),
            x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1,
            x.2.1 +
              {Item.dir { cmd := x.1, ptr := x.2.2.1, exGntd := x.2.2.2.1, shr := x.2.2.2.2.1, inv := x.2.2.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × CacheState × Req × Gnt × ℕ × Req × Cmd × ℕ) =>
          ((x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2, true, {x.2.2.2.2.1}, ∅, x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {Item.cache
                  { id := x.2.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.2.1, ch2 := Gnt.noGnt,
                    ch3 := Ack.invAck }}),
            x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2, x.2.2.2.2.1, x.2.2.2.2.2.1,
            {Item.cache { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := x.2.2.2.1, ch3 := Ack.invAck }}),
        Unification.Unifier.bind fun (x : ℕ × CacheState × Req × Gnt × ℕ × Req × Cmd × ℕ × Items) =>
          ((x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, true, {x.2.2.2.2.1}, ∅, x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              x.2.2.2.2.2.2.2.2 +
                {Item.cache
                    { id := x.2.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.2.1, ch2 := Gnt.noGnt,
                      ch3 := Ack.invAck }}),
            x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
            x.2.2.2.2.2.2.2.2 +
              {Item.cache { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := x.2.2.2.1, ch3 := Ack.invAck }}),
        Unification.Unifier.bind fun (x : ℕ × Req × Cmd × ℕ) =>
          ((x.2.2.1, x.2.2.2, true, {x.1}, ∅, x.1, CacheState.invalid, x.2.1, Gnt.noGnt, ∅), x.2.2.1, x.2.2.2, x.1,
            x.2.1, ∅),
        Unification.Unifier.bind fun (x : Items × ℕ × Req × Cmd × ℕ) =>
          ((x.2.2.2.1, x.2.2.2.2, true, {x.2.1}, ∅, x.2.1, CacheState.invalid, x.2.2.1, Gnt.noGnt, x.1), x.2.2.2.1,
            x.2.2.2.2, x.2.1, x.2.2.1, x.1)] := by
  sorry

theorem sendGntSN_inv.obligation_1 :
    Unification.complete (Narrowing.mayFire sendGntSN freeP)
      [Unification.Unifier.bind fun (x : ℕ × Oids × CacheState × Req × Ack × Oids × Oids × Cmd × ℕ × Oids) =>
          ((x.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
              {Item.dir
                  { cmd := x.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.1, exGntd := false, shr := x.2.2.2.2.2.2.2.2.2,
                    inv := x.2.1 }}),
            x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2, x.2.1,
            {Item.cache { id := x.1, state := x.2.2.1, ch1 := x.2.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.cmdS, ptr := x.1, exGntd := false, shr := x.2.2.2.2.2.1, inv := x.2.2.2.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × Oids × Items × CacheState × Req × Ack × Oids × Oids × Cmd × ℕ × Oids) =>
          ((x.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
              x.2.2.1 +
                {Item.dir
                    { cmd := x.2.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.2.1, exGntd := false,
                      shr := x.2.2.2.2.2.2.2.2.2.2, inv := x.2.1 }}),
            x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2, x.2.1,
            x.2.2.1 +
                {Item.cache
                    { id := x.1, state := x.2.2.2.1, ch1 := x.2.2.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.cmdS, ptr := x.1, exGntd := false, shr := x.2.2.2.2.2.2.1, inv := x.2.2.2.2.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : CacheState × Req × Ack × ℕ × Oids × Oids) =>
          ((x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2, x.1, x.2.1, x.2.2.1, ∅), Cmd.cmdS, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2,
            {Item.cache { id := x.2.2.2.1, state := x.1, ch1 := x.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.1 }}),
        Unification.Unifier.bind fun (x : Items × CacheState × Req × Ack × ℕ × Oids × Oids) =>
          ((x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2, x.2.1, x.2.2.1, x.2.2.2.1, x.1), Cmd.cmdS, x.2.2.2.2.1,
            x.2.2.2.2.2.1, x.2.2.2.2.2.2,
            x.1 +
              {Item.cache
                  { id := x.2.2.2.2.1, state := x.2.1, ch1 := x.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.1 }})] := by
  maude_certify_comp

theorem sendGntSN_inv.obligation_2 :
    Unification.sound (Narrowing.mayFire sendGntSN freeP)
      [Unification.Unifier.bind fun (x : ℕ × Oids × CacheState × Req × Ack × Oids × Oids × Cmd × ℕ × Oids) =>
          ((x.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
              {Item.dir
                  { cmd := x.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.1, exGntd := false, shr := x.2.2.2.2.2.2.2.2.2,
                    inv := x.2.1 }}),
            x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2, x.2.1,
            {Item.cache { id := x.1, state := x.2.2.1, ch1 := x.2.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.cmdS, ptr := x.1, exGntd := false, shr := x.2.2.2.2.2.1, inv := x.2.2.2.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × Oids × Items × CacheState × Req × Ack × Oids × Oids × Cmd × ℕ × Oids) =>
          ((x.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
              x.2.2.1 +
                {Item.dir
                    { cmd := x.2.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.2.1, exGntd := false,
                      shr := x.2.2.2.2.2.2.2.2.2.2, inv := x.2.1 }}),
            x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2, x.2.1,
            x.2.2.1 +
                {Item.cache
                    { id := x.1, state := x.2.2.2.1, ch1 := x.2.2.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.cmdS, ptr := x.1, exGntd := false, shr := x.2.2.2.2.2.2.1, inv := x.2.2.2.2.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : CacheState × Req × Ack × ℕ × Oids × Oids) =>
          ((x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2, x.1, x.2.1, x.2.2.1, ∅), Cmd.cmdS, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2,
            {Item.cache { id := x.2.2.2.1, state := x.1, ch1 := x.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.1 }}),
        Unification.Unifier.bind fun (x : Items × CacheState × Req × Ack × ℕ × Oids × Oids) =>
          ((x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2, x.2.1, x.2.2.1, x.2.2.2.1, x.1), Cmd.cmdS, x.2.2.2.2.1,
            x.2.2.2.2.2.1, x.2.2.2.2.2.2,
            x.1 +
              {Item.cache
                  { id := x.2.2.2.2.1, state := x.2.1, ch1 := x.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.1 }})] := by
  sorry

theorem sendGntSN_inv.obligation_3 :
    Unification.complete (Narrowing.mayFire sendGntSN ownE)
      [Unification.Unifier.bind fun (x : ℕ × ℕ × Oids × CacheState × Req × Ack × Oids × Oids × ℕ × Req × Cmd) =>
          ((x.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
              {Item.cache
                    { id := x.2.2.2.2.2.2.2.2.1, state := CacheState.exclusive, ch1 := x.2.2.2.2.2.2.2.2.2.1,
                      ch2 := Gnt.noGnt, ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.2.2.2.2.2, ptr := x.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.1},
                      inv := x.2.2.1 }}),
            x.2.2.2.2.2.2.2.2.2.2, x.2.1, x.2.2.1, x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1,
            {Item.cache { id := x.1, state := x.2.2.2.1, ch1 := x.2.2.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.cmdS, ptr := x.1, exGntd := false, shr := x.2.2.2.2.2.2.1, inv := x.2.2.2.2.2.2.2.1 }}),
        Unification.Unifier.bind
          fun (x : ℕ × ℕ × Oids × Items × CacheState × Req × Ack × Oids × Oids × ℕ × Req × Cmd) =>
          ((x.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
              x.2.2.2.1 +
                  {Item.cache
                      { id := x.2.2.2.2.2.2.2.2.2.1, state := CacheState.exclusive, ch1 := x.2.2.2.2.2.2.2.2.2.2.1,
                        ch2 := Gnt.noGnt, ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.2.2.2.2.2.2, ptr := x.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.2.1},
                      inv := x.2.2.1 }}),
            x.2.2.2.2.2.2.2.2.2.2.2, x.2.1, x.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1,
            x.2.2.2.1 +
                {Item.cache
                    { id := x.1, state := x.2.2.2.2.1, ch1 := x.2.2.2.2.2.1, ch2 := Gnt.noGnt,
                      ch3 := x.2.2.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.cmdS, ptr := x.1, exGntd := false, shr := x.2.2.2.2.2.2.2.1,
                    inv := x.2.2.2.2.2.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : Oids × Oids × ℕ × Req × Cmd × ℕ × Oids) =>
          ((x.2.2.1, x.1, x.2.1, CacheState.exclusive, x.2.2.2.1, Ack.noAck,
              {Item.dir
                  { cmd := x.2.2.2.2.1, ptr := x.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.1},
                    inv := x.2.2.2.2.2.2 }}),
            x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2, x.2.2.1, x.2.2.2.1,
            {Item.dir { cmd := Cmd.cmdS, ptr := x.2.2.1, exGntd := false, shr := x.1, inv := x.2.1 }}),
        Unification.Unifier.bind fun (x : Oids × Oids × ℕ × Req × Cmd × ℕ × Oids × Items) =>
          ((x.2.2.1, x.1, x.2.1, CacheState.exclusive, x.2.2.2.1, Ack.noAck,
              x.2.2.2.2.2.2.2 +
                {Item.dir
                    { cmd := x.2.2.2.2.1, ptr := x.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.1},
                      inv := x.2.2.2.2.2.2.1 }}),
            x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.1, x.2.2.2.1,
            x.2.2.2.2.2.2.2 +
              {Item.dir { cmd := Cmd.cmdS, ptr := x.2.2.1, exGntd := false, shr := x.1, inv := x.2.1 }})] := by
  maude_certify_comp

theorem sendGntSN_inv.obligation_4 :
    Unification.sound (Narrowing.mayFire sendGntSN ownE)
      [Unification.Unifier.bind fun (x : ℕ × ℕ × Oids × CacheState × Req × Ack × Oids × Oids × ℕ × Req × Cmd) =>
          ((x.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
              {Item.cache
                    { id := x.2.2.2.2.2.2.2.2.1, state := CacheState.exclusive, ch1 := x.2.2.2.2.2.2.2.2.2.1,
                      ch2 := Gnt.noGnt, ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.2.2.2.2.2, ptr := x.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.1},
                      inv := x.2.2.1 }}),
            x.2.2.2.2.2.2.2.2.2.2, x.2.1, x.2.2.1, x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1,
            {Item.cache { id := x.1, state := x.2.2.2.1, ch1 := x.2.2.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.cmdS, ptr := x.1, exGntd := false, shr := x.2.2.2.2.2.2.1, inv := x.2.2.2.2.2.2.2.1 }}),
        Unification.Unifier.bind
          fun (x : ℕ × ℕ × Oids × Items × CacheState × Req × Ack × Oids × Oids × ℕ × Req × Cmd) =>
          ((x.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
              x.2.2.2.1 +
                  {Item.cache
                      { id := x.2.2.2.2.2.2.2.2.2.1, state := CacheState.exclusive, ch1 := x.2.2.2.2.2.2.2.2.2.2.1,
                        ch2 := Gnt.noGnt, ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.2.2.2.2.2.2, ptr := x.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.2.1},
                      inv := x.2.2.1 }}),
            x.2.2.2.2.2.2.2.2.2.2.2, x.2.1, x.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1,
            x.2.2.2.1 +
                {Item.cache
                    { id := x.1, state := x.2.2.2.2.1, ch1 := x.2.2.2.2.2.1, ch2 := Gnt.noGnt,
                      ch3 := x.2.2.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.cmdS, ptr := x.1, exGntd := false, shr := x.2.2.2.2.2.2.2.1,
                    inv := x.2.2.2.2.2.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : Oids × Oids × ℕ × Req × Cmd × ℕ × Oids) =>
          ((x.2.2.1, x.1, x.2.1, CacheState.exclusive, x.2.2.2.1, Ack.noAck,
              {Item.dir
                  { cmd := x.2.2.2.2.1, ptr := x.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.1},
                    inv := x.2.2.2.2.2.2 }}),
            x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2, x.2.2.1, x.2.2.2.1,
            {Item.dir { cmd := Cmd.cmdS, ptr := x.2.2.1, exGntd := false, shr := x.1, inv := x.2.1 }}),
        Unification.Unifier.bind fun (x : Oids × Oids × ℕ × Req × Cmd × ℕ × Oids × Items) =>
          ((x.2.2.1, x.1, x.2.1, CacheState.exclusive, x.2.2.2.1, Ack.noAck,
              x.2.2.2.2.2.2.2 +
                {Item.dir
                    { cmd := x.2.2.2.2.1, ptr := x.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.1},
                      inv := x.2.2.2.2.2.2.1 }}),
            x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.1, x.2.2.2.1,
            x.2.2.2.2.2.2.2 +
              {Item.dir { cmd := Cmd.cmdS, ptr := x.2.2.1, exGntd := false, shr := x.1, inv := x.2.1 }})] := by
  sorry

theorem sendGntSN_inv.obligation_5 :
    Unification.complete (Narrowing.mayFire sendGntSN ownG)
      [Unification.Unifier.bind fun (x : ℕ × ℕ × Oids × CacheState × Req × Ack × Oids × Oids × ℕ × Req × Cmd) =>
          ((x.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
              {Item.cache
                    { id := x.2.2.2.2.2.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.2.2.2.2.2.1,
                      ch2 := Gnt.gntE, ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.2.2.2.2.2, ptr := x.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.1},
                      inv := x.2.2.1 }}),
            x.2.2.2.2.2.2.2.2.2.2, x.2.1, x.2.2.1, x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1,
            {Item.cache { id := x.1, state := x.2.2.2.1, ch1 := x.2.2.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.cmdS, ptr := x.1, exGntd := false, shr := x.2.2.2.2.2.2.1, inv := x.2.2.2.2.2.2.2.1 }}),
        Unification.Unifier.bind
          fun (x : ℕ × ℕ × Oids × Items × CacheState × Req × Ack × Oids × Oids × ℕ × Req × Cmd) =>
          ((x.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
              x.2.2.2.1 +
                  {Item.cache
                      { id := x.2.2.2.2.2.2.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.2.2.2.2.2.2.1,
                        ch2 := Gnt.gntE, ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.2.2.2.2.2.2, ptr := x.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.2.1},
                      inv := x.2.2.1 }}),
            x.2.2.2.2.2.2.2.2.2.2.2, x.2.1, x.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1,
            x.2.2.2.1 +
                {Item.cache
                    { id := x.1, state := x.2.2.2.2.1, ch1 := x.2.2.2.2.2.1, ch2 := Gnt.noGnt,
                      ch3 := x.2.2.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.cmdS, ptr := x.1, exGntd := false, shr := x.2.2.2.2.2.2.2.1,
                    inv := x.2.2.2.2.2.2.2.2.1 }})] := by
  maude_certify_comp

theorem sendGntSN_inv.obligation_6 :
    Unification.sound (Narrowing.mayFire sendGntSN ownG)
      [Unification.Unifier.bind fun (x : ℕ × ℕ × Oids × CacheState × Req × Ack × Oids × Oids × ℕ × Req × Cmd) =>
          ((x.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
              {Item.cache
                    { id := x.2.2.2.2.2.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.2.2.2.2.2.1,
                      ch2 := Gnt.gntE, ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.2.2.2.2.2, ptr := x.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.1},
                      inv := x.2.2.1 }}),
            x.2.2.2.2.2.2.2.2.2.2, x.2.1, x.2.2.1, x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1,
            {Item.cache { id := x.1, state := x.2.2.2.1, ch1 := x.2.2.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.cmdS, ptr := x.1, exGntd := false, shr := x.2.2.2.2.2.2.1, inv := x.2.2.2.2.2.2.2.1 }}),
        Unification.Unifier.bind
          fun (x : ℕ × ℕ × Oids × Items × CacheState × Req × Ack × Oids × Oids × ℕ × Req × Cmd) =>
          ((x.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
              x.2.2.2.1 +
                  {Item.cache
                      { id := x.2.2.2.2.2.2.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.2.2.2.2.2.2.1,
                        ch2 := Gnt.gntE, ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.2.2.2.2.2.2, ptr := x.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.2.1},
                      inv := x.2.2.1 }}),
            x.2.2.2.2.2.2.2.2.2.2.2, x.2.1, x.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1,
            x.2.2.2.1 +
                {Item.cache
                    { id := x.1, state := x.2.2.2.2.1, ch1 := x.2.2.2.2.2.1, ch2 := Gnt.noGnt,
                      ch3 := x.2.2.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.cmdS, ptr := x.1, exGntd := false, shr := x.2.2.2.2.2.2.2.1,
                    inv := x.2.2.2.2.2.2.2.2.1 }})] := by
  sorry

theorem sendGntSN_inv.obligation_7 :
    Unification.complete (Narrowing.mayFire sendGntSN ownInv)
      [Unification.Unifier.bind fun (x : ℕ × ℕ × CacheState × Req × Ack × Oids × Oids × ℕ × Req × Cmd) =>
          ((x.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
              {Item.cache
                    { id := x.2.2.2.2.2.2.2.1, state := CacheState.exclusive, ch1 := x.2.2.2.2.2.2.2.2.1,
                      ch2 := Gnt.inv, ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.2.2.2.2, ptr := x.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.1},
                      inv := ∅ }}),
            x.2.2.2.2.2.2.2.2.2, x.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1,
            {Item.cache { id := x.1, state := x.2.2.1, ch1 := x.2.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.cmdS, ptr := x.1, exGntd := false, shr := x.2.2.2.2.2.1, inv := x.2.2.2.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × ℕ × Items × CacheState × Req × Ack × Oids × Oids × ℕ × Req × Cmd) =>
          ((x.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
              x.2.2.1 +
                  {Item.cache
                      { id := x.2.2.2.2.2.2.2.2.1, state := CacheState.exclusive, ch1 := x.2.2.2.2.2.2.2.2.2.1,
                        ch2 := Gnt.inv, ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.2.2.2.2.2, ptr := x.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.1},
                      inv := ∅ }}),
            x.2.2.2.2.2.2.2.2.2.2, x.2.1, x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1,
            x.2.2.1 +
                {Item.cache
                    { id := x.1, state := x.2.2.2.1, ch1 := x.2.2.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.cmdS, ptr := x.1, exGntd := false, shr := x.2.2.2.2.2.2.1,
                    inv := x.2.2.2.2.2.2.2.1 }})] := by
  maude_certify_comp

theorem sendGntSN_inv.obligation_8 :
    Unification.sound (Narrowing.mayFire sendGntSN ownInv)
      [Unification.Unifier.bind fun (x : ℕ × ℕ × CacheState × Req × Ack × Oids × Oids × ℕ × Req × Cmd) =>
          ((x.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
              {Item.cache
                    { id := x.2.2.2.2.2.2.2.1, state := CacheState.exclusive, ch1 := x.2.2.2.2.2.2.2.2.1,
                      ch2 := Gnt.inv, ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.2.2.2.2, ptr := x.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.1},
                      inv := ∅ }}),
            x.2.2.2.2.2.2.2.2.2, x.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1,
            {Item.cache { id := x.1, state := x.2.2.1, ch1 := x.2.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.cmdS, ptr := x.1, exGntd := false, shr := x.2.2.2.2.2.1, inv := x.2.2.2.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × ℕ × Items × CacheState × Req × Ack × Oids × Oids × ℕ × Req × Cmd) =>
          ((x.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
              x.2.2.1 +
                  {Item.cache
                      { id := x.2.2.2.2.2.2.2.2.1, state := CacheState.exclusive, ch1 := x.2.2.2.2.2.2.2.2.2.1,
                        ch2 := Gnt.inv, ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.2.2.2.2.2, ptr := x.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.1},
                      inv := ∅ }}),
            x.2.2.2.2.2.2.2.2.2.2, x.2.1, x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1,
            x.2.2.1 +
                {Item.cache
                    { id := x.1, state := x.2.2.2.1, ch1 := x.2.2.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.cmdS, ptr := x.1, exGntd := false, shr := x.2.2.2.2.2.2.1,
                    inv := x.2.2.2.2.2.2.2.1 }})] := by
  sorry

theorem sendGntSN_inv.obligation_9 :
    Unification.complete (Narrowing.mayFire sendGntSN ownAck)
      [Unification.Unifier.bind fun (x : ℕ × ℕ × CacheState × Req × Ack × Oids × Oids × ℕ × Req × Cmd) =>
          ((x.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
              {Item.cache
                    { id := x.2.2.2.2.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.2.2.2.2.1,
                      ch2 := Gnt.noGnt, ch3 := Ack.invAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.2.2.2.2, ptr := x.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.1},
                      inv := ∅ }}),
            x.2.2.2.2.2.2.2.2.2, x.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1,
            {Item.cache { id := x.1, state := x.2.2.1, ch1 := x.2.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.cmdS, ptr := x.1, exGntd := false, shr := x.2.2.2.2.2.1, inv := x.2.2.2.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × ℕ × Items × CacheState × Req × Ack × Oids × Oids × ℕ × Req × Cmd) =>
          ((x.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
              x.2.2.1 +
                  {Item.cache
                      { id := x.2.2.2.2.2.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.2.2.2.2.2.1,
                        ch2 := Gnt.noGnt, ch3 := Ack.invAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.2.2.2.2.2, ptr := x.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.1},
                      inv := ∅ }}),
            x.2.2.2.2.2.2.2.2.2.2, x.2.1, x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1,
            x.2.2.1 +
                {Item.cache
                    { id := x.1, state := x.2.2.2.1, ch1 := x.2.2.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.cmdS, ptr := x.1, exGntd := false, shr := x.2.2.2.2.2.2.1, inv := x.2.2.2.2.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : Oids × Oids × ℕ × Req × Cmd × ℕ) =>
          ((x.2.2.1, x.1, x.2.1, CacheState.invalid, x.2.2.2.1, Ack.invAck,
              {Item.dir { cmd := x.2.2.2.2.1, ptr := x.2.2.2.2.2, exGntd := true, shr := {x.2.2.1}, inv := ∅ }}),
            x.2.2.2.2.1, x.2.2.2.2.2, x.2.2.1, x.2.2.2.1,
            {Item.dir { cmd := Cmd.cmdS, ptr := x.2.2.1, exGntd := false, shr := x.1, inv := x.2.1 }}),
        Unification.Unifier.bind fun (x : Oids × Oids × ℕ × Req × Cmd × ℕ × Items) =>
          ((x.2.2.1, x.1, x.2.1, CacheState.invalid, x.2.2.2.1, Ack.invAck,
              x.2.2.2.2.2.2 +
                {Item.dir { cmd := x.2.2.2.2.1, ptr := x.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.1}, inv := ∅ }}),
            x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.1, x.2.2.2.1,
            x.2.2.2.2.2.2 +
              {Item.dir { cmd := Cmd.cmdS, ptr := x.2.2.1, exGntd := false, shr := x.1, inv := x.2.1 }})] := by
  maude_certify_comp

theorem sendGntSN_inv.obligation_10 :
    Unification.sound (Narrowing.mayFire sendGntSN ownAck)
      [Unification.Unifier.bind fun (x : ℕ × ℕ × CacheState × Req × Ack × Oids × Oids × ℕ × Req × Cmd) =>
          ((x.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
              {Item.cache
                    { id := x.2.2.2.2.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.2.2.2.2.1,
                      ch2 := Gnt.noGnt, ch3 := Ack.invAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.2.2.2.2, ptr := x.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.1},
                      inv := ∅ }}),
            x.2.2.2.2.2.2.2.2.2, x.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1,
            {Item.cache { id := x.1, state := x.2.2.1, ch1 := x.2.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.cmdS, ptr := x.1, exGntd := false, shr := x.2.2.2.2.2.1, inv := x.2.2.2.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × ℕ × Items × CacheState × Req × Ack × Oids × Oids × ℕ × Req × Cmd) =>
          ((x.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
              x.2.2.1 +
                  {Item.cache
                      { id := x.2.2.2.2.2.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.2.2.2.2.2.1,
                        ch2 := Gnt.noGnt, ch3 := Ack.invAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.2.2.2.2.2, ptr := x.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.1},
                      inv := ∅ }}),
            x.2.2.2.2.2.2.2.2.2.2, x.2.1, x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1,
            x.2.2.1 +
                {Item.cache
                    { id := x.1, state := x.2.2.2.1, ch1 := x.2.2.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.cmdS, ptr := x.1, exGntd := false, shr := x.2.2.2.2.2.2.1, inv := x.2.2.2.2.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : Oids × Oids × ℕ × Req × Cmd × ℕ) =>
          ((x.2.2.1, x.1, x.2.1, CacheState.invalid, x.2.2.2.1, Ack.invAck,
              {Item.dir { cmd := x.2.2.2.2.1, ptr := x.2.2.2.2.2, exGntd := true, shr := {x.2.2.1}, inv := ∅ }}),
            x.2.2.2.2.1, x.2.2.2.2.2, x.2.2.1, x.2.2.2.1,
            {Item.dir { cmd := Cmd.cmdS, ptr := x.2.2.1, exGntd := false, shr := x.1, inv := x.2.1 }}),
        Unification.Unifier.bind fun (x : Oids × Oids × ℕ × Req × Cmd × ℕ × Items) =>
          ((x.2.2.1, x.1, x.2.1, CacheState.invalid, x.2.2.2.1, Ack.invAck,
              x.2.2.2.2.2.2 +
                {Item.dir { cmd := x.2.2.2.2.1, ptr := x.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.1}, inv := ∅ }}),
            x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.1, x.2.2.2.1,
            x.2.2.2.2.2.2 +
              {Item.dir { cmd := Cmd.cmdS, ptr := x.2.2.1, exGntd := false, shr := x.1, inv := x.2.1 }})] := by
  sorry

theorem sendGntSS_inv.obligation_1 :
    Unification.complete (Narrowing.mayFire sendGntSS freeP)
      [Unification.Unifier.bind fun (x : ℕ × CacheState × Req × Ack × Oids × Cmd × ℕ × Oids × Oids) =>
          ((x.1, ∅, x.2.2.2.2.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {Item.dir
                  { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.1, exGntd := false, shr := x.2.2.2.2.2.2.2.1,
                    inv := x.2.2.2.2.2.2.2.2 }}),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2,
            {Item.cache { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.1 }} +
              {Item.dir { cmd := Cmd.cmdS, ptr := x.1, exGntd := false, shr := {x.1}, inv := x.2.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × Oids × CacheState × Req × Ack × Oids × Oids × Cmd × ℕ × Oids) =>
          ((x.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
              {Item.dir
                  { cmd := x.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.1, exGntd := false, shr := x.2.2.2.2.2.2.2.2.2,
                    inv := x.2.1 }}),
            x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2, x.2.1,
            {Item.cache { id := x.1, state := x.2.2.1, ch1 := x.2.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.cmdS, ptr := x.1, exGntd := false, shr := {x.1} + x.2.2.2.2.2.1,
                    inv := x.2.2.2.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × Items × CacheState × Req × Ack × Oids × Cmd × ℕ × Oids × Oids) =>
          ((x.1, ∅, x.2.2.2.2.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
              x.2.1 +
                {Item.dir
                    { cmd := x.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.1, exGntd := false, shr := x.2.2.2.2.2.2.2.2.1,
                      inv := x.2.2.2.2.2.2.2.2.2 }}),
            x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2,
            x.2.1 +
                {Item.cache { id := x.1, state := x.2.2.1, ch1 := x.2.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.2.1 }} +
              {Item.dir { cmd := Cmd.cmdS, ptr := x.1, exGntd := false, shr := {x.1}, inv := x.2.2.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × Oids × Items × CacheState × Req × Ack × Oids × Oids × Cmd × ℕ × Oids) =>
          ((x.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
              x.2.2.1 +
                {Item.dir
                    { cmd := x.2.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.2.1, exGntd := false,
                      shr := x.2.2.2.2.2.2.2.2.2.2, inv := x.2.1 }}),
            x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2, x.2.1,
            x.2.2.1 +
                {Item.cache
                    { id := x.1, state := x.2.2.2.1, ch1 := x.2.2.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.cmdS, ptr := x.1, exGntd := false, shr := {x.1} + x.2.2.2.2.2.2.1,
                    inv := x.2.2.2.2.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : CacheState × Req × Ack × ℕ × Oids) =>
          ((x.2.2.2.1, ∅, x.2.2.2.2, x.1, x.2.1, x.2.2.1, ∅), Cmd.cmdS, x.2.2.2.1, {x.2.2.2.1}, x.2.2.2.2,
            {Item.cache { id := x.2.2.2.1, state := x.1, ch1 := x.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.1 }}),
        Unification.Unifier.bind fun (x : CacheState × Req × Ack × Oids × ℕ × Oids) =>
          ((x.2.2.2.2.1, x.2.2.2.1, x.2.2.2.2.2, x.1, x.2.1, x.2.2.1, ∅), Cmd.cmdS, x.2.2.2.2.1,
            {x.2.2.2.2.1} + x.2.2.2.1, x.2.2.2.2.2,
            {Item.cache { id := x.2.2.2.2.1, state := x.1, ch1 := x.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.1 }}),
        Unification.Unifier.bind fun (x : Items × CacheState × Req × Ack × ℕ × Oids) =>
          ((x.2.2.2.2.1, ∅, x.2.2.2.2.2, x.2.1, x.2.2.1, x.2.2.2.1, x.1), Cmd.cmdS, x.2.2.2.2.1, {x.2.2.2.2.1},
            x.2.2.2.2.2,
            x.1 +
              {Item.cache { id := x.2.2.2.2.1, state := x.2.1, ch1 := x.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : Items × CacheState × Req × Ack × Oids × ℕ × Oids) =>
          ((x.2.2.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.2, x.2.1, x.2.2.1, x.2.2.2.1, x.1), Cmd.cmdS, x.2.2.2.2.2.1,
            {x.2.2.2.2.2.1} + x.2.2.2.2.1, x.2.2.2.2.2.2,
            x.1 +
              {Item.cache
                  { id := x.2.2.2.2.2.1, state := x.2.1, ch1 := x.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.1 }})] := by
  maude_certify_comp

theorem sendGntSS_inv.obligation_2 :
    Unification.sound (Narrowing.mayFire sendGntSS freeP)
      [Unification.Unifier.bind fun (x : ℕ × CacheState × Req × Ack × Oids × Cmd × ℕ × Oids × Oids) =>
          ((x.1, ∅, x.2.2.2.2.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {Item.dir
                  { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.1, exGntd := false, shr := x.2.2.2.2.2.2.2.1,
                    inv := x.2.2.2.2.2.2.2.2 }}),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2,
            {Item.cache { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.1 }} +
              {Item.dir { cmd := Cmd.cmdS, ptr := x.1, exGntd := false, shr := {x.1}, inv := x.2.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × Oids × CacheState × Req × Ack × Oids × Oids × Cmd × ℕ × Oids) =>
          ((x.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
              {Item.dir
                  { cmd := x.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.1, exGntd := false, shr := x.2.2.2.2.2.2.2.2.2,
                    inv := x.2.1 }}),
            x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2, x.2.1,
            {Item.cache { id := x.1, state := x.2.2.1, ch1 := x.2.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.cmdS, ptr := x.1, exGntd := false, shr := {x.1} + x.2.2.2.2.2.1,
                    inv := x.2.2.2.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × Items × CacheState × Req × Ack × Oids × Cmd × ℕ × Oids × Oids) =>
          ((x.1, ∅, x.2.2.2.2.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
              x.2.1 +
                {Item.dir
                    { cmd := x.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.1, exGntd := false, shr := x.2.2.2.2.2.2.2.2.1,
                      inv := x.2.2.2.2.2.2.2.2.2 }}),
            x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2,
            x.2.1 +
                {Item.cache { id := x.1, state := x.2.2.1, ch1 := x.2.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.2.1 }} +
              {Item.dir { cmd := Cmd.cmdS, ptr := x.1, exGntd := false, shr := {x.1}, inv := x.2.2.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × Oids × Items × CacheState × Req × Ack × Oids × Oids × Cmd × ℕ × Oids) =>
          ((x.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
              x.2.2.1 +
                {Item.dir
                    { cmd := x.2.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.2.1, exGntd := false,
                      shr := x.2.2.2.2.2.2.2.2.2.2, inv := x.2.1 }}),
            x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2, x.2.1,
            x.2.2.1 +
                {Item.cache
                    { id := x.1, state := x.2.2.2.1, ch1 := x.2.2.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.cmdS, ptr := x.1, exGntd := false, shr := {x.1} + x.2.2.2.2.2.2.1,
                    inv := x.2.2.2.2.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : CacheState × Req × Ack × ℕ × Oids) =>
          ((x.2.2.2.1, ∅, x.2.2.2.2, x.1, x.2.1, x.2.2.1, ∅), Cmd.cmdS, x.2.2.2.1, {x.2.2.2.1}, x.2.2.2.2,
            {Item.cache { id := x.2.2.2.1, state := x.1, ch1 := x.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.1 }}),
        Unification.Unifier.bind fun (x : CacheState × Req × Ack × Oids × ℕ × Oids) =>
          ((x.2.2.2.2.1, x.2.2.2.1, x.2.2.2.2.2, x.1, x.2.1, x.2.2.1, ∅), Cmd.cmdS, x.2.2.2.2.1,
            {x.2.2.2.2.1} + x.2.2.2.1, x.2.2.2.2.2,
            {Item.cache { id := x.2.2.2.2.1, state := x.1, ch1 := x.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.1 }}),
        Unification.Unifier.bind fun (x : Items × CacheState × Req × Ack × ℕ × Oids) =>
          ((x.2.2.2.2.1, ∅, x.2.2.2.2.2, x.2.1, x.2.2.1, x.2.2.2.1, x.1), Cmd.cmdS, x.2.2.2.2.1, {x.2.2.2.2.1},
            x.2.2.2.2.2,
            x.1 +
              {Item.cache { id := x.2.2.2.2.1, state := x.2.1, ch1 := x.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : Items × CacheState × Req × Ack × Oids × ℕ × Oids) =>
          ((x.2.2.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.2, x.2.1, x.2.2.1, x.2.2.2.1, x.1), Cmd.cmdS, x.2.2.2.2.2.1,
            {x.2.2.2.2.2.1} + x.2.2.2.2.1, x.2.2.2.2.2.2,
            x.1 +
              {Item.cache
                  { id := x.2.2.2.2.2.1, state := x.2.1, ch1 := x.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.1 }})] := by
  sorry

theorem sendGntSS_inv.obligation_3 :
    Unification.complete (Narrowing.mayFire sendGntSS ownE)
      [Unification.Unifier.bind fun (x : ℕ × Oids × CacheState × Req × Ack × Oids × ℕ × Req × Cmd × ℕ) =>
          ((x.1, ∅, x.2.2.2.2.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
              {Item.cache
                    { id := x.2.2.2.2.2.2.1, state := CacheState.exclusive, ch1 := x.2.2.2.2.2.2.2.1, ch2 := Gnt.noGnt,
                      ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.2, exGntd := true, shr := {x.2.2.2.2.2.2.1},
                      inv := x.2.1 }}),
            x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2, x.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1,
            {Item.cache { id := x.1, state := x.2.2.1, ch1 := x.2.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.2.1 }} +
              {Item.dir { cmd := Cmd.cmdS, ptr := x.1, exGntd := false, shr := {x.1}, inv := x.2.2.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × ℕ × Oids × CacheState × Req × Ack × Oids × Oids × ℕ × Req × Cmd) =>
          ((x.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
              {Item.cache
                    { id := x.2.2.2.2.2.2.2.2.1, state := CacheState.exclusive, ch1 := x.2.2.2.2.2.2.2.2.2.1,
                      ch2 := Gnt.noGnt, ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.2.2.2.2.2, ptr := x.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.1},
                      inv := x.2.2.1 }}),
            x.2.2.2.2.2.2.2.2.2.2, x.2.1, x.2.2.1, x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1,
            {Item.cache { id := x.1, state := x.2.2.2.1, ch1 := x.2.2.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.cmdS, ptr := x.1, exGntd := false, shr := {x.1} + x.2.2.2.2.2.2.1,
                    inv := x.2.2.2.2.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × Oids × Items × CacheState × Req × Ack × Oids × ℕ × Req × Cmd × ℕ) =>
          ((x.1, ∅, x.2.2.2.2.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
              x.2.2.1 +
                  {Item.cache
                      { id := x.2.2.2.2.2.2.2.1, state := CacheState.exclusive, ch1 := x.2.2.2.2.2.2.2.2.1,
                        ch2 := Gnt.noGnt, ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.2.2, exGntd := true,
                      shr := {x.2.2.2.2.2.2.2.1}, inv := x.2.1 }}),
            x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2, x.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1,
            x.2.2.1 +
                {Item.cache
                    { id := x.1, state := x.2.2.2.1, ch1 := x.2.2.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.2.2.1 }} +
              {Item.dir { cmd := Cmd.cmdS, ptr := x.1, exGntd := false, shr := {x.1}, inv := x.2.2.2.2.2.2.1 }}),
        Unification.Unifier.bind
          fun (x : ℕ × ℕ × Oids × Items × CacheState × Req × Ack × Oids × Oids × ℕ × Req × Cmd) =>
          ((x.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
              x.2.2.2.1 +
                  {Item.cache
                      { id := x.2.2.2.2.2.2.2.2.2.1, state := CacheState.exclusive, ch1 := x.2.2.2.2.2.2.2.2.2.2.1,
                        ch2 := Gnt.noGnt, ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.2.2.2.2.2.2, ptr := x.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.2.1},
                      inv := x.2.2.1 }}),
            x.2.2.2.2.2.2.2.2.2.2.2, x.2.1, x.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1,
            x.2.2.2.1 +
                {Item.cache
                    { id := x.1, state := x.2.2.2.2.1, ch1 := x.2.2.2.2.2.1, ch2 := Gnt.noGnt,
                      ch3 := x.2.2.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.cmdS, ptr := x.1, exGntd := false, shr := {x.1} + x.2.2.2.2.2.2.2.1,
                    inv := x.2.2.2.2.2.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : Oids × ℕ × Req × Cmd × ℕ × Oids) =>
          ((x.2.1, ∅, x.1, CacheState.exclusive, x.2.2.1, Ack.noAck,
              {Item.dir { cmd := x.2.2.2.1, ptr := x.2.2.2.2.1, exGntd := true, shr := {x.2.1}, inv := x.2.2.2.2.2 }}),
            x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2, x.2.1, x.2.2.1,
            {Item.dir { cmd := Cmd.cmdS, ptr := x.2.1, exGntd := false, shr := {x.2.1}, inv := x.1 }}),
        Unification.Unifier.bind fun (x : Oids × Oids × ℕ × Req × Cmd × ℕ × Oids) =>
          ((x.2.2.1, x.1, x.2.1, CacheState.exclusive, x.2.2.2.1, Ack.noAck,
              {Item.dir
                  { cmd := x.2.2.2.2.1, ptr := x.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.1},
                    inv := x.2.2.2.2.2.2 }}),
            x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2, x.2.2.1, x.2.2.2.1,
            {Item.dir { cmd := Cmd.cmdS, ptr := x.2.2.1, exGntd := false, shr := {x.2.2.1} + x.1, inv := x.2.1 }}),
        Unification.Unifier.bind fun (x : Oids × ℕ × Req × Cmd × ℕ × Oids × Items) =>
          ((x.2.1, ∅, x.1, CacheState.exclusive, x.2.2.1, Ack.noAck,
              x.2.2.2.2.2.2 +
                {Item.dir
                    { cmd := x.2.2.2.1, ptr := x.2.2.2.2.1, exGntd := true, shr := {x.2.1}, inv := x.2.2.2.2.2.1 }}),
            x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.1, x.2.2.1,
            x.2.2.2.2.2.2 + {Item.dir { cmd := Cmd.cmdS, ptr := x.2.1, exGntd := false, shr := {x.2.1}, inv := x.1 }}),
        Unification.Unifier.bind fun (x : Oids × Oids × ℕ × Req × Cmd × ℕ × Oids × Items) =>
          ((x.2.2.1, x.1, x.2.1, CacheState.exclusive, x.2.2.2.1, Ack.noAck,
              x.2.2.2.2.2.2.2 +
                {Item.dir
                    { cmd := x.2.2.2.2.1, ptr := x.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.1},
                      inv := x.2.2.2.2.2.2.1 }}),
            x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.1, x.2.2.2.1,
            x.2.2.2.2.2.2.2 +
              {Item.dir
                  { cmd := Cmd.cmdS, ptr := x.2.2.1, exGntd := false, shr := {x.2.2.1} + x.1, inv := x.2.1 }})] := by
  maude_certify_comp

theorem sendGntSS_inv.obligation_4 :
    Unification.sound (Narrowing.mayFire sendGntSS ownE)
      [Unification.Unifier.bind fun (x : ℕ × Oids × CacheState × Req × Ack × Oids × ℕ × Req × Cmd × ℕ) =>
          ((x.1, ∅, x.2.2.2.2.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
              {Item.cache
                    { id := x.2.2.2.2.2.2.1, state := CacheState.exclusive, ch1 := x.2.2.2.2.2.2.2.1, ch2 := Gnt.noGnt,
                      ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.2, exGntd := true, shr := {x.2.2.2.2.2.2.1},
                      inv := x.2.1 }}),
            x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2, x.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1,
            {Item.cache { id := x.1, state := x.2.2.1, ch1 := x.2.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.2.1 }} +
              {Item.dir { cmd := Cmd.cmdS, ptr := x.1, exGntd := false, shr := {x.1}, inv := x.2.2.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × ℕ × Oids × CacheState × Req × Ack × Oids × Oids × ℕ × Req × Cmd) =>
          ((x.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
              {Item.cache
                    { id := x.2.2.2.2.2.2.2.2.1, state := CacheState.exclusive, ch1 := x.2.2.2.2.2.2.2.2.2.1,
                      ch2 := Gnt.noGnt, ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.2.2.2.2.2, ptr := x.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.1},
                      inv := x.2.2.1 }}),
            x.2.2.2.2.2.2.2.2.2.2, x.2.1, x.2.2.1, x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1,
            {Item.cache { id := x.1, state := x.2.2.2.1, ch1 := x.2.2.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.cmdS, ptr := x.1, exGntd := false, shr := {x.1} + x.2.2.2.2.2.2.1,
                    inv := x.2.2.2.2.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × Oids × Items × CacheState × Req × Ack × Oids × ℕ × Req × Cmd × ℕ) =>
          ((x.1, ∅, x.2.2.2.2.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
              x.2.2.1 +
                  {Item.cache
                      { id := x.2.2.2.2.2.2.2.1, state := CacheState.exclusive, ch1 := x.2.2.2.2.2.2.2.2.1,
                        ch2 := Gnt.noGnt, ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.2.2, exGntd := true,
                      shr := {x.2.2.2.2.2.2.2.1}, inv := x.2.1 }}),
            x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2, x.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1,
            x.2.2.1 +
                {Item.cache
                    { id := x.1, state := x.2.2.2.1, ch1 := x.2.2.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.2.2.1 }} +
              {Item.dir { cmd := Cmd.cmdS, ptr := x.1, exGntd := false, shr := {x.1}, inv := x.2.2.2.2.2.2.1 }}),
        Unification.Unifier.bind
          fun (x : ℕ × ℕ × Oids × Items × CacheState × Req × Ack × Oids × Oids × ℕ × Req × Cmd) =>
          ((x.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
              x.2.2.2.1 +
                  {Item.cache
                      { id := x.2.2.2.2.2.2.2.2.2.1, state := CacheState.exclusive, ch1 := x.2.2.2.2.2.2.2.2.2.2.1,
                        ch2 := Gnt.noGnt, ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.2.2.2.2.2.2, ptr := x.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.2.1},
                      inv := x.2.2.1 }}),
            x.2.2.2.2.2.2.2.2.2.2.2, x.2.1, x.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1,
            x.2.2.2.1 +
                {Item.cache
                    { id := x.1, state := x.2.2.2.2.1, ch1 := x.2.2.2.2.2.1, ch2 := Gnt.noGnt,
                      ch3 := x.2.2.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.cmdS, ptr := x.1, exGntd := false, shr := {x.1} + x.2.2.2.2.2.2.2.1,
                    inv := x.2.2.2.2.2.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : Oids × ℕ × Req × Cmd × ℕ × Oids) =>
          ((x.2.1, ∅, x.1, CacheState.exclusive, x.2.2.1, Ack.noAck,
              {Item.dir { cmd := x.2.2.2.1, ptr := x.2.2.2.2.1, exGntd := true, shr := {x.2.1}, inv := x.2.2.2.2.2 }}),
            x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2, x.2.1, x.2.2.1,
            {Item.dir { cmd := Cmd.cmdS, ptr := x.2.1, exGntd := false, shr := {x.2.1}, inv := x.1 }}),
        Unification.Unifier.bind fun (x : Oids × Oids × ℕ × Req × Cmd × ℕ × Oids) =>
          ((x.2.2.1, x.1, x.2.1, CacheState.exclusive, x.2.2.2.1, Ack.noAck,
              {Item.dir
                  { cmd := x.2.2.2.2.1, ptr := x.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.1},
                    inv := x.2.2.2.2.2.2 }}),
            x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2, x.2.2.1, x.2.2.2.1,
            {Item.dir { cmd := Cmd.cmdS, ptr := x.2.2.1, exGntd := false, shr := {x.2.2.1} + x.1, inv := x.2.1 }}),
        Unification.Unifier.bind fun (x : Oids × ℕ × Req × Cmd × ℕ × Oids × Items) =>
          ((x.2.1, ∅, x.1, CacheState.exclusive, x.2.2.1, Ack.noAck,
              x.2.2.2.2.2.2 +
                {Item.dir
                    { cmd := x.2.2.2.1, ptr := x.2.2.2.2.1, exGntd := true, shr := {x.2.1}, inv := x.2.2.2.2.2.1 }}),
            x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.1, x.2.2.1,
            x.2.2.2.2.2.2 + {Item.dir { cmd := Cmd.cmdS, ptr := x.2.1, exGntd := false, shr := {x.2.1}, inv := x.1 }}),
        Unification.Unifier.bind fun (x : Oids × Oids × ℕ × Req × Cmd × ℕ × Oids × Items) =>
          ((x.2.2.1, x.1, x.2.1, CacheState.exclusive, x.2.2.2.1, Ack.noAck,
              x.2.2.2.2.2.2.2 +
                {Item.dir
                    { cmd := x.2.2.2.2.1, ptr := x.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.1},
                      inv := x.2.2.2.2.2.2.1 }}),
            x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.1, x.2.2.2.1,
            x.2.2.2.2.2.2.2 +
              {Item.dir
                  { cmd := Cmd.cmdS, ptr := x.2.2.1, exGntd := false, shr := {x.2.2.1} + x.1, inv := x.2.1 }})] := by
  sorry

theorem sendGntSS_inv.obligation_5 :
    Unification.complete (Narrowing.mayFire sendGntSS ownG)
      [Unification.Unifier.bind fun (x : ℕ × Oids × CacheState × Req × Ack × Oids × ℕ × Req × Cmd × ℕ) =>
          ((x.1, ∅, x.2.2.2.2.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
              {Item.cache
                    { id := x.2.2.2.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.2.2.2.1, ch2 := Gnt.gntE,
                      ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.2, exGntd := true, shr := {x.2.2.2.2.2.2.1},
                      inv := x.2.1 }}),
            x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2, x.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1,
            {Item.cache { id := x.1, state := x.2.2.1, ch1 := x.2.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.2.1 }} +
              {Item.dir { cmd := Cmd.cmdS, ptr := x.1, exGntd := false, shr := {x.1}, inv := x.2.2.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × ℕ × Oids × CacheState × Req × Ack × Oids × Oids × ℕ × Req × Cmd) =>
          ((x.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
              {Item.cache
                    { id := x.2.2.2.2.2.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.2.2.2.2.2.1,
                      ch2 := Gnt.gntE, ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.2.2.2.2.2, ptr := x.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.1},
                      inv := x.2.2.1 }}),
            x.2.2.2.2.2.2.2.2.2.2, x.2.1, x.2.2.1, x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1,
            {Item.cache { id := x.1, state := x.2.2.2.1, ch1 := x.2.2.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.cmdS, ptr := x.1, exGntd := false, shr := {x.1} + x.2.2.2.2.2.2.1,
                    inv := x.2.2.2.2.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × Oids × Items × CacheState × Req × Ack × Oids × ℕ × Req × Cmd × ℕ) =>
          ((x.1, ∅, x.2.2.2.2.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
              x.2.2.1 +
                  {Item.cache
                      { id := x.2.2.2.2.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.2.2.2.2.1,
                        ch2 := Gnt.gntE, ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.2.2, exGntd := true,
                      shr := {x.2.2.2.2.2.2.2.1}, inv := x.2.1 }}),
            x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2, x.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1,
            x.2.2.1 +
                {Item.cache
                    { id := x.1, state := x.2.2.2.1, ch1 := x.2.2.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.2.2.1 }} +
              {Item.dir { cmd := Cmd.cmdS, ptr := x.1, exGntd := false, shr := {x.1}, inv := x.2.2.2.2.2.2.1 }}),
        Unification.Unifier.bind
          fun (x : ℕ × ℕ × Oids × Items × CacheState × Req × Ack × Oids × Oids × ℕ × Req × Cmd) =>
          ((x.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
              x.2.2.2.1 +
                  {Item.cache
                      { id := x.2.2.2.2.2.2.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.2.2.2.2.2.2.1,
                        ch2 := Gnt.gntE, ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.2.2.2.2.2.2, ptr := x.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.2.1},
                      inv := x.2.2.1 }}),
            x.2.2.2.2.2.2.2.2.2.2.2, x.2.1, x.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1,
            x.2.2.2.1 +
                {Item.cache
                    { id := x.1, state := x.2.2.2.2.1, ch1 := x.2.2.2.2.2.1, ch2 := Gnt.noGnt,
                      ch3 := x.2.2.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.cmdS, ptr := x.1, exGntd := false, shr := {x.1} + x.2.2.2.2.2.2.2.1,
                    inv := x.2.2.2.2.2.2.2.2.1 }})] := by
  maude_certify_comp

theorem sendGntSS_inv.obligation_6 :
    Unification.sound (Narrowing.mayFire sendGntSS ownG)
      [Unification.Unifier.bind fun (x : ℕ × Oids × CacheState × Req × Ack × Oids × ℕ × Req × Cmd × ℕ) =>
          ((x.1, ∅, x.2.2.2.2.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
              {Item.cache
                    { id := x.2.2.2.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.2.2.2.1, ch2 := Gnt.gntE,
                      ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.2, exGntd := true, shr := {x.2.2.2.2.2.2.1},
                      inv := x.2.1 }}),
            x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2, x.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1,
            {Item.cache { id := x.1, state := x.2.2.1, ch1 := x.2.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.2.1 }} +
              {Item.dir { cmd := Cmd.cmdS, ptr := x.1, exGntd := false, shr := {x.1}, inv := x.2.2.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × ℕ × Oids × CacheState × Req × Ack × Oids × Oids × ℕ × Req × Cmd) =>
          ((x.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
              {Item.cache
                    { id := x.2.2.2.2.2.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.2.2.2.2.2.1,
                      ch2 := Gnt.gntE, ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.2.2.2.2.2, ptr := x.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.1},
                      inv := x.2.2.1 }}),
            x.2.2.2.2.2.2.2.2.2.2, x.2.1, x.2.2.1, x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1,
            {Item.cache { id := x.1, state := x.2.2.2.1, ch1 := x.2.2.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.cmdS, ptr := x.1, exGntd := false, shr := {x.1} + x.2.2.2.2.2.2.1,
                    inv := x.2.2.2.2.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × Oids × Items × CacheState × Req × Ack × Oids × ℕ × Req × Cmd × ℕ) =>
          ((x.1, ∅, x.2.2.2.2.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
              x.2.2.1 +
                  {Item.cache
                      { id := x.2.2.2.2.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.2.2.2.2.1,
                        ch2 := Gnt.gntE, ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.2.2, exGntd := true,
                      shr := {x.2.2.2.2.2.2.2.1}, inv := x.2.1 }}),
            x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2, x.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1,
            x.2.2.1 +
                {Item.cache
                    { id := x.1, state := x.2.2.2.1, ch1 := x.2.2.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.2.2.1 }} +
              {Item.dir { cmd := Cmd.cmdS, ptr := x.1, exGntd := false, shr := {x.1}, inv := x.2.2.2.2.2.2.1 }}),
        Unification.Unifier.bind
          fun (x : ℕ × ℕ × Oids × Items × CacheState × Req × Ack × Oids × Oids × ℕ × Req × Cmd) =>
          ((x.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
              x.2.2.2.1 +
                  {Item.cache
                      { id := x.2.2.2.2.2.2.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.2.2.2.2.2.2.1,
                        ch2 := Gnt.gntE, ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.2.2.2.2.2.2, ptr := x.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.2.1},
                      inv := x.2.2.1 }}),
            x.2.2.2.2.2.2.2.2.2.2.2, x.2.1, x.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1,
            x.2.2.2.1 +
                {Item.cache
                    { id := x.1, state := x.2.2.2.2.1, ch1 := x.2.2.2.2.2.1, ch2 := Gnt.noGnt,
                      ch3 := x.2.2.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.cmdS, ptr := x.1, exGntd := false, shr := {x.1} + x.2.2.2.2.2.2.2.1,
                    inv := x.2.2.2.2.2.2.2.2.1 }})] := by
  sorry

theorem sendGntSS_inv.obligation_7 :
    Unification.complete (Narrowing.mayFire sendGntSS ownInv)
      [Unification.Unifier.bind fun (x : ℕ × CacheState × Req × Ack × Oids × ℕ × Req × Cmd × ℕ) =>
          ((x.1, ∅, x.2.2.2.2.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {Item.cache
                    { id := x.2.2.2.2.2.1, state := CacheState.exclusive, ch1 := x.2.2.2.2.2.2.1, ch2 := Gnt.inv,
                      ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2, exGntd := true, shr := {x.2.2.2.2.2.1},
                      inv := ∅ }}),
            x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
            {Item.cache { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.1 }} +
              {Item.dir { cmd := Cmd.cmdS, ptr := x.1, exGntd := false, shr := {x.1}, inv := x.2.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × ℕ × CacheState × Req × Ack × Oids × Oids × ℕ × Req × Cmd) =>
          ((x.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
              {Item.cache
                    { id := x.2.2.2.2.2.2.2.1, state := CacheState.exclusive, ch1 := x.2.2.2.2.2.2.2.2.1,
                      ch2 := Gnt.inv, ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.2.2.2.2, ptr := x.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.1},
                      inv := ∅ }}),
            x.2.2.2.2.2.2.2.2.2, x.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1,
            {Item.cache { id := x.1, state := x.2.2.1, ch1 := x.2.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.cmdS, ptr := x.1, exGntd := false, shr := {x.1} + x.2.2.2.2.2.1,
                    inv := x.2.2.2.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × Items × CacheState × Req × Ack × Oids × ℕ × Req × Cmd × ℕ) =>
          ((x.1, ∅, x.2.2.2.2.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
              x.2.1 +
                  {Item.cache
                      { id := x.2.2.2.2.2.2.1, state := CacheState.exclusive, ch1 := x.2.2.2.2.2.2.2.1, ch2 := Gnt.inv,
                        ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.2, exGntd := true, shr := {x.2.2.2.2.2.2.1},
                      inv := ∅ }}),
            x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1,
            x.2.1 +
                {Item.cache { id := x.1, state := x.2.2.1, ch1 := x.2.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.2.1 }} +
              {Item.dir { cmd := Cmd.cmdS, ptr := x.1, exGntd := false, shr := {x.1}, inv := x.2.2.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × ℕ × Items × CacheState × Req × Ack × Oids × Oids × ℕ × Req × Cmd) =>
          ((x.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
              x.2.2.1 +
                  {Item.cache
                      { id := x.2.2.2.2.2.2.2.2.1, state := CacheState.exclusive, ch1 := x.2.2.2.2.2.2.2.2.2.1,
                        ch2 := Gnt.inv, ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.2.2.2.2.2, ptr := x.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.1},
                      inv := ∅ }}),
            x.2.2.2.2.2.2.2.2.2.2, x.2.1, x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1,
            x.2.2.1 +
                {Item.cache
                    { id := x.1, state := x.2.2.2.1, ch1 := x.2.2.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.cmdS, ptr := x.1, exGntd := false, shr := {x.1} + x.2.2.2.2.2.2.1,
                    inv := x.2.2.2.2.2.2.2.1 }})] := by
  maude_certify_comp

theorem sendGntSS_inv.obligation_8 :
    Unification.sound (Narrowing.mayFire sendGntSS ownInv)
      [Unification.Unifier.bind fun (x : ℕ × CacheState × Req × Ack × Oids × ℕ × Req × Cmd × ℕ) =>
          ((x.1, ∅, x.2.2.2.2.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {Item.cache
                    { id := x.2.2.2.2.2.1, state := CacheState.exclusive, ch1 := x.2.2.2.2.2.2.1, ch2 := Gnt.inv,
                      ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2, exGntd := true, shr := {x.2.2.2.2.2.1},
                      inv := ∅ }}),
            x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
            {Item.cache { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.1 }} +
              {Item.dir { cmd := Cmd.cmdS, ptr := x.1, exGntd := false, shr := {x.1}, inv := x.2.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × ℕ × CacheState × Req × Ack × Oids × Oids × ℕ × Req × Cmd) =>
          ((x.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
              {Item.cache
                    { id := x.2.2.2.2.2.2.2.1, state := CacheState.exclusive, ch1 := x.2.2.2.2.2.2.2.2.1,
                      ch2 := Gnt.inv, ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.2.2.2.2, ptr := x.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.1},
                      inv := ∅ }}),
            x.2.2.2.2.2.2.2.2.2, x.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1,
            {Item.cache { id := x.1, state := x.2.2.1, ch1 := x.2.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.cmdS, ptr := x.1, exGntd := false, shr := {x.1} + x.2.2.2.2.2.1,
                    inv := x.2.2.2.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × Items × CacheState × Req × Ack × Oids × ℕ × Req × Cmd × ℕ) =>
          ((x.1, ∅, x.2.2.2.2.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
              x.2.1 +
                  {Item.cache
                      { id := x.2.2.2.2.2.2.1, state := CacheState.exclusive, ch1 := x.2.2.2.2.2.2.2.1, ch2 := Gnt.inv,
                        ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.2, exGntd := true, shr := {x.2.2.2.2.2.2.1},
                      inv := ∅ }}),
            x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1,
            x.2.1 +
                {Item.cache { id := x.1, state := x.2.2.1, ch1 := x.2.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.2.1 }} +
              {Item.dir { cmd := Cmd.cmdS, ptr := x.1, exGntd := false, shr := {x.1}, inv := x.2.2.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × ℕ × Items × CacheState × Req × Ack × Oids × Oids × ℕ × Req × Cmd) =>
          ((x.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
              x.2.2.1 +
                  {Item.cache
                      { id := x.2.2.2.2.2.2.2.2.1, state := CacheState.exclusive, ch1 := x.2.2.2.2.2.2.2.2.2.1,
                        ch2 := Gnt.inv, ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.2.2.2.2.2, ptr := x.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.1},
                      inv := ∅ }}),
            x.2.2.2.2.2.2.2.2.2.2, x.2.1, x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1,
            x.2.2.1 +
                {Item.cache
                    { id := x.1, state := x.2.2.2.1, ch1 := x.2.2.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.cmdS, ptr := x.1, exGntd := false, shr := {x.1} + x.2.2.2.2.2.2.1,
                    inv := x.2.2.2.2.2.2.2.1 }})] := by
  sorry

theorem sendGntSS_inv.obligation_9 :
    Unification.complete (Narrowing.mayFire sendGntSS ownAck)
      [Unification.Unifier.bind fun (x : ℕ × CacheState × Req × Ack × Oids × ℕ × Req × Cmd × ℕ) =>
          ((x.1, ∅, x.2.2.2.2.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {Item.cache
                    { id := x.2.2.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.2.2.1, ch2 := Gnt.noGnt,
                      ch3 := Ack.invAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2, exGntd := true, shr := {x.2.2.2.2.2.1},
                      inv := ∅ }}),
            x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
            {Item.cache { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.1 }} +
              {Item.dir { cmd := Cmd.cmdS, ptr := x.1, exGntd := false, shr := {x.1}, inv := x.2.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × ℕ × CacheState × Req × Ack × Oids × Oids × ℕ × Req × Cmd) =>
          ((x.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
              {Item.cache
                    { id := x.2.2.2.2.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.2.2.2.2.1,
                      ch2 := Gnt.noGnt, ch3 := Ack.invAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.2.2.2.2, ptr := x.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.1},
                      inv := ∅ }}),
            x.2.2.2.2.2.2.2.2.2, x.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1,
            {Item.cache { id := x.1, state := x.2.2.1, ch1 := x.2.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.cmdS, ptr := x.1, exGntd := false, shr := {x.1} + x.2.2.2.2.2.1,
                    inv := x.2.2.2.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × Items × CacheState × Req × Ack × Oids × ℕ × Req × Cmd × ℕ) =>
          ((x.1, ∅, x.2.2.2.2.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
              x.2.1 +
                  {Item.cache
                      { id := x.2.2.2.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.2.2.2.1, ch2 := Gnt.noGnt,
                        ch3 := Ack.invAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.2, exGntd := true, shr := {x.2.2.2.2.2.2.1},
                      inv := ∅ }}),
            x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1,
            x.2.1 +
                {Item.cache { id := x.1, state := x.2.2.1, ch1 := x.2.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.2.1 }} +
              {Item.dir { cmd := Cmd.cmdS, ptr := x.1, exGntd := false, shr := {x.1}, inv := x.2.2.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × ℕ × Items × CacheState × Req × Ack × Oids × Oids × ℕ × Req × Cmd) =>
          ((x.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
              x.2.2.1 +
                  {Item.cache
                      { id := x.2.2.2.2.2.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.2.2.2.2.2.1,
                        ch2 := Gnt.noGnt, ch3 := Ack.invAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.2.2.2.2.2, ptr := x.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.1},
                      inv := ∅ }}),
            x.2.2.2.2.2.2.2.2.2.2, x.2.1, x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1,
            x.2.2.1 +
                {Item.cache
                    { id := x.1, state := x.2.2.2.1, ch1 := x.2.2.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.cmdS, ptr := x.1, exGntd := false, shr := {x.1} + x.2.2.2.2.2.2.1,
                    inv := x.2.2.2.2.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : Oids × ℕ × Req × Cmd × ℕ) =>
          ((x.2.1, ∅, x.1, CacheState.invalid, x.2.2.1, Ack.invAck,
              {Item.dir { cmd := x.2.2.2.1, ptr := x.2.2.2.2, exGntd := true, shr := {x.2.1}, inv := ∅ }}),
            x.2.2.2.1, x.2.2.2.2, x.2.1, x.2.2.1,
            {Item.dir { cmd := Cmd.cmdS, ptr := x.2.1, exGntd := false, shr := {x.2.1}, inv := x.1 }}),
        Unification.Unifier.bind fun (x : Oids × Oids × ℕ × Req × Cmd × ℕ) =>
          ((x.2.2.1, x.1, x.2.1, CacheState.invalid, x.2.2.2.1, Ack.invAck,
              {Item.dir { cmd := x.2.2.2.2.1, ptr := x.2.2.2.2.2, exGntd := true, shr := {x.2.2.1}, inv := ∅ }}),
            x.2.2.2.2.1, x.2.2.2.2.2, x.2.2.1, x.2.2.2.1,
            {Item.dir { cmd := Cmd.cmdS, ptr := x.2.2.1, exGntd := false, shr := {x.2.2.1} + x.1, inv := x.2.1 }}),
        Unification.Unifier.bind fun (x : Oids × ℕ × Req × Cmd × ℕ × Items) =>
          ((x.2.1, ∅, x.1, CacheState.invalid, x.2.2.1, Ack.invAck,
              x.2.2.2.2.2 +
                {Item.dir { cmd := x.2.2.2.1, ptr := x.2.2.2.2.1, exGntd := true, shr := {x.2.1}, inv := ∅ }}),
            x.2.2.2.1, x.2.2.2.2.1, x.2.1, x.2.2.1,
            x.2.2.2.2.2 + {Item.dir { cmd := Cmd.cmdS, ptr := x.2.1, exGntd := false, shr := {x.2.1}, inv := x.1 }}),
        Unification.Unifier.bind fun (x : Oids × Oids × ℕ × Req × Cmd × ℕ × Items) =>
          ((x.2.2.1, x.1, x.2.1, CacheState.invalid, x.2.2.2.1, Ack.invAck,
              x.2.2.2.2.2.2 +
                {Item.dir { cmd := x.2.2.2.2.1, ptr := x.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.1}, inv := ∅ }}),
            x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.1, x.2.2.2.1,
            x.2.2.2.2.2.2 +
              {Item.dir
                  { cmd := Cmd.cmdS, ptr := x.2.2.1, exGntd := false, shr := {x.2.2.1} + x.1, inv := x.2.1 }})] := by
  maude_certify_comp

theorem sendGntSS_inv.obligation_10 :
    Unification.sound (Narrowing.mayFire sendGntSS ownAck)
      [Unification.Unifier.bind fun (x : ℕ × CacheState × Req × Ack × Oids × ℕ × Req × Cmd × ℕ) =>
          ((x.1, ∅, x.2.2.2.2.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {Item.cache
                    { id := x.2.2.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.2.2.1, ch2 := Gnt.noGnt,
                      ch3 := Ack.invAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2, exGntd := true, shr := {x.2.2.2.2.2.1},
                      inv := ∅ }}),
            x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
            {Item.cache { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.1 }} +
              {Item.dir { cmd := Cmd.cmdS, ptr := x.1, exGntd := false, shr := {x.1}, inv := x.2.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × ℕ × CacheState × Req × Ack × Oids × Oids × ℕ × Req × Cmd) =>
          ((x.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
              {Item.cache
                    { id := x.2.2.2.2.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.2.2.2.2.1,
                      ch2 := Gnt.noGnt, ch3 := Ack.invAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.2.2.2.2, ptr := x.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.1},
                      inv := ∅ }}),
            x.2.2.2.2.2.2.2.2.2, x.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1,
            {Item.cache { id := x.1, state := x.2.2.1, ch1 := x.2.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.cmdS, ptr := x.1, exGntd := false, shr := {x.1} + x.2.2.2.2.2.1,
                    inv := x.2.2.2.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × Items × CacheState × Req × Ack × Oids × ℕ × Req × Cmd × ℕ) =>
          ((x.1, ∅, x.2.2.2.2.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
              x.2.1 +
                  {Item.cache
                      { id := x.2.2.2.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.2.2.2.1, ch2 := Gnt.noGnt,
                        ch3 := Ack.invAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.2, exGntd := true, shr := {x.2.2.2.2.2.2.1},
                      inv := ∅ }}),
            x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1,
            x.2.1 +
                {Item.cache { id := x.1, state := x.2.2.1, ch1 := x.2.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.2.1 }} +
              {Item.dir { cmd := Cmd.cmdS, ptr := x.1, exGntd := false, shr := {x.1}, inv := x.2.2.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × ℕ × Items × CacheState × Req × Ack × Oids × Oids × ℕ × Req × Cmd) =>
          ((x.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
              x.2.2.1 +
                  {Item.cache
                      { id := x.2.2.2.2.2.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.2.2.2.2.2.1,
                        ch2 := Gnt.noGnt, ch3 := Ack.invAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.2.2.2.2.2, ptr := x.2.1, exGntd := true, shr := {x.2.2.2.2.2.2.2.2.1},
                      inv := ∅ }}),
            x.2.2.2.2.2.2.2.2.2.2, x.2.1, x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1,
            x.2.2.1 +
                {Item.cache
                    { id := x.1, state := x.2.2.2.1, ch1 := x.2.2.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.2.2.1 }} +
              {Item.dir
                  { cmd := Cmd.cmdS, ptr := x.1, exGntd := false, shr := {x.1} + x.2.2.2.2.2.2.1,
                    inv := x.2.2.2.2.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : Oids × ℕ × Req × Cmd × ℕ) =>
          ((x.2.1, ∅, x.1, CacheState.invalid, x.2.2.1, Ack.invAck,
              {Item.dir { cmd := x.2.2.2.1, ptr := x.2.2.2.2, exGntd := true, shr := {x.2.1}, inv := ∅ }}),
            x.2.2.2.1, x.2.2.2.2, x.2.1, x.2.2.1,
            {Item.dir { cmd := Cmd.cmdS, ptr := x.2.1, exGntd := false, shr := {x.2.1}, inv := x.1 }}),
        Unification.Unifier.bind fun (x : Oids × Oids × ℕ × Req × Cmd × ℕ) =>
          ((x.2.2.1, x.1, x.2.1, CacheState.invalid, x.2.2.2.1, Ack.invAck,
              {Item.dir { cmd := x.2.2.2.2.1, ptr := x.2.2.2.2.2, exGntd := true, shr := {x.2.2.1}, inv := ∅ }}),
            x.2.2.2.2.1, x.2.2.2.2.2, x.2.2.1, x.2.2.2.1,
            {Item.dir { cmd := Cmd.cmdS, ptr := x.2.2.1, exGntd := false, shr := {x.2.2.1} + x.1, inv := x.2.1 }}),
        Unification.Unifier.bind fun (x : Oids × ℕ × Req × Cmd × ℕ × Items) =>
          ((x.2.1, ∅, x.1, CacheState.invalid, x.2.2.1, Ack.invAck,
              x.2.2.2.2.2 +
                {Item.dir { cmd := x.2.2.2.1, ptr := x.2.2.2.2.1, exGntd := true, shr := {x.2.1}, inv := ∅ }}),
            x.2.2.2.1, x.2.2.2.2.1, x.2.1, x.2.2.1,
            x.2.2.2.2.2 + {Item.dir { cmd := Cmd.cmdS, ptr := x.2.1, exGntd := false, shr := {x.2.1}, inv := x.1 }}),
        Unification.Unifier.bind fun (x : Oids × Oids × ℕ × Req × Cmd × ℕ × Items) =>
          ((x.2.2.1, x.1, x.2.1, CacheState.invalid, x.2.2.2.1, Ack.invAck,
              x.2.2.2.2.2.2 +
                {Item.dir { cmd := x.2.2.2.2.1, ptr := x.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.1}, inv := ∅ }}),
            x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.1, x.2.2.2.1,
            x.2.2.2.2.2.2 +
              {Item.dir
                  { cmd := Cmd.cmdS, ptr := x.2.2.1, exGntd := false, shr := {x.2.2.1} + x.1, inv := x.2.1 }})] := by
  sorry

theorem sendGntE_inv.obligation_1 :
    Unification.complete (Narrowing.mayFire sendGntE freeP)
      [Unification.Unifier.bind fun (x : ℕ × CacheState × Req × Ack × Oids × Cmd × ℕ × Oids × Oids) =>
          ((x.1, x.2.2.2.2.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {Item.dir
                  { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.1, exGntd := false, shr := x.2.2.2.2.2.2.2.1,
                    inv := x.2.2.2.2.2.2.2.2 }}),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2,
            {Item.cache { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.1 }} +
              {Item.dir { cmd := Cmd.cmdE, ptr := x.1, exGntd := false, shr := ∅, inv := x.2.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × Items × CacheState × Req × Ack × Oids × Cmd × ℕ × Oids × Oids) =>
          ((x.1, x.2.2.2.2.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
              x.2.1 +
                {Item.dir
                    { cmd := x.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.1, exGntd := false, shr := x.2.2.2.2.2.2.2.2.1,
                      inv := x.2.2.2.2.2.2.2.2.2 }}),
            x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2,
            x.2.1 +
                {Item.cache { id := x.1, state := x.2.2.1, ch1 := x.2.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.2.1 }} +
              {Item.dir { cmd := Cmd.cmdE, ptr := x.1, exGntd := false, shr := ∅, inv := x.2.2.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : CacheState × Req × Ack × ℕ × Oids) =>
          ((x.2.2.2.1, x.2.2.2.2, x.1, x.2.1, x.2.2.1, ∅), Cmd.cmdE, x.2.2.2.1, ∅, x.2.2.2.2,
            {Item.cache { id := x.2.2.2.1, state := x.1, ch1 := x.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.1 }}),
        Unification.Unifier.bind fun (x : Items × CacheState × Req × Ack × ℕ × Oids) =>
          ((x.2.2.2.2.1, x.2.2.2.2.2, x.2.1, x.2.2.1, x.2.2.2.1, x.1), Cmd.cmdE, x.2.2.2.2.1, ∅, x.2.2.2.2.2,
            x.1 +
              {Item.cache
                  { id := x.2.2.2.2.1, state := x.2.1, ch1 := x.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.1 }})] := by
  maude_certify_comp

theorem sendGntE_inv.obligation_2 :
    Unification.sound (Narrowing.mayFire sendGntE freeP)
      [Unification.Unifier.bind fun (x : ℕ × CacheState × Req × Ack × Oids × Cmd × ℕ × Oids × Oids) =>
          ((x.1, x.2.2.2.2.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {Item.dir
                  { cmd := x.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.1, exGntd := false, shr := x.2.2.2.2.2.2.2.1,
                    inv := x.2.2.2.2.2.2.2.2 }}),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2,
            {Item.cache { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.1 }} +
              {Item.dir { cmd := Cmd.cmdE, ptr := x.1, exGntd := false, shr := ∅, inv := x.2.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × Items × CacheState × Req × Ack × Oids × Cmd × ℕ × Oids × Oids) =>
          ((x.1, x.2.2.2.2.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
              x.2.1 +
                {Item.dir
                    { cmd := x.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.1, exGntd := false, shr := x.2.2.2.2.2.2.2.2.1,
                      inv := x.2.2.2.2.2.2.2.2.2 }}),
            x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2,
            x.2.1 +
                {Item.cache { id := x.1, state := x.2.2.1, ch1 := x.2.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.2.1 }} +
              {Item.dir { cmd := Cmd.cmdE, ptr := x.1, exGntd := false, shr := ∅, inv := x.2.2.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : CacheState × Req × Ack × ℕ × Oids) =>
          ((x.2.2.2.1, x.2.2.2.2, x.1, x.2.1, x.2.2.1, ∅), Cmd.cmdE, x.2.2.2.1, ∅, x.2.2.2.2,
            {Item.cache { id := x.2.2.2.1, state := x.1, ch1 := x.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.1 }}),
        Unification.Unifier.bind fun (x : Items × CacheState × Req × Ack × ℕ × Oids) =>
          ((x.2.2.2.2.1, x.2.2.2.2.2, x.2.1, x.2.2.1, x.2.2.2.1, x.1), Cmd.cmdE, x.2.2.2.2.1, ∅, x.2.2.2.2.2,
            x.1 +
              {Item.cache
                  { id := x.2.2.2.2.1, state := x.2.1, ch1 := x.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.1 }})] := by
  sorry

theorem sendGntE_inv.obligation_3 :
    Unification.complete (Narrowing.mayFire sendGntE ownE)
      [Unification.Unifier.bind fun (x : ℕ × Oids × CacheState × Req × Ack × Oids × ℕ × Req × Cmd × ℕ) =>
          ((x.1, x.2.2.2.2.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
              {Item.cache
                    { id := x.2.2.2.2.2.2.1, state := CacheState.exclusive, ch1 := x.2.2.2.2.2.2.2.1, ch2 := Gnt.noGnt,
                      ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.2, exGntd := true, shr := {x.2.2.2.2.2.2.1},
                      inv := x.2.1 }}),
            x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2, x.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1,
            {Item.cache { id := x.1, state := x.2.2.1, ch1 := x.2.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.2.1 }} +
              {Item.dir { cmd := Cmd.cmdE, ptr := x.1, exGntd := false, shr := ∅, inv := x.2.2.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × Oids × Items × CacheState × Req × Ack × Oids × ℕ × Req × Cmd × ℕ) =>
          ((x.1, x.2.2.2.2.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
              x.2.2.1 +
                  {Item.cache
                      { id := x.2.2.2.2.2.2.2.1, state := CacheState.exclusive, ch1 := x.2.2.2.2.2.2.2.2.1,
                        ch2 := Gnt.noGnt, ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.2.2, exGntd := true,
                      shr := {x.2.2.2.2.2.2.2.1}, inv := x.2.1 }}),
            x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2, x.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1,
            x.2.2.1 +
                {Item.cache
                    { id := x.1, state := x.2.2.2.1, ch1 := x.2.2.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.2.2.1 }} +
              {Item.dir { cmd := Cmd.cmdE, ptr := x.1, exGntd := false, shr := ∅, inv := x.2.2.2.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : Oids × ℕ × Req × Cmd × ℕ × Oids) =>
          ((x.2.1, x.1, CacheState.exclusive, x.2.2.1, Ack.noAck,
              {Item.dir { cmd := x.2.2.2.1, ptr := x.2.2.2.2.1, exGntd := true, shr := {x.2.1}, inv := x.2.2.2.2.2 }}),
            x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2, x.2.1, x.2.2.1,
            {Item.dir { cmd := Cmd.cmdE, ptr := x.2.1, exGntd := false, shr := ∅, inv := x.1 }}),
        Unification.Unifier.bind fun (x : Oids × ℕ × Req × Cmd × ℕ × Oids × Items) =>
          ((x.2.1, x.1, CacheState.exclusive, x.2.2.1, Ack.noAck,
              x.2.2.2.2.2.2 +
                {Item.dir
                    { cmd := x.2.2.2.1, ptr := x.2.2.2.2.1, exGntd := true, shr := {x.2.1}, inv := x.2.2.2.2.2.1 }}),
            x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.1, x.2.2.1,
            x.2.2.2.2.2.2 + {Item.dir { cmd := Cmd.cmdE, ptr := x.2.1, exGntd := false, shr := ∅, inv := x.1 }})] := by
  maude_certify_comp

theorem sendGntE_inv.obligation_4 :
    Unification.sound (Narrowing.mayFire sendGntE ownE)
      [Unification.Unifier.bind fun (x : ℕ × Oids × CacheState × Req × Ack × Oids × ℕ × Req × Cmd × ℕ) =>
          ((x.1, x.2.2.2.2.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
              {Item.cache
                    { id := x.2.2.2.2.2.2.1, state := CacheState.exclusive, ch1 := x.2.2.2.2.2.2.2.1, ch2 := Gnt.noGnt,
                      ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.2, exGntd := true, shr := {x.2.2.2.2.2.2.1},
                      inv := x.2.1 }}),
            x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2, x.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1,
            {Item.cache { id := x.1, state := x.2.2.1, ch1 := x.2.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.2.1 }} +
              {Item.dir { cmd := Cmd.cmdE, ptr := x.1, exGntd := false, shr := ∅, inv := x.2.2.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × Oids × Items × CacheState × Req × Ack × Oids × ℕ × Req × Cmd × ℕ) =>
          ((x.1, x.2.2.2.2.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
              x.2.2.1 +
                  {Item.cache
                      { id := x.2.2.2.2.2.2.2.1, state := CacheState.exclusive, ch1 := x.2.2.2.2.2.2.2.2.1,
                        ch2 := Gnt.noGnt, ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.2.2, exGntd := true,
                      shr := {x.2.2.2.2.2.2.2.1}, inv := x.2.1 }}),
            x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2, x.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1,
            x.2.2.1 +
                {Item.cache
                    { id := x.1, state := x.2.2.2.1, ch1 := x.2.2.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.2.2.1 }} +
              {Item.dir { cmd := Cmd.cmdE, ptr := x.1, exGntd := false, shr := ∅, inv := x.2.2.2.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : Oids × ℕ × Req × Cmd × ℕ × Oids) =>
          ((x.2.1, x.1, CacheState.exclusive, x.2.2.1, Ack.noAck,
              {Item.dir { cmd := x.2.2.2.1, ptr := x.2.2.2.2.1, exGntd := true, shr := {x.2.1}, inv := x.2.2.2.2.2 }}),
            x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2, x.2.1, x.2.2.1,
            {Item.dir { cmd := Cmd.cmdE, ptr := x.2.1, exGntd := false, shr := ∅, inv := x.1 }}),
        Unification.Unifier.bind fun (x : Oids × ℕ × Req × Cmd × ℕ × Oids × Items) =>
          ((x.2.1, x.1, CacheState.exclusive, x.2.2.1, Ack.noAck,
              x.2.2.2.2.2.2 +
                {Item.dir
                    { cmd := x.2.2.2.1, ptr := x.2.2.2.2.1, exGntd := true, shr := {x.2.1}, inv := x.2.2.2.2.2.1 }}),
            x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.1, x.2.2.1,
            x.2.2.2.2.2.2 + {Item.dir { cmd := Cmd.cmdE, ptr := x.2.1, exGntd := false, shr := ∅, inv := x.1 }})] := by
  sorry

theorem sendGntE_inv.obligation_5 :
    Unification.complete (Narrowing.mayFire sendGntE ownG)
      [Unification.Unifier.bind fun (x : ℕ × Oids × CacheState × Req × Ack × Oids × ℕ × Req × Cmd × ℕ) =>
          ((x.1, x.2.2.2.2.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
              {Item.cache
                    { id := x.2.2.2.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.2.2.2.1, ch2 := Gnt.gntE,
                      ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.2, exGntd := true, shr := {x.2.2.2.2.2.2.1},
                      inv := x.2.1 }}),
            x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2, x.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1,
            {Item.cache { id := x.1, state := x.2.2.1, ch1 := x.2.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.2.1 }} +
              {Item.dir { cmd := Cmd.cmdE, ptr := x.1, exGntd := false, shr := ∅, inv := x.2.2.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × Oids × Items × CacheState × Req × Ack × Oids × ℕ × Req × Cmd × ℕ) =>
          ((x.1, x.2.2.2.2.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
              x.2.2.1 +
                  {Item.cache
                      { id := x.2.2.2.2.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.2.2.2.2.1,
                        ch2 := Gnt.gntE, ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.2.2, exGntd := true,
                      shr := {x.2.2.2.2.2.2.2.1}, inv := x.2.1 }}),
            x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2, x.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1,
            x.2.2.1 +
                {Item.cache
                    { id := x.1, state := x.2.2.2.1, ch1 := x.2.2.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.2.2.1 }} +
              {Item.dir { cmd := Cmd.cmdE, ptr := x.1, exGntd := false, shr := ∅, inv := x.2.2.2.2.2.2.1 }})] := by
  maude_certify_comp

theorem sendGntE_inv.obligation_6 :
    Unification.sound (Narrowing.mayFire sendGntE ownG)
      [Unification.Unifier.bind fun (x : ℕ × Oids × CacheState × Req × Ack × Oids × ℕ × Req × Cmd × ℕ) =>
          ((x.1, x.2.2.2.2.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
              {Item.cache
                    { id := x.2.2.2.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.2.2.2.1, ch2 := Gnt.gntE,
                      ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.2, exGntd := true, shr := {x.2.2.2.2.2.2.1},
                      inv := x.2.1 }}),
            x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2, x.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1,
            {Item.cache { id := x.1, state := x.2.2.1, ch1 := x.2.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.2.1 }} +
              {Item.dir { cmd := Cmd.cmdE, ptr := x.1, exGntd := false, shr := ∅, inv := x.2.2.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × Oids × Items × CacheState × Req × Ack × Oids × ℕ × Req × Cmd × ℕ) =>
          ((x.1, x.2.2.2.2.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
              x.2.2.1 +
                  {Item.cache
                      { id := x.2.2.2.2.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.2.2.2.2.1,
                        ch2 := Gnt.gntE, ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.2.2, exGntd := true,
                      shr := {x.2.2.2.2.2.2.2.1}, inv := x.2.1 }}),
            x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2, x.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1,
            x.2.2.1 +
                {Item.cache
                    { id := x.1, state := x.2.2.2.1, ch1 := x.2.2.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.2.2.1 }} +
              {Item.dir { cmd := Cmd.cmdE, ptr := x.1, exGntd := false, shr := ∅, inv := x.2.2.2.2.2.2.1 }})] := by
  sorry

theorem sendGntE_inv.obligation_7 :
    Unification.complete (Narrowing.mayFire sendGntE ownInv)
      [Unification.Unifier.bind fun (x : ℕ × CacheState × Req × Ack × Oids × ℕ × Req × Cmd × ℕ) =>
          ((x.1, x.2.2.2.2.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {Item.cache
                    { id := x.2.2.2.2.2.1, state := CacheState.exclusive, ch1 := x.2.2.2.2.2.2.1, ch2 := Gnt.inv,
                      ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2, exGntd := true, shr := {x.2.2.2.2.2.1},
                      inv := ∅ }}),
            x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
            {Item.cache { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.1 }} +
              {Item.dir { cmd := Cmd.cmdE, ptr := x.1, exGntd := false, shr := ∅, inv := x.2.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × Items × CacheState × Req × Ack × Oids × ℕ × Req × Cmd × ℕ) =>
          ((x.1, x.2.2.2.2.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
              x.2.1 +
                  {Item.cache
                      { id := x.2.2.2.2.2.2.1, state := CacheState.exclusive, ch1 := x.2.2.2.2.2.2.2.1, ch2 := Gnt.inv,
                        ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.2, exGntd := true, shr := {x.2.2.2.2.2.2.1},
                      inv := ∅ }}),
            x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1,
            x.2.1 +
                {Item.cache { id := x.1, state := x.2.2.1, ch1 := x.2.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.2.1 }} +
              {Item.dir { cmd := Cmd.cmdE, ptr := x.1, exGntd := false, shr := ∅, inv := x.2.2.2.2.2.1 }})] := by
  maude_certify_comp

theorem sendGntE_inv.obligation_8 :
    Unification.sound (Narrowing.mayFire sendGntE ownInv)
      [Unification.Unifier.bind fun (x : ℕ × CacheState × Req × Ack × Oids × ℕ × Req × Cmd × ℕ) =>
          ((x.1, x.2.2.2.2.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {Item.cache
                    { id := x.2.2.2.2.2.1, state := CacheState.exclusive, ch1 := x.2.2.2.2.2.2.1, ch2 := Gnt.inv,
                      ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2, exGntd := true, shr := {x.2.2.2.2.2.1},
                      inv := ∅ }}),
            x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
            {Item.cache { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.1 }} +
              {Item.dir { cmd := Cmd.cmdE, ptr := x.1, exGntd := false, shr := ∅, inv := x.2.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × Items × CacheState × Req × Ack × Oids × ℕ × Req × Cmd × ℕ) =>
          ((x.1, x.2.2.2.2.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
              x.2.1 +
                  {Item.cache
                      { id := x.2.2.2.2.2.2.1, state := CacheState.exclusive, ch1 := x.2.2.2.2.2.2.2.1, ch2 := Gnt.inv,
                        ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.2, exGntd := true, shr := {x.2.2.2.2.2.2.1},
                      inv := ∅ }}),
            x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1,
            x.2.1 +
                {Item.cache { id := x.1, state := x.2.2.1, ch1 := x.2.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.2.1 }} +
              {Item.dir { cmd := Cmd.cmdE, ptr := x.1, exGntd := false, shr := ∅, inv := x.2.2.2.2.2.1 }})] := by
  sorry

theorem sendGntE_inv.obligation_9 :
    Unification.complete (Narrowing.mayFire sendGntE ownAck)
      [Unification.Unifier.bind fun (x : ℕ × CacheState × Req × Ack × Oids × ℕ × Req × Cmd × ℕ) =>
          ((x.1, x.2.2.2.2.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {Item.cache
                    { id := x.2.2.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.2.2.1, ch2 := Gnt.noGnt,
                      ch3 := Ack.invAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2, exGntd := true, shr := {x.2.2.2.2.2.1},
                      inv := ∅ }}),
            x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
            {Item.cache { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.1 }} +
              {Item.dir { cmd := Cmd.cmdE, ptr := x.1, exGntd := false, shr := ∅, inv := x.2.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × Items × CacheState × Req × Ack × Oids × ℕ × Req × Cmd × ℕ) =>
          ((x.1, x.2.2.2.2.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
              x.2.1 +
                  {Item.cache
                      { id := x.2.2.2.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.2.2.2.1, ch2 := Gnt.noGnt,
                        ch3 := Ack.invAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.2, exGntd := true, shr := {x.2.2.2.2.2.2.1},
                      inv := ∅ }}),
            x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1,
            x.2.1 +
                {Item.cache { id := x.1, state := x.2.2.1, ch1 := x.2.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.2.1 }} +
              {Item.dir { cmd := Cmd.cmdE, ptr := x.1, exGntd := false, shr := ∅, inv := x.2.2.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : Oids × ℕ × Req × Cmd × ℕ) =>
          ((x.2.1, x.1, CacheState.invalid, x.2.2.1, Ack.invAck,
              {Item.dir { cmd := x.2.2.2.1, ptr := x.2.2.2.2, exGntd := true, shr := {x.2.1}, inv := ∅ }}),
            x.2.2.2.1, x.2.2.2.2, x.2.1, x.2.2.1,
            {Item.dir { cmd := Cmd.cmdE, ptr := x.2.1, exGntd := false, shr := ∅, inv := x.1 }}),
        Unification.Unifier.bind fun (x : Oids × ℕ × Req × Cmd × ℕ × Items) =>
          ((x.2.1, x.1, CacheState.invalid, x.2.2.1, Ack.invAck,
              x.2.2.2.2.2 +
                {Item.dir { cmd := x.2.2.2.1, ptr := x.2.2.2.2.1, exGntd := true, shr := {x.2.1}, inv := ∅ }}),
            x.2.2.2.1, x.2.2.2.2.1, x.2.1, x.2.2.1,
            x.2.2.2.2.2 + {Item.dir { cmd := Cmd.cmdE, ptr := x.2.1, exGntd := false, shr := ∅, inv := x.1 }})] := by
  maude_certify_comp

theorem sendGntE_inv.obligation_10 :
    Unification.sound (Narrowing.mayFire sendGntE ownAck)
      [Unification.Unifier.bind fun (x : ℕ × CacheState × Req × Ack × Oids × ℕ × Req × Cmd × ℕ) =>
          ((x.1, x.2.2.2.2.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {Item.cache
                    { id := x.2.2.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.2.2.1, ch2 := Gnt.noGnt,
                      ch3 := Ack.invAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2, exGntd := true, shr := {x.2.2.2.2.2.1},
                      inv := ∅ }}),
            x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
            {Item.cache { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.1 }} +
              {Item.dir { cmd := Cmd.cmdE, ptr := x.1, exGntd := false, shr := ∅, inv := x.2.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × Items × CacheState × Req × Ack × Oids × ℕ × Req × Cmd × ℕ) =>
          ((x.1, x.2.2.2.2.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
              x.2.1 +
                  {Item.cache
                      { id := x.2.2.2.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.2.2.2.1, ch2 := Gnt.noGnt,
                        ch3 := Ack.invAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.2, exGntd := true, shr := {x.2.2.2.2.2.2.1},
                      inv := ∅ }}),
            x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1,
            x.2.1 +
                {Item.cache { id := x.1, state := x.2.2.1, ch1 := x.2.2.2.1, ch2 := Gnt.noGnt, ch3 := x.2.2.2.2.1 }} +
              {Item.dir { cmd := Cmd.cmdE, ptr := x.1, exGntd := false, shr := ∅, inv := x.2.2.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : Oids × ℕ × Req × Cmd × ℕ) =>
          ((x.2.1, x.1, CacheState.invalid, x.2.2.1, Ack.invAck,
              {Item.dir { cmd := x.2.2.2.1, ptr := x.2.2.2.2, exGntd := true, shr := {x.2.1}, inv := ∅ }}),
            x.2.2.2.1, x.2.2.2.2, x.2.1, x.2.2.1,
            {Item.dir { cmd := Cmd.cmdE, ptr := x.2.1, exGntd := false, shr := ∅, inv := x.1 }}),
        Unification.Unifier.bind fun (x : Oids × ℕ × Req × Cmd × ℕ × Items) =>
          ((x.2.1, x.1, CacheState.invalid, x.2.2.1, Ack.invAck,
              x.2.2.2.2.2 +
                {Item.dir { cmd := x.2.2.2.1, ptr := x.2.2.2.2.1, exGntd := true, shr := {x.2.1}, inv := ∅ }}),
            x.2.2.2.1, x.2.2.2.2.1, x.2.1, x.2.2.1,
            x.2.2.2.2.2 + {Item.dir { cmd := Cmd.cmdE, ptr := x.2.1, exGntd := false, shr := ∅, inv := x.1 }})] := by
  sorry

theorem sendGntE_inv.obligation_11 :
    ∃ b ∈ inv, Expresso.subsumes [sendGntE_inv.post_1] [b] := by
  sorry

theorem sendGntE_inv.obligation_12 :
    ∃ b ∈ inv, Expresso.subsumes [sendGntE_inv.post_2] [b] := by
  sorry

theorem recvGntS_inv.obligation_1 :
    Unification.complete (Narrowing.mayFire recvGntS freeP)
      [Unification.Unifier.bind fun (x : ℕ × CacheState × Req × Ack × Cmd × ℕ × Oids × Oids) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {Item.dir
                  { cmd := x.2.2.2.2.1, ptr := x.2.2.2.2.2.1, exGntd := false, shr := x.2.2.2.2.2.2.1,
                    inv := x.2.2.2.2.2.2.2 }}),
            x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2,
            {Item.cache { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := Gnt.gntS, ch3 := x.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × CacheState × Req × Ack × Cmd × ℕ × Oids × Oids × Items) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              x.2.2.2.2.2.2.2.2 +
                {Item.dir
                    { cmd := x.2.2.2.2.1, ptr := x.2.2.2.2.2.1, exGntd := false, shr := x.2.2.2.2.2.2.1,
                      inv := x.2.2.2.2.2.2.2.1 }}),
            x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1,
            x.2.2.2.2.2.2.2.2 +
              {Item.cache { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := Gnt.gntS, ch3 := x.2.2.2.1 }})] := by
  maude_certify_comp

theorem recvGntS_inv.obligation_2 :
    Unification.sound (Narrowing.mayFire recvGntS freeP)
      [Unification.Unifier.bind fun (x : ℕ × CacheState × Req × Ack × Cmd × ℕ × Oids × Oids) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {Item.dir
                  { cmd := x.2.2.2.2.1, ptr := x.2.2.2.2.2.1, exGntd := false, shr := x.2.2.2.2.2.2.1,
                    inv := x.2.2.2.2.2.2.2 }}),
            x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2,
            {Item.cache { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := Gnt.gntS, ch3 := x.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × CacheState × Req × Ack × Cmd × ℕ × Oids × Oids × Items) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              x.2.2.2.2.2.2.2.2 +
                {Item.dir
                    { cmd := x.2.2.2.2.1, ptr := x.2.2.2.2.2.1, exGntd := false, shr := x.2.2.2.2.2.2.1,
                      inv := x.2.2.2.2.2.2.2.1 }}),
            x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1,
            x.2.2.2.2.2.2.2.2 +
              {Item.cache { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := Gnt.gntS, ch3 := x.2.2.2.1 }})] := by
  sorry

theorem recvGntS_inv.obligation_3 :
    Unification.complete (Narrowing.mayFire recvGntS ownE)
      [Unification.Unifier.bind fun (x : ℕ × CacheState × Req × Ack × ℕ × Req × Cmd × ℕ × Oids) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {Item.cache
                    { id := x.2.2.2.2.1, state := CacheState.exclusive, ch1 := x.2.2.2.2.2.1, ch2 := Gnt.noGnt,
                      ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.1},
                      inv := x.2.2.2.2.2.2.2.2 }}),
            x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2, x.2.2.2.2.1, x.2.2.2.2.2.1,
            {Item.cache { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := Gnt.gntS, ch3 := x.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × Items × CacheState × Req × Ack × ℕ × Req × Cmd × ℕ × Oids) =>
          ((x.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
              x.2.1 +
                  {Item.cache
                      { id := x.2.2.2.2.2.1, state := CacheState.exclusive, ch1 := x.2.2.2.2.2.2.1, ch2 := Gnt.noGnt,
                        ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.2.1},
                      inv := x.2.2.2.2.2.2.2.2.2 }}),
            x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
            x.2.1 +
              {Item.cache
                  { id := x.1, state := x.2.2.1, ch1 := x.2.2.2.1, ch2 := Gnt.gntS, ch3 := x.2.2.2.2.1 }})] := by
  maude_certify_comp

theorem recvGntS_inv.obligation_4 :
    Unification.sound (Narrowing.mayFire recvGntS ownE)
      [Unification.Unifier.bind fun (x : ℕ × CacheState × Req × Ack × ℕ × Req × Cmd × ℕ × Oids) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {Item.cache
                    { id := x.2.2.2.2.1, state := CacheState.exclusive, ch1 := x.2.2.2.2.2.1, ch2 := Gnt.noGnt,
                      ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.1},
                      inv := x.2.2.2.2.2.2.2.2 }}),
            x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2, x.2.2.2.2.1, x.2.2.2.2.2.1,
            {Item.cache { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := Gnt.gntS, ch3 := x.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × Items × CacheState × Req × Ack × ℕ × Req × Cmd × ℕ × Oids) =>
          ((x.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
              x.2.1 +
                  {Item.cache
                      { id := x.2.2.2.2.2.1, state := CacheState.exclusive, ch1 := x.2.2.2.2.2.2.1, ch2 := Gnt.noGnt,
                        ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.2.1},
                      inv := x.2.2.2.2.2.2.2.2.2 }}),
            x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
            x.2.1 +
              {Item.cache
                  { id := x.1, state := x.2.2.1, ch1 := x.2.2.2.1, ch2 := Gnt.gntS, ch3 := x.2.2.2.2.1 }})] := by
  sorry

theorem recvGntS_inv.obligation_5 :
    Unification.complete (Narrowing.mayFire recvGntS ownG)
      [Unification.Unifier.bind fun (x : ℕ × CacheState × Req × Ack × ℕ × Req × Cmd × ℕ × Oids) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {Item.cache
                    { id := x.2.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.2.1, ch2 := Gnt.gntE,
                      ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.1},
                      inv := x.2.2.2.2.2.2.2.2 }}),
            x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2, x.2.2.2.2.1, x.2.2.2.2.2.1,
            {Item.cache { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := Gnt.gntS, ch3 := x.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × Items × CacheState × Req × Ack × ℕ × Req × Cmd × ℕ × Oids) =>
          ((x.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
              x.2.1 +
                  {Item.cache
                      { id := x.2.2.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.2.2.1, ch2 := Gnt.gntE,
                        ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.2.1},
                      inv := x.2.2.2.2.2.2.2.2.2 }}),
            x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
            x.2.1 +
              {Item.cache
                  { id := x.1, state := x.2.2.1, ch1 := x.2.2.2.1, ch2 := Gnt.gntS, ch3 := x.2.2.2.2.1 }})] := by
  maude_certify_comp

theorem recvGntS_inv.obligation_6 :
    Unification.sound (Narrowing.mayFire recvGntS ownG)
      [Unification.Unifier.bind fun (x : ℕ × CacheState × Req × Ack × ℕ × Req × Cmd × ℕ × Oids) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {Item.cache
                    { id := x.2.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.2.1, ch2 := Gnt.gntE,
                      ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.1},
                      inv := x.2.2.2.2.2.2.2.2 }}),
            x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2, x.2.2.2.2.1, x.2.2.2.2.2.1,
            {Item.cache { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := Gnt.gntS, ch3 := x.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × Items × CacheState × Req × Ack × ℕ × Req × Cmd × ℕ × Oids) =>
          ((x.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
              x.2.1 +
                  {Item.cache
                      { id := x.2.2.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.2.2.1, ch2 := Gnt.gntE,
                        ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.2.1},
                      inv := x.2.2.2.2.2.2.2.2.2 }}),
            x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
            x.2.1 +
              {Item.cache
                  { id := x.1, state := x.2.2.1, ch1 := x.2.2.2.1, ch2 := Gnt.gntS, ch3 := x.2.2.2.2.1 }})] := by
  sorry

theorem recvGntS_inv.obligation_7 :
    Unification.complete (Narrowing.mayFire recvGntS ownInv)
      [Unification.Unifier.bind fun (x : ℕ × CacheState × Req × Ack × ℕ × Req × Cmd × ℕ) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {Item.cache
                    { id := x.2.2.2.2.1, state := CacheState.exclusive, ch1 := x.2.2.2.2.2.1, ch2 := Gnt.inv,
                      ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2, exGntd := true, shr := {x.2.2.2.2.1},
                      inv := ∅ }}),
            x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2, x.2.2.2.2.1, x.2.2.2.2.2.1,
            {Item.cache { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := Gnt.gntS, ch3 := x.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × CacheState × Req × Ack × ℕ × Req × Cmd × ℕ × Items) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              x.2.2.2.2.2.2.2.2 +
                  {Item.cache
                      { id := x.2.2.2.2.1, state := CacheState.exclusive, ch1 := x.2.2.2.2.2.1, ch2 := Gnt.inv,
                        ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.1},
                      inv := ∅ }}),
            x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
            x.2.2.2.2.2.2.2.2 +
              {Item.cache { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := Gnt.gntS, ch3 := x.2.2.2.1 }})] := by
  maude_certify_comp

theorem recvGntS_inv.obligation_8 :
    Unification.sound (Narrowing.mayFire recvGntS ownInv)
      [Unification.Unifier.bind fun (x : ℕ × CacheState × Req × Ack × ℕ × Req × Cmd × ℕ) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {Item.cache
                    { id := x.2.2.2.2.1, state := CacheState.exclusive, ch1 := x.2.2.2.2.2.1, ch2 := Gnt.inv,
                      ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2, exGntd := true, shr := {x.2.2.2.2.1},
                      inv := ∅ }}),
            x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2, x.2.2.2.2.1, x.2.2.2.2.2.1,
            {Item.cache { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := Gnt.gntS, ch3 := x.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × CacheState × Req × Ack × ℕ × Req × Cmd × ℕ × Items) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              x.2.2.2.2.2.2.2.2 +
                  {Item.cache
                      { id := x.2.2.2.2.1, state := CacheState.exclusive, ch1 := x.2.2.2.2.2.1, ch2 := Gnt.inv,
                        ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.1},
                      inv := ∅ }}),
            x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
            x.2.2.2.2.2.2.2.2 +
              {Item.cache { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := Gnt.gntS, ch3 := x.2.2.2.1 }})] := by
  sorry

theorem recvGntS_inv.obligation_9 :
    Unification.complete (Narrowing.mayFire recvGntS ownAck)
      [Unification.Unifier.bind fun (x : ℕ × CacheState × Req × Ack × ℕ × Req × Cmd × ℕ) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {Item.cache
                    { id := x.2.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.2.1, ch2 := Gnt.noGnt,
                      ch3 := Ack.invAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2, exGntd := true, shr := {x.2.2.2.2.1},
                      inv := ∅ }}),
            x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2, x.2.2.2.2.1, x.2.2.2.2.2.1,
            {Item.cache { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := Gnt.gntS, ch3 := x.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × CacheState × Req × Ack × ℕ × Req × Cmd × ℕ × Items) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              x.2.2.2.2.2.2.2.2 +
                  {Item.cache
                      { id := x.2.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.2.1, ch2 := Gnt.noGnt,
                        ch3 := Ack.invAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.1},
                      inv := ∅ }}),
            x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
            x.2.2.2.2.2.2.2.2 +
              {Item.cache { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := Gnt.gntS, ch3 := x.2.2.2.1 }})] := by
  maude_certify_comp

theorem recvGntS_inv.obligation_10 :
    Unification.sound (Narrowing.mayFire recvGntS ownAck)
      [Unification.Unifier.bind fun (x : ℕ × CacheState × Req × Ack × ℕ × Req × Cmd × ℕ) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {Item.cache
                    { id := x.2.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.2.1, ch2 := Gnt.noGnt,
                      ch3 := Ack.invAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2, exGntd := true, shr := {x.2.2.2.2.1},
                      inv := ∅ }}),
            x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2, x.2.2.2.2.1, x.2.2.2.2.2.1,
            {Item.cache { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := Gnt.gntS, ch3 := x.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × CacheState × Req × Ack × ℕ × Req × Cmd × ℕ × Items) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              x.2.2.2.2.2.2.2.2 +
                  {Item.cache
                      { id := x.2.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.2.1, ch2 := Gnt.noGnt,
                        ch3 := Ack.invAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.1},
                      inv := ∅ }}),
            x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
            x.2.2.2.2.2.2.2.2 +
              {Item.cache { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := Gnt.gntS, ch3 := x.2.2.2.1 }})] := by
  sorry

theorem recvGntE_inv.obligation_1 :
    Unification.complete (Narrowing.mayFire recvGntE freeP)
      [Unification.Unifier.bind fun (x : ℕ × CacheState × Req × Ack × Cmd × ℕ × Oids × Oids) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {Item.dir
                  { cmd := x.2.2.2.2.1, ptr := x.2.2.2.2.2.1, exGntd := false, shr := x.2.2.2.2.2.2.1,
                    inv := x.2.2.2.2.2.2.2 }}),
            x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2,
            {Item.cache { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := Gnt.gntE, ch3 := x.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × CacheState × Req × Ack × Cmd × ℕ × Oids × Oids × Items) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              x.2.2.2.2.2.2.2.2 +
                {Item.dir
                    { cmd := x.2.2.2.2.1, ptr := x.2.2.2.2.2.1, exGntd := false, shr := x.2.2.2.2.2.2.1,
                      inv := x.2.2.2.2.2.2.2.1 }}),
            x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1,
            x.2.2.2.2.2.2.2.2 +
              {Item.cache { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := Gnt.gntE, ch3 := x.2.2.2.1 }})] := by
  maude_certify_comp

theorem recvGntE_inv.obligation_2 :
    Unification.sound (Narrowing.mayFire recvGntE freeP)
      [Unification.Unifier.bind fun (x : ℕ × CacheState × Req × Ack × Cmd × ℕ × Oids × Oids) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {Item.dir
                  { cmd := x.2.2.2.2.1, ptr := x.2.2.2.2.2.1, exGntd := false, shr := x.2.2.2.2.2.2.1,
                    inv := x.2.2.2.2.2.2.2 }}),
            x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2,
            {Item.cache { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := Gnt.gntE, ch3 := x.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × CacheState × Req × Ack × Cmd × ℕ × Oids × Oids × Items) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              x.2.2.2.2.2.2.2.2 +
                {Item.dir
                    { cmd := x.2.2.2.2.1, ptr := x.2.2.2.2.2.1, exGntd := false, shr := x.2.2.2.2.2.2.1,
                      inv := x.2.2.2.2.2.2.2.1 }}),
            x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1,
            x.2.2.2.2.2.2.2.2 +
              {Item.cache { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := Gnt.gntE, ch3 := x.2.2.2.1 }})] := by
  sorry

theorem recvGntE_inv.obligation_3 :
    Unification.complete (Narrowing.mayFire recvGntE ownE)
      [Unification.Unifier.bind fun (x : ℕ × CacheState × Req × Ack × ℕ × Req × Cmd × ℕ × Oids) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {Item.cache
                    { id := x.2.2.2.2.1, state := CacheState.exclusive, ch1 := x.2.2.2.2.2.1, ch2 := Gnt.noGnt,
                      ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.1},
                      inv := x.2.2.2.2.2.2.2.2 }}),
            x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2, x.2.2.2.2.1, x.2.2.2.2.2.1,
            {Item.cache { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := Gnt.gntE, ch3 := x.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × Items × CacheState × Req × Ack × ℕ × Req × Cmd × ℕ × Oids) =>
          ((x.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
              x.2.1 +
                  {Item.cache
                      { id := x.2.2.2.2.2.1, state := CacheState.exclusive, ch1 := x.2.2.2.2.2.2.1, ch2 := Gnt.noGnt,
                        ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.2.1},
                      inv := x.2.2.2.2.2.2.2.2.2 }}),
            x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
            x.2.1 +
              {Item.cache
                  { id := x.1, state := x.2.2.1, ch1 := x.2.2.2.1, ch2 := Gnt.gntE, ch3 := x.2.2.2.2.1 }})] := by
  maude_certify_comp

theorem recvGntE_inv.obligation_4 :
    Unification.sound (Narrowing.mayFire recvGntE ownE)
      [Unification.Unifier.bind fun (x : ℕ × CacheState × Req × Ack × ℕ × Req × Cmd × ℕ × Oids) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {Item.cache
                    { id := x.2.2.2.2.1, state := CacheState.exclusive, ch1 := x.2.2.2.2.2.1, ch2 := Gnt.noGnt,
                      ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.1},
                      inv := x.2.2.2.2.2.2.2.2 }}),
            x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2, x.2.2.2.2.1, x.2.2.2.2.2.1,
            {Item.cache { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := Gnt.gntE, ch3 := x.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × Items × CacheState × Req × Ack × ℕ × Req × Cmd × ℕ × Oids) =>
          ((x.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
              x.2.1 +
                  {Item.cache
                      { id := x.2.2.2.2.2.1, state := CacheState.exclusive, ch1 := x.2.2.2.2.2.2.1, ch2 := Gnt.noGnt,
                        ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.2.1},
                      inv := x.2.2.2.2.2.2.2.2.2 }}),
            x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
            x.2.1 +
              {Item.cache
                  { id := x.1, state := x.2.2.1, ch1 := x.2.2.2.1, ch2 := Gnt.gntE, ch3 := x.2.2.2.2.1 }})] := by
  sorry

theorem recvGntE_inv.obligation_5 :
    Unification.complete (Narrowing.mayFire recvGntE ownG)
      [Unification.Unifier.bind fun (x : ℕ × CacheState × Req × Ack × ℕ × Req × Cmd × ℕ × Oids) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {Item.cache
                    { id := x.2.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.2.1, ch2 := Gnt.gntE,
                      ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.1},
                      inv := x.2.2.2.2.2.2.2.2 }}),
            x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2, x.2.2.2.2.1, x.2.2.2.2.2.1,
            {Item.cache { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := Gnt.gntE, ch3 := x.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × Items × CacheState × Req × Ack × ℕ × Req × Cmd × ℕ × Oids) =>
          ((x.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
              x.2.1 +
                  {Item.cache
                      { id := x.2.2.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.2.2.1, ch2 := Gnt.gntE,
                        ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.2.1},
                      inv := x.2.2.2.2.2.2.2.2.2 }}),
            x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
            x.2.1 +
              {Item.cache { id := x.1, state := x.2.2.1, ch1 := x.2.2.2.1, ch2 := Gnt.gntE, ch3 := x.2.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × Req × Cmd × ℕ × Oids) =>
          ((x.1, CacheState.invalid, x.2.1, Ack.noAck,
              {Item.dir { cmd := x.2.2.1, ptr := x.2.2.2.1, exGntd := true, shr := {x.1}, inv := x.2.2.2.2 }}),
            x.2.2.1, x.2.2.2.1, x.2.2.2.2, x.1, x.2.1, ∅),
        Unification.Unifier.bind fun (x : Items × ℕ × Req × Cmd × ℕ × Oids) =>
          ((x.2.1, CacheState.invalid, x.2.2.1, Ack.noAck,
              x.1 +
                {Item.dir
                    { cmd := x.2.2.2.1, ptr := x.2.2.2.2.1, exGntd := true, shr := {x.2.1}, inv := x.2.2.2.2.2 }}),
            x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2, x.2.1, x.2.2.1, x.1)] := by
  maude_certify_comp

theorem recvGntE_inv.obligation_6 :
    Unification.sound (Narrowing.mayFire recvGntE ownG)
      [Unification.Unifier.bind fun (x : ℕ × CacheState × Req × Ack × ℕ × Req × Cmd × ℕ × Oids) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {Item.cache
                    { id := x.2.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.2.1, ch2 := Gnt.gntE,
                      ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.1},
                      inv := x.2.2.2.2.2.2.2.2 }}),
            x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2, x.2.2.2.2.1, x.2.2.2.2.2.1,
            {Item.cache { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := Gnt.gntE, ch3 := x.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × Items × CacheState × Req × Ack × ℕ × Req × Cmd × ℕ × Oids) =>
          ((x.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
              x.2.1 +
                  {Item.cache
                      { id := x.2.2.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.2.2.1, ch2 := Gnt.gntE,
                        ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.2.1},
                      inv := x.2.2.2.2.2.2.2.2.2 }}),
            x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
            x.2.1 +
              {Item.cache { id := x.1, state := x.2.2.1, ch1 := x.2.2.2.1, ch2 := Gnt.gntE, ch3 := x.2.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × Req × Cmd × ℕ × Oids) =>
          ((x.1, CacheState.invalid, x.2.1, Ack.noAck,
              {Item.dir { cmd := x.2.2.1, ptr := x.2.2.2.1, exGntd := true, shr := {x.1}, inv := x.2.2.2.2 }}),
            x.2.2.1, x.2.2.2.1, x.2.2.2.2, x.1, x.2.1, ∅),
        Unification.Unifier.bind fun (x : Items × ℕ × Req × Cmd × ℕ × Oids) =>
          ((x.2.1, CacheState.invalid, x.2.2.1, Ack.noAck,
              x.1 +
                {Item.dir
                    { cmd := x.2.2.2.1, ptr := x.2.2.2.2.1, exGntd := true, shr := {x.2.1}, inv := x.2.2.2.2.2 }}),
            x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2, x.2.1, x.2.2.1, x.1)] := by
  sorry

theorem recvGntE_inv.obligation_7 :
    Unification.complete (Narrowing.mayFire recvGntE ownInv)
      [Unification.Unifier.bind fun (x : ℕ × CacheState × Req × Ack × ℕ × Req × Cmd × ℕ) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {Item.cache
                    { id := x.2.2.2.2.1, state := CacheState.exclusive, ch1 := x.2.2.2.2.2.1, ch2 := Gnt.inv,
                      ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2, exGntd := true, shr := {x.2.2.2.2.1},
                      inv := ∅ }}),
            x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2, x.2.2.2.2.1, x.2.2.2.2.2.1,
            {Item.cache { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := Gnt.gntE, ch3 := x.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × CacheState × Req × Ack × ℕ × Req × Cmd × ℕ × Items) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              x.2.2.2.2.2.2.2.2 +
                  {Item.cache
                      { id := x.2.2.2.2.1, state := CacheState.exclusive, ch1 := x.2.2.2.2.2.1, ch2 := Gnt.inv,
                        ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.1},
                      inv := ∅ }}),
            x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
            x.2.2.2.2.2.2.2.2 +
              {Item.cache { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := Gnt.gntE, ch3 := x.2.2.2.1 }})] := by
  maude_certify_comp

theorem recvGntE_inv.obligation_8 :
    Unification.sound (Narrowing.mayFire recvGntE ownInv)
      [Unification.Unifier.bind fun (x : ℕ × CacheState × Req × Ack × ℕ × Req × Cmd × ℕ) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {Item.cache
                    { id := x.2.2.2.2.1, state := CacheState.exclusive, ch1 := x.2.2.2.2.2.1, ch2 := Gnt.inv,
                      ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2, exGntd := true, shr := {x.2.2.2.2.1},
                      inv := ∅ }}),
            x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2, x.2.2.2.2.1, x.2.2.2.2.2.1,
            {Item.cache { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := Gnt.gntE, ch3 := x.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × CacheState × Req × Ack × ℕ × Req × Cmd × ℕ × Items) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              x.2.2.2.2.2.2.2.2 +
                  {Item.cache
                      { id := x.2.2.2.2.1, state := CacheState.exclusive, ch1 := x.2.2.2.2.2.1, ch2 := Gnt.inv,
                        ch3 := Ack.noAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.1},
                      inv := ∅ }}),
            x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
            x.2.2.2.2.2.2.2.2 +
              {Item.cache { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := Gnt.gntE, ch3 := x.2.2.2.1 }})] := by
  sorry

theorem recvGntE_inv.obligation_9 :
    Unification.complete (Narrowing.mayFire recvGntE ownAck)
      [Unification.Unifier.bind fun (x : ℕ × CacheState × Req × Ack × ℕ × Req × Cmd × ℕ) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {Item.cache
                    { id := x.2.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.2.1, ch2 := Gnt.noGnt,
                      ch3 := Ack.invAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2, exGntd := true, shr := {x.2.2.2.2.1},
                      inv := ∅ }}),
            x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2, x.2.2.2.2.1, x.2.2.2.2.2.1,
            {Item.cache { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := Gnt.gntE, ch3 := x.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × CacheState × Req × Ack × ℕ × Req × Cmd × ℕ × Items) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              x.2.2.2.2.2.2.2.2 +
                  {Item.cache
                      { id := x.2.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.2.1, ch2 := Gnt.noGnt,
                        ch3 := Ack.invAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.1},
                      inv := ∅ }}),
            x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
            x.2.2.2.2.2.2.2.2 +
              {Item.cache { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := Gnt.gntE, ch3 := x.2.2.2.1 }})] := by
  maude_certify_comp

theorem recvGntE_inv.obligation_10 :
    Unification.sound (Narrowing.mayFire recvGntE ownAck)
      [Unification.Unifier.bind fun (x : ℕ × CacheState × Req × Ack × ℕ × Req × Cmd × ℕ) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              {Item.cache
                    { id := x.2.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.2.1, ch2 := Gnt.noGnt,
                      ch3 := Ack.invAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2, exGntd := true, shr := {x.2.2.2.2.1},
                      inv := ∅ }}),
            x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2, x.2.2.2.2.1, x.2.2.2.2.2.1,
            {Item.cache { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := Gnt.gntE, ch3 := x.2.2.2.1 }}),
        Unification.Unifier.bind fun (x : ℕ × CacheState × Req × Ack × ℕ × Req × Cmd × ℕ × Items) =>
          ((x.1, x.2.1, x.2.2.1, x.2.2.2.1,
              x.2.2.2.2.2.2.2.2 +
                  {Item.cache
                      { id := x.2.2.2.2.1, state := CacheState.invalid, ch1 := x.2.2.2.2.2.1, ch2 := Gnt.noGnt,
                        ch3 := Ack.invAck }} +
                {Item.dir
                    { cmd := x.2.2.2.2.2.2.1, ptr := x.2.2.2.2.2.2.2.1, exGntd := true, shr := {x.2.2.2.2.1},
                      inv := ∅ }}),
            x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
            x.2.2.2.2.2.2.2.2 +
              {Item.cache { id := x.1, state := x.2.1, ch1 := x.2.2.1, ch2 := Gnt.gntE, ch3 := x.2.2.2.1 }})] := by
  sorry

end German
