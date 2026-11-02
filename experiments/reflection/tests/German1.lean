import examples.German.proof
import Reflect.Tactic

set_option linter.style.longLine false
set_option profiler true

theorem R.sendReqS_inv.obligation_5 :
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
  udf_reflect

theorem R.recvReqS_inv.obligation_9 :
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
  udf_reflect

