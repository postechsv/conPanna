import examples.PetriNet.ReadersWriters.proof
import conPanna.Reflect.Tactic

/-!
Readers-writers: the certification obligations of `net_preserves_inv`, as `#obligations`
prints them. Completeness: the certificate narrowing stored for the claim, checked by
reflection (`certify_comp`). Soundness: each unifier, substituted into both sides, gives
terms equal modulo ACU, checked by reflection (`certify_sound`).
-/

set_option linter.style.longLine false

open Expresso Unification Narrowing

theorem ReadersWriters.net_preserves_inv.obligation_1 :
    Unification.complete (Narrowing.mayFire ReadersWriters.startRead ReadersWriters.freeP)
      [Unification.Unifier.bind fun (x : PetriNet.Marking ReadersWriters.Place) =>
          ({ReadersWriters.Place.tok} + x, {ReadersWriters.Place.idle} + x)] := by
  certify_comp

theorem ReadersWriters.net_preserves_inv.obligation_2 :
    Unification.sound (Narrowing.mayFire ReadersWriters.startRead ReadersWriters.freeP)
      [Unification.Unifier.bind fun (x : PetriNet.Marking ReadersWriters.Place) =>
          ({ReadersWriters.Place.tok} + x, {ReadersWriters.Place.idle} + x)] := by
  certify_sound

theorem ReadersWriters.net_preserves_inv.obligation_3 :
    Unification.complete (Narrowing.mayFire ReadersWriters.startRead ReadersWriters.oneReaderP)
      [Unification.Unifier.bind fun (x : PetriNet.Marking ReadersWriters.Place) =>
          ({ReadersWriters.Place.reading} + x, {ReadersWriters.Place.idle} + x)] := by
  certify_comp

theorem ReadersWriters.net_preserves_inv.obligation_4 :
    Unification.sound (Narrowing.mayFire ReadersWriters.startRead ReadersWriters.oneReaderP)
      [Unification.Unifier.bind fun (x : PetriNet.Marking ReadersWriters.Place) =>
          ({ReadersWriters.Place.reading} + x, {ReadersWriters.Place.idle} + x)] := by
  certify_sound

theorem ReadersWriters.net_preserves_inv.obligation_5 :
    Unification.complete (Narrowing.mayFire ReadersWriters.startRead ReadersWriters.twoReadersP)
      [Unification.Unifier.bind fun (x : PetriNet.Marking ReadersWriters.Place) =>
          ({ReadersWriters.Place.reading} + {ReadersWriters.Place.reading} + x,
            {ReadersWriters.Place.idle} + {ReadersWriters.Place.tok} + x)] := by
  certify_comp

theorem ReadersWriters.net_preserves_inv.obligation_6 :
    Unification.sound (Narrowing.mayFire ReadersWriters.startRead ReadersWriters.twoReadersP)
      [Unification.Unifier.bind fun (x : PetriNet.Marking ReadersWriters.Place) =>
          ({ReadersWriters.Place.reading} + {ReadersWriters.Place.reading} + x,
            {ReadersWriters.Place.idle} + {ReadersWriters.Place.tok} + x)] := by
  certify_sound

theorem ReadersWriters.net_preserves_inv.obligation_7 :
    Unification.complete (Narrowing.mayFire ReadersWriters.startRead ReadersWriters.writerP)
      [Unification.Unifier.bind fun (x : PetriNet.Marking ReadersWriters.Place) =>
          ({ReadersWriters.Place.writing} + x, {ReadersWriters.Place.idle} + {ReadersWriters.Place.tok} + x)] := by
  certify_comp

theorem ReadersWriters.net_preserves_inv.obligation_8 :
    Unification.sound (Narrowing.mayFire ReadersWriters.startRead ReadersWriters.writerP)
      [Unification.Unifier.bind fun (x : PetriNet.Marking ReadersWriters.Place) =>
          ({ReadersWriters.Place.writing} + x, {ReadersWriters.Place.idle} + {ReadersWriters.Place.tok} + x)] := by
  certify_sound

theorem ReadersWriters.net_preserves_inv.obligation_9 :
    Unification.complete (Narrowing.mayFire ReadersWriters.endRead ReadersWriters.freeP)
      [Unification.Unifier.bind fun (x : PetriNet.Marking ReadersWriters.Place) =>
          ({ReadersWriters.Place.tok} + {ReadersWriters.Place.tok} + x, {ReadersWriters.Place.reading} + x)] := by
  certify_comp

theorem ReadersWriters.net_preserves_inv.obligation_10 :
    Unification.sound (Narrowing.mayFire ReadersWriters.endRead ReadersWriters.freeP)
      [Unification.Unifier.bind fun (x : PetriNet.Marking ReadersWriters.Place) =>
          ({ReadersWriters.Place.tok} + {ReadersWriters.Place.tok} + x, {ReadersWriters.Place.reading} + x)] := by
  certify_sound

theorem ReadersWriters.net_preserves_inv.obligation_11 :
    Unification.complete (Narrowing.mayFire ReadersWriters.endRead ReadersWriters.oneReaderP)
      [Unification.Unifier.bind fun (x : PetriNet.Marking ReadersWriters.Place) =>
          ({ReadersWriters.Place.tok} + x, x)] := by
  certify_comp

theorem ReadersWriters.net_preserves_inv.obligation_12 :
    Unification.sound (Narrowing.mayFire ReadersWriters.endRead ReadersWriters.oneReaderP)
      [Unification.Unifier.bind fun (x : PetriNet.Marking ReadersWriters.Place) =>
          ({ReadersWriters.Place.tok} + x, x)] := by
  certify_sound

theorem ReadersWriters.net_preserves_inv.obligation_13 :
    Unification.complete (Narrowing.mayFire ReadersWriters.endRead ReadersWriters.twoReadersP)
      [Unification.Unifier.bind fun (x : PetriNet.Marking ReadersWriters.Place) =>
          ({ReadersWriters.Place.reading} + x, x)] := by
  certify_comp

theorem ReadersWriters.net_preserves_inv.obligation_14 :
    Unification.sound (Narrowing.mayFire ReadersWriters.endRead ReadersWriters.twoReadersP)
      [Unification.Unifier.bind fun (x : PetriNet.Marking ReadersWriters.Place) =>
          ({ReadersWriters.Place.reading} + x, x)] := by
  certify_sound

theorem ReadersWriters.net_preserves_inv.obligation_15 :
    Unification.complete (Narrowing.mayFire ReadersWriters.endRead ReadersWriters.writerP)
      [Unification.Unifier.bind fun (x : PetriNet.Marking ReadersWriters.Place) =>
          ({ReadersWriters.Place.writing} + x, {ReadersWriters.Place.reading} + x)] := by
  certify_comp

theorem ReadersWriters.net_preserves_inv.obligation_16 :
    Unification.sound (Narrowing.mayFire ReadersWriters.endRead ReadersWriters.writerP)
      [Unification.Unifier.bind fun (x : PetriNet.Marking ReadersWriters.Place) =>
          ({ReadersWriters.Place.writing} + x, {ReadersWriters.Place.reading} + x)] := by
  certify_sound

theorem ReadersWriters.net_preserves_inv.obligation_17 :
    Unification.complete (Narrowing.mayFire ReadersWriters.startWrite ReadersWriters.freeP)
      [Unification.Unifier.bind fun (x : PetriNet.Marking ReadersWriters.Place) =>
          (x, {ReadersWriters.Place.idle} + x)] := by
  certify_comp

theorem ReadersWriters.net_preserves_inv.obligation_18 :
    Unification.sound (Narrowing.mayFire ReadersWriters.startWrite ReadersWriters.freeP)
      [Unification.Unifier.bind fun (x : PetriNet.Marking ReadersWriters.Place) =>
          (x, {ReadersWriters.Place.idle} + x)] := by
  certify_sound

theorem ReadersWriters.net_preserves_inv.obligation_19 :
    Unification.complete (Narrowing.mayFire ReadersWriters.startWrite ReadersWriters.oneReaderP)
      [Unification.Unifier.bind fun (x : PetriNet.Marking ReadersWriters.Place) =>
          ({ReadersWriters.Place.reading} + x, {ReadersWriters.Place.idle} + {ReadersWriters.Place.tok} + x)] := by
  certify_comp

theorem ReadersWriters.net_preserves_inv.obligation_20 :
    Unification.sound (Narrowing.mayFire ReadersWriters.startWrite ReadersWriters.oneReaderP)
      [Unification.Unifier.bind fun (x : PetriNet.Marking ReadersWriters.Place) =>
          ({ReadersWriters.Place.reading} + x, {ReadersWriters.Place.idle} + {ReadersWriters.Place.tok} + x)] := by
  certify_sound

theorem ReadersWriters.net_preserves_inv.obligation_21 :
    Unification.complete (Narrowing.mayFire ReadersWriters.startWrite ReadersWriters.twoReadersP)
      [Unification.Unifier.bind fun (x : PetriNet.Marking ReadersWriters.Place) =>
          ({ReadersWriters.Place.reading} + {ReadersWriters.Place.reading} + x,
            {ReadersWriters.Place.idle} + {ReadersWriters.Place.tok} + {ReadersWriters.Place.tok} + x)] := by
  certify_comp

theorem ReadersWriters.net_preserves_inv.obligation_22 :
    Unification.sound (Narrowing.mayFire ReadersWriters.startWrite ReadersWriters.twoReadersP)
      [Unification.Unifier.bind fun (x : PetriNet.Marking ReadersWriters.Place) =>
          ({ReadersWriters.Place.reading} + {ReadersWriters.Place.reading} + x,
            {ReadersWriters.Place.idle} + {ReadersWriters.Place.tok} + {ReadersWriters.Place.tok} + x)] := by
  certify_sound

theorem ReadersWriters.net_preserves_inv.obligation_23 :
    Unification.complete (Narrowing.mayFire ReadersWriters.startWrite ReadersWriters.writerP)
      [Unification.Unifier.bind fun (x : PetriNet.Marking ReadersWriters.Place) =>
          ({ReadersWriters.Place.writing} + x,
            {ReadersWriters.Place.idle} + {ReadersWriters.Place.tok} + {ReadersWriters.Place.tok} + x)] := by
  certify_comp

theorem ReadersWriters.net_preserves_inv.obligation_24 :
    Unification.sound (Narrowing.mayFire ReadersWriters.startWrite ReadersWriters.writerP)
      [Unification.Unifier.bind fun (x : PetriNet.Marking ReadersWriters.Place) =>
          ({ReadersWriters.Place.writing} + x,
            {ReadersWriters.Place.idle} + {ReadersWriters.Place.tok} + {ReadersWriters.Place.tok} + x)] := by
  certify_sound

theorem ReadersWriters.net_preserves_inv.obligation_25 :
    Unification.complete (Narrowing.mayFire ReadersWriters.endWrite ReadersWriters.freeP)
      [Unification.Unifier.bind fun (x : PetriNet.Marking ReadersWriters.Place) =>
          ({ReadersWriters.Place.tok} + {ReadersWriters.Place.tok} + x, {ReadersWriters.Place.writing} + x)] := by
  certify_comp

theorem ReadersWriters.net_preserves_inv.obligation_26 :
    Unification.sound (Narrowing.mayFire ReadersWriters.endWrite ReadersWriters.freeP)
      [Unification.Unifier.bind fun (x : PetriNet.Marking ReadersWriters.Place) =>
          ({ReadersWriters.Place.tok} + {ReadersWriters.Place.tok} + x, {ReadersWriters.Place.writing} + x)] := by
  certify_sound

theorem ReadersWriters.net_preserves_inv.obligation_27 :
    Unification.complete (Narrowing.mayFire ReadersWriters.endWrite ReadersWriters.oneReaderP)
      [Unification.Unifier.bind fun (x : PetriNet.Marking ReadersWriters.Place) =>
          ({ReadersWriters.Place.reading} + {ReadersWriters.Place.tok} + x, {ReadersWriters.Place.writing} + x)] := by
  certify_comp

theorem ReadersWriters.net_preserves_inv.obligation_28 :
    Unification.sound (Narrowing.mayFire ReadersWriters.endWrite ReadersWriters.oneReaderP)
      [Unification.Unifier.bind fun (x : PetriNet.Marking ReadersWriters.Place) =>
          ({ReadersWriters.Place.reading} + {ReadersWriters.Place.tok} + x, {ReadersWriters.Place.writing} + x)] := by
  certify_sound

theorem ReadersWriters.net_preserves_inv.obligation_29 :
    Unification.complete (Narrowing.mayFire ReadersWriters.endWrite ReadersWriters.twoReadersP)
      [Unification.Unifier.bind fun (x : PetriNet.Marking ReadersWriters.Place) =>
          ({ReadersWriters.Place.reading} + {ReadersWriters.Place.reading} + x,
            {ReadersWriters.Place.writing} + x)] := by
  certify_comp

theorem ReadersWriters.net_preserves_inv.obligation_30 :
    Unification.sound (Narrowing.mayFire ReadersWriters.endWrite ReadersWriters.twoReadersP)
      [Unification.Unifier.bind fun (x : PetriNet.Marking ReadersWriters.Place) =>
          ({ReadersWriters.Place.reading} + {ReadersWriters.Place.reading} + x,
            {ReadersWriters.Place.writing} + x)] := by
  certify_sound

theorem ReadersWriters.net_preserves_inv.obligation_31 :
    Unification.complete (Narrowing.mayFire ReadersWriters.endWrite ReadersWriters.writerP)
      [Unification.Unifier.bind fun (x : PetriNet.Marking ReadersWriters.Place) => (x, x)] := by
  certify_comp

theorem ReadersWriters.net_preserves_inv.obligation_32 :
    Unification.sound (Narrowing.mayFire ReadersWriters.endWrite ReadersWriters.writerP)
      [Unification.Unifier.bind fun (x : PetriNet.Marking ReadersWriters.Place) => (x, x)] := by
  certify_sound
