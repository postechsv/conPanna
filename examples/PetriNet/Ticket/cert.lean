import examples.PetriNet.Ticket.proof
import conPanna.Reflect.Tactic

/-!
The ticket machine: the certification obligations of `net_preserves_inv`, as
`#obligations` prints them. Completeness: the certificate narrowing stored for the claim,
checked by reflection (`certify_comp`). Soundness: each unifier, substituted into both
sides, gives terms equal modulo ACU, checked by reflection (`certify_sound`).
-/

set_option linter.style.longLine false

open Expresso Unification Narrowing

theorem Ticket.net_preserves_inv.obligation_1 :
    Unification.complete (Narrowing.mayFire Ticket.b_t1 Ticket.worthP)
      [Unification.Unifier.bind fun (x : PetriNet.Marking Ticket.Place) => (x, {Ticket.Place.dollar} + x)] := by
  certify_comp

theorem Ticket.net_preserves_inv.obligation_2 :
    Unification.sound (Narrowing.mayFire Ticket.b_t1 Ticket.worthP)
      [Unification.Unifier.bind fun (x : PetriNet.Marking Ticket.Place) => (x, {Ticket.Place.dollar} + x)] := by
  certify_sound

theorem Ticket.net_preserves_inv.obligation_3 :
    Unification.complete (Narrowing.mayFire Ticket.b_t2 Ticket.worthP)
      [Unification.Unifier.bind fun (x : PetriNet.Marking Ticket.Place) => (x, {Ticket.Place.dollar} + x)] := by
  certify_comp

theorem Ticket.net_preserves_inv.obligation_4 :
    Unification.sound (Narrowing.mayFire Ticket.b_t2 Ticket.worthP)
      [Unification.Unifier.bind fun (x : PetriNet.Marking Ticket.Place) => (x, {Ticket.Place.dollar} + x)] := by
  certify_sound

theorem Ticket.net_preserves_inv.obligation_5 :
    Unification.complete (Narrowing.mayFire Ticket.change Ticket.worthP)
      [Unification.Unifier.bind fun (x : PetriNet.Marking Ticket.Place) => (x, {Ticket.Place.dollar} + x)] := by
  certify_comp

theorem Ticket.net_preserves_inv.obligation_6 :
    Unification.sound (Narrowing.mayFire Ticket.change Ticket.worthP)
      [Unification.Unifier.bind fun (x : PetriNet.Marking Ticket.Place) => (x, {Ticket.Place.dollar} + x)] := by
  certify_sound

theorem Ticket.net_preserves_inv.obligation_7 :
    Unification.complete (Narrowing.mayFire Ticket.b'_t1 Ticket.worthP)
      [Unification.Unifier.bind fun (x : PetriNet.Marking Ticket.Place) =>
          (x, {Ticket.Place.quarter} + {Ticket.Place.quarter} + x)] := by
  certify_comp

theorem Ticket.net_preserves_inv.obligation_8 :
    Unification.sound (Narrowing.mayFire Ticket.b'_t1 Ticket.worthP)
      [Unification.Unifier.bind fun (x : PetriNet.Marking Ticket.Place) =>
          (x, {Ticket.Place.quarter} + {Ticket.Place.quarter} + x)] := by
  certify_sound

theorem Ticket.net_preserves_inv.obligation_9 :
    Unification.complete (Narrowing.mayFire Ticket.b'_t2 Ticket.worthP)
      [Unification.Unifier.bind fun (x : PetriNet.Marking Ticket.Place) =>
          (x, {Ticket.Place.quarter} + {Ticket.Place.quarter} + {Ticket.Place.quarter} + x)] := by
  certify_comp

theorem Ticket.net_preserves_inv.obligation_10 :
    Unification.sound (Narrowing.mayFire Ticket.b'_t2 Ticket.worthP)
      [Unification.Unifier.bind fun (x : PetriNet.Marking Ticket.Place) =>
          (x, {Ticket.Place.quarter} + {Ticket.Place.quarter} + {Ticket.Place.quarter} + x)] := by
  certify_sound
