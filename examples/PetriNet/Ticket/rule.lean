import examples.PetriNet.Net
import examples.PetriNet.Ticket.ctor

/-!
The ticket machine: the transitions of Fig. 7, each with the paper's Maude rule
(`@` is the paper's multiset union). In the Petri net notation, `(p)` is a place, `|t|` a
transition, and `k·(p)` an arc of weight `k`.
-/

namespace Ticket

open PetriNet Place

/-- `rl b-t1 : $ => t1 @ q @ q` · `(dollar) ──▶ |b-t1| ──▶ (t1), 2·(quarter)`:
a ticket t1 for a dollar, two quarters back. -/
def b_t1 := transition {dollar} ({t1} + {quarter} + {quarter})

/-- `rl b-t2 : $ => t2 @ q` · `(dollar) ──▶ |b-t2| ──▶ (t2), (quarter)`:
a ticket t2 for a dollar, one quarter back. -/
def b_t2 := transition {dollar} ({t2} + {quarter})

/-- `rl change : $ => q @ q @ q @ q` · `(dollar) ──▶ |change| ──▶ 4·(quarter)`:
four quarters for a dollar. -/
def change := transition {dollar} ({quarter} + {quarter} + {quarter} + {quarter})

/-- `rl b'-t1 : q @ q => t1` · `2·(quarter) ──▶ |b'-t1| ──▶ (t1)`:
a ticket t1 for two quarters. -/
def b'_t1 := transition ({quarter} + {quarter}) {t1}

/-- `rl b'-t2 : q @ q @ q => t2` · `3·(quarter) ──▶ |b'-t2| ──▶ (t2)`:
a ticket t2 for three quarters. -/
def b'_t2 := transition ({quarter} + {quarter} + {quarter}) {t2}

def net : Expresso.System (Marking Place) := [b_t1, b_t2, change, b'_t1, b'_t2]

end Ticket
