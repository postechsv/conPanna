import examples.PetriNet.Net
import examples.PetriNet.ReadersWriters.ctor

/-!
Readers-writers: the net, as data. In the comments, `(p)` is a place, `|t|` a transition,
and the arcs show the tokens a transition consumes (left) and produces (right); `2·(tok)`
is an arc of weight 2.
-/

namespace ReadersWriters

open PetriNet Place

/-- `(idle), (tok) ──▶ |startRead| ──▶ (reading)`: start reading, taking one token. -/
def startRead := transition ({idle} + {tok}) {reading}

/-- `(reading) ──▶ |endRead| ──▶ (idle), (tok)`: stop reading, returning the token. -/
def endRead := transition {reading} ({idle} + {tok})

/-- `(idle), 2·(tok) ──▶ |startWrite| ──▶ (writing)`: start writing, taking both tokens. -/
def startWrite := transition ({idle} + {tok} + {tok}) {writing}

/-- `(writing) ──▶ |endWrite| ──▶ (idle), 2·(tok)`: stop writing, returning both tokens. -/
def endWrite := transition {writing} ({idle} + {tok} + {tok})

def net : Expresso.System (Marking Place) := [startRead, endRead, startWrite, endWrite]

end ReadersWriters
