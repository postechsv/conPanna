import examples.ReadersWriters.ctor
import conPanna.core
import conPanna.BaseTheory.Multiset

/-!
Readers-writers: the transitions of the net, one package of type `System`. Each rule
consumes and produces tokens; `R` is the rest of the marking.
-/

namespace ReadersWriters

open Expresso Place

/-- `idle ⊗ tok ⇒ reading`: start reading, taking one token. -/
def startReadR : Rule Conf := .bind fun (R : Marking) =>
  { lhs := ⟨{idle} + {tok} + R⟩, rhs := ⟨{reading} + R⟩ }

/-- `reading ⇒ idle ⊗ tok`: stop reading, returning the token. -/
def endReadR : Rule Conf := .bind fun (R : Marking) =>
  { lhs := ⟨{reading} + R⟩, rhs := ⟨{idle} + {tok} + R⟩ }

/-- `idle ⊗ tok ⊗ tok ⇒ writing`: start writing, taking both tokens. -/
def startWriteR : Rule Conf := .bind fun (R : Marking) =>
  { lhs := ⟨{idle} + {tok} + {tok} + R⟩, rhs := ⟨{writing} + R⟩ }

/-- `writing ⇒ idle ⊗ tok ⊗ tok`: stop writing, returning both tokens. -/
def endWriteR : Rule Conf := .bind fun (R : Marking) =>
  { lhs := ⟨{writing} + R⟩, rhs := ⟨{idle} + {tok} + {tok} + R⟩ }

def net : System Conf := [startReadR, endReadR, startWriteR, endWriteR]

end ReadersWriters
