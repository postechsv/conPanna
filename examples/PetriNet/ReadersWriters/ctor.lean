/-!
Readers-writers as a Petri net, N processes: the places. The resource place `tok` holds two
tokens; a reader takes one, a writer both.
-/

namespace ReadersWriters

inductive Place where
  | idle
  | reading
  | writing
  | tok
  deriving DecidableEq

end ReadersWriters
