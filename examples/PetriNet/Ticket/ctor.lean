/-!
The subway ticket machine of Meseguer, "Conditional rewriting logic as a unified model of
concurrency" (TCS 96, 1992), §5.3.1, Fig. 7: the places. A dollar (`$` in the paper) or
quarters (`q`) buy a ticket `t1` (50¢) or a longer-distance ticket `t2` (75¢).
-/

namespace Ticket

inductive Place where
  | dollar      -- `$`
  | quarter     -- `q`
  | t1
  | t2
  deriving DecidableEq

end Ticket
