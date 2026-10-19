import conPanna.Unification.Unification
import conPanna.Unification.Certification.Tactics
import conPanna.Narrowing.Narrowing
import conPanna.Dumper
import conPanna.Unification.Tactics.maudeUnify
import conPanna.Unification.Tactics.maudeCertifyComp
import conPanna.Later
import conPanna.Subsumption

/-! Everything: unification and its certification calculus, narrowing, the model
dumper, the Maude tactics, deferred obligations (`later`), and subsumption by
matching. -/
