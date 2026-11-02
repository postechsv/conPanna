import conPanna.Unification.Unification
import conPanna.Narrowing.Narrowing
import conPanna.Dumper
import conPanna.Unification.Tactics.maudeUnify
import conPanna.Unification.Tactics.udfCertify
import conPanna.Unification.Tactics.maudeMatch
import conPanna.Later
import conPanna.Subsumption
import conPanna.narrow

/-! Everything: unification and its certification calculus, narrowing and the `narrow`
tactic, the model dumper, the Maude tactics (unify with certificates, match), certificate
replay (`udf_certify`), deferred obligations (`later`, `laterAx`), and subsumption by
matching. -/
