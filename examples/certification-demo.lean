import conPanna.Certification.Replay
import examples.bakery_acu

/-!
Precompile the general backend with `python3 certification_compiler.py --build`.
This Lean session supplies the problem AND its already-known answer. It asks
Maude for certification evidence via Python, then checks the returned proof here.
No native unify call, external Lean verifier, or proof-file prerequisite is used.
The optional --demo harness separately checks the upstream native answer too.

Scope: free/binding, singleton/zero, sharing, finite factors, configuration fields,
and purification. The unbounded schedule is argued in CERTIFICATION.md §7.4;
no formal search theorem or universal success within safety caps is claimed.
The final `certificate` states exactness using ordinary Bakery constructors.
-/
namespace CertificationDemo

open BakeryACU Structural.Indexed BakeryACU.BakeryTheory.Generated
open DirectCertification DirectCertification.Substitution DirectCertification.Substitution.Worklist

derive_direct_profile profile for BakeryTheory.certified

-- Readable names for generated constructor metadata (DATA, not proof lemmas).
-- The serializer uses the corresponding generated codes internally.
private abbrev processUnion := Operator.acu
private abbrev singletonConstructor := Symbol.c6
private abbrev waitingConstructor := Symbol.c3

-- INPUT and native Maude's proposed ANSWER: data, not certification lemmas.
def waitingAtom {Γ} (n : Term Sig Γ Tag.s0) : Term Sig Γ Tag.s2 :=
  .app Symbol.c6 (.cons (.app Symbol.c3 (.cons n .nil)) .nil)

def bindSystem : List (Problem Sig [Tag.s0, Tag.s2, Tag.s2]) :=
  [equation (.var (.there .here)) (.var (.there (.there .here))),
   equation (.var (.there (.there .here))) (waitingAtom (.var .here))]

def bindAnswers : List (Answer Sig [Tag.s0, Tag.s2, Tag.s2]) :=
  [{ parameters := [Tag.s0]
     images := .cons (.var .here)
       (.cons (waitingAtom (.var .here)) (.cons (waitingAtom (.var .here)) .nil)) }]

-- The expected goal is fixed HERE, independently of Maude/Python output.
-- prepareProof rejects holes/sorry; addDecl invokes the kernel on the result.
run_elab do
  let dump ← match ← IO.getEnv "CONPANNA_CERTIFICATE" with
    | some path => IO.FS.readFile path -- negative replay testing only
    | none => LeanReady.produce (LeanReady.requestJson profile profile_sortCode
        bindSystem bindAnswers "bindSystem" "bindAnswers" profile_signature)
  let expected ← `(∀ values, Worklist.Holds registration bindSystem values ↔
    Solutions registration bindAnswers values)
  let (type, proof) ← LeanReady.prepareProof expected dump
  let name := `CertificationDemo.checked_trace
  Lean.addDecl (.thmDecl { name := name, levelParams := [], type := type, value := proof })

-- END RESULT: BOTH completeness (→) and soundness (←), modulo registered ACU.
-- This last step only unfolds the data representation; it does not search/prove
-- completeness. That has already been kernel-checked from the Maude rule trace.
theorem certificate (n : Nat) (P Q : ProcSet) :
    (P =[BakeryTheory.certified] Q ∧
      Q =[BakeryTheory.certified] ProcSet.singleton (Mode.wait n)) ↔
    ∃ N : Nat, n =[BakeryTheory.certified] N ∧
      P =[BakeryTheory.certified] ProcSet.singleton (Mode.wait N) ∧
      Q =[BakeryTheory.certified] ProcSet.singleton (Mode.wait N) := by
  simpa [Worklist.Holds, bindSystem, bindAnswers, Solutions, Answer.Holds,
    Problem.Holds, equation, Terms.eval, Term.eval, Variable.eval, Args, ArgsRel, waitingAtom]
    using checked_trace (n, P, Q, PUnit.unit)

#check certificate
#print axioms certificate

-- Same producer; nested free decomposition exposes n =B m before binding.
def payloadSystem : List (Problem Sig [Tag.s0, Tag.s0]) :=
  [equation (.app Symbol.c3 (.cons (.var .here) .nil))
    (.app Symbol.c3 (.cons (.var (.there .here)) .nil))]

def payloadAnswers : List (Answer Sig [Tag.s0, Tag.s0]) :=
  [{ parameters := [Tag.s0], images := .cons (.var .here) (.cons (.var .here) .nil) }]

run_elab do
  let dump ← LeanReady.produce (LeanReady.requestJson profile profile_sortCode
    payloadSystem payloadAnswers "payloadSystem" "payloadAnswers" profile_signature)
  let expected ← `(∀ values, Worklist.Holds registration payloadSystem values ↔
    Solutions registration payloadAnswers values)
  let (type, proof) ← LeanReady.prepareProof expected dump
  let name := `CertificationDemo.payload_certificate
  Lean.addDecl (.thmDecl { name := name, levelParams := [], type := type, value := proof })

-- Empty proposed family: free constructors wait and crit cannot unify.
def clashSystem : List (Problem Sig [Tag.s0]) :=
  [equation (.app Symbol.c3 (.cons (.var .here) .nil))
    (.app Symbol.c4 (.cons (.var .here) .nil))]
def noAnswers : List (Answer Sig [Tag.s0]) := []

run_elab do
  let dump ← LeanReady.produce (LeanReady.requestJson profile profile_sortCode
    clashSystem noAnswers "clashSystem" "noAnswers" profile_signature)
  let expected ← `(∀ values, Worklist.Holds registration clashSystem values ↔
    Solutions registration noAnswers values)
  let (type, proof) ← LeanReady.prepareProof expected dump
  let name := `CertificationDemo.clash_certificate
  Lean.addDecl (.thmDecl { name := name, levelParams := [], type := type, value := proof })

#print axioms payload_certificate
#print axioms clash_certificate

-- Reject a genuine free cycle. ACU cycles are NOT handled by this rule.
def occursSystem : List (Problem Sig [Tag.s0]) :=
  [equation (.var .here) (.app Symbol.c1 (.cons (.var .here) .nil))]

run_elab do
  let dump ← LeanReady.produce (LeanReady.requestJson profile profile_sortCode
    occursSystem noAnswers "occursSystem" "noAnswers" profile_signature)
  let expected ← `(∀ values, Worklist.Holds registration occursSystem values ↔
    Solutions registration noAnswers values)
  let (type, proof) ← LeanReady.prepareProof expected dump
  let name := `CertificationDemo.occurs_certificate
  Lean.addDecl (.thmDecl { name := name, levelParams := [], type := type, value := proof })

#print axioms occurs_certificate

-- The supplied answer omits a syntactic unit. Proof reconstruction must handle
-- ACU equality in BOTH answer soundness and branch coverage, not demand rfl.
def unitSystem : List (Problem Sig [Tag.s2, Tag.s2]) :=
  [equation (.var .here) (add Operator.acu (.var (.there .here)) (zero Operator.acu))]
def unitAnswers : List (Answer Sig [Tag.s2, Tag.s2]) :=
  [{ parameters := [Tag.s2], images := .cons (.var .here) (.cons (.var .here) .nil) }]

run_elab do
  let dump ← LeanReady.produce (LeanReady.requestJson profile profile_sortCode
    unitSystem unitAnswers "unitSystem" "unitAnswers" profile_signature)
  let expected ← `(∀ values, Worklist.Holds registration unitSystem values ↔
    Solutions registration unitAnswers values)
  let (type, proof) ← LeanReady.prepareProof expected dump
  let name := `CertificationDemo.unit_certificate
  Lean.addDecl (.thmDecl { name := name, levelParams := [], type := type, value := proof })

#print axioms unit_certificate

-- One ACU equation, TWO supplied unifiers. All singleton choices must be
-- present in the completeness tree; the producer cannot just pick one answer.
def atomSystem : List (Problem Sig [Tag.s0, Tag.s2, Tag.s2]) :=
  [equation (add Operator.acu (.var (.there .here)) (.var (.there (.there .here))))
    (waitingAtom (.var .here))]
def atomAnswers : List (Answer Sig [Tag.s0, Tag.s2, Tag.s2]) :=
  [{ parameters := [Tag.s0], images := .cons (.var .here)
      (.cons (waitingAtom (.var .here)) (.cons (zero Operator.acu) .nil)) },
   { parameters := [Tag.s0], images := .cons (.var .here)
      (.cons (zero Operator.acu) (.cons (waitingAtom (.var .here)) .nil)) }]

run_elab do
  let dump ← LeanReady.produce (LeanReady.requestJson profile profile_sortCode
    atomSystem atomAnswers "atomSystem" "atomAnswers" profile_signature)
  let expected ← `(∀ values, Worklist.Holds registration atomSystem values ↔
    Solutions registration atomAnswers values)
  let (type, proof) ← LeanReady.prepareProof expected dump
  let name := `CertificationDemo.atom_certificate
  Lean.addDecl (.thmDecl { name := name, levelParams := [], type := type, value := proof })

-- The AUTOMATED certificate, presented with ordinary user constructors.
-- `simpa` only unfolds the data encoding of the already kernel-checked theorem.
-- It does not do certification search or prove unification completeness.
theorem atom_automated_certificate (n : Nat) (P Q : ProcSet) :
    P.union Q =[BakeryTheory.certified] ProcSet.singleton (Mode.wait n) ↔
      (∃ N : Nat, n =[BakeryTheory.certified] N ∧
        P =[BakeryTheory.certified] ProcSet.singleton (Mode.wait N) ∧
        Q =[BakeryTheory.certified] ProcSet.empty) ∨
      (∃ N : Nat, n =[BakeryTheory.certified] N ∧
        P =[BakeryTheory.certified] ProcSet.empty ∧
        Q =[BakeryTheory.certified] ProcSet.singleton (Mode.wait N)) := by
  simpa [Worklist.Holds, atomSystem, atomAnswers, Solutions, Answer.Holds,
    Problem.Holds, equation, Terms.eval, Term.eval, Variable.eval, Args, ArgsRel,
    waitingAtom, Substitution.add, Substitution.zero]
    using atom_certificate (n, P, Q, PUnit.unit)

#print axioms atom_automated_certificate

/- MANUAL CERTIFICATION — the same problem and the same two supplied answers.

The proof below is an ordinary semantic theorem, not a producer/parser command.
Only general calculus rules are applied. Constructors in its statement are the
user's own constructors; no generated variable indices occur in its proof.

Actual Maude completeness tree for atomSystem/atomAnswers:
  ATOM
    P =B [wait(n)], Q =B empty: COVER(answer 0, N := n) using these equations
    P =B empty, Q =B [wait(n)]: COVER(answer 1, N := n) using these equations

`singletonCases` presents ATOM as two native equality cases. In each branch,
the equalities supplied by ATOM establish the proposed assignment immediately;
the existential witness is the COVER parameter N := n. The producer now closes
these cases directly too, without BIND or scoped substitution snapshots. The
branches below are written empty-first (the generic rule's order), whereas the
dump enumerates singleton-first. No branch is omitted in either presentation.

For soundness, Maude's equality dump uses CONGR, COMM, and UNIT. The same rules
below substitute each supplied answer and reduce [wait(N)]+empty or its reverse.
`rightUnit` abbreviates COMM -> UNIT; `unaryCongruence` abbreviates unary CONGR.
This is rule-level correspondence, NOT a claim of identical serialized trees.
-/
theorem atom_manual_certificate (n : Nat) (P Q : ProcSet) :
    P.union Q =[BakeryTheory.certified] ProcSet.singleton (Mode.wait n) ↔
      (∃ N : Nat, n =[BakeryTheory.certified] N ∧
        P =[BakeryTheory.certified] ProcSet.singleton (Mode.wait N) ∧
        Q =[BakeryTheory.certified] ProcSet.empty) ∨
      (∃ N : Nat, n =[BakeryTheory.certified] N ∧
        P =[BakeryTheory.certified] ProcSet.empty ∧
        Q =[BakeryTheory.certified] ProcSet.singleton (Mode.wait N)) :=
  ⟨-- COMPLETENESS: ATOM, then conditional COVER in both branches.
    fun equation =>
      Or.elim
        ((NativeRules.singletonCases profile registration processUnion singletonConstructor
          rfl (Mode.wait n, PUnit.unit) P Q).mp equation)
        (fun ⟨hP, hQ⟩ => Or.inr ⟨n, .refl _, hP, hQ⟩)
        (fun ⟨hP, hQ⟩ => Or.inl ⟨n, .refl _, hP, hQ⟩),
    -- SOUNDNESS: check both proposed answers, without searching for unifiers.
    fun answer => Or.elim answer
      (fun ⟨N, hN, hP, hQ⟩ =>
        native_trans registration
          (native_add_congr registration processUnion hP hQ)
          (native_trans registration
            (NativeRules.rightUnit registration processUnion (ProcSet.singleton (Mode.wait N)))
            (native_symm registration
              (NativeRules.unaryCongruence registration singletonConstructor
                (NativeRules.unaryCongruence registration waitingConstructor hN)))))
      (fun ⟨N, hN, hP, hQ⟩ =>
        native_trans registration
          (native_add_congr registration processUnion hP hQ)
          (native_trans registration
            (native_unit registration processUnion (ProcSet.singleton (Mode.wait N)))
            (native_symm registration
              (NativeRules.unaryCongruence registration singletonConstructor
                (NativeRules.unaryCongruence registration waitingConstructor hN)))))⟩

#print axioms atom_manual_certificate

-- Targeted nonlinear closure: the supplied diagonal answer makes positive
-- multiplicity cancellation useful. ACTUAL dump: COVER, with MULTIPLICITY in
-- its equation evidence; no BIND or 2-by-2 finite-sharing expansion.
def powerSystem : List (Problem Sig [Tag.s2, Tag.s2]) :=
  [equation (add Operator.acu (.var .here) (.var .here))
    (add Operator.acu (.var (.there .here)) (.var (.there .here)))]
def powerAnswers : List (Answer Sig [Tag.s2, Tag.s2]) :=
  [{ parameters := [Tag.s2], images := .cons (.var .here) (.cons (.var .here) .nil) }]
run_elab do
  let dump ← LeanReady.produce (LeanReady.requestJson profile profile_sortCode
    powerSystem powerAnswers "powerSystem" "powerAnswers" profile_signature)
  let expected ← `(∀ values, Worklist.Holds registration powerSystem values ↔
    Solutions registration powerAnswers values)
  let (type, proof) ← LeanReady.prepareProof expected dump
  Lean.addDecl (.thmDecl { name := `CertificationDemo.power_checked, levelParams := [], type := type, value := proof })
theorem power_certificate (P Q : ProcSet) :
    P.union P =[BakeryTheory.certified] Q.union Q ↔
      ∃ Z : ProcSet, P =[BakeryTheory.certified] Z ∧ Q =[BakeryTheory.certified] Z := by
  simpa [Worklist.Holds, powerSystem, powerAnswers, Solutions, Answer.Holds,
    Problem.Holds, equation, Terms.eval, Term.eval, Variable.eval, Args, ArgsRel,
    Substitution.add] using power_checked (P, Q, PUnit.unit)
#print axioms power_certificate

-- Repeated variables are kept shared: 2P cannot equal one singleton.
def repeatedSystem : List (Problem Sig [Tag.s0, Tag.s2]) :=
  [equation (add Operator.acu (.var (.there .here)) (.var (.there .here)))
    (waitingAtom (.var .here))]
def repeatedAnswers : List (Answer Sig [Tag.s0, Tag.s2]) := []

run_elab do
  let dump ← LeanReady.produce (LeanReady.requestJson profile profile_sortCode
    repeatedSystem repeatedAnswers "repeatedSystem" "repeatedAnswers" profile_signature)
  let expected ← `(∀ values, Worklist.Holds registration repeatedSystem values ↔
    Solutions registration repeatedAnswers values)
  let (type, proof) ← LeanReady.prepareProof expected dump
  let name := `CertificationDemo.repeated_certificate
  Lean.addDecl (.thmDecl { name := name, levelParams := [], type := type, value := proof })

#print axioms atom_certificate
#print axioms repeated_certificate

-- Native-style compact answer, NOT the producer's redundant internal scope.
-- An exhaustive 2-by-3 grid gives P=3Z,Q=2Z; whole-vector factoring relates
-- the generated fresh Z/ticket/unused-old slots to these two native parameters.
def nonlinearSystem : List (Problem Sig [Tag.s0, Tag.s2, Tag.s2]) :=
  [equation (add Operator.acu (.var (.there .here)) (.var (.there .here)))
    (add Operator.acu (.var (.there (.there .here)))
      (add Operator.acu (.var (.there (.there .here))) (.var (.there (.there .here)))))]
def nonlinearAnswers : List (Answer Sig [Tag.s0, Tag.s2, Tag.s2]) :=
  [{ parameters := [Tag.s0, Tag.s2], images := .cons (.var .here)
      (.cons (add Operator.acu (.var (.there .here))
        (add Operator.acu (.var (.there .here)) (.var (.there .here))))
        (.cons (add Operator.acu (.var (.there .here)) (.var (.there .here))) .nil)) }]

-- Keep request DATA as raw constructor trees, exactly as parsed native answers.
-- The equivalent recursive `copies` presentation triggered excessive checking
-- cost in this regression. It is not a supported computational input shortcut.
run_elab do
  let dump ← LeanReady.produce (LeanReady.requestJson profile profile_sortCode
    nonlinearSystem nonlinearAnswers "nonlinearSystem" "nonlinearAnswers" profile_signature)
  let expected ← `(∀ values, Worklist.Holds registration nonlinearSystem values ↔
    Solutions registration nonlinearAnswers values)
  let (type, proof) ← LeanReady.prepareProof expected dump
  let name := `CertificationDemo.nonlinear_certificate
  Lean.addDecl (.thmDecl { name := name, levelParams := [], type := type, value := proof })

#print axioms nonlinear_certificate

-- Factor-search regression: this deliberately nonminimal complete family needs
-- an EMPTY parameter image. Structural tree matching alone cannot find it.
-- This tests certification of a supplied family, not native answer acquisition.
def factorSystem : List (Problem Sig [Tag.s2]) :=
  [equation (.var .here) (.var .here)]
def factorAnswers : List (Answer Sig [Tag.s2]) :=
  [{ parameters := [Tag.s2, Tag.s2], images :=
      .cons (add Operator.acu (.var .here) (.var (.there .here))) .nil }]

run_elab do
  let dump ← LeanReady.produce (LeanReady.requestJson profile profile_sortCode
    factorSystem factorAnswers "factorSystem" "factorAnswers" profile_signature)
  let expected ← `(∀ values, Worklist.Holds registration factorSystem values ↔
    Solutions registration factorAnswers values)
  let (type, proof) ← LeanReady.prepareProof expected dump
  Lean.addDecl (.thmDecl { name := `CertificationDemo.factor_certificate, levelParams := [], type := type, value := proof })

-- The same singleton problem UNDER the user's three-field configuration head.
-- Bag selection derives the third-field equality; no arity-specific rule.
def configurationSystem : List (Problem Sig [Tag.s0, Tag.s2, Tag.s2]) :=
  [equation
    (.app Symbol.c8 (.cons (.var .here) (.cons (.var .here)
      (.cons (add Operator.acu (.var (.there .here)) (.var (.there (.there .here)))) .nil))))
    (.app Symbol.c8 (.cons (.var .here) (.cons (.var .here)
      (.cons (waitingAtom (.var .here)) .nil))))]

run_elab do
  let dump ← LeanReady.produce (LeanReady.requestJson profile profile_sortCode
    configurationSystem atomAnswers "configurationSystem" "atomAnswers" profile_signature)
  let expected ← `(∀ values, Worklist.Holds registration configurationSystem values ↔
    Solutions registration atomAnswers values)
  let (type, proof) ← LeanReady.prepareProof expected dump
  Lean.addDecl (.thmDecl { name := `CertificationDemo.configuration_certificate, levelParams := [], type := type, value := proof })

#print axioms factor_certificate
#print axioms configuration_certificate

-- PURIFY names the common singleton, SHARING cancels that name and relates P/Q,
-- and BIND retains its defining equation. This exercises all three stages.
def purificationSystem : List (Problem Sig [Tag.s0, Tag.s2, Tag.s2]) :=
  [equation (add Operator.acu (.var (.there .here)) (waitingAtom (.var .here)))
    (add Operator.acu (.var (.there (.there .here))) (waitingAtom (.var .here)))]
def purificationAnswers : List (Answer Sig [Tag.s0, Tag.s2, Tag.s2]) :=
  [{ parameters := [Tag.s0, Tag.s2], images := .cons (.var .here)
      (.cons (.var (.there .here)) (.cons (.var (.there .here)) .nil)) }]

run_elab do
  let dump ← LeanReady.produce (LeanReady.requestJson profile profile_sortCode
    purificationSystem purificationAnswers "purificationSystem" "purificationAnswers" profile_signature)
  let expected ← `(∀ values, Worklist.Holds registration purificationSystem values ↔
    Solutions registration purificationAnswers values)
  let (type, proof) ← LeanReady.prepareProof expected dump
  Lean.addDecl (.thmDecl { name := `CertificationDemo.purification_certificate, levelParams := [], type := type, value := proof })

#print axioms purification_certificate

-- Two jointly solved EQUATIONS, not independent per-equation answer choices:
-- P+Q=[wait(n)] together with P=0 has only the second singleton family.
def jointSystem : List (Problem Sig [Tag.s0, Tag.s2, Tag.s2]) :=
  [equation (add Operator.acu (.var (.there .here)) (.var (.there (.there .here))))
      (waitingAtom (.var .here)),
   equation (.var (.there .here)) (zero Operator.acu)]
def jointAnswers : List (Answer Sig [Tag.s0, Tag.s2, Tag.s2]) :=
  [{ parameters := [Tag.s0], images := .cons (.var .here)
      (.cons (zero Operator.acu) (.cons (waitingAtom (.var .here)) .nil)) }]

run_elab do
  let dump ← LeanReady.produce (LeanReady.requestJson profile profile_sortCode
    jointSystem jointAnswers "jointSystem" "jointAnswers" profile_signature)
  let expected ← `(∀ values, Worklist.Holds registration jointSystem values ↔
    Solutions registration jointAnswers values)
  let (type, proof) ← LeanReady.prepareProof expected dump
  Lean.addDecl (.thmDecl { name := `CertificationDemo.joint_certificate, levelParams := [], type := type, value := proof })

#print axioms joint_certificate

-- ACU cycles are NOT free-constructor occurs failures. Here P=P+Q forces Q=0
-- while P remains arbitrary. SHARING handles cancellation and the zero side.
def cycleSystem : List (Problem Sig [Tag.s2, Tag.s2]) :=
  [equation (.var .here) (add Operator.acu (.var .here) (.var (.there .here)))]
def cycleAnswers : List (Answer Sig [Tag.s2, Tag.s2]) :=
  [{ parameters := [Tag.s2], images := .cons (.var .here) (.cons (zero Operator.acu) .nil) }]

run_elab do
  let dump ← LeanReady.produce (LeanReady.requestJson profile profile_sortCode
    cycleSystem cycleAnswers "cycleSystem" "cycleAnswers" profile_signature)
  let expected ← `(∀ values, Worklist.Holds registration cycleSystem values ↔
    Solutions registration cycleAnswers values)
  let (type, proof) ← LeanReady.prepareProof expected dump
  Lean.addDecl (.thmDecl { name := `CertificationDemo.cycle_certificate, levelParams := [], type := type, value := proof })

-- The analogous cycle with a singleton is impossible. Retain its defining
-- constraint and prove NONEMPTY; do not discard a branch by an occurs heuristic.
def impossibleCycleSystem : List (Problem Sig [Tag.s0, Tag.s2]) :=
  [equation (.var (.there .here))
    (add Operator.acu (.var (.there .here)) (waitingAtom (.var .here)))]

run_elab do
  let dump ← LeanReady.produce (LeanReady.requestJson profile profile_sortCode
    impossibleCycleSystem repeatedAnswers "impossibleCycleSystem" "repeatedAnswers" profile_signature)
  let expected ← `(∀ values, Worklist.Holds registration impossibleCycleSystem values ↔
    Solutions registration repeatedAnswers values)
  let (type, proof) ← LeanReady.prepareProof expected dump
  Lean.addDecl (.thmDecl { name := `CertificationDemo.impossible_cycle_certificate, levelParams := [], type := type, value := proof })

-- Finite-factor audit, deliberately nonminimal supplied family:
-- P=Q is covered by P=Q=2U+V using U=0,V=P. U is repeated, not two fresh
-- independent parameters, and the SAME assignment must cover both input fields.
def repeatedFactorSystem : List (Problem Sig [Tag.s2, Tag.s2]) :=
  [equation (.var .here) (.var (.there .here))]
def repeatedFactorAnswers : List (Answer Sig [Tag.s2, Tag.s2]) :=
  [{ parameters := [Tag.s2, Tag.s2], images :=
      .cons (add Operator.acu (add Operator.acu (.var .here) (.var .here)) (.var (.there .here)))
        (.cons (add Operator.acu (add Operator.acu (.var .here) (.var .here)) (.var (.there .here))) .nil) }]

run_elab do
  let dump ← LeanReady.produce (LeanReady.requestJson profile profile_sortCode
    repeatedFactorSystem repeatedFactorAnswers "repeatedFactorSystem" "repeatedFactorAnswers" profile_signature)
  let expected ← `(∀ values, Worklist.Holds registration repeatedFactorSystem values ↔
    Solutions registration repeatedFactorAnswers values)
  let (type, proof) ← LeanReady.prepareProof expected dump
  Lean.addDecl (.thmDecl { name := `CertificationDemo.repeated_factor_certificate, levelParams := [], type := type, value := proof })

-- An unconstrained pair cannot be covered by (Z,Z). The next supplied answer
-- (U+V,U+W) covers it with ONE shared U=0, V=P, W=Q. Matching each vector
-- component independently would incorrectly accept the first candidate.
def independentSystem : List (Problem Sig [Tag.s2, Tag.s2]) := []
def correlatedFactorAnswers : List (Answer Sig [Tag.s2, Tag.s2]) :=
  [{ parameters := [Tag.s2], images := .cons (.var .here) (.cons (.var .here) .nil) },
   { parameters := [Tag.s2, Tag.s2, Tag.s2], images :=
      .cons (add Operator.acu (.var .here) (.var (.there .here)))
        (.cons (add Operator.acu (.var .here) (.var (.there (.there .here)))) .nil) }]

run_elab do
  let dump ← LeanReady.produce (LeanReady.requestJson profile profile_sortCode
    independentSystem correlatedFactorAnswers "independentSystem" "correlatedFactorAnswers" profile_signature)
  let expected ← `(∀ values, Worklist.Holds registration independentSystem values ↔
    Solutions registration correlatedFactorAnswers values)
  let (type, proof) ← LeanReady.prepareProof expected dump
  Lean.addDecl (.thmDecl { name := `CertificationDemo.correlated_factor_certificate, levelParams := [], type := type, value := proof })

#print axioms cycle_certificate
#print axioms impossible_cycle_certificate
#print axioms repeated_factor_certificate
#print axioms correlated_factor_certificate

-- Two genuinely correlated equations and TWO supplied answer families:
-- P+Q=[wait(n)], Q+R=[wait(m)]. Either Q=0, or Q is the common singleton and
-- n=m. In the latter branch payload decomposition shares the SAME ticket.
def overlapSystem : List (Problem Sig [Tag.s0, Tag.s0, Tag.s2, Tag.s2, Tag.s2]) :=
  [equation (add Operator.acu (.var (.there (.there .here)))
      (.var (.there (.there (.there .here))))) (waitingAtom (.var .here)),
   equation (add Operator.acu (.var (.there (.there (.there .here))))
      (.var (.there (.there (.there (.there .here)))))) (waitingAtom (.var (.there .here)))]
def overlapAnswers : List (Answer Sig [Tag.s0, Tag.s0, Tag.s2, Tag.s2, Tag.s2]) :=
  [{ parameters := [Tag.s0, Tag.s0], images := .cons (.var .here)
      (.cons (.var (.there .here)) (.cons (waitingAtom (.var .here))
        (.cons (zero Operator.acu) (.cons (waitingAtom (.var (.there .here))) .nil)))) },
   { parameters := [Tag.s0], images := .cons (.var .here)
      (.cons (.var .here) (.cons (zero Operator.acu)
        (.cons (waitingAtom (.var .here)) (.cons (zero Operator.acu) .nil)))) }]

run_elab do
  let dump ← LeanReady.produce (LeanReady.requestJson profile profile_sortCode
    overlapSystem overlapAnswers "overlapSystem" "overlapAnswers" profile_signature)
  let expected ← `(∀ values, Worklist.Holds registration overlapSystem values ↔
    Solutions registration overlapAnswers values)
  let (type, proof) ← LeanReady.prepareProof expected dump
  Lean.addDecl (.thmDecl { name := `CertificationDemo.overlap_checked, levelParams := [], type := type, value := proof })

theorem overlap_certificate (n m : Nat) (P Q R : ProcSet) :
    (ProcSet.union P Q =[BakeryTheory.certified] ProcSet.singleton (Mode.wait n) ∧
      ProcSet.union Q R =[BakeryTheory.certified] ProcSet.singleton (Mode.wait m)) ↔
    (∃ N M : Nat, n =[BakeryTheory.certified] N ∧ m =[BakeryTheory.certified] M ∧
      P =[BakeryTheory.certified] ProcSet.singleton (Mode.wait N) ∧
      Q =[BakeryTheory.certified] ProcSet.empty ∧
      R =[BakeryTheory.certified] ProcSet.singleton (Mode.wait M)) ∨
    (∃ N : Nat, n =[BakeryTheory.certified] N ∧ m =[BakeryTheory.certified] N ∧
      P =[BakeryTheory.certified] ProcSet.empty ∧
      Q =[BakeryTheory.certified] ProcSet.singleton (Mode.wait N) ∧
      R =[BakeryTheory.certified] ProcSet.empty) := by
  simpa [Worklist.Holds, overlapSystem, overlapAnswers, Solutions, Answer.Holds,
    Problem.Holds, equation, Terms.eval, Term.eval, Variable.eval, Args, ArgsRel,
    waitingAtom, DirectCertification.Substitution.add, DirectCertification.Substitution.zero]
    using overlap_checked (n, m, P, Q, R, PUnit.unit)

#check overlap_certificate
#print axioms overlap_certificate

-- Optional negative replay tests; disabled in the editor's ordinary elaboration.
-- Corrupt fresh evidence, not an old hand-written fixture. The final semantic
-- goal is unchanged. A well-sorted but wrong successor must fail its transition
-- equality; scope corruption, a hole, or a duplicated node must also fail.
run_elab do
  if (← IO.getEnv "CONPANNA_CERT_NEGATIVES") == some "1" then
    let dump ← LeanReady.produce (LeanReady.requestJson profile profile_sortCode
      atomSystem atomAnswers "atomSystem" "atomAnswers" profile_signature)
    let bundle ← IO.ofExcept (Lean.Json.parse dump)
    let steps ← IO.ofExcept (bundle.getObjValAs? (Array Lean.Json) "steps")
    let some transition := steps.findIdx? (fun step =>
        (step.getObjValAs? String "rule").toOption == some "atom_successor")
      | throwError "negative fixture has no atom transition"
    let some variableNode := steps.findIdx? (fun step =>
        (step.getObjValAs? String "type").toOption == some "Term Sig [Tag.s0, Tag.s2, Tag.s2] Tag.s2")
      | throwError "negative fixture has no scoped variable"
    let transitionType ← IO.ofExcept (steps[transition]!.getObjValAs? String "type")
    let sides := transitionType.splitOn " = "
    unless sides.length ≥ 2 do throwError "unexpected transition fixture"
    -- The computed source can contain `if i = j`; the LAST equality separates
    -- it from the named successor snapshot. Do not split binder conditions.
    let leftSide := String.intercalate " = " (sides.take (sides.length - 1))
    let wrongSuccessor := leftSide ++ " = (ReplayState.prepend " ++ sides[sides.length - 1]! ++
      " [equation (zero Operator.acu) (zero Operator.acu)])"
    let replace := fun i key value => bundle.setObjVal! "steps" (.arr
      (steps.set! i (steps[i]!.setObjVal! key (.str value))))
    let some coverNode := steps.findIdx? (fun step =>
        (step.getObjValAs? String "rule").toOption == some "cover")
      | throwError "negative fixture has no conditional cover"
    let coverValue ← IO.ofExcept (steps[coverNode]!.getObjValAs? String "value")
    let wrongHypothesis := coverValue.replace ".hyp ⟨0," ".hyp ⟨1,"
    unless wrongHypothesis != coverValue do throwError "cover fixture has no branch hypothesis"
    let fixtures := #[
      ("wrong successor", replace transition "type" wrongSuccessor),
      ("wrong scope", replace variableNode "value" "(Term.var (sig := Sig) (.there (.there (.there .here))))"),
      ("wrong conditional hypothesis", replace coverNode "value" wrongHypothesis),
      ("proof hole", replace transition "value" "by sorry"),
      ("duplicate node", bundle.setObjVal! "steps" (.arr (steps.push steps[0]!))),
      ("unsupported node kind", replace variableNode "kind" "axiom"),
      ("wrong final proof", bundle.setObjVal! "proof" (.str "fun _ => Iff.rfl"))]
    let expected ← `(∀ values, Worklist.Holds registration atomSystem values ↔
      Solutions registration atomAnswers values)
    -- Validate the fixture BEFORE corrupting it, so rejection is meaningful.
    let (type, proof) ← LeanReady.prepareProof expected dump
    Lean.addDecl (.thmDecl { name := `CertificationDemo.negative_control, levelParams := [], type := type, value := proof })
    for (label, bad) in fixtures do
      let saved ← Lean.Elab.Term.saveState
      let rejected ← try
        discard (LeanReady.prepareProof expected bad.compress)
        pure false
      catch e =>
        if label == "wrong successor" then
          let message ← e.toMessageData.toString
          unless (message.splitOn "atom_successor").length > 1 do
            throwError "wrong successor failed outside its transition: {e.toMessageData}"
        pure true
      saved.restore true
      unless rejected do throwError "accepted corrupt certificate: {label}"
      IO.println s!"Rejected {label}"

end CertificationDemo
