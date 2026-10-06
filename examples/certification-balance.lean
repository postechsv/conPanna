import conPanna.Certification.Replay
import examples.bakery_acu

/-!
One certified ACU unification problem, using the registered Bakery model.

Problem: 2P =B [wait(n)] + Q.
Supplied answer: n=N, P=[wait(N)]+R, Q=[wait(N)]+2R.

The answer is already known; this does NOT ask native Maude to unify again.
Maude produces PURIFY -> SHARING -> ATOM/BIND/NONEMPTY/COVER evidence.
Python writes applications of those same general rules. Lean checks every node
and then soundness AND completeness. No problem-specific certification lemma,
new tactic, admission, or second implementation of the calculus is used.

The final ordinary theorem presents exactness in Bakery's native constructors.
Its `simpa` only unfolds the internal representation AFTER certification.
Run this file separately from the smaller regression suite to respect the caps:
  CONPANNA_CERT_STRESS=1 python3 -B certification_compiler.py --demo
-/
namespace CertificationBalance

open BakeryACU Structural.Indexed BakeryACU.BakeryTheory.Generated
open DirectCertification DirectCertification.Substitution DirectCertification.Substitution.Worklist

derive_direct_profile profile for BakeryTheory.certified

def waitingAtom {Γ} (n : Term Sig Γ Tag.s0) : Term Sig Γ Tag.s2 :=
  .app Symbol.c6 (.cons (.app Symbol.c3 (.cons n .nil)) .nil)

-- DATA: the original input scope is (n, P, Q); the parameter scope is (N, R).
def problem : List (Problem Sig [Tag.s0, Tag.s2, Tag.s2]) :=
  [equation (add Operator.acu (.var (.there .here)) (.var (.there .here)))
    (add Operator.acu (waitingAtom (.var .here)) (.var (.there (.there .here))))]

def proposed : List (Answer Sig [Tag.s0, Tag.s2, Tag.s2]) :=
  [{ parameters := [Tag.s0, Tag.s2], images := .cons (.var .here)
      (.cons (add Operator.acu (waitingAtom (.var .here)) (.var (.there .here)))
        (.cons (add Operator.acu (waitingAtom (.var .here))
          (add Operator.acu (.var (.there .here)) (.var (.there .here)))) .nil)) }]

-- CERTIFICATION: the goal is fixed by Lean, independently of the external dump.
-- Closed replay nodes are individually kernel-checked, not accepted as axioms.
--
-- What the ACTUAL rule tree checks (write a=[wait(n)]):
--
--   PURIFY: introduce A=a, retaining 2P=A+Q and every original input.
--   SHARING: the exhaustive 2-by-2 occurrence-grid table gives
--     A = 2Z₀ + Z₁ + Z₂ + 2Z₄
--     P =  Z₀ + Z₁ + Z₂ + Z₃ + 2Z₄
--     Q =       Z₁ + Z₂ + 2Z₃ + 2Z₄.
--     The two degree-identical supports Z₁/Z₂ are deliberately BOTH retained.
--   ATOM: A=a forces Z₀=Z₄=empty, and either (Z₁=a,Z₂=empty)
--     or (Z₁=empty,Z₂=a). The repeated-occurrence branches are also replayed;
--     BIND and NONEMPTY close their contradictions, rather than dropping them.
--   COVER: each surviving whole vector factors through the proposed answer,
--     with R=Z₃. This includes the n component, not just the two bags.
--
-- Independently, candidate SOUNDNESS substitutes P=a+R,Q=a+2R and uses the
-- general ACU equality rules to check 2(a+R) =B a+(a+2R).
-- No feasibility oracle, reference unifier family, or assumed completeness.
run_elab do
  let dump ← LeanReady.produce (LeanReady.requestJson profile profile_sortCode
    problem proposed "problem" "proposed" profile_signature)
  let expected ← `(∀ values, Worklist.Holds registration problem values ↔
    Solutions registration proposed values)
  let (type, proof) ← LeanReady.prepareProof expected dump
  Lean.addDecl (.thmDecl { name := `CertificationBalance.checked, levelParams := [], type := type, value := proof })

-- RESULT: → is completeness, ← is soundness. Both come from the replay above.
theorem certificate (n : Nat) (P Q : ProcSet) :
    (ProcSet.union P P =[BakeryTheory.certified]
      ProcSet.union (ProcSet.singleton (Mode.wait n)) Q) ↔
    ∃ (N : Nat) (R : ProcSet), n =[BakeryTheory.certified] N ∧
      P =[BakeryTheory.certified] ProcSet.union (ProcSet.singleton (Mode.wait N)) R ∧
      Q =[BakeryTheory.certified] ProcSet.union (ProcSet.singleton (Mode.wait N))
        (ProcSet.union R R) := by
  simpa [Worklist.Holds, problem, proposed, Solutions, Answer.Holds,
    Problem.Holds, equation, Terms.eval, Term.eval, Variable.eval, Args, ArgsRel,
    waitingAtom, DirectCertification.Substitution.add]
    using checked (n, P, Q, PUnit.unit)

#check certificate
#print axioms certificate
-- Inspect the actual root rule application; its named child is the separately
-- checked SHARING node, whose children follow the ATOM/BIND/etc. rule tree.
#print checked

end CertificationBalance
