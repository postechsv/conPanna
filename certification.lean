import conPanna.Certification.Replay
import examples.bakery_acu

/-!
# ACU certification: semantic rules and checked coverage

Specification and provenance: CERTIFICATION.md, especially §§4–9 and §14.
General proofs are precompiled in conPanna/Certification/{Core,Sharing,
Enumeration,Replay}.lean. This file retains their explicit demonstration proofs.
Together they form ONE prototype, with four parts:
1. GENERAL SEMANTIC RULES over the existing registered structural equality.
2. EXHAUSTIVE FINITE SHARING: semantic exactness and typed substitution generation.
3. TYPED CERTIFICATE DATA and acceptance (soundness plus complete coverage).
4. BAKERY CERTIFICATES: explicit proof terms and computed occurs/clash closure,
   without custom proof tactics.

Kept from the previous prototype: quotient-based internal proofs, arbitrary-arity
free-head rules, native lifting, typed image vectors, and checked worklist trees.
Removed: shape-specific family recognizers, one-tail guard wrappers, duplicated
replay engines, bounded Maude search, and elaboration-time external calls.
The separate Maude experiments are NOT evidence for a general search guarantee.

The equality is Structural.Indexed.NativeEq, written `=[BakeryTheory.certified]`.
Quotients and multiplicity vectors are INTERNAL proof tools, not user encodings.
Only the last section uses Bakery; the rules work over a generic signature.
The profile command generates/checks syntactic metadata, not semantic user proofs.
Scoped binding preparation and free-step classification compute checked data;
proper free-occurrence/clash closure is automatic. The external worklist driver,
bag-phase schedule, and complete factor matcher now live in certification.maude;
their informal search argument is in CERTIFICATION.md §§7.4–8.1. A formal Lean
search-success theorem remains unfinished; individual certificates are checked.

Proved acceptance is not proved search success:
* equality traces establish SOUNDNESS of each proposed substitution;
* a coverage tree establishes COMPLETENESS for every native valuation;
* checked early coverage can close a whole branch before sharing expansion;
* exhaustive finite-sharing search success is the INFORMAL argument in the
  document. No Lean search-success theorem or complete ACU solver is claimed.

Initial frontend contract: one homogeneous three-constructor ACU bag fragment;
payloads cannot reach that bag sort; remaining constructors are free. Arbitrary
repeated variables are permitted. General semantic rules may hold more widely.
Multiple interacting structural components require a future combination argument.

Rule provenance:
* DELETE/ORIENT/DECOMPOSE/CLASH/BIND: standard first-order unification.
* Finite occurrence sharing: Boudet–Contejean (1994), adapted to ACU emptiness.
* Cancellation, atom splitting, and positive-multiplicity cancellation:
  consequences of constructor-generated free bags, NOT arbitrary ACU monoids.
* Whole-vector factorization: standard complete-unifier-set instantiation.
* External search / checked acceptance: skeptical certification (e.g. SMTCoq).
No complement/disunification calculus or order-sorted membership rules are used.
Full references, differences, and limits on novelty are in CERTIFICATION.md §14.
-/

-- BEGIN LEAN-READY BOUNDARY EXPERIMENT
/-!
Small producer-to-kernel test (2026-10-06), independent of the large typed replay.
GENERAL rules below use the existing indexed registration, not another equality.
Maude's RIGHT-UNIT / BIND / EMIT steps generate the certificate body verbatim.

Problem: P union empty =B Q. Answer: P := Z, Q := Z.
LEFT-EQ transports the original problem; BIND proves the answer family exact.
The emitter is a deliberately small boundary test, NOT a general ACU certifier.
No external process runs when this Lean file elaborates.

Measured isolated test: parse <1 ms, elaborate 7 ms, kernel <1 ms; wrong answer
rejected; no axioms. Whole process 1.88 s / 1,278,580 KiB including model imports.
This does NOT establish the cause of the earlier full-file memory failure.
Reproduce producer: see LEAN-READY-BOUNDARY-EMITTER in certification.maude.
-/
namespace DirectCertification.LeanReadyBoundary

open Structural.Indexed

variable {Sorts : Type} {sig : Signature Sorts}

/- GENERAL RULES: no Bakery names, syntax interpreter, or unification search.
   LEFT-EQ transports an equation along an explicit structural equality.
   BIND identifies two variables with one shared fresh parameter. Its iff
   proves completeness AND soundness for the displayed substitution. -/
theorem leftEq (reg : Registration sig) {s} {a b c : reg.Carrier s}
    (step : NativeEq sig reg a b) :
    NativeEq sig reg a c ↔ NativeEq sig reg b c :=
  ⟨fun h => .trans (.symm step) h, fun h => .trans step h⟩

theorem bind (reg : Registration sig) {s} (a b : reg.Carrier s) :
    NativeEq sig reg a b ↔
      ∃ z : reg.Carrier s, NativeEq sig reg a z ∧ NativeEq sig reg b z :=
  ⟨fun h => ⟨b, h, .refl _⟩,
    fun h => Exists.elim h (fun _ h => .trans h.1 (.symm h.2))⟩

theorem rightUnit (reg : Registration sig) {s} (op : sig.ACUOp s)
    (a : reg.Carrier s) :
    NativeEq sig reg
      (reg.apply (sig.add op) (a, reg.apply (sig.zero op) PUnit.unit, PUnit.unit)) a := by
  simp only [NativeEq, reg.quote_apply, Args.quote]
  exact .trans (.comm op _ _) (.unit op _)

end DirectCertification.LeanReadyBoundary


namespace DirectCertification.LeanReadyBoundary.Bakery

open BakeryACU Structural.Indexed BakeryACU.BakeryTheory.Generated
open DirectCertification.LeanReadyBoundary

/-- Independently specified problem and whole answer family. -/
def expected : Prop := ∀ P Q : ProcSet,
  NativeEq Sig registration (s := Tag.s2) (ProcSet.union P ProcSet.empty) Q ↔
    ∃ Z : ProcSet, NativeEq Sig registration (s := Tag.s2) P Z ∧
      NativeEq Sig registration (s := Tag.s2) Q Z

/-- Body copied VERBATIM from actual Maude output; no reconstruction tactic.
Each named rule is general; no problem-specific supporting lemma is used. -/
theorem maude_unit_bind_certificate : expected :=
  fun P Q : ProcSet => (Iff.trans (leftEq registration (s := Tag.s2) (rightUnit registration Operator.acu P)) (bind registration (s := Tag.s2) P Q))

#print axioms maude_unit_bind_certificate

end DirectCertification.LeanReadyBoundary.Bakery
-- END LEAN-READY BOUNDARY EXPERIMENT

/-! ## Certificates over Bakery's ordinary registered datatypes

Only this section depends on Bakery. Definitions below are INPUT/ANSWER DATA,
not problem-specific proof lemmas. Each certification proof is one explicit
application of the general checker to a finite proof tree plus soundness traces.
No Maude process, proof-search tactic, or hidden registration obligation runs.

The data terms use generated constructor identifiers solely as a future dump
would. The readable native theorems immediately below use the user constructors.
Handwritten proposals are deliberate here: dump/parser/search engineering is
deferred until the general semantic rules and finite-sharing theorem stabilize.
-/

namespace DirectCertification.Bakery

open BakeryACU Structural.Indexed BakeryACU.BakeryTheory.Generated
open Substitution Substitution.Worklist

derive_direct_profile profile for BakeryTheory.certified

/- Nonlinear Bakery certificate, by ONE application of the general rule.
The occurrence grid is (P,P) against (Q,Q,Q), so the computed family has exactly
one support with degrees (3,2): P =B Z+Z+Z and Q =B Z+Z, including Z = empty.
nativeBagSum writes the coefficient equation 2P =B 3Q using ONLY the ordinary
registered ProcSet.empty/union constructors; trailing units are harmless modulo B.
The let-bound data below belong to a future FiniteSharing dump, not extra lemmas
for this problem. Count/disjointness proofs are finite syntactic case checks.
No completeness premise, payload restriction, or proof-search tactic is used.
-/
theorem nonlinear_sharing_certificate (values : Fin 2 → ProcSet) :
    let left : FiniteSharing.Vector 2 := Fin.cases 2 (fun _ => 0)
    let right : FiniteSharing.Vector 2 := Fin.cases 0 (fun _ => 3)
    let rows : Fin 2 → Fin 2 := fun _ => 0
    let cols : Fin 3 → Fin 2 := fun _ => 1
    let generators := FiniteSharing.supportGenerators rows cols
    NativeEq Sig registration (nativeBagSum registration Operator.acu left values)
      (nativeBagSum registration Operator.acu right values) ↔
      ∃ parameters : Fin generators.length → ProcSet,
        ∃ passthrough : Fin 2 → ProcSet,
          ∀ i, NativeEq Sig registration (s := Tag.s2) (values i)
            (nativeSharingImages registration Operator.acu left right generators parameters passthrough i) :=
  finiteSharing_native (sig := Sig) profile registration (s := Tag.s2)
    (n := 2) (rows := 2) (cols := 3) Operator.acu
    (Fin.cases 2 (fun _ => 0) : FiniteSharing.Vector 2)
    (Fin.cases 0 (fun _ => 3) : FiniteSharing.Vector 2)
    (fun _ : Fin 2 => (0 : Fin 2)) (fun _ : Fin 3 => (1 : Fin 2))
    (Fin.cases rfl (fun i => Fin.cases rfl (fun j => Fin.elim0 j) i))
    (Fin.cases rfl (fun i => Fin.cases rfl (fun j => Fin.elim0 j) i))
    (Fin.cases (Or.inr rfl) (fun i => Fin.cases (Or.inl rfl) (fun j => Fin.elim0 j) i)) values

/-- Data for singleton(wait(ticket)); no semantic assumption about the payload. -/
def waitingAtom {Γ} (ticket : Term Sig Γ Tag.s0) : Term Sig Γ Tag.s2 :=
  .app Symbol.c6 (.cons (.app Symbol.c3 (.cons ticket .nil)) .nil)

/- One equation, TWO necessary unifiers:

     P + Q =B singleton(wait(n))

     σ₀(n,P,Q) = (N, empty, singleton(wait(N)))
     σ₁(n,P,Q) = (N, singleton(wait(N)), empty)

N is fresh; the same N fills every occurrence of the ticket in its family.
Both branches are included. The infinitely many possible tickets are not
enumerated: the constructor has mass one for EVERY assignment to its payload.
-/
def atomicProblem : Problem Sig [Tag.s0, Tag.s2, Tag.s2] :=
  equation (add Operator.acu (.var (.there .here)) (.var (.there (.there .here))))
    (waitingAtom (.var .here))

def atomicAnswers : List (Answer Sig [Tag.s0, Tag.s2, Tag.s2]) :=
  [{ parameters := [Tag.s0]
     images := .cons (.var .here)
       (.cons (zero Operator.acu) (.cons (waitingAtom (.var .here)) .nil)) },
   { parameters := [Tag.s0]
     images := .cons (.var .here)
       (.cons (waitingAtom (.var .here)) (.cons (zero Operator.acu) .nil)) }]

/- Finite certificate tree, directly translatable to a future rule dump:

     ATOM-CHOOSE / SplitAtom(P,Q,singleton(wait(n)))
       branch P=empty, Q=singleton(wait(n)):
         COVER(answer=0, β(N)=n, input-vector=(n,P,Q))
       branch P=singleton(wait(n)), Q=empty:
         COVER(answer=1, β(N)=n, input-vector=(n,P,Q))

Each COVER proves the WHOLE vector from that branch's hypotheses. Separately,
UNIT proves σ₀ sound; COMM then UNIT proves σ₁ sound. The checker combines them
into the semantic iff, not merely a proof that both proposed answers unify.
-/
theorem atomic_exact_data :
    ∀ values, atomicProblem.Holds registration values ↔
      Solutions registration atomicAnswers values :=
  Worklist.exact registration (profile := profile) atomicProblem atomicAnswers
    (.split Operator.acu (.var (.there .here)) (.var (.there (.there .here)))
      Symbol.c6 rfl (.cons (.app Symbol.c3 (.cons (.var .here) .nil)) .nil)
      (.hyp ⟨0, of_decide_eq_true rfl⟩)
      (.cover ⟨0, of_decide_eq_true rfl⟩ (.cons (.var .here) .nil)
        (.cons (.axiom (.refl (.var .here)))
          (.cons (.hyp ⟨0, of_decide_eq_true rfl⟩)
            (.cons (.hyp ⟨1, of_decide_eq_true rfl⟩) .nil))))
      (.cover ⟨1, of_decide_eq_true rfl⟩ (.cons (.var .here) .nil)
        (.cons (.axiom (.refl (.var .here)))
          (.cons (.hyp ⟨0, of_decide_eq_true rfl⟩)
            (.cons (.hyp ⟨1, of_decide_eq_true rfl⟩) .nil)))))
    (.cons (.unit Operator.acu (waitingAtom (.var .here)))
      (.cons (.trans (.comm Operator.acu (waitingAtom (.var .here)) (zero Operator.acu))
        (.unit Operator.acu (waitingAtom (.var .here)))) .nil))

/-- Readable native statement of the same general two-way splitting rule. -/
theorem atomic_certificate (n : Nat) (P Q : ProcSet) :
    ProcSet.union P Q =[BakeryTheory.certified] ProcSet.singleton (.wait n) ↔
      (P =[BakeryTheory.certified] ProcSet.empty ∧
        Q =[BakeryTheory.certified] ProcSet.singleton (.wait n)) ∨
      (P =[BakeryTheory.certified] ProcSet.singleton (.wait n) ∧
        Q =[BakeryTheory.certified] ProcSet.empty) :=
  split_native profile registration Operator.acu P Q (ProcSet.singleton (.wait n)) rfl

/- Answer-guided nonlinear certificate (CERTIFICATION.md §9.1).

     E = { kP =B kQ }, k>0; native proposal σ(P,Q)=(R,R).
     Pick β(R)=P. From E, MULTIPLICITY-CANCEL derives P=B Q.
     REFLEXIVITY proves P=B σ(P)β; SYMMETRY proves Q=B σ(Q)β.
     EARLY-COVER closes the entire branch, with NO sharing-grid expansion.

Soundness is a separate reflexive equality trace after applying σ. This works
for EVERY positive k, not just one tested coefficient or a linear fragment.
This theorem is handwritten targeted evidence. The same MULTIPLICITY/COVER
steps are now produced automatically in examples/certification-demo.lean.
-/
def repeatedProblem (k : Nat) : Problem Sig [Tag.s2, Tag.s2] :=
  equation (copies Operator.acu k (.var .here))
    (copies Operator.acu k (.var (.there .here)))

def diagonalAnswers : List (Answer Sig [Tag.s2, Tag.s2]) :=
  [{ parameters := [Tag.s2]
     images := .cons (.var .here) (.cons (.var .here) .nil) }]

theorem repeated_exact_data (k : Nat) (positive : 0 < k) :
    ∀ values, (repeatedProblem k).Holds registration values ↔
      Solutions registration diagonalAnswers values :=
  Worklist.exact registration (profile := profile) (repeatedProblem k) diagonalAnswers
    (.cover ⟨0, of_decide_eq_true rfl⟩ (.cons (.var .here) .nil)
      (.cons (.axiom (.refl (.var .here)))
        (.cons (.symm (.multiplicity Operator.acu k positive (.var .here)
          (.var (.there .here)) (.hyp ⟨0, of_decide_eq_true rfl⟩))) .nil)))
    (.cons (.copies_substitution (sig := Sig) (Γ := [Tag.s2, Tag.s2]) (Δ := [Tag.s2])
      Operator.acu k (.var .here) (.var (.there .here))
      (diagonalAnswers.get ⟨0, of_decide_eq_true rfl⟩).images (.refl (.var .here))) .nil)

/-- Native presentation: k-fold union has exactly the diagonal family.
The positive-k guard is mathematical, not a hidden constraint on bag variables. -/
theorem repeated_certificate (k : Nat) (positive : 0 < k) (P Q : ProcSet) :
    NativeEq Sig registration (s := Tag.s2)
      (nativeRepeat registration Operator.acu k P)
      (nativeRepeat registration Operator.acu k Q) ↔
      ∃ R : ProcSet, P =[BakeryTheory.certified] R ∧ Q =[BakeryTheory.certified] R :=
  (multiplicity_native profile registration Operator.acu k positive P Q).trans
    (share_native registration (s := Tag.s2) P Q)

/- A contradictory payload equation must not become a guessed "no answers".
The trace decomposes singleton first and then proves wait/crit free-head clash.
Its empty answer set is complete because every original solution is impossible.
-/
def clashProblem : Problem Sig [Tag.s0, Tag.s0] :=
  equation (waitingAtom (.var .here))
    (.app Symbol.c6 (.cons (.app Symbol.c4 (.cons (.var (.there .here)) .nil)) .nil))

theorem clash_exact_data :
    ∀ values, clashProblem.Holds registration values ↔
      Solutions registration ([] : List (Answer Sig [Tag.s0, Tag.s0])) values :=
  Worklist.exact registration (profile := profile) clashProblem []
    (.clash Symbol.c3 Symbol.c4 rfl rfl
      (fun same => nomatch same)
      (.cons (.var .here) .nil) (.cons (.var (.there .here)) .nil)
      (.decompose (profile := profile) (Γ := [Tag.s0, Tag.s0]) Symbol.c6 rfl
        (.cons (.app Symbol.c3 (.cons (.var .here) .nil)) .nil)
        (.cons (.app Symbol.c4 (.cons (.var (.there .here)) .nil)) .nil)
        .here (.hyp ⟨0, of_decide_eq_true rfl⟩)))
    .nil

/- Actual typed replay, not just the semantic rule instantiated in a theorem.

Original scope = [ticket : Nat, P : ProcSet, Q : ProcSet].
The Slots table skips ticket and selects P,Q ONCE. The occurrence coefficients
are 2P =B 3Q. One support gives Z, so the generated open image vector is
  (ticket, 3Z, 2Z), modulo trailing registered units.
The generated context retains the old scope after Z; unused old P,Q indices are
harmless internal passthrough slots, not extra constraints or extra solutions.

COMPLETENESS dump: FiniteSharing -> Cover(the sole generated answer, identity β).
SOUNDNESS dump: FiniteSharing(the SAME layout/Slots) -> end.
The top proof is exactly these data constructors. General rule metatheorems above
handle the semantic reasoning; no problem-specific supporting lemma/tactic/hole.
-/
def nonlinearSlots : Sharing.Slots Tag.s2 [Tag.s0, Tag.s2, Tag.s2] 2 :=
  .skip (.take (.take .nil))

def nonlinearLeft : FiniteSharing.Vector 2 := fun i => if i = 0 then 2 else 0
def nonlinearRight : FiniteSharing.Vector 2 := fun i => if i = 0 then 0 else 3

def nonlinearProblem : Problem Sig [Tag.s0, Tag.s2, Tag.s2] :=
  Sharing.problem Operator.acu nonlinearSlots nonlinearLeft nonlinearRight

def nonlinearAnswers : List (Answer Sig [Tag.s0, Tag.s2, Tag.s2]) :=
  [Sharing.answer Operator.acu nonlinearSlots nonlinearLeft nonlinearRight
    (FiniteSharing.supportGenerators (fun _ : Fin 2 => (0 : Fin 2)) (fun _ : Fin 3 => (1 : Fin 2)))]

theorem nonlinear_replay_certificate :
    ∀ values, nonlinearProblem.Holds registration values ↔ Solutions registration nonlinearAnswers values :=
  Worklist.exact registration (profile := profile) nonlinearProblem nonlinearAnswers
    (.sharing (sig := Sig) (s := Tag.s2) (Γ := [Tag.s0, Tag.s2, Tag.s2])
      (n := 2) (rows := 2) (cols := 3) Operator.acu nonlinearSlots
      nonlinearLeft nonlinearRight
      (fun _ : Fin 2 => (0 : Fin 2)) (fun _ : Fin 3 => (1 : Fin 2))
      (Fin.cases rfl (fun i => Fin.cases rfl (fun j => Fin.elim0 j) i))
      (Fin.cases rfl (fun i => Fin.cases rfl (fun j => Fin.elim0 j) i))
      (Fin.cases (Or.inr rfl) (fun i => Fin.cases (Or.inl rfl) (fun j => Fin.elim0 j) i))
      (.hyp ⟨0, of_decide_eq_true rfl⟩)
      (.cover ⟨0, of_decide_eq_true rfl⟩ (Terms.identity _)
        (.cons (.axiom (.refl _)) (.cons (.axiom (.refl _)) (.cons (.axiom (.refl _)) .nil)))))
    (.sharing (sig := Sig) (s := Tag.s2) (inputs := [Tag.s0, Tag.s2, Tag.s2])
      (n := 2) (rows := 2) (cols := 3) profile Operator.acu nonlinearSlots
      nonlinearLeft nonlinearRight
      (fun _ : Fin 2 => (0 : Fin 2)) (fun _ : Fin 3 => (1 : Fin 2))
      (Fin.cases rfl (fun i => Fin.cases rfl (fun j => Fin.elim0 j) i))
      (Fin.cases rfl (fun i => Fin.cases rfl (fun j => Fin.elim0 j) i))
      (Fin.cases (Or.inr rfl) (fun i => Fin.cases (Or.inl rfl) (fun j => Fin.elim0 j) i)) .nil)

/- Coefficient-aware ATOM-CHOOSE with TWO answers, not two handpicked branches:

   2P + Q + R =B singleton(wait(n))
   → j=Q: P=0, Q=singleton(wait(n)), R=0
   → j=R: P=0, Q=0, R=singleton(wait(n))

Complete.atom requests a child for EVERY coefficient-one index. There is no
P branch (its coefficient is two), and no external supplied-list coverage premise.
Soundness is the general, generated sum_choice equality trace for each answer.
-/
def choiceSlots : Sharing.Slots Tag.s2 [Tag.s0, Tag.s2, Tag.s2, Tag.s2] 3 :=
  .skip (.take (.take (.take .nil)))

def choiceCoefficients : FiniteSharing.Vector 3 := fun i => if i = 0 then 2 else 1

def choiceTerms (i : Fin 3) : Term Sig [Tag.s0, Tag.s2, Tag.s2, Tag.s2] Tag.s2 :=
  .var (choiceSlots.variable i)

def choiceProblem : Problem Sig [Tag.s0, Tag.s2, Tag.s2, Tag.s2] :=
  equation (Sharing.sum Operator.acu choiceCoefficients choiceTerms) (waitingAtom (.var .here))

def choiceAnswers : List (Answer Sig [Tag.s0, Tag.s2, Tag.s2, Tag.s2]) :=
  [{ parameters := [Tag.s0]
     images := .cons (.var .here) (.cons (zero Operator.acu)
       (.cons (waitingAtom (.var .here)) (.cons (zero Operator.acu) .nil))) },
   { parameters := [Tag.s0]
     images := .cons (.var .here) (.cons (zero Operator.acu)
       (.cons (zero Operator.acu) (.cons (waitingAtom (.var .here)) .nil))) }]

theorem coefficient_choice_certificate :
    ∀ values, choiceProblem.Holds registration values ↔ Solutions registration choiceAnswers values :=
  Worklist.exact registration (profile := profile) choiceProblem choiceAnswers
    (.atom Operator.acu choiceCoefficients choiceTerms Symbol.c6 rfl
      (.cons (.app Symbol.c3 (.cons (.var .here) .nil)) .nil)
      (.hyp ⟨0, of_decide_eq_true rfl⟩)
      (Fin.cases (fun impossible => False.elim ((of_decide_eq_true rfl : (2 : Nat) ≠ 1) impossible))
        (Fin.cases (fun _ =>
          .cover ⟨0, of_decide_eq_true rfl⟩ (.cons (.var .here) .nil)
            (.cons (.axiom (.refl _)) (.cons (.hyp ⟨0, of_decide_eq_true rfl⟩)
              (.cons (.hyp ⟨1, of_decide_eq_true rfl⟩) (.cons (.hyp ⟨2, of_decide_eq_true rfl⟩) .nil)))))
          (Fin.cases (fun _ =>
            .cover ⟨1, of_decide_eq_true rfl⟩ (.cons (.var .here) .nil)
              (.cons (.axiom (.refl _)) (.cons (.hyp ⟨0, of_decide_eq_true rfl⟩)
                (.cons (.hyp ⟨1, of_decide_eq_true rfl⟩) (.cons (.hyp ⟨2, of_decide_eq_true rfl⟩) .nil)))))
            (fun j => Fin.elim0 j)))))
    (.cons (.sum_choice Operator.acu (waitingAtom (.var .here)) choiceCoefficients
      ⟨1, of_decide_eq_true rfl⟩ rfl)
      (.cons (.sum_choice Operator.acu (waitingAtom (.var .here)) choiceCoefficients
        ⟨2, of_decide_eq_true rfl⟩ rfl) .nil))

/- ATOM-ONE exposes a payload equation, not a literal-equality shortcut:

   singleton(wait(n)) + 2P =B singleton(wait(m))
   → P=0 and singleton(wait(n)) =B singleton(wait(m))
   → wait(n) =B wait(m) → n =B m → cover (N,N,0).

All stages are existing/general rule data. No separate problem proof lemma.
-/
def payloadCoefficients : FiniteSharing.Vector 2 := fun i => if i = 0 then 1 else 2

def payloadTerms : Fin 2 → Term Sig [Tag.s0, Tag.s0, Tag.s2] Tag.s2 :=
  Fin.cases (waitingAtom (.var .here)) (Fin.cases (.var (.there (.there .here))) Fin.elim0)

def payloadProblem : Problem Sig [Tag.s0, Tag.s0, Tag.s2] :=
  equation (Sharing.sum Operator.acu payloadCoefficients payloadTerms)
    (waitingAtom (.var (.there .here)))

def payloadAnswers : List (Answer Sig [Tag.s0, Tag.s0, Tag.s2]) :=
  [{ parameters := [Tag.s0]
     images := .cons (.var .here) (.cons (.var .here) (.cons (zero Operator.acu) .nil)) }]

theorem payload_requirement_certificate :
    ∀ values, payloadProblem.Holds registration values ↔ Solutions registration payloadAnswers values :=
  Worklist.exact registration (profile := profile) payloadProblem payloadAnswers
    (.atom Operator.acu payloadCoefficients payloadTerms Symbol.c6 rfl
      (.cons (.app Symbol.c3 (.cons (.var (.there .here)) .nil)) .nil)
      (.hyp ⟨0, of_decide_eq_true rfl⟩)
      (Fin.cases (fun _ =>
        .cover ⟨0, of_decide_eq_true rfl⟩ (.cons (.var .here) .nil)
          (.cons (.axiom (.refl _))
            (.cons (.symm (.decompose (profile := profile) (Γ := [Tag.s0, Tag.s0, Tag.s2]) Symbol.c3 rfl
              (.cons (.var .here) .nil) (.cons (.var (.there .here)) .nil) .here
              (.decompose (profile := profile) (Γ := [Tag.s0, Tag.s0, Tag.s2]) Symbol.c6 rfl
                (.cons (.app Symbol.c3 (.cons (.var .here) .nil)) .nil)
                (.cons (.app Symbol.c3 (.cons (.var (.there .here)) .nil)) .nil) .here
                (.hyp ⟨0, of_decide_eq_true rfl⟩))))
              (.cons (.hyp ⟨1, of_decide_eq_true rfl⟩) .nil))))
        (Fin.cases (fun impossible => False.elim ((of_decide_eq_true rfl : (2 : Nat) ≠ 1) impossible))
          (fun i => Fin.elim0 i))))
    (.cons (.sum_choice Operator.acu (waitingAtom (.var .here)) payloadCoefficients
      ⟨0, of_decide_eq_true rfl⟩ rfl) .nil)

/- ZERO preserves a canceled/inactive variable:
   0P + 2Q =B empty → Q=empty, P arbitrary. -/
def zeroCoefficients : FiniteSharing.Vector 2 := fun i => if i = 0 then 0 else 2

def zeroTerms : Fin 2 → Term Sig [Tag.s2, Tag.s2] Tag.s2 :=
  Fin.cases (.var .here) (Fin.cases (.var (.there .here)) Fin.elim0)

def zeroProblem : Problem Sig [Tag.s2, Tag.s2] :=
  equation (Sharing.sum Operator.acu zeroCoefficients zeroTerms) (zero Operator.acu)

def zeroAnswers : List (Answer Sig [Tag.s2, Tag.s2]) :=
  [{ parameters := [Tag.s2]
     images := .cons (.var .here) (.cons (zero Operator.acu) .nil) }]

theorem zero_requirement_certificate :
    ∀ values, zeroProblem.Holds registration values ↔ Solutions registration zeroAnswers values :=
  Worklist.exact registration (profile := profile) zeroProblem zeroAnswers
    (.zero Operator.acu zeroCoefficients zeroTerms (.hyp ⟨0, of_decide_eq_true rfl⟩)
      (.cover ⟨0, of_decide_eq_true rfl⟩ (.cons (.var .here) .nil)
        (.cons (.axiom (.refl _)) (.cons (.hyp ⟨1, of_decide_eq_true rfl⟩) .nil))))
    (.cons (Equality.sum_zero (sig := Sig) (Γ := [Tag.s2]) Operator.acu zeroCoefficients) .nil)

/- No coefficient-one supplier: 2P =B singleton(wait(n)) has NO solution.
No bounded search failure or assumption that Maude reported no answers is used. -/
theorem impossible_requirement_certificate :
    ∀ values, (equation (Sharing.sum Operator.acu (fun _ : Fin 1 => 2)
      (fun _ => (.var (.there .here) : Term Sig [Tag.s0, Tag.s2] Tag.s2)))
      (waitingAtom (.var .here))).Holds registration values ↔
      Solutions registration ([] : List (Answer Sig [Tag.s0, Tag.s2])) values :=
  Worklist.exact registration (profile := profile) _ []
    (.atom Operator.acu (fun _ : Fin 1 => 2) (fun _ => .var (.there .here)) Symbol.c6 rfl
      (.cons (.app Symbol.c3 (.cons (.var .here) .nil)) .nil)
      (.hyp ⟨0, of_decide_eq_true rfl⟩)
      (fun _ impossible => False.elim ((of_decide_eq_true rfl : (2 : Nat) ≠ 1) impossible)))
    .nil

/- BIND across a whole many-sorted equation system:

  scope (n,P,Q), equations P =B Q and Q =B singleton(wait(n))
  bind P:=Q → scope (n,Q), images (n,Q,Q), BOTH equations substituted
  bind Q:=singleton(wait(n)) → scope (n), images (n,[wait(n)],[wait(n)])
  cover the generated answer using identity β.

The bag variables are removed even though their equality is modulo B, not Lean
literal equality. No assumption identifying raw constructor trees is introduced.
-/
def bindFirst : Binding.Removal Tag.s2 [Tag.s0, Tag.s2, Tag.s2] [Tag.s0, Tag.s2] :=
  .there .here

def bindSecond : Binding.Removal Tag.s2 [Tag.s0, Tag.s2] [Tag.s0] := .there .here

def bindSystem : List (Problem Sig [Tag.s0, Tag.s2, Tag.s2]) :=
  [Binding.problem bindFirst (.var (.there .here)),
   equation (.var (.there (.there .here))) (waitingAtom (.var .here))]

def bindAnswers : List (Answer Sig [Tag.s0, Tag.s2, Tag.s2]) :=
  [{ parameters := [Tag.s0]
     images := ((Terms.identity [Tag.s0, Tag.s2, Tag.s2]).subst
       (bindFirst.substitution (.var (.there .here)))).subst
       (bindSecond.substitution (waitingAtom (.var .here))) }]

theorem binding_system_certificate :
    ∀ values, Worklist.Holds registration bindSystem values ↔ Solutions registration bindAnswers values :=
  Worklist.exact_system registration (profile := profile) bindSystem bindAnswers
    (.bind bindFirst (.var (.there .here)) (.hyp ⟨0, of_decide_eq_true rfl⟩)
      (.bind bindSecond (waitingAtom (.var .here)) (.hyp ⟨1, of_decide_eq_true rfl⟩)
        (.cover ⟨0, of_decide_eq_true rfl⟩ (.cons (.var .here) .nil)
          (.cons (.axiom (.refl _)) (.cons (.axiom (.refl _)) (.cons (.axiom (.refl _)) .nil))))))
    (.cons (.cons (.refl _) .nil) (.cons (.cons (.refl _) .nil) .nil))

/- Hand-prepared LEAN-READY dump for the SAME BIND/BIND/COVER derivation.
This is the final format a Maude emitter (or external proof-term translator)
could produce; it is NOT yet emitted by Maude. No tactics, no interpreter, no
problem-specific proof lemma. The two sorted removals and every premise are
explicit in the term; general metatheorems perform the semantic justification.

Input remains bindSystem/bindAnswers, fixed by Lean, not chosen by the dump.
The long-lived prover signature supplies all constructor and sort identifiers.
-/
def leanReadyBindingDump : String := "
  Worklist.exact_system registration (profile := profile) bindSystem bindAnswers
    (.bind
      (.there .here : Binding.Removal Tag.s2 [Tag.s0, Tag.s2, Tag.s2] [Tag.s0, Tag.s2])
      (.var (.there .here)) (.hyp ⟨0, of_decide_eq_true rfl⟩)
      (.bind
        (.there .here : Binding.Removal Tag.s2 [Tag.s0, Tag.s2] [Tag.s0])
        (waitingAtom (.var .here)) (.hyp ⟨1, of_decide_eq_true rfl⟩)
        (.cover ⟨0, of_decide_eq_true rfl⟩ (.cons (.var .here) .nil)
          (.cons (.axiom (.refl _))
            (.cons (.axiom (.refl _)) (.cons (.axiom (.refl _)) .nil))))))
    (.cons (.cons (.refl _) .nil) (.cons (.cons (.refl _) .nil) .nil))
"

/- FULL CERTIFICATE TEST DISABLED IN THIS MONOLITHIC FILE.
The unchanged dump was subsequently accepted against its full native exactness
goal after temporarily splitting/compiling the general library (2026-10-06).
Parsing 1 ms, elaboration 209 ms, kernel 1 ms; axiom audit has no admissions.
External explicit BIND/BIND/COVER and nonlinear SHARING/COVER also passed.
Experiment results belong in HANDOFF.md. The general infrastructure is now
compiled separately; this success does not diagnose the historical timeout.
Do not automatically run it in an unrestricted editor/server session.

Built-in elaboration command: no new user tactic or command is introduced.
-- addDecl invokes Lean's kernel on the explicit proof; it does not trust text.
open Lean Meta Elab Term in
run_elab do
  let expected ← `(∀ values,
    Worklist.Holds registration bindSystem values ↔ Solutions registration bindAnswers values)
  let (type, proof) ← LeanReady.prepareProof expected leanReadyBindingDump
  let started ← IO.monoMsNow
  addDecl (.thmDecl {
    name := `DirectCertification.Bakery.lean_ready_binding_certificate
    levelParams := []
    type := type
    value := proof })
  let checked ← IO.monoMsNow
  logInfo m!"Lean-ready kernel checking: {checked - started} ms"

-- A broken whole-vector factor must fail against the SAME fixed proposition.
-- Save/restore elaboration state so expected rejection leaves no holes/errors.
open Lean Meta Elab Term in
run_elab do
  let expected ← `(∀ values,
    Worklist.Holds registration bindSystem values ↔ Solutions registration bindAnswers values)
  let broken := leanReadyBindingDump.replace
    "(.cover ⟨0, of_decide_eq_true rfl⟩ (.cons (.var .here) .nil)"
    "(.cover ⟨0, of_decide_eq_true rfl⟩ .nil"
  let saved ← Term.saveState
  let rejected ← try
      let _ ← LeanReady.prepareProof expected broken
      pure false
    catch _ => pure true
  saved.restore
  unless rejected do throwError "incomplete factor was accepted"
  logInfo "Lean-ready negative test: incomplete factor rejected"
-/

/- PURIFY followed by BIND, over ordinary Bakery constructors:

  [wait(n)] =B [wait(m)]
  → A =B [wait(n)], A =B [wait(m)]                 PURIFY
  → [wait(m)] =B [wait(n)], [wait(m)] =B [wait(m)] BIND A:=[wait(m)]
  → m =B n → cover answer (N,N).                 DECOMPOSE/COVER

The fresh A is completely internal. The original variables n,m remain shared;
the proof is one explicit replay term, not supporting problem-specific lemmas.
-/
def purifiedTerm : Term Sig [Tag.s0, Tag.s0] Tag.s2 := waitingAtom (.var .here)

def purifiedTemplate : Problem Sig [Tag.s2, Tag.s0, Tag.s0] :=
  equation (.var .here) (waitingAtom (.var (.there (.there .here))))

def purifiedProblem : Problem Sig [Tag.s0, Tag.s0] :=
  Worklist.Purification.source purifiedTerm purifiedTemplate

def purifiedAnswers : List (Answer Sig [Tag.s0, Tag.s0]) :=
  [{ parameters := [Tag.s0]
     images := .cons (.var .here) (.cons (.var .here) .nil) }]

theorem purification_binding_certificate :
    ∀ values, purifiedProblem.Holds registration values ↔ Solutions registration purifiedAnswers values :=
  Worklist.exact registration (profile := profile) purifiedProblem purifiedAnswers
    (.purify purifiedTerm purifiedTemplate [] []
      (.bind (.here : Binding.Removal Tag.s2 [Tag.s2, Tag.s0, Tag.s0] [Tag.s0, Tag.s0])
        (waitingAtom (.var (.there .here))) (.hyp ⟨1, of_decide_eq_true rfl⟩)
        (.cover ⟨0, of_decide_eq_true rfl⟩ (.cons (.var .here) .nil)
          (.cons (.axiom (.refl _))
            (.cons (.decompose (profile := profile) (Γ := [Tag.s0, Tag.s0]) Symbol.c3 rfl
              (.cons (.var (.there .here)) .nil) (.cons (.var .here) .nil) .here
              (.decompose (profile := profile) (Γ := [Tag.s0, Tag.s0]) Symbol.c6 rfl
                (.cons (.app Symbol.c3 (.cons (.var (.there .here)) .nil)) .nil)
                (.cons (.app Symbol.c3 (.cons (.var .here) .nil)) .nil) .here
                (.hyp ⟨0, of_decide_eq_true rfl⟩))) .nil)))))
    (.cons (.refl _) .nil)

/- Automatic scope and occurrence checks, still over the SAME registered terms.
The selector traverses the signature generically. These guards are regression
tests, not the metatheorem justifying the FREE-OCCURS rule. -/
def cyclicNat : Problem Sig [Tag.s0] :=
  equation (.var .here) (.app Symbol.c1 (.cons (.var .here) .nil))

def cancellableBag : Problem Sig [Tag.s2, Tag.s2] :=
  equation (.var .here) (add Operator.acu (.var .here) (.var (.there .here)))

def freeHeadClash : Problem Sig [Tag.s0] :=
  equation (.app Symbol.c3 (.cons (.var .here) .nil)) (.app Symbol.c4 (.cons (.var .here) .nil))

#guard (Binding.prepare (sig := Sig) (Γ := [Tag.s0, Tag.s2]) (.there .here)
  (waitingAtom (.var .here))).isSome
#guard !(Binding.prepare (sig := Sig) (Γ := [Tag.s0]) .here cyclicNat.right).isSome
#guard !(Binding.prepare (sig := Sig) (Γ := [Tag.s2, Tag.s2]) .here cancellableBag.right).isSome
#guard (FreeOccurs.findProper profile (.here : Variable [Tag.s0] Tag.s0) cyclicNat.right).isSome
#guard !(FreeOccurs.findProper profile (.here : Variable [Tag.s2, Tag.s2] Tag.s2)
  cancellableBag.right).isSome
#guard (Worklist.closeFree profile [] (Terms.identity [Tag.s0]) [cyclicNat]
  ⟨0, of_decide_eq_true rfl⟩).isSome
#guard !(Worklist.closeFree profile [] (Terms.identity [Tag.s2, Tag.s2]) [cancellableBag]
  ⟨0, of_decide_eq_true rfl⟩).isSome
#guard match FreePhase.classify profile (.var (.there .here) : Term Sig [Tag.s0, Tag.s2] Tag.s2)
    (waitingAtom (.var .here)) with
  | .bind .. => true
  | _ => false
#guard match FreePhase.classify profile (waitingAtom (.var .here) : Term Sig [Tag.s0, Tag.s2] Tag.s2)
    (.var (.there .here)) with
  | .orient (.bind ..) => true
  | _ => false
#guard match FreePhase.classify profile (waitingAtom (.var .here) : Term Sig [Tag.s0, Tag.s0] Tag.s2)
    (waitingAtom (.var (.there .here))) with
  | .decompose .. => true
  | _ => false
#guard match FreePhase.classify profile cancellableBag.left cancellableBag.right with
  | .postpone => true
  | _ => false
#guard (Worklist.closeFree profile [] (Terms.identity [Tag.s0]) [equation cyclicNat.right cyclicNat.left]
  ⟨0, of_decide_eq_true rfl⟩).isSome

/- Actual unconstrained certification of n =B succ(n), without supplying the
occurrence path. The algorithm discovers it, constructs Complete.occurs, and
the general checker proves the semantic empty-answer certificate. -/
theorem automatic_occurs_certificate :
    ∀ values, cyclicNat.Holds registration values ↔
      Solutions registration ([] : List (Answer Sig [Tag.s0])) values :=
  Worklist.exact registration (profile := profile) cyclicNat []
    ((Worklist.closeFree profile [] (Terms.identity [Tag.s0]) [cyclicNat]
      ⟨0, of_decide_eq_true rfl⟩).get (of_decide_eq_true rfl)) .nil

theorem automatic_clash_certificate :
    ∀ values, freeHeadClash.Holds registration values ↔
      Solutions registration ([] : List (Answer Sig [Tag.s0])) values :=
  Worklist.exact registration (profile := profile) freeHeadClash []
    ((Worklist.closeFree profile [] (Terms.identity [Tag.s0]) [freeHeadClash]
      ⟨0, of_decide_eq_true rfl⟩).get (of_decide_eq_true rfl)) .nil

-- Kernel audits: standard Lean axioms are acceptable; sorryAx is not.
#print axioms atomic_exact_data
#print axioms repeated_exact_data
#print axioms clash_exact_data
#print axioms Worklist.exact_system
#print axioms multiplicity_cancel
#print axioms FiniteSharing.boolean_transport_exists
#print axioms FiniteSharing.minimal_nonempty_boolean_support
#print axioms FiniteSharing.boolean_supports_exact
#print axioms FiniteSharing.supportGenerators_exact
#print axioms FiniteSharing.bags_generated
#print axioms finiteSharing_native
#print axioms nonlinear_sharing_certificate
#print axioms Sharing.complete
#print axioms Sharing.sound
#print axioms nonlinear_replay_certificate
#print axioms AtomProcessing.sum_zero
#print axioms AtomProcessing.sum_atom
#print axioms coefficient_choice_certificate
#print axioms payload_requirement_certificate
#print axioms zero_requirement_certificate
#print axioms impossible_requirement_certificate
#print axioms Binding.complete
#print axioms Binding.sound
#print axioms binding_system_certificate
-- Verified via temporary compiled-module experiment; disabled here for resources.
-- #print axioms lean_ready_binding_certificate
#print axioms Worklist.Purification.exact
#print axioms purification_binding_certificate
#print axioms Binding.lower_sound
#print axioms FreeOccurs.Proper.sound
#print axioms automatic_occurs_certificate
#print axioms automatic_clash_certificate

end DirectCertification.Bakery
