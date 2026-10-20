import conPanna.conPanna
import conPanna.Unification.Certification.Multiset

/-!
# OneThirdRule: a feasibility draft

OneThirdRule (Charron-Bost & Schiper), after the Maude model of Kang & Bae ("Narrowing and
Heuristic Search for Symbolic Reachability Analysis of Concurrent Object-Oriented
Systems", §3), in our own form: plain constructors, two ACU bags (the configuration,
and the receivers of a multicast), `Nat` counters, and rule conditions as Lean
propositions (no `decide?`/`update?` encoding or finite-variant tricks are needed).

Two invariants are proved, each by narrowing the whole system at once: every node is
well-formed (invariant 1), and no message comes from the future (invariant 3). Their
certificates are deferred by `narrow` and linked at the end (`otr_inv1.linked`,
`otr_inv3.linked`). Agreement is not attempted: it needs counting across nodes.
-/

namespace OTR

open Expresso Unification Narrowing Subsumption

/-! ## Model -/

inductive Step where
  | init | wait | done

/-- A node's decision: none yet, or a value. -/
inductive Dec where
  | undecided
  | decided (v : Bool)

/-- A set of node identifiers, e.g. the remaining receivers of a multicast. -/
abbrev OidSet := ACU Nat

/-- A node: identifier, round, step, current value, decision, and the votes received in
this round: for `true`, for `false`, and in total. -/
structure Node where
  id : Nat
  round : Nat
  step : Step
  value : Bool
  dec : Dec
  vt : Nat
  vf : Nat
  va : Nat

/-- A configuration item: a node, or a multicast `vote(v, r) from src to receivers`. -/
inductive Item where
  | node (n : Node)
  | msg (v : Bool) (r : Nat) (src : Nat) (rcv : OidSet)

abbrev Items := ACU Item

/-- A global state: the decision threshold, all identifiers, and the configuration. -/
structure Conf where
  th : Nat
  ids : OidSet
  items : Items

#dump_model Conf

/-! ## Rules
One rule per Maude rule, with the vote's value split into `true`/`false` cases (the
counter it increments differs), and conditions as plain propositions. -/

/-- `[vote]`: broadcast the own value to all other nodes. -/
def voteT : Rule Conf := .bind fun ((TH, O, OS, R, VT, VF, VA, CF) :
    Nat × Nat × OidSet × Nat × Nat × Nat × Nat × Items) =>
  { lhs := ⟨TH, {O} + OS, {Item.node ⟨O, R, .init, true, .undecided, VT, VF, VA⟩} + CF⟩
    rhs := ⟨TH, {O} + OS, {Item.node ⟨O, R, .wait, true, .undecided, VT + 1, VF, VA + 1⟩} +
      ({Item.msg true R O OS} + CF)⟩ }

def voteF : Rule Conf := .bind fun ((TH, O, OS, R, VT, VF, VA, CF) :
    Nat × Nat × OidSet × Nat × Nat × Nat × Nat × Items) =>
  { lhs := ⟨TH, {O} + OS, {Item.node ⟨O, R, .init, false, .undecided, VT, VF, VA⟩} + CF⟩
    rhs := ⟨TH, {O} + OS, {Item.node ⟨O, R, .wait, false, .undecided, VT, VF + 1, VA + 1⟩} +
      ({Item.msg false R O OS} + CF)⟩ }

/-- `[receive]`: a waiting node takes in a vote of its round addressed to it. -/
def recvT : Rule Conf := .bind fun ((TH, IDS, O, R, V, D, VT, VF, VA, S, OS, CF) :
    Nat × OidSet × Nat × Nat × Bool × Dec × Nat × Nat × Nat × Nat × OidSet × Items) =>
  { lhs := ⟨TH, IDS, {Item.node ⟨O, R, .wait, V, D, VT, VF, VA⟩} +
      ({Item.msg true R S ({O} + OS)} + CF)⟩
    rhs := ⟨TH, IDS, {Item.node ⟨O, R, .wait, V, D, VT + 1, VF, VA + 1⟩} +
      ({Item.msg true R S OS} + CF)⟩ }

def recvF : Rule Conf := .bind fun ((TH, IDS, O, R, V, D, VT, VF, VA, S, OS, CF) :
    Nat × OidSet × Nat × Nat × Bool × Dec × Nat × Nat × Nat × Nat × OidSet × Items) =>
  { lhs := ⟨TH, IDS, {Item.node ⟨O, R, .wait, V, D, VT, VF, VA⟩} +
      ({Item.msg false R S ({O} + OS)} + CF)⟩
    rhs := ⟨TH, IDS, {Item.node ⟨O, R, .wait, V, D, VT, VF + 1, VA + 1⟩} +
      ({Item.msg false R S OS} + CF)⟩ }

/-- `[decide]`: more than the threshold of votes for a value: decide it. -/
def decideT : Rule Conf := .bind fun ((TH, IDS, O, R, V, VT, VF, VA, CF) :
    Nat × OidSet × Nat × Nat × Bool × Nat × Nat × Nat × Items) =>
  { lhs := ⟨TH, IDS, {Item.node ⟨O, R, .wait, V, .undecided, VT, VF, VA⟩} + CF⟩
    rhs := ⟨TH, IDS, {Item.node ⟨O, R, .done, V, .decided true, VT, VF, VA⟩} + CF⟩
    cond := TH ≤ VT }

def decideF : Rule Conf := .bind fun ((TH, IDS, O, R, V, VT, VF, VA, CF) :
    Nat × OidSet × Nat × Nat × Bool × Nat × Nat × Nat × Items) =>
  { lhs := ⟨TH, IDS, {Item.node ⟨O, R, .wait, V, .undecided, VT, VF, VA⟩} + CF⟩
    rhs := ⟨TH, IDS, {Item.node ⟨O, R, .done, V, .decided false, VT, VF, VA⟩} + CF⟩
    cond := TH ≤ VF }

/-- `[update]`: enough votes but no decision: adopt the smallest most frequent value
and go to the next round. -/
def updateT : Rule Conf := .bind fun ((TH, IDS, O, R, V, VT, VF, VA, CF) :
    Nat × OidSet × Nat × Nat × Bool × Nat × Nat × Nat × Items) =>
  { lhs := ⟨TH, IDS, {Item.node ⟨O, R, .wait, V, .undecided, VT, VF, VA⟩} + CF⟩
    rhs := ⟨TH, IDS, {Item.node ⟨O, R + 1, .init, true, .undecided, 0, 0, 0⟩} + CF⟩
    cond := VT < TH ∧ TH ≤ VA ∧ VF ≤ VT }

def updateF : Rule Conf := .bind fun ((TH, IDS, O, R, V, VT, VF, VA, CF) :
    Nat × OidSet × Nat × Nat × Bool × Nat × Nat × Nat × Items) =>
  { lhs := ⟨TH, IDS, {Item.node ⟨O, R, .wait, V, .undecided, VT, VF, VA⟩} + CF⟩
    rhs := ⟨TH, IDS, {Item.node ⟨O, R + 1, .init, false, .undecided, 0, 0, 0⟩} + CF⟩
    cond := VF < TH ∧ TH ≤ VA ∧ VT < VF }

/-- `[loss]`: a multicast is lost. -/
def loss : Rule Conf := .bind fun ((TH, IDS, V, R, S, OS, CF) :
    Nat × OidSet × Bool × Nat × Nat × OidSet × Items) =>
  { lhs := ⟨TH, IDS, {Item.msg V R S OS} + CF⟩
    rhs := ⟨TH, IDS, CF⟩ }

def otr : System Conf := [voteT, voteF, recvT, recvF, decideT, decideF, updateT, updateF, loss]

/-! ## Invariant 1: every node is well-formed
Its vote record is consistent, and it is done exactly when it has decided. -/

def nodeOK (n : Node) : Prop :=
  n.va = n.vt + n.vf ∧ (n.step = .done ↔ n.dec ≠ .undecided)

def itemOK : Item → Prop
  | .node n => nodeOK n
  | .msg .. => True

def allOK (CF : Items) : Prop := ∀ it ∈ CF.toMultiset, itemOK it

def okP : Patch Conf := .bind fun ((TH, IDS, CF) : Nat × OidSet × Items) =>
  ⟨⟨TH, IDS, CF⟩, allOK CF⟩

def inv1 : Pattern Conf := [okP]

theorem allOK_plus (X Y : Items) : allOK (X + Y) ↔ allOK X ∧ allOK Y := by
  simp [allOK, or_imp, forall_and]

theorem allOK_node (n : Node) : allOK {Item.node n} ↔ nodeOK n := by
  simp [allOK, itemOK]

theorem allOK_msg (v : Bool) (r s : Nat) (OS : OidSet) : allOK {Item.msg v r s OS} := by
  simp [allOK, itemOK]

theorem allOK_unit : allOK ∅ := by
  simp [allOK]

theorem otr_inv1 : isOverPost otr inv1 inv1 := by
  narrow otr from inv1
    using [ACU.plus_unit, ACU.unit_plus, allOK_plus, allOK_node, allOK_msg, allOK_unit]
    as post hpost
  -- every post patch lands in the single invariant patch `okP`; one script for all
  refine over_of_subsumes hpost.1 (subsumes_of_cover fun a ha => ?_)
  rw [← post_eq] at ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    apply subsumes_one
    maude_match okP
    try simp only [allOK_plus, allOK_node, allOK_msg, allOK_unit, nodeOK, and_true, true_and] at hc ⊢
    try omega
    try (simp_all; try omega)

/-! ## Invariant 3: no messages from the future (relational)
Every message in transit was sent in a round no later than its sender's current round;
node identifiers are unique. It relates two elements of the bag (a message and its
sender), so its condition is not a "for each item" predicate. -/

/-- The nodes' identifiers, with multiplicity. -/
def nodeIds (CF : Items) : Multiset Nat :=
  CF.toMultiset.bind fun | .node n => {n.id} | .msg .. => 0

/-- Each message's round is at most its sender's round. -/
def msgsOK (CF : Items) : Prop :=
  ∀ v r s rcv, Item.msg v r s rcv ∈ CF.toMultiset →
    ∃ n, Item.node n ∈ CF.toMultiset ∧ n.id = s ∧ r ≤ n.round

def pastOK (CF : Items) : Prop := (nodeIds CF).Nodup ∧ msgsOK CF

def pastP : Patch Conf := .bind fun ((TH, IDS, CF) : Nat × OidSet × Items) =>
  ⟨⟨TH, IDS, CF⟩, pastOK CF⟩

theorem nodeIds_plus (X Y : Items) : nodeIds (X + Y) = nodeIds X + nodeIds Y := by
  simp [nodeIds]
theorem nodeIds_node (n : Node) : nodeIds {Item.node n} = {n.id} := by simp [nodeIds]
theorem nodeIds_msg (v : Bool) (r s : Nat) (OS : OidSet) : nodeIds {Item.msg v r s OS} = 0 := by
  simp [nodeIds]
theorem nodeIds_unit : nodeIds ∅ = 0 := by simp [nodeIds]

/-- The transfer principle of a step `P ⟶ Q`: the identifiers are unchanged, every node
persists with a round no smaller, and every message is an old one (maybe with fewer
receivers) or has a sender in `Q` at its round or later. -/
theorem pastOK_of {P Q : Items} (h : pastOK P) (hid : nodeIds Q = nodeIds P)
    (hn : ∀ n, Item.node n ∈ P.toMultiset →
      ∃ n', Item.node n' ∈ Q.toMultiset ∧ n'.id = n.id ∧ n.round ≤ n'.round)
    (hm : ∀ v r s rcv, Item.msg v r s rcv ∈ Q.toMultiset →
      (∃ rcv', Item.msg v r s rcv' ∈ P.toMultiset) ∨
      ∃ n', Item.node n' ∈ Q.toMultiset ∧ n'.id = s ∧ r ≤ n'.round) :
    pastOK Q := by
  refine ⟨hid ▸ h.1, fun v r s rcv hq => ?_⟩
  rcases hm v r s rcv hq with ⟨rcv', hp⟩ | h'
  · obtain ⟨n, hn1, rfl, hr⟩ := h.2 v r s rcv' hp
    obtain ⟨n', h1, h2, h3⟩ := hn n hn1
    exact ⟨n', h1, h2, by omega⟩
  · exact h'

def inv3 : Pattern Conf := [pastP]

-- 26 cases, each closed by `aesop`, share one heartbeat budget
set_option maxHeartbeats 1000000 in
theorem otr_inv3 : isOverPost otr inv3 inv3 := by
  narrow otr from inv3 using [ACU.plus_unit, ACU.unit_plus] as post hpost
  refine over_of_subsumes hpost.1 (subsumes_of_cover fun a ha => ?_)
  rw [← post_eq] at ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    apply subsumes_one
    maude_match pastP
    -- the relational reasoning: the sender of each message is still there, its round
    -- only grows (`update`), and new messages carry the sender's own round (`vote`)
    refine pastOK_of (by first | exact hc | exact hc.1) ?_ ?_ ?_
    · simp only [nodeIds_plus, nodeIds_node, nodeIds_msg, add_zero]
      try ac_rfl
    all_goals
      simp only [ACU.toMultiset_plus, ACU.toMultiset_elem, Multiset.mem_add,
        Multiset.mem_singleton, or_false, false_or,
        Item.msg.injEq, Item.node.injEq, reduceCtorEq]
      aesop

/-! ## Obligations
The certificates deferred by `narrow`: completeness by Maude's derivation replayed in Lean,
soundness by instantiating each unifier. Printed by `#obligations`, then linked. -/

set_option linter.style.longLine false
set_option linter.unusedSimpArgs false

theorem otr_inv1.obligation_1 :
    complete (mayFire voteT okP)
      [Unifier.bind fun (x : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) =>
          ((x.2.2.2.2.2, x.1, ∅, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, ∅), x.2.2.2.2.2, {x.1},
            {Item.node
                { id := x.1, round := x.2.1, step := Step.init, value := true, dec := Dec.undecided, vt := x.2.2.1,
                  vf := x.2.2.2.1, va := x.2.2.2.2.1 }}),
        Unifier.bind fun (x : ℕ × Items × ℕ × ℕ × ℕ × ℕ × ℕ) =>
          ((x.2.2.2.2.2.2, x.1, ∅, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.1), x.2.2.2.2.2.2, {x.1},
            x.2.1 +
              {Item.node
                  { id := x.1, round := x.2.2.1, step := Step.init, value := true, dec := Dec.undecided,
                    vt := x.2.2.2.1, vf := x.2.2.2.2.1, va := x.2.2.2.2.2.1 }}),
        Unifier.bind fun (x : ℕ × OidSet × ℕ × ℕ × ℕ × ℕ × ℕ) =>
          ((x.2.2.2.2.2.2, x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, ∅), x.2.2.2.2.2.2, {x.1} + x.2.1,
            {Item.node
                { id := x.1, round := x.2.2.1, step := Step.init, value := true, dec := Dec.undecided, vt := x.2.2.2.1,
                  vf := x.2.2.2.2.1, va := x.2.2.2.2.2.1 }}),
        Unifier.bind fun (x : ℕ × OidSet × Items × ℕ × ℕ × ℕ × ℕ × ℕ) =>
          ((x.2.2.2.2.2.2.2, x.1, x.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.1),
            x.2.2.2.2.2.2.2, {x.1} + x.2.1,
            x.2.2.1 +
              {Item.node
                  { id := x.1, round := x.2.2.2.1, step := Step.init, value := true, dec := Dec.undecided,
                    vt := x.2.2.2.2.1, vf := x.2.2.2.2.2.1, va := x.2.2.2.2.2.2.1 }})] := by
  maude_certify_comp

theorem otr_inv1.obligation_2 :
    sound (mayFire voteT okP)
      [Unifier.bind fun (x : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) =>
          ((x.2.2.2.2.2, x.1, ∅, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, ∅), x.2.2.2.2.2, {x.1},
            {Item.node
                { id := x.1, round := x.2.1, step := Step.init, value := true, dec := Dec.undecided, vt := x.2.2.1,
                  vf := x.2.2.2.1, va := x.2.2.2.2.1 }}),
        Unifier.bind fun (x : ℕ × Items × ℕ × ℕ × ℕ × ℕ × ℕ) =>
          ((x.2.2.2.2.2.2, x.1, ∅, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.1), x.2.2.2.2.2.2, {x.1},
            x.2.1 +
              {Item.node
                  { id := x.1, round := x.2.2.1, step := Step.init, value := true, dec := Dec.undecided,
                    vt := x.2.2.2.1, vf := x.2.2.2.2.1, va := x.2.2.2.2.2.1 }}),
        Unifier.bind fun (x : ℕ × OidSet × ℕ × ℕ × ℕ × ℕ × ℕ) =>
          ((x.2.2.2.2.2.2, x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, ∅), x.2.2.2.2.2.2, {x.1} + x.2.1,
            {Item.node
                { id := x.1, round := x.2.2.1, step := Step.init, value := true, dec := Dec.undecided, vt := x.2.2.2.1,
                  vf := x.2.2.2.2.1, va := x.2.2.2.2.2.1 }}),
        Unifier.bind fun (x : ℕ × OidSet × Items × ℕ × ℕ × ℕ × ℕ × ℕ) =>
          ((x.2.2.2.2.2.2.2, x.1, x.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.1),
            x.2.2.2.2.2.2.2, {x.1} + x.2.1,
            x.2.2.1 +
              {Item.node
                  { id := x.1, round := x.2.2.2.1, step := Step.init, value := true, dec := Dec.undecided,
                    vt := x.2.2.2.2.1, vf := x.2.2.2.2.2.1, va := x.2.2.2.2.2.2.1 }})] := by
  simp only [sound, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  repeat' apply And.intro
  all_goals
    rintro γ ⟨x, rfl⟩
    simp only [unifiedBy, mayFire, voteT, okP]
    try ac_rfl

theorem otr_inv1.obligation_3 :
    complete (mayFire voteF okP)
      [Unifier.bind fun (x : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) =>
          ((x.2.2.2.2.2, x.1, ∅, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, ∅), x.2.2.2.2.2, {x.1},
            {Item.node
                { id := x.1, round := x.2.1, step := Step.init, value := false, dec := Dec.undecided, vt := x.2.2.1,
                  vf := x.2.2.2.1, va := x.2.2.2.2.1 }}),
        Unifier.bind fun (x : ℕ × Items × ℕ × ℕ × ℕ × ℕ × ℕ) =>
          ((x.2.2.2.2.2.2, x.1, ∅, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.1), x.2.2.2.2.2.2, {x.1},
            x.2.1 +
              {Item.node
                  { id := x.1, round := x.2.2.1, step := Step.init, value := false, dec := Dec.undecided,
                    vt := x.2.2.2.1, vf := x.2.2.2.2.1, va := x.2.2.2.2.2.1 }}),
        Unifier.bind fun (x : ℕ × OidSet × ℕ × ℕ × ℕ × ℕ × ℕ) =>
          ((x.2.2.2.2.2.2, x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, ∅), x.2.2.2.2.2.2, {x.1} + x.2.1,
            {Item.node
                { id := x.1, round := x.2.2.1, step := Step.init, value := false, dec := Dec.undecided, vt := x.2.2.2.1,
                  vf := x.2.2.2.2.1, va := x.2.2.2.2.2.1 }}),
        Unifier.bind fun (x : ℕ × OidSet × Items × ℕ × ℕ × ℕ × ℕ × ℕ) =>
          ((x.2.2.2.2.2.2.2, x.1, x.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.1),
            x.2.2.2.2.2.2.2, {x.1} + x.2.1,
            x.2.2.1 +
              {Item.node
                  { id := x.1, round := x.2.2.2.1, step := Step.init, value := false, dec := Dec.undecided,
                    vt := x.2.2.2.2.1, vf := x.2.2.2.2.2.1, va := x.2.2.2.2.2.2.1 }})] := by
  maude_certify_comp

theorem otr_inv1.obligation_4 :
    sound (mayFire voteF okP)
      [Unifier.bind fun (x : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) =>
          ((x.2.2.2.2.2, x.1, ∅, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, ∅), x.2.2.2.2.2, {x.1},
            {Item.node
                { id := x.1, round := x.2.1, step := Step.init, value := false, dec := Dec.undecided, vt := x.2.2.1,
                  vf := x.2.2.2.1, va := x.2.2.2.2.1 }}),
        Unifier.bind fun (x : ℕ × Items × ℕ × ℕ × ℕ × ℕ × ℕ) =>
          ((x.2.2.2.2.2.2, x.1, ∅, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.1), x.2.2.2.2.2.2, {x.1},
            x.2.1 +
              {Item.node
                  { id := x.1, round := x.2.2.1, step := Step.init, value := false, dec := Dec.undecided,
                    vt := x.2.2.2.1, vf := x.2.2.2.2.1, va := x.2.2.2.2.2.1 }}),
        Unifier.bind fun (x : ℕ × OidSet × ℕ × ℕ × ℕ × ℕ × ℕ) =>
          ((x.2.2.2.2.2.2, x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, ∅), x.2.2.2.2.2.2, {x.1} + x.2.1,
            {Item.node
                { id := x.1, round := x.2.2.1, step := Step.init, value := false, dec := Dec.undecided, vt := x.2.2.2.1,
                  vf := x.2.2.2.2.1, va := x.2.2.2.2.2.1 }}),
        Unifier.bind fun (x : ℕ × OidSet × Items × ℕ × ℕ × ℕ × ℕ × ℕ) =>
          ((x.2.2.2.2.2.2.2, x.1, x.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.1),
            x.2.2.2.2.2.2.2, {x.1} + x.2.1,
            x.2.2.1 +
              {Item.node
                  { id := x.1, round := x.2.2.2.1, step := Step.init, value := false, dec := Dec.undecided,
                    vt := x.2.2.2.2.1, vf := x.2.2.2.2.2.1, va := x.2.2.2.2.2.2.1 }})] := by
  simp only [sound, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  repeat' apply And.intro
  all_goals
    rintro γ ⟨x, rfl⟩
    simp only [unifiedBy, mayFire, voteF, okP]
    try ac_rfl

theorem otr_inv1.obligation_5 :
    complete (mayFire recvT okP)
      [Unifier.bind fun (x : ℕ × OidSet × ℕ × Bool × Dec × ℕ × ℕ × ℕ × ℕ × ℕ) =>
          ((x.2.2.2.2.2.2.2.2.2, x.2.1, x.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1, ∅, ∅),
            x.2.2.2.2.2.2.2.2.2, x.2.1,
            {Item.node
                  { id := x.1, round := x.2.2.1, step := Step.wait, value := x.2.2.2.1, dec := x.2.2.2.2.1,
                    vt := x.2.2.2.2.2.1, vf := x.2.2.2.2.2.2.1, va := x.2.2.2.2.2.2.2.1 }} +
              {Item.msg true x.2.2.1 x.2.2.2.2.2.2.2.2.1 {x.1}}),
        Unifier.bind fun (x : ℕ × ℕ × OidSet × ℕ × Bool × Dec × ℕ × ℕ × ℕ × ℕ × OidSet) =>
          ((x.2.1, x.2.2.1, x.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2, ∅),
            x.2.1, x.2.2.1,
            {Item.node
                  { id := x.1, round := x.2.2.2.1, step := Step.wait, value := x.2.2.2.2.1, dec := x.2.2.2.2.2.1,
                    vt := x.2.2.2.2.2.2.1, vf := x.2.2.2.2.2.2.2.1, va := x.2.2.2.2.2.2.2.2.1 }} +
              {Item.msg true x.2.2.2.1 x.2.2.2.2.2.2.2.2.2.1 ({x.1} + x.2.2.2.2.2.2.2.2.2.2)}),
        Unifier.bind fun (x : Items × ℕ × OidSet × ℕ × ℕ × Bool × Dec × ℕ × ℕ × ℕ × ℕ) =>
          ((x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2, ∅, x.1),
            x.2.1, x.2.2.1,
            x.1 +
                {Item.node
                    { id := x.2.2.2.1, round := x.2.2.2.2.1, step := Step.wait, value := x.2.2.2.2.2.1,
                      dec := x.2.2.2.2.2.2.1, vt := x.2.2.2.2.2.2.2.1, vf := x.2.2.2.2.2.2.2.2.1,
                      va := x.2.2.2.2.2.2.2.2.2.1 }} +
              {Item.msg true x.2.2.2.2.1 x.2.2.2.2.2.2.2.2.2.2 {x.2.2.2.1}}),
        Unifier.bind fun (x : Items × OidSet × ℕ × OidSet × ℕ × ℕ × Bool × Dec × ℕ × ℕ × ℕ × ℕ) =>
          ((x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2, x.2.1, x.1),
            x.2.2.1, x.2.2.2.1,
            x.1 +
                {Item.node
                    { id := x.2.2.2.2.1, round := x.2.2.2.2.2.1, step := Step.wait, value := x.2.2.2.2.2.2.1,
                      dec := x.2.2.2.2.2.2.2.1, vt := x.2.2.2.2.2.2.2.2.1, vf := x.2.2.2.2.2.2.2.2.2.1,
                      va := x.2.2.2.2.2.2.2.2.2.2.1 }} +
              {Item.msg true x.2.2.2.2.2.1 x.2.2.2.2.2.2.2.2.2.2.2 ({x.2.2.2.2.1} + x.2.1)})] := by
  maude_certify_comp

theorem otr_inv1.obligation_6 :
    sound (mayFire recvT okP)
      [Unifier.bind fun (x : ℕ × OidSet × ℕ × Bool × Dec × ℕ × ℕ × ℕ × ℕ × ℕ) =>
          ((x.2.2.2.2.2.2.2.2.2, x.2.1, x.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1, ∅, ∅),
            x.2.2.2.2.2.2.2.2.2, x.2.1,
            {Item.node
                  { id := x.1, round := x.2.2.1, step := Step.wait, value := x.2.2.2.1, dec := x.2.2.2.2.1,
                    vt := x.2.2.2.2.2.1, vf := x.2.2.2.2.2.2.1, va := x.2.2.2.2.2.2.2.1 }} +
              {Item.msg true x.2.2.1 x.2.2.2.2.2.2.2.2.1 {x.1}}),
        Unifier.bind fun (x : ℕ × ℕ × OidSet × ℕ × Bool × Dec × ℕ × ℕ × ℕ × ℕ × OidSet) =>
          ((x.2.1, x.2.2.1, x.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2, ∅),
            x.2.1, x.2.2.1,
            {Item.node
                  { id := x.1, round := x.2.2.2.1, step := Step.wait, value := x.2.2.2.2.1, dec := x.2.2.2.2.2.1,
                    vt := x.2.2.2.2.2.2.1, vf := x.2.2.2.2.2.2.2.1, va := x.2.2.2.2.2.2.2.2.1 }} +
              {Item.msg true x.2.2.2.1 x.2.2.2.2.2.2.2.2.2.1 ({x.1} + x.2.2.2.2.2.2.2.2.2.2)}),
        Unifier.bind fun (x : Items × ℕ × OidSet × ℕ × ℕ × Bool × Dec × ℕ × ℕ × ℕ × ℕ) =>
          ((x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2, ∅, x.1),
            x.2.1, x.2.2.1,
            x.1 +
                {Item.node
                    { id := x.2.2.2.1, round := x.2.2.2.2.1, step := Step.wait, value := x.2.2.2.2.2.1,
                      dec := x.2.2.2.2.2.2.1, vt := x.2.2.2.2.2.2.2.1, vf := x.2.2.2.2.2.2.2.2.1,
                      va := x.2.2.2.2.2.2.2.2.2.1 }} +
              {Item.msg true x.2.2.2.2.1 x.2.2.2.2.2.2.2.2.2.2 {x.2.2.2.1}}),
        Unifier.bind fun (x : Items × OidSet × ℕ × OidSet × ℕ × ℕ × Bool × Dec × ℕ × ℕ × ℕ × ℕ) =>
          ((x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2, x.2.1, x.1),
            x.2.2.1, x.2.2.2.1,
            x.1 +
                {Item.node
                    { id := x.2.2.2.2.1, round := x.2.2.2.2.2.1, step := Step.wait, value := x.2.2.2.2.2.2.1,
                      dec := x.2.2.2.2.2.2.2.1, vt := x.2.2.2.2.2.2.2.2.1, vf := x.2.2.2.2.2.2.2.2.2.1,
                      va := x.2.2.2.2.2.2.2.2.2.2.1 }} +
              {Item.msg true x.2.2.2.2.2.1 x.2.2.2.2.2.2.2.2.2.2.2 ({x.2.2.2.2.1} + x.2.1)})] := by
  simp only [sound, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  repeat' apply And.intro
  all_goals
    rintro γ ⟨x, rfl⟩
    simp only [unifiedBy, mayFire, recvT, okP]
    try ac_rfl

theorem otr_inv1.obligation_7 :
    complete (mayFire recvF okP)
      [Unifier.bind fun (x : ℕ × OidSet × ℕ × Bool × Dec × ℕ × ℕ × ℕ × ℕ × ℕ) =>
          ((x.2.2.2.2.2.2.2.2.2, x.2.1, x.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1, ∅, ∅),
            x.2.2.2.2.2.2.2.2.2, x.2.1,
            {Item.node
                  { id := x.1, round := x.2.2.1, step := Step.wait, value := x.2.2.2.1, dec := x.2.2.2.2.1,
                    vt := x.2.2.2.2.2.1, vf := x.2.2.2.2.2.2.1, va := x.2.2.2.2.2.2.2.1 }} +
              {Item.msg false x.2.2.1 x.2.2.2.2.2.2.2.2.1 {x.1}}),
        Unifier.bind fun (x : ℕ × ℕ × OidSet × ℕ × Bool × Dec × ℕ × ℕ × ℕ × ℕ × OidSet) =>
          ((x.2.1, x.2.2.1, x.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2, ∅),
            x.2.1, x.2.2.1,
            {Item.node
                  { id := x.1, round := x.2.2.2.1, step := Step.wait, value := x.2.2.2.2.1, dec := x.2.2.2.2.2.1,
                    vt := x.2.2.2.2.2.2.1, vf := x.2.2.2.2.2.2.2.1, va := x.2.2.2.2.2.2.2.2.1 }} +
              {Item.msg false x.2.2.2.1 x.2.2.2.2.2.2.2.2.2.1 ({x.1} + x.2.2.2.2.2.2.2.2.2.2)}),
        Unifier.bind fun (x : Items × ℕ × OidSet × ℕ × ℕ × Bool × Dec × ℕ × ℕ × ℕ × ℕ) =>
          ((x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2, ∅, x.1),
            x.2.1, x.2.2.1,
            x.1 +
                {Item.node
                    { id := x.2.2.2.1, round := x.2.2.2.2.1, step := Step.wait, value := x.2.2.2.2.2.1,
                      dec := x.2.2.2.2.2.2.1, vt := x.2.2.2.2.2.2.2.1, vf := x.2.2.2.2.2.2.2.2.1,
                      va := x.2.2.2.2.2.2.2.2.2.1 }} +
              {Item.msg false x.2.2.2.2.1 x.2.2.2.2.2.2.2.2.2.2 {x.2.2.2.1}}),
        Unifier.bind fun (x : Items × OidSet × ℕ × OidSet × ℕ × ℕ × Bool × Dec × ℕ × ℕ × ℕ × ℕ) =>
          ((x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2, x.2.1, x.1),
            x.2.2.1, x.2.2.2.1,
            x.1 +
                {Item.node
                    { id := x.2.2.2.2.1, round := x.2.2.2.2.2.1, step := Step.wait, value := x.2.2.2.2.2.2.1,
                      dec := x.2.2.2.2.2.2.2.1, vt := x.2.2.2.2.2.2.2.2.1, vf := x.2.2.2.2.2.2.2.2.2.1,
                      va := x.2.2.2.2.2.2.2.2.2.2.1 }} +
              {Item.msg false x.2.2.2.2.2.1 x.2.2.2.2.2.2.2.2.2.2.2 ({x.2.2.2.2.1} + x.2.1)})] := by
  maude_certify_comp

theorem otr_inv1.obligation_8 :
    sound (mayFire recvF okP)
      [Unifier.bind fun (x : ℕ × OidSet × ℕ × Bool × Dec × ℕ × ℕ × ℕ × ℕ × ℕ) =>
          ((x.2.2.2.2.2.2.2.2.2, x.2.1, x.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1, ∅, ∅),
            x.2.2.2.2.2.2.2.2.2, x.2.1,
            {Item.node
                  { id := x.1, round := x.2.2.1, step := Step.wait, value := x.2.2.2.1, dec := x.2.2.2.2.1,
                    vt := x.2.2.2.2.2.1, vf := x.2.2.2.2.2.2.1, va := x.2.2.2.2.2.2.2.1 }} +
              {Item.msg false x.2.2.1 x.2.2.2.2.2.2.2.2.1 {x.1}}),
        Unifier.bind fun (x : ℕ × ℕ × OidSet × ℕ × Bool × Dec × ℕ × ℕ × ℕ × ℕ × OidSet) =>
          ((x.2.1, x.2.2.1, x.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2, ∅),
            x.2.1, x.2.2.1,
            {Item.node
                  { id := x.1, round := x.2.2.2.1, step := Step.wait, value := x.2.2.2.2.1, dec := x.2.2.2.2.2.1,
                    vt := x.2.2.2.2.2.2.1, vf := x.2.2.2.2.2.2.2.1, va := x.2.2.2.2.2.2.2.2.1 }} +
              {Item.msg false x.2.2.2.1 x.2.2.2.2.2.2.2.2.2.1 ({x.1} + x.2.2.2.2.2.2.2.2.2.2)}),
        Unifier.bind fun (x : Items × ℕ × OidSet × ℕ × ℕ × Bool × Dec × ℕ × ℕ × ℕ × ℕ) =>
          ((x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2, ∅, x.1),
            x.2.1, x.2.2.1,
            x.1 +
                {Item.node
                    { id := x.2.2.2.1, round := x.2.2.2.2.1, step := Step.wait, value := x.2.2.2.2.2.1,
                      dec := x.2.2.2.2.2.2.1, vt := x.2.2.2.2.2.2.2.1, vf := x.2.2.2.2.2.2.2.2.1,
                      va := x.2.2.2.2.2.2.2.2.2.1 }} +
              {Item.msg false x.2.2.2.2.1 x.2.2.2.2.2.2.2.2.2.2 {x.2.2.2.1}}),
        Unifier.bind fun (x : Items × OidSet × ℕ × OidSet × ℕ × ℕ × Bool × Dec × ℕ × ℕ × ℕ × ℕ) =>
          ((x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2, x.2.1, x.1),
            x.2.2.1, x.2.2.2.1,
            x.1 +
                {Item.node
                    { id := x.2.2.2.2.1, round := x.2.2.2.2.2.1, step := Step.wait, value := x.2.2.2.2.2.2.1,
                      dec := x.2.2.2.2.2.2.2.1, vt := x.2.2.2.2.2.2.2.2.1, vf := x.2.2.2.2.2.2.2.2.2.1,
                      va := x.2.2.2.2.2.2.2.2.2.2.1 }} +
              {Item.msg false x.2.2.2.2.2.1 x.2.2.2.2.2.2.2.2.2.2.2 ({x.2.2.2.2.1} + x.2.1)})] := by
  simp only [sound, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  repeat' apply And.intro
  all_goals
    rintro γ ⟨x, rfl⟩
    simp only [unifiedBy, mayFire, recvF, okP]
    try ac_rfl

theorem otr_inv1.obligation_9 :
    complete (mayFire decideT okP)
      [Unifier.bind fun (x : ℕ × ℕ × Bool × ℕ × ℕ × ℕ × ℕ × OidSet) =>
          ((x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2, x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, ∅),
            x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2,
            {Item.node
                { id := x.1, round := x.2.1, step := Step.wait, value := x.2.2.1, dec := Dec.undecided, vt := x.2.2.2.1,
                  vf := x.2.2.2.2.1, va := x.2.2.2.2.2.1 }}),
        Unifier.bind fun (x : Items × ℕ × ℕ × Bool × ℕ × ℕ × ℕ × ℕ × OidSet) =>
          ((x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
              x.2.2.2.2.2.2.1, x.1),
            x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2,
            x.1 +
              {Item.node
                  { id := x.2.1, round := x.2.2.1, step := Step.wait, value := x.2.2.2.1, dec := Dec.undecided,
                    vt := x.2.2.2.2.1, vf := x.2.2.2.2.2.1, va := x.2.2.2.2.2.2.1 }})] := by
  maude_certify_comp

theorem otr_inv1.obligation_10 :
    sound (mayFire decideT okP)
      [Unifier.bind fun (x : ℕ × ℕ × Bool × ℕ × ℕ × ℕ × ℕ × OidSet) =>
          ((x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2, x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, ∅),
            x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2,
            {Item.node
                { id := x.1, round := x.2.1, step := Step.wait, value := x.2.2.1, dec := Dec.undecided, vt := x.2.2.2.1,
                  vf := x.2.2.2.2.1, va := x.2.2.2.2.2.1 }}),
        Unifier.bind fun (x : Items × ℕ × ℕ × Bool × ℕ × ℕ × ℕ × ℕ × OidSet) =>
          ((x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
              x.2.2.2.2.2.2.1, x.1),
            x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2,
            x.1 +
              {Item.node
                  { id := x.2.1, round := x.2.2.1, step := Step.wait, value := x.2.2.2.1, dec := Dec.undecided,
                    vt := x.2.2.2.2.1, vf := x.2.2.2.2.2.1, va := x.2.2.2.2.2.2.1 }})] := by
  simp only [sound, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  repeat' apply And.intro
  all_goals
    rintro γ ⟨x, rfl⟩
    simp only [unifiedBy, mayFire, decideT, okP]
    try ac_rfl

theorem otr_inv1.obligation_11 :
    complete (mayFire decideF okP)
      [Unifier.bind fun (x : ℕ × ℕ × Bool × ℕ × ℕ × ℕ × ℕ × OidSet) =>
          ((x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2, x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, ∅),
            x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2,
            {Item.node
                { id := x.1, round := x.2.1, step := Step.wait, value := x.2.2.1, dec := Dec.undecided, vt := x.2.2.2.1,
                  vf := x.2.2.2.2.1, va := x.2.2.2.2.2.1 }}),
        Unifier.bind fun (x : Items × ℕ × ℕ × Bool × ℕ × ℕ × ℕ × ℕ × OidSet) =>
          ((x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
              x.2.2.2.2.2.2.1, x.1),
            x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2,
            x.1 +
              {Item.node
                  { id := x.2.1, round := x.2.2.1, step := Step.wait, value := x.2.2.2.1, dec := Dec.undecided,
                    vt := x.2.2.2.2.1, vf := x.2.2.2.2.2.1, va := x.2.2.2.2.2.2.1 }})] := by
  maude_certify_comp

theorem otr_inv1.obligation_12 :
    sound (mayFire decideF okP)
      [Unifier.bind fun (x : ℕ × ℕ × Bool × ℕ × ℕ × ℕ × ℕ × OidSet) =>
          ((x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2, x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, ∅),
            x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2,
            {Item.node
                { id := x.1, round := x.2.1, step := Step.wait, value := x.2.2.1, dec := Dec.undecided, vt := x.2.2.2.1,
                  vf := x.2.2.2.2.1, va := x.2.2.2.2.2.1 }}),
        Unifier.bind fun (x : Items × ℕ × ℕ × Bool × ℕ × ℕ × ℕ × ℕ × OidSet) =>
          ((x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
              x.2.2.2.2.2.2.1, x.1),
            x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2,
            x.1 +
              {Item.node
                  { id := x.2.1, round := x.2.2.1, step := Step.wait, value := x.2.2.2.1, dec := Dec.undecided,
                    vt := x.2.2.2.2.1, vf := x.2.2.2.2.2.1, va := x.2.2.2.2.2.2.1 }})] := by
  simp only [sound, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  repeat' apply And.intro
  all_goals
    rintro γ ⟨x, rfl⟩
    simp only [unifiedBy, mayFire, decideF, okP]
    try ac_rfl

theorem otr_inv1.obligation_13 :
    complete (mayFire updateT okP)
      [Unifier.bind fun (x : ℕ × ℕ × Bool × ℕ × ℕ × ℕ × ℕ × OidSet) =>
          ((x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2, x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, ∅),
            x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2,
            {Item.node
                { id := x.1, round := x.2.1, step := Step.wait, value := x.2.2.1, dec := Dec.undecided, vt := x.2.2.2.1,
                  vf := x.2.2.2.2.1, va := x.2.2.2.2.2.1 }}),
        Unifier.bind fun (x : Items × ℕ × ℕ × Bool × ℕ × ℕ × ℕ × ℕ × OidSet) =>
          ((x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
              x.2.2.2.2.2.2.1, x.1),
            x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2,
            x.1 +
              {Item.node
                  { id := x.2.1, round := x.2.2.1, step := Step.wait, value := x.2.2.2.1, dec := Dec.undecided,
                    vt := x.2.2.2.2.1, vf := x.2.2.2.2.2.1, va := x.2.2.2.2.2.2.1 }})] := by
  maude_certify_comp

theorem otr_inv1.obligation_14 :
    sound (mayFire updateT okP)
      [Unifier.bind fun (x : ℕ × ℕ × Bool × ℕ × ℕ × ℕ × ℕ × OidSet) =>
          ((x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2, x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, ∅),
            x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2,
            {Item.node
                { id := x.1, round := x.2.1, step := Step.wait, value := x.2.2.1, dec := Dec.undecided, vt := x.2.2.2.1,
                  vf := x.2.2.2.2.1, va := x.2.2.2.2.2.1 }}),
        Unifier.bind fun (x : Items × ℕ × ℕ × Bool × ℕ × ℕ × ℕ × ℕ × OidSet) =>
          ((x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
              x.2.2.2.2.2.2.1, x.1),
            x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2,
            x.1 +
              {Item.node
                  { id := x.2.1, round := x.2.2.1, step := Step.wait, value := x.2.2.2.1, dec := Dec.undecided,
                    vt := x.2.2.2.2.1, vf := x.2.2.2.2.2.1, va := x.2.2.2.2.2.2.1 }})] := by
  simp only [sound, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  repeat' apply And.intro
  all_goals
    rintro γ ⟨x, rfl⟩
    simp only [unifiedBy, mayFire, updateT, okP]
    try ac_rfl

theorem otr_inv1.obligation_15 :
    complete (mayFire updateF okP)
      [Unifier.bind fun (x : ℕ × ℕ × Bool × ℕ × ℕ × ℕ × ℕ × OidSet) =>
          ((x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2, x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, ∅),
            x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2,
            {Item.node
                { id := x.1, round := x.2.1, step := Step.wait, value := x.2.2.1, dec := Dec.undecided, vt := x.2.2.2.1,
                  vf := x.2.2.2.2.1, va := x.2.2.2.2.2.1 }}),
        Unifier.bind fun (x : Items × ℕ × ℕ × Bool × ℕ × ℕ × ℕ × ℕ × OidSet) =>
          ((x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
              x.2.2.2.2.2.2.1, x.1),
            x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2,
            x.1 +
              {Item.node
                  { id := x.2.1, round := x.2.2.1, step := Step.wait, value := x.2.2.2.1, dec := Dec.undecided,
                    vt := x.2.2.2.2.1, vf := x.2.2.2.2.2.1, va := x.2.2.2.2.2.2.1 }})] := by
  maude_certify_comp

theorem otr_inv1.obligation_16 :
    sound (mayFire updateF okP)
      [Unifier.bind fun (x : ℕ × ℕ × Bool × ℕ × ℕ × ℕ × ℕ × OidSet) =>
          ((x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2, x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, ∅),
            x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2,
            {Item.node
                { id := x.1, round := x.2.1, step := Step.wait, value := x.2.2.1, dec := Dec.undecided, vt := x.2.2.2.1,
                  vf := x.2.2.2.2.1, va := x.2.2.2.2.2.1 }}),
        Unifier.bind fun (x : Items × ℕ × ℕ × Bool × ℕ × ℕ × ℕ × ℕ × OidSet) =>
          ((x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
              x.2.2.2.2.2.2.1, x.1),
            x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2,
            x.1 +
              {Item.node
                  { id := x.2.1, round := x.2.2.1, step := Step.wait, value := x.2.2.2.1, dec := Dec.undecided,
                    vt := x.2.2.2.2.1, vf := x.2.2.2.2.2.1, va := x.2.2.2.2.2.2.1 }})] := by
  simp only [sound, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  repeat' apply And.intro
  all_goals
    rintro γ ⟨x, rfl⟩
    simp only [unifiedBy, mayFire, updateF, okP]
    try ac_rfl

theorem otr_inv1.obligation_17 :
    complete (mayFire loss okP)
      [Unifier.bind fun (x : Bool × ℕ × ℕ × OidSet × ℕ × OidSet) =>
          ((x.2.2.2.2.1, x.2.2.2.2.2, x.1, x.2.1, x.2.2.1, x.2.2.2.1, ∅), x.2.2.2.2.1, x.2.2.2.2.2,
            {Item.msg x.1 x.2.1 x.2.2.1 x.2.2.2.1}),
        Unifier.bind fun (x : Items × Bool × ℕ × ℕ × OidSet × ℕ × OidSet) =>
          ((x.2.2.2.2.2.1, x.2.2.2.2.2.2, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.1), x.2.2.2.2.2.1, x.2.2.2.2.2.2,
            x.1 + {Item.msg x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1})] := by
  maude_certify_comp

theorem otr_inv1.obligation_18 :
    sound (mayFire loss okP)
      [Unifier.bind fun (x : Bool × ℕ × ℕ × OidSet × ℕ × OidSet) =>
          ((x.2.2.2.2.1, x.2.2.2.2.2, x.1, x.2.1, x.2.2.1, x.2.2.2.1, ∅), x.2.2.2.2.1, x.2.2.2.2.2,
            {Item.msg x.1 x.2.1 x.2.2.1 x.2.2.2.1}),
        Unifier.bind fun (x : Items × Bool × ℕ × ℕ × OidSet × ℕ × OidSet) =>
          ((x.2.2.2.2.2.1, x.2.2.2.2.2.2, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.1), x.2.2.2.2.2.1, x.2.2.2.2.2.2,
            x.1 + {Item.msg x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1})] := by
  simp only [sound, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  repeat' apply And.intro
  all_goals
    rintro γ ⟨x, rfl⟩
    simp only [unifiedBy, mayFire, loss, okP]
    try ac_rfl

theorem otr_inv3.obligation_1 :
    complete (mayFire voteT pastP)
      [Unifier.bind fun (x : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) =>
          ((x.2.2.2.2.2, x.1, ∅, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, ∅), x.2.2.2.2.2, {x.1},
            {Item.node
                { id := x.1, round := x.2.1, step := Step.init, value := true, dec := Dec.undecided, vt := x.2.2.1,
                  vf := x.2.2.2.1, va := x.2.2.2.2.1 }}),
        Unifier.bind fun (x : ℕ × Items × ℕ × ℕ × ℕ × ℕ × ℕ) =>
          ((x.2.2.2.2.2.2, x.1, ∅, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.1), x.2.2.2.2.2.2, {x.1},
            x.2.1 +
              {Item.node
                  { id := x.1, round := x.2.2.1, step := Step.init, value := true, dec := Dec.undecided,
                    vt := x.2.2.2.1, vf := x.2.2.2.2.1, va := x.2.2.2.2.2.1 }}),
        Unifier.bind fun (x : ℕ × OidSet × ℕ × ℕ × ℕ × ℕ × ℕ) =>
          ((x.2.2.2.2.2.2, x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, ∅), x.2.2.2.2.2.2, {x.1} + x.2.1,
            {Item.node
                { id := x.1, round := x.2.2.1, step := Step.init, value := true, dec := Dec.undecided, vt := x.2.2.2.1,
                  vf := x.2.2.2.2.1, va := x.2.2.2.2.2.1 }}),
        Unifier.bind fun (x : ℕ × OidSet × Items × ℕ × ℕ × ℕ × ℕ × ℕ) =>
          ((x.2.2.2.2.2.2.2, x.1, x.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.1),
            x.2.2.2.2.2.2.2, {x.1} + x.2.1,
            x.2.2.1 +
              {Item.node
                  { id := x.1, round := x.2.2.2.1, step := Step.init, value := true, dec := Dec.undecided,
                    vt := x.2.2.2.2.1, vf := x.2.2.2.2.2.1, va := x.2.2.2.2.2.2.1 }})] := by
  maude_certify_comp

theorem otr_inv3.obligation_2 :
    sound (mayFire voteT pastP)
      [Unifier.bind fun (x : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) =>
          ((x.2.2.2.2.2, x.1, ∅, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, ∅), x.2.2.2.2.2, {x.1},
            {Item.node
                { id := x.1, round := x.2.1, step := Step.init, value := true, dec := Dec.undecided, vt := x.2.2.1,
                  vf := x.2.2.2.1, va := x.2.2.2.2.1 }}),
        Unifier.bind fun (x : ℕ × Items × ℕ × ℕ × ℕ × ℕ × ℕ) =>
          ((x.2.2.2.2.2.2, x.1, ∅, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.1), x.2.2.2.2.2.2, {x.1},
            x.2.1 +
              {Item.node
                  { id := x.1, round := x.2.2.1, step := Step.init, value := true, dec := Dec.undecided,
                    vt := x.2.2.2.1, vf := x.2.2.2.2.1, va := x.2.2.2.2.2.1 }}),
        Unifier.bind fun (x : ℕ × OidSet × ℕ × ℕ × ℕ × ℕ × ℕ) =>
          ((x.2.2.2.2.2.2, x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, ∅), x.2.2.2.2.2.2, {x.1} + x.2.1,
            {Item.node
                { id := x.1, round := x.2.2.1, step := Step.init, value := true, dec := Dec.undecided, vt := x.2.2.2.1,
                  vf := x.2.2.2.2.1, va := x.2.2.2.2.2.1 }}),
        Unifier.bind fun (x : ℕ × OidSet × Items × ℕ × ℕ × ℕ × ℕ × ℕ) =>
          ((x.2.2.2.2.2.2.2, x.1, x.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.1),
            x.2.2.2.2.2.2.2, {x.1} + x.2.1,
            x.2.2.1 +
              {Item.node
                  { id := x.1, round := x.2.2.2.1, step := Step.init, value := true, dec := Dec.undecided,
                    vt := x.2.2.2.2.1, vf := x.2.2.2.2.2.1, va := x.2.2.2.2.2.2.1 }})] := by
  simp only [sound, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  repeat' apply And.intro
  all_goals
    rintro γ ⟨x, rfl⟩
    simp only [unifiedBy, mayFire, voteT, pastP]
    try ac_rfl

theorem otr_inv3.obligation_3 :
    complete (mayFire voteF pastP)
      [Unifier.bind fun (x : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) =>
          ((x.2.2.2.2.2, x.1, ∅, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, ∅), x.2.2.2.2.2, {x.1},
            {Item.node
                { id := x.1, round := x.2.1, step := Step.init, value := false, dec := Dec.undecided, vt := x.2.2.1,
                  vf := x.2.2.2.1, va := x.2.2.2.2.1 }}),
        Unifier.bind fun (x : ℕ × Items × ℕ × ℕ × ℕ × ℕ × ℕ) =>
          ((x.2.2.2.2.2.2, x.1, ∅, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.1), x.2.2.2.2.2.2, {x.1},
            x.2.1 +
              {Item.node
                  { id := x.1, round := x.2.2.1, step := Step.init, value := false, dec := Dec.undecided,
                    vt := x.2.2.2.1, vf := x.2.2.2.2.1, va := x.2.2.2.2.2.1 }}),
        Unifier.bind fun (x : ℕ × OidSet × ℕ × ℕ × ℕ × ℕ × ℕ) =>
          ((x.2.2.2.2.2.2, x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, ∅), x.2.2.2.2.2.2, {x.1} + x.2.1,
            {Item.node
                { id := x.1, round := x.2.2.1, step := Step.init, value := false, dec := Dec.undecided, vt := x.2.2.2.1,
                  vf := x.2.2.2.2.1, va := x.2.2.2.2.2.1 }}),
        Unifier.bind fun (x : ℕ × OidSet × Items × ℕ × ℕ × ℕ × ℕ × ℕ) =>
          ((x.2.2.2.2.2.2.2, x.1, x.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.1),
            x.2.2.2.2.2.2.2, {x.1} + x.2.1,
            x.2.2.1 +
              {Item.node
                  { id := x.1, round := x.2.2.2.1, step := Step.init, value := false, dec := Dec.undecided,
                    vt := x.2.2.2.2.1, vf := x.2.2.2.2.2.1, va := x.2.2.2.2.2.2.1 }})] := by
  maude_certify_comp

theorem otr_inv3.obligation_4 :
    sound (mayFire voteF pastP)
      [Unifier.bind fun (x : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) =>
          ((x.2.2.2.2.2, x.1, ∅, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, ∅), x.2.2.2.2.2, {x.1},
            {Item.node
                { id := x.1, round := x.2.1, step := Step.init, value := false, dec := Dec.undecided, vt := x.2.2.1,
                  vf := x.2.2.2.1, va := x.2.2.2.2.1 }}),
        Unifier.bind fun (x : ℕ × Items × ℕ × ℕ × ℕ × ℕ × ℕ) =>
          ((x.2.2.2.2.2.2, x.1, ∅, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.1), x.2.2.2.2.2.2, {x.1},
            x.2.1 +
              {Item.node
                  { id := x.1, round := x.2.2.1, step := Step.init, value := false, dec := Dec.undecided,
                    vt := x.2.2.2.1, vf := x.2.2.2.2.1, va := x.2.2.2.2.2.1 }}),
        Unifier.bind fun (x : ℕ × OidSet × ℕ × ℕ × ℕ × ℕ × ℕ) =>
          ((x.2.2.2.2.2.2, x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, ∅), x.2.2.2.2.2.2, {x.1} + x.2.1,
            {Item.node
                { id := x.1, round := x.2.2.1, step := Step.init, value := false, dec := Dec.undecided, vt := x.2.2.2.1,
                  vf := x.2.2.2.2.1, va := x.2.2.2.2.2.1 }}),
        Unifier.bind fun (x : ℕ × OidSet × Items × ℕ × ℕ × ℕ × ℕ × ℕ) =>
          ((x.2.2.2.2.2.2.2, x.1, x.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.1),
            x.2.2.2.2.2.2.2, {x.1} + x.2.1,
            x.2.2.1 +
              {Item.node
                  { id := x.1, round := x.2.2.2.1, step := Step.init, value := false, dec := Dec.undecided,
                    vt := x.2.2.2.2.1, vf := x.2.2.2.2.2.1, va := x.2.2.2.2.2.2.1 }})] := by
  simp only [sound, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  repeat' apply And.intro
  all_goals
    rintro γ ⟨x, rfl⟩
    simp only [unifiedBy, mayFire, voteF, pastP]
    try ac_rfl

theorem otr_inv3.obligation_5 :
    complete (mayFire recvT pastP)
      [Unifier.bind fun (x : ℕ × OidSet × ℕ × Bool × Dec × ℕ × ℕ × ℕ × ℕ × ℕ) =>
          ((x.2.2.2.2.2.2.2.2.2, x.2.1, x.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1, ∅, ∅),
            x.2.2.2.2.2.2.2.2.2, x.2.1,
            {Item.node
                  { id := x.1, round := x.2.2.1, step := Step.wait, value := x.2.2.2.1, dec := x.2.2.2.2.1,
                    vt := x.2.2.2.2.2.1, vf := x.2.2.2.2.2.2.1, va := x.2.2.2.2.2.2.2.1 }} +
              {Item.msg true x.2.2.1 x.2.2.2.2.2.2.2.2.1 {x.1}}),
        Unifier.bind fun (x : ℕ × ℕ × OidSet × ℕ × Bool × Dec × ℕ × ℕ × ℕ × ℕ × OidSet) =>
          ((x.2.1, x.2.2.1, x.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2, ∅),
            x.2.1, x.2.2.1,
            {Item.node
                  { id := x.1, round := x.2.2.2.1, step := Step.wait, value := x.2.2.2.2.1, dec := x.2.2.2.2.2.1,
                    vt := x.2.2.2.2.2.2.1, vf := x.2.2.2.2.2.2.2.1, va := x.2.2.2.2.2.2.2.2.1 }} +
              {Item.msg true x.2.2.2.1 x.2.2.2.2.2.2.2.2.2.1 ({x.1} + x.2.2.2.2.2.2.2.2.2.2)}),
        Unifier.bind fun (x : Items × ℕ × OidSet × ℕ × ℕ × Bool × Dec × ℕ × ℕ × ℕ × ℕ) =>
          ((x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2, ∅, x.1),
            x.2.1, x.2.2.1,
            x.1 +
                {Item.node
                    { id := x.2.2.2.1, round := x.2.2.2.2.1, step := Step.wait, value := x.2.2.2.2.2.1,
                      dec := x.2.2.2.2.2.2.1, vt := x.2.2.2.2.2.2.2.1, vf := x.2.2.2.2.2.2.2.2.1,
                      va := x.2.2.2.2.2.2.2.2.2.1 }} +
              {Item.msg true x.2.2.2.2.1 x.2.2.2.2.2.2.2.2.2.2 {x.2.2.2.1}}),
        Unifier.bind fun (x : Items × OidSet × ℕ × OidSet × ℕ × ℕ × Bool × Dec × ℕ × ℕ × ℕ × ℕ) =>
          ((x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2, x.2.1, x.1),
            x.2.2.1, x.2.2.2.1,
            x.1 +
                {Item.node
                    { id := x.2.2.2.2.1, round := x.2.2.2.2.2.1, step := Step.wait, value := x.2.2.2.2.2.2.1,
                      dec := x.2.2.2.2.2.2.2.1, vt := x.2.2.2.2.2.2.2.2.1, vf := x.2.2.2.2.2.2.2.2.2.1,
                      va := x.2.2.2.2.2.2.2.2.2.2.1 }} +
              {Item.msg true x.2.2.2.2.2.1 x.2.2.2.2.2.2.2.2.2.2.2 ({x.2.2.2.2.1} + x.2.1)})] := by
  maude_certify_comp

theorem otr_inv3.obligation_6 :
    sound (mayFire recvT pastP)
      [Unifier.bind fun (x : ℕ × OidSet × ℕ × Bool × Dec × ℕ × ℕ × ℕ × ℕ × ℕ) =>
          ((x.2.2.2.2.2.2.2.2.2, x.2.1, x.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1, ∅, ∅),
            x.2.2.2.2.2.2.2.2.2, x.2.1,
            {Item.node
                  { id := x.1, round := x.2.2.1, step := Step.wait, value := x.2.2.2.1, dec := x.2.2.2.2.1,
                    vt := x.2.2.2.2.2.1, vf := x.2.2.2.2.2.2.1, va := x.2.2.2.2.2.2.2.1 }} +
              {Item.msg true x.2.2.1 x.2.2.2.2.2.2.2.2.1 {x.1}}),
        Unifier.bind fun (x : ℕ × ℕ × OidSet × ℕ × Bool × Dec × ℕ × ℕ × ℕ × ℕ × OidSet) =>
          ((x.2.1, x.2.2.1, x.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2, ∅),
            x.2.1, x.2.2.1,
            {Item.node
                  { id := x.1, round := x.2.2.2.1, step := Step.wait, value := x.2.2.2.2.1, dec := x.2.2.2.2.2.1,
                    vt := x.2.2.2.2.2.2.1, vf := x.2.2.2.2.2.2.2.1, va := x.2.2.2.2.2.2.2.2.1 }} +
              {Item.msg true x.2.2.2.1 x.2.2.2.2.2.2.2.2.2.1 ({x.1} + x.2.2.2.2.2.2.2.2.2.2)}),
        Unifier.bind fun (x : Items × ℕ × OidSet × ℕ × ℕ × Bool × Dec × ℕ × ℕ × ℕ × ℕ) =>
          ((x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2, ∅, x.1),
            x.2.1, x.2.2.1,
            x.1 +
                {Item.node
                    { id := x.2.2.2.1, round := x.2.2.2.2.1, step := Step.wait, value := x.2.2.2.2.2.1,
                      dec := x.2.2.2.2.2.2.1, vt := x.2.2.2.2.2.2.2.1, vf := x.2.2.2.2.2.2.2.2.1,
                      va := x.2.2.2.2.2.2.2.2.2.1 }} +
              {Item.msg true x.2.2.2.2.1 x.2.2.2.2.2.2.2.2.2.2 {x.2.2.2.1}}),
        Unifier.bind fun (x : Items × OidSet × ℕ × OidSet × ℕ × ℕ × Bool × Dec × ℕ × ℕ × ℕ × ℕ) =>
          ((x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2, x.2.1, x.1),
            x.2.2.1, x.2.2.2.1,
            x.1 +
                {Item.node
                    { id := x.2.2.2.2.1, round := x.2.2.2.2.2.1, step := Step.wait, value := x.2.2.2.2.2.2.1,
                      dec := x.2.2.2.2.2.2.2.1, vt := x.2.2.2.2.2.2.2.2.1, vf := x.2.2.2.2.2.2.2.2.2.1,
                      va := x.2.2.2.2.2.2.2.2.2.2.1 }} +
              {Item.msg true x.2.2.2.2.2.1 x.2.2.2.2.2.2.2.2.2.2.2 ({x.2.2.2.2.1} + x.2.1)})] := by
  simp only [sound, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  repeat' apply And.intro
  all_goals
    rintro γ ⟨x, rfl⟩
    simp only [unifiedBy, mayFire, recvT, pastP]
    try ac_rfl

theorem otr_inv3.obligation_7 :
    complete (mayFire recvF pastP)
      [Unifier.bind fun (x : ℕ × OidSet × ℕ × Bool × Dec × ℕ × ℕ × ℕ × ℕ × ℕ) =>
          ((x.2.2.2.2.2.2.2.2.2, x.2.1, x.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1, ∅, ∅),
            x.2.2.2.2.2.2.2.2.2, x.2.1,
            {Item.node
                  { id := x.1, round := x.2.2.1, step := Step.wait, value := x.2.2.2.1, dec := x.2.2.2.2.1,
                    vt := x.2.2.2.2.2.1, vf := x.2.2.2.2.2.2.1, va := x.2.2.2.2.2.2.2.1 }} +
              {Item.msg false x.2.2.1 x.2.2.2.2.2.2.2.2.1 {x.1}}),
        Unifier.bind fun (x : ℕ × ℕ × OidSet × ℕ × Bool × Dec × ℕ × ℕ × ℕ × ℕ × OidSet) =>
          ((x.2.1, x.2.2.1, x.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2, ∅),
            x.2.1, x.2.2.1,
            {Item.node
                  { id := x.1, round := x.2.2.2.1, step := Step.wait, value := x.2.2.2.2.1, dec := x.2.2.2.2.2.1,
                    vt := x.2.2.2.2.2.2.1, vf := x.2.2.2.2.2.2.2.1, va := x.2.2.2.2.2.2.2.2.1 }} +
              {Item.msg false x.2.2.2.1 x.2.2.2.2.2.2.2.2.2.1 ({x.1} + x.2.2.2.2.2.2.2.2.2.2)}),
        Unifier.bind fun (x : Items × ℕ × OidSet × ℕ × ℕ × Bool × Dec × ℕ × ℕ × ℕ × ℕ) =>
          ((x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2, ∅, x.1),
            x.2.1, x.2.2.1,
            x.1 +
                {Item.node
                    { id := x.2.2.2.1, round := x.2.2.2.2.1, step := Step.wait, value := x.2.2.2.2.2.1,
                      dec := x.2.2.2.2.2.2.1, vt := x.2.2.2.2.2.2.2.1, vf := x.2.2.2.2.2.2.2.2.1,
                      va := x.2.2.2.2.2.2.2.2.2.1 }} +
              {Item.msg false x.2.2.2.2.1 x.2.2.2.2.2.2.2.2.2.2 {x.2.2.2.1}}),
        Unifier.bind fun (x : Items × OidSet × ℕ × OidSet × ℕ × ℕ × Bool × Dec × ℕ × ℕ × ℕ × ℕ) =>
          ((x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2, x.2.1, x.1),
            x.2.2.1, x.2.2.2.1,
            x.1 +
                {Item.node
                    { id := x.2.2.2.2.1, round := x.2.2.2.2.2.1, step := Step.wait, value := x.2.2.2.2.2.2.1,
                      dec := x.2.2.2.2.2.2.2.1, vt := x.2.2.2.2.2.2.2.2.1, vf := x.2.2.2.2.2.2.2.2.2.1,
                      va := x.2.2.2.2.2.2.2.2.2.2.1 }} +
              {Item.msg false x.2.2.2.2.2.1 x.2.2.2.2.2.2.2.2.2.2.2 ({x.2.2.2.2.1} + x.2.1)})] := by
  maude_certify_comp

theorem otr_inv3.obligation_8 :
    sound (mayFire recvF pastP)
      [Unifier.bind fun (x : ℕ × OidSet × ℕ × Bool × Dec × ℕ × ℕ × ℕ × ℕ × ℕ) =>
          ((x.2.2.2.2.2.2.2.2.2, x.2.1, x.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1, ∅, ∅),
            x.2.2.2.2.2.2.2.2.2, x.2.1,
            {Item.node
                  { id := x.1, round := x.2.2.1, step := Step.wait, value := x.2.2.2.1, dec := x.2.2.2.2.1,
                    vt := x.2.2.2.2.2.1, vf := x.2.2.2.2.2.2.1, va := x.2.2.2.2.2.2.2.1 }} +
              {Item.msg false x.2.2.1 x.2.2.2.2.2.2.2.2.1 {x.1}}),
        Unifier.bind fun (x : ℕ × ℕ × OidSet × ℕ × Bool × Dec × ℕ × ℕ × ℕ × ℕ × OidSet) =>
          ((x.2.1, x.2.2.1, x.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2, ∅),
            x.2.1, x.2.2.1,
            {Item.node
                  { id := x.1, round := x.2.2.2.1, step := Step.wait, value := x.2.2.2.2.1, dec := x.2.2.2.2.2.1,
                    vt := x.2.2.2.2.2.2.1, vf := x.2.2.2.2.2.2.2.1, va := x.2.2.2.2.2.2.2.2.1 }} +
              {Item.msg false x.2.2.2.1 x.2.2.2.2.2.2.2.2.2.1 ({x.1} + x.2.2.2.2.2.2.2.2.2.2)}),
        Unifier.bind fun (x : Items × ℕ × OidSet × ℕ × ℕ × Bool × Dec × ℕ × ℕ × ℕ × ℕ) =>
          ((x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2, ∅, x.1),
            x.2.1, x.2.2.1,
            x.1 +
                {Item.node
                    { id := x.2.2.2.1, round := x.2.2.2.2.1, step := Step.wait, value := x.2.2.2.2.2.1,
                      dec := x.2.2.2.2.2.2.1, vt := x.2.2.2.2.2.2.2.1, vf := x.2.2.2.2.2.2.2.2.1,
                      va := x.2.2.2.2.2.2.2.2.2.1 }} +
              {Item.msg false x.2.2.2.2.1 x.2.2.2.2.2.2.2.2.2.2 {x.2.2.2.1}}),
        Unifier.bind fun (x : Items × OidSet × ℕ × OidSet × ℕ × ℕ × Bool × Dec × ℕ × ℕ × ℕ × ℕ) =>
          ((x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2, x.2.1, x.1),
            x.2.2.1, x.2.2.2.1,
            x.1 +
                {Item.node
                    { id := x.2.2.2.2.1, round := x.2.2.2.2.2.1, step := Step.wait, value := x.2.2.2.2.2.2.1,
                      dec := x.2.2.2.2.2.2.2.1, vt := x.2.2.2.2.2.2.2.2.1, vf := x.2.2.2.2.2.2.2.2.2.1,
                      va := x.2.2.2.2.2.2.2.2.2.2.1 }} +
              {Item.msg false x.2.2.2.2.2.1 x.2.2.2.2.2.2.2.2.2.2.2 ({x.2.2.2.2.1} + x.2.1)})] := by
  simp only [sound, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  repeat' apply And.intro
  all_goals
    rintro γ ⟨x, rfl⟩
    simp only [unifiedBy, mayFire, recvF, pastP]
    try ac_rfl

theorem otr_inv3.obligation_9 :
    complete (mayFire decideT pastP)
      [Unifier.bind fun (x : ℕ × ℕ × Bool × ℕ × ℕ × ℕ × ℕ × OidSet) =>
          ((x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2, x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, ∅),
            x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2,
            {Item.node
                { id := x.1, round := x.2.1, step := Step.wait, value := x.2.2.1, dec := Dec.undecided, vt := x.2.2.2.1,
                  vf := x.2.2.2.2.1, va := x.2.2.2.2.2.1 }}),
        Unifier.bind fun (x : Items × ℕ × ℕ × Bool × ℕ × ℕ × ℕ × ℕ × OidSet) =>
          ((x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
              x.2.2.2.2.2.2.1, x.1),
            x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2,
            x.1 +
              {Item.node
                  { id := x.2.1, round := x.2.2.1, step := Step.wait, value := x.2.2.2.1, dec := Dec.undecided,
                    vt := x.2.2.2.2.1, vf := x.2.2.2.2.2.1, va := x.2.2.2.2.2.2.1 }})] := by
  maude_certify_comp

theorem otr_inv3.obligation_10 :
    sound (mayFire decideT pastP)
      [Unifier.bind fun (x : ℕ × ℕ × Bool × ℕ × ℕ × ℕ × ℕ × OidSet) =>
          ((x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2, x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, ∅),
            x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2,
            {Item.node
                { id := x.1, round := x.2.1, step := Step.wait, value := x.2.2.1, dec := Dec.undecided, vt := x.2.2.2.1,
                  vf := x.2.2.2.2.1, va := x.2.2.2.2.2.1 }}),
        Unifier.bind fun (x : Items × ℕ × ℕ × Bool × ℕ × ℕ × ℕ × ℕ × OidSet) =>
          ((x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
              x.2.2.2.2.2.2.1, x.1),
            x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2,
            x.1 +
              {Item.node
                  { id := x.2.1, round := x.2.2.1, step := Step.wait, value := x.2.2.2.1, dec := Dec.undecided,
                    vt := x.2.2.2.2.1, vf := x.2.2.2.2.2.1, va := x.2.2.2.2.2.2.1 }})] := by
  simp only [sound, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  repeat' apply And.intro
  all_goals
    rintro γ ⟨x, rfl⟩
    simp only [unifiedBy, mayFire, decideT, pastP]
    try ac_rfl

theorem otr_inv3.obligation_11 :
    complete (mayFire decideF pastP)
      [Unifier.bind fun (x : ℕ × ℕ × Bool × ℕ × ℕ × ℕ × ℕ × OidSet) =>
          ((x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2, x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, ∅),
            x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2,
            {Item.node
                { id := x.1, round := x.2.1, step := Step.wait, value := x.2.2.1, dec := Dec.undecided, vt := x.2.2.2.1,
                  vf := x.2.2.2.2.1, va := x.2.2.2.2.2.1 }}),
        Unifier.bind fun (x : Items × ℕ × ℕ × Bool × ℕ × ℕ × ℕ × ℕ × OidSet) =>
          ((x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
              x.2.2.2.2.2.2.1, x.1),
            x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2,
            x.1 +
              {Item.node
                  { id := x.2.1, round := x.2.2.1, step := Step.wait, value := x.2.2.2.1, dec := Dec.undecided,
                    vt := x.2.2.2.2.1, vf := x.2.2.2.2.2.1, va := x.2.2.2.2.2.2.1 }})] := by
  maude_certify_comp

theorem otr_inv3.obligation_12 :
    sound (mayFire decideF pastP)
      [Unifier.bind fun (x : ℕ × ℕ × Bool × ℕ × ℕ × ℕ × ℕ × OidSet) =>
          ((x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2, x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, ∅),
            x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2,
            {Item.node
                { id := x.1, round := x.2.1, step := Step.wait, value := x.2.2.1, dec := Dec.undecided, vt := x.2.2.2.1,
                  vf := x.2.2.2.2.1, va := x.2.2.2.2.2.1 }}),
        Unifier.bind fun (x : Items × ℕ × ℕ × Bool × ℕ × ℕ × ℕ × ℕ × OidSet) =>
          ((x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
              x.2.2.2.2.2.2.1, x.1),
            x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2,
            x.1 +
              {Item.node
                  { id := x.2.1, round := x.2.2.1, step := Step.wait, value := x.2.2.2.1, dec := Dec.undecided,
                    vt := x.2.2.2.2.1, vf := x.2.2.2.2.2.1, va := x.2.2.2.2.2.2.1 }})] := by
  simp only [sound, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  repeat' apply And.intro
  all_goals
    rintro γ ⟨x, rfl⟩
    simp only [unifiedBy, mayFire, decideF, pastP]
    try ac_rfl

theorem otr_inv3.obligation_13 :
    complete (mayFire updateT pastP)
      [Unifier.bind fun (x : ℕ × ℕ × Bool × ℕ × ℕ × ℕ × ℕ × OidSet) =>
          ((x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2, x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, ∅),
            x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2,
            {Item.node
                { id := x.1, round := x.2.1, step := Step.wait, value := x.2.2.1, dec := Dec.undecided, vt := x.2.2.2.1,
                  vf := x.2.2.2.2.1, va := x.2.2.2.2.2.1 }}),
        Unifier.bind fun (x : Items × ℕ × ℕ × Bool × ℕ × ℕ × ℕ × ℕ × OidSet) =>
          ((x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
              x.2.2.2.2.2.2.1, x.1),
            x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2,
            x.1 +
              {Item.node
                  { id := x.2.1, round := x.2.2.1, step := Step.wait, value := x.2.2.2.1, dec := Dec.undecided,
                    vt := x.2.2.2.2.1, vf := x.2.2.2.2.2.1, va := x.2.2.2.2.2.2.1 }})] := by
  maude_certify_comp

theorem otr_inv3.obligation_14 :
    sound (mayFire updateT pastP)
      [Unifier.bind fun (x : ℕ × ℕ × Bool × ℕ × ℕ × ℕ × ℕ × OidSet) =>
          ((x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2, x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, ∅),
            x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2,
            {Item.node
                { id := x.1, round := x.2.1, step := Step.wait, value := x.2.2.1, dec := Dec.undecided, vt := x.2.2.2.1,
                  vf := x.2.2.2.2.1, va := x.2.2.2.2.2.1 }}),
        Unifier.bind fun (x : Items × ℕ × ℕ × Bool × ℕ × ℕ × ℕ × ℕ × OidSet) =>
          ((x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
              x.2.2.2.2.2.2.1, x.1),
            x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2,
            x.1 +
              {Item.node
                  { id := x.2.1, round := x.2.2.1, step := Step.wait, value := x.2.2.2.1, dec := Dec.undecided,
                    vt := x.2.2.2.2.1, vf := x.2.2.2.2.2.1, va := x.2.2.2.2.2.2.1 }})] := by
  simp only [sound, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  repeat' apply And.intro
  all_goals
    rintro γ ⟨x, rfl⟩
    simp only [unifiedBy, mayFire, updateT, pastP]
    try ac_rfl

theorem otr_inv3.obligation_15 :
    complete (mayFire updateF pastP)
      [Unifier.bind fun (x : ℕ × ℕ × Bool × ℕ × ℕ × ℕ × ℕ × OidSet) =>
          ((x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2, x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, ∅),
            x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2,
            {Item.node
                { id := x.1, round := x.2.1, step := Step.wait, value := x.2.2.1, dec := Dec.undecided, vt := x.2.2.2.1,
                  vf := x.2.2.2.2.1, va := x.2.2.2.2.2.1 }}),
        Unifier.bind fun (x : Items × ℕ × ℕ × Bool × ℕ × ℕ × ℕ × ℕ × OidSet) =>
          ((x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
              x.2.2.2.2.2.2.1, x.1),
            x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2,
            x.1 +
              {Item.node
                  { id := x.2.1, round := x.2.2.1, step := Step.wait, value := x.2.2.2.1, dec := Dec.undecided,
                    vt := x.2.2.2.2.1, vf := x.2.2.2.2.2.1, va := x.2.2.2.2.2.2.1 }})] := by
  maude_certify_comp

theorem otr_inv3.obligation_16 :
    sound (mayFire updateF pastP)
      [Unifier.bind fun (x : ℕ × ℕ × Bool × ℕ × ℕ × ℕ × ℕ × OidSet) =>
          ((x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2, x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, ∅),
            x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2,
            {Item.node
                { id := x.1, round := x.2.1, step := Step.wait, value := x.2.2.1, dec := Dec.undecided, vt := x.2.2.2.1,
                  vf := x.2.2.2.2.1, va := x.2.2.2.2.2.1 }}),
        Unifier.bind fun (x : Items × ℕ × ℕ × Bool × ℕ × ℕ × ℕ × ℕ × OidSet) =>
          ((x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1,
              x.2.2.2.2.2.2.1, x.1),
            x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2,
            x.1 +
              {Item.node
                  { id := x.2.1, round := x.2.2.1, step := Step.wait, value := x.2.2.2.1, dec := Dec.undecided,
                    vt := x.2.2.2.2.1, vf := x.2.2.2.2.2.1, va := x.2.2.2.2.2.2.1 }})] := by
  simp only [sound, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  repeat' apply And.intro
  all_goals
    rintro γ ⟨x, rfl⟩
    simp only [unifiedBy, mayFire, updateF, pastP]
    try ac_rfl

theorem otr_inv3.obligation_17 :
    complete (mayFire loss pastP)
      [Unifier.bind fun (x : Bool × ℕ × ℕ × OidSet × ℕ × OidSet) =>
          ((x.2.2.2.2.1, x.2.2.2.2.2, x.1, x.2.1, x.2.2.1, x.2.2.2.1, ∅), x.2.2.2.2.1, x.2.2.2.2.2,
            {Item.msg x.1 x.2.1 x.2.2.1 x.2.2.2.1}),
        Unifier.bind fun (x : Items × Bool × ℕ × ℕ × OidSet × ℕ × OidSet) =>
          ((x.2.2.2.2.2.1, x.2.2.2.2.2.2, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.1), x.2.2.2.2.2.1, x.2.2.2.2.2.2,
            x.1 + {Item.msg x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1})] := by
  maude_certify_comp

theorem otr_inv3.obligation_18 :
    sound (mayFire loss pastP)
      [Unifier.bind fun (x : Bool × ℕ × ℕ × OidSet × ℕ × OidSet) =>
          ((x.2.2.2.2.1, x.2.2.2.2.2, x.1, x.2.1, x.2.2.1, x.2.2.2.1, ∅), x.2.2.2.2.1, x.2.2.2.2.2,
            {Item.msg x.1 x.2.1 x.2.2.1 x.2.2.2.1}),
        Unifier.bind fun (x : Items × Bool × ℕ × ℕ × OidSet × ℕ × OidSet) =>
          ((x.2.2.2.2.2.1, x.2.2.2.2.2.2, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.1), x.2.2.2.2.2.1, x.2.2.2.2.2.2,
            x.1 + {Item.msg x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1})] := by
  simp only [sound, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  repeat' apply And.intro
  all_goals
    rintro γ ⟨x, rfl⟩
    simp only [unifiedBy, mayFire, loss, pastP]
    try ac_rfl

#link otr_inv1
#link otr_inv3

#print axioms otr_inv1.linked
#print axioms otr_inv3.linked

end OTR
