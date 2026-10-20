import conPanna.conPanna
import conPanna.Unification.Certification.Multiset

/-!
# OneThirdRule: model and agreement invariant

The model of `../draft/OTR.lean` with one addition, a ghost log of the votes cast: `vote`
also records `⟨o, r, v⟩` (node `o` voted `v` in round `r`). The rules never read it.

The invariant `Inv` is a conjunction of counting facts (`Multiset.countP`, sums of maps)
after the Isabelle proof of Charron-Bost, Debrat and Merz (AFP `Heard_Of`), restated
round by round for asynchronous rounds. Agreement follows from it (`agreement`), and each
rule preserves it (`inv_*`); `pf.lean` checks the latter by narrowing.
-/

namespace OTRA

open Expresso

/-! ## Model -/

inductive Step where
  | init | wait | done
  deriving DecidableEq

inductive Dec where
  | undecided
  | decided (v : Bool)
  deriving DecidableEq

abbrev OidSet := ACU Nat

structure Node where
  id : Nat
  round : Nat
  step : Step
  value : Bool
  dec : Dec
  vt : Nat
  vf : Nat
  va : Nat

inductive Item where
  | node (n : Node)
  | msg (v : Bool) (r : Nat) (src : Nat) (rcv : OidSet)

abbrev Items := ACU Item

/-- Ghost: node `o` voted `v` in round `r`. -/
structure Cast where
  o : Nat
  r : Nat
  v : Bool

abbrev Log := ACU Cast

structure Conf where
  th : Nat
  ids : OidSet
  items : Items
  log : Log

#dump_model Conf

/-! ## Rules -/

def voteT : Rule Conf := .bind fun ((TH, O, OS, R, VT, VF, VA, CF, LG) :
    Nat × Nat × OidSet × Nat × Nat × Nat × Nat × Items × Log) =>
  { lhs := ⟨TH, {O} + OS, {Item.node ⟨O, R, .init, true, .undecided, VT, VF, VA⟩} + CF, LG⟩
    rhs := ⟨TH, {O} + OS, {Item.node ⟨O, R, .wait, true, .undecided, VT + 1, VF, VA + 1⟩} +
      ({Item.msg true R O OS} + CF), {Cast.mk O R true} + LG⟩ }

def voteF : Rule Conf := .bind fun ((TH, O, OS, R, VT, VF, VA, CF, LG) :
    Nat × Nat × OidSet × Nat × Nat × Nat × Nat × Items × Log) =>
  { lhs := ⟨TH, {O} + OS, {Item.node ⟨O, R, .init, false, .undecided, VT, VF, VA⟩} + CF, LG⟩
    rhs := ⟨TH, {O} + OS, {Item.node ⟨O, R, .wait, false, .undecided, VT, VF + 1, VA + 1⟩} +
      ({Item.msg false R O OS} + CF), {Cast.mk O R false} + LG⟩ }

def recvT : Rule Conf := .bind fun ((TH, IDS, O, R, V, D, VT, VF, VA, S, OS, CF, LG) :
    Nat × OidSet × Nat × Nat × Bool × Dec × Nat × Nat × Nat × Nat × OidSet × Items × Log) =>
  { lhs := ⟨TH, IDS, {Item.node ⟨O, R, .wait, V, D, VT, VF, VA⟩} +
      ({Item.msg true R S ({O} + OS)} + CF), LG⟩
    rhs := ⟨TH, IDS, {Item.node ⟨O, R, .wait, V, D, VT + 1, VF, VA + 1⟩} +
      ({Item.msg true R S OS} + CF), LG⟩ }

def recvF : Rule Conf := .bind fun ((TH, IDS, O, R, V, D, VT, VF, VA, S, OS, CF, LG) :
    Nat × OidSet × Nat × Nat × Bool × Dec × Nat × Nat × Nat × Nat × OidSet × Items × Log) =>
  { lhs := ⟨TH, IDS, {Item.node ⟨O, R, .wait, V, D, VT, VF, VA⟩} +
      ({Item.msg false R S ({O} + OS)} + CF), LG⟩
    rhs := ⟨TH, IDS, {Item.node ⟨O, R, .wait, V, D, VT, VF + 1, VA + 1⟩} +
      ({Item.msg false R S OS} + CF), LG⟩ }

def decideT : Rule Conf := .bind fun ((TH, IDS, O, R, V, VT, VF, VA, CF, LG) :
    Nat × OidSet × Nat × Nat × Bool × Nat × Nat × Nat × Items × Log) =>
  { lhs := ⟨TH, IDS, {Item.node ⟨O, R, .wait, V, .undecided, VT, VF, VA⟩} + CF, LG⟩
    rhs := ⟨TH, IDS, {Item.node ⟨O, R, .done, V, .decided true, VT, VF, VA⟩} + CF, LG⟩
    cond := TH ≤ VT }

def decideF : Rule Conf := .bind fun ((TH, IDS, O, R, V, VT, VF, VA, CF, LG) :
    Nat × OidSet × Nat × Nat × Bool × Nat × Nat × Nat × Items × Log) =>
  { lhs := ⟨TH, IDS, {Item.node ⟨O, R, .wait, V, .undecided, VT, VF, VA⟩} + CF, LG⟩
    rhs := ⟨TH, IDS, {Item.node ⟨O, R, .done, V, .decided false, VT, VF, VA⟩} + CF, LG⟩
    cond := TH ≤ VF }

def updateT : Rule Conf := .bind fun ((TH, IDS, O, R, V, VT, VF, VA, CF, LG) :
    Nat × OidSet × Nat × Nat × Bool × Nat × Nat × Nat × Items × Log) =>
  { lhs := ⟨TH, IDS, {Item.node ⟨O, R, .wait, V, .undecided, VT, VF, VA⟩} + CF, LG⟩
    rhs := ⟨TH, IDS, {Item.node ⟨O, R + 1, .init, true, .undecided, 0, 0, 0⟩} + CF, LG⟩
    cond := VT < TH ∧ TH ≤ VA ∧ VF ≤ VT }

def updateF : Rule Conf := .bind fun ((TH, IDS, O, R, V, VT, VF, VA, CF, LG) :
    Nat × OidSet × Nat × Nat × Bool × Nat × Nat × Nat × Items × Log) =>
  { lhs := ⟨TH, IDS, {Item.node ⟨O, R, .wait, V, .undecided, VT, VF, VA⟩} + CF, LG⟩
    rhs := ⟨TH, IDS, {Item.node ⟨O, R + 1, .init, false, .undecided, 0, 0, 0⟩} + CF, LG⟩
    cond := VF < TH ∧ TH ≤ VA ∧ VT < VF }

def loss : Rule Conf := .bind fun ((TH, IDS, V, R, S, OS, CF, LG) :
    Nat × OidSet × Bool × Nat × Nat × OidSet × Items × Log) =>
  { lhs := ⟨TH, IDS, {Item.msg V R S OS} + CF, LG⟩
    rhs := ⟨TH, IDS, CF, LG⟩ }

def otr : System Conf := [voteT, voteF, recvT, recvF, decideT, decideF, updateT, updateF, loss]

/-! ## Counting -/

/-- The nodes of a configuration. -/
def nodesOf (m : Multiset Item) : Multiset Node :=
  m.bind fun | .node n => {n} | .msg .. => 0

/-- The votes for `v` that node `n` has counted. -/
def cnt (n : Node) : Bool → Nat
  | true => n.vt
  | false => n.vf

/-- Pending deliveries of `v`-votes of round `r` to node `o`. -/
def pend (m : Multiset Item) (r : Nat) (v : Bool) (o : Nat) : Nat :=
  (m.map fun | .msg v' r' _ rcv => if r' = r ∧ v' = v then rcv.toMultiset.count o else 0
             | .node _ => 0).sum

/-- The votes for `v` cast in round `r`. -/
def casts (g : Multiset Cast) (r : Nat) (v : Bool) : Nat :=
  g.countP fun c => c.r = r ∧ c.v = v

/-- The nodes that have voted in round `r`. -/
def voted (m : Multiset Item) (r : Nat) : Nat :=
  (nodesOf m).countP fun n => r < n.round ∨ r = n.round ∧ n.step ≠ .init

/-- Value `w` is justified by round `r`: some vote counts `a` for `true` and `b` for
`false`, within the votes cast and reaching the threshold, choose it. -/
def just (g : Multiset Cast) (TH r : Nat) (w : Bool) : Prop :=
  ∃ a b, a ≤ casts g r true ∧ b ≤ casts g r false ∧ TH ≤ a + b ∧ (w = true ↔ b ≤ a)

/-! ## The invariant -/

structure InvM (TH : Nat) (ids : Multiset Nat) (m : Multiset Item) (g : Multiset Cast) :
    Prop where
  th : 2 * Multiset.card (nodesOf m) < 3 * TH
  ids : ids.Nodup
  counters : ∀ n ∈ nodesOf m, n.va = n.vt + n.vf ∧ (n.step = .init → n.vt = 0 ∧ n.vf = 0)
  pending : ∀ o r v, pend m r v o ≤ casts g r v
  counted : ∀ n ∈ nodesOf m, ∀ v, cnt n v + pend m n.round v n.id ≤ casts g n.round v
  voters : ∀ r, casts g r true + casts g r false ≤ voted m r
  decided : ∀ n ∈ nodesOf m, ∀ v, n.dec = .decided v → TH ≤ casts g n.round v
  values : ∀ n ∈ nodesOf m, ∀ r, n.round = r + 1 → just g TH r n.value
  votes : ∀ c ∈ g, ∀ r, c.r = r + 1 → just g TH r c.v

@[irreducible] def Inv (TH : Nat) (IDS : OidSet) (CF : Items) (LG : Log) : Prop :=
  InvM TH IDS.toMultiset CF.toMultiset LG.toMultiset

/-- `Inv` of a whole state. -/
def InvS (s : Conf) : Prop := Inv s.th s.ids s.items s.log

def invP : Patch Conf := .bind fun ((TH, IDS, CF, LG) : Nat × OidSet × Items × Log) =>
  ⟨⟨TH, IDS, CF, LG⟩, Inv TH IDS CF LG⟩

def inv : Pattern Conf := [invP]

/-! ## Counting over sums -/

theorem nodesOf_add (X Y : Multiset Item) : nodesOf (X + Y) = nodesOf X + nodesOf Y := by
  simp [nodesOf]
theorem nodesOf_zero : nodesOf 0 = 0 := by simp [nodesOf]
theorem nodesOf_node (n : Node) : nodesOf {Item.node n} = {n} := by simp [nodesOf]
theorem nodesOf_msg (v : Bool) (r s : Nat) (os : OidSet) : nodesOf {Item.msg v r s os} = 0 := by
  simp [nodesOf]

theorem pend_add (X Y : Multiset Item) (r : Nat) (v : Bool) (o : Nat) :
    pend (X + Y) r v o = pend X r v o + pend Y r v o := by simp [pend]
theorem pend_node (n : Node) (r : Nat) (v : Bool) (o : Nat) : pend {Item.node n} r v o = 0 := by
  simp [pend]
theorem pend_msg (v' : Bool) (r' s : Nat) (os : OidSet) (r : Nat) (v : Bool) (o : Nat) :
    pend {Item.msg v' r' s os} r v o = if r' = r ∧ v' = v then os.toMultiset.count o else 0 := by
  simp [pend]

theorem casts_add (g h : Multiset Cast) (r : Nat) (v : Bool) :
    casts (g + h) r v = casts g r v + casts h r v := by simp [casts]
theorem casts_one (c : Cast) (r : Nat) (v : Bool) :
    casts {c} r v = if c.r = r ∧ c.v = v then 1 else 0 := by
  rw [casts, ← Multiset.cons_zero, Multiset.countP_cons]; simp

theorem voted_add (X Y : Multiset Item) (r : Nat) : voted (X + Y) r = voted X r + voted Y r := by
  simp [voted, nodesOf_add]
theorem voted_node (n : Node) (r : Nat) :
    voted {Item.node n} r = if r < n.round ∨ r = n.round ∧ n.step ≠ .init then 1 else 0 := by
  rw [voted, nodesOf_node, ← Multiset.cons_zero, Multiset.countP_cons]; simp
theorem voted_msg (v : Bool) (r' s : Nat) (os : OidSet) (r : Nat) :
    voted {Item.msg v r' s os} r = 0 := by
  simp [voted, nodesOf_msg]

theorem just_mono {g g' : Multiset Cast} {TH r : Nat} {w : Bool}
    (hg : ∀ v, casts g r v ≤ casts g' r v) (h : just g TH r w) : just g' TH r w := by
  obtain ⟨a, b, ha, hb, hab, hw⟩ := h
  exact ⟨a, b, ha.trans (hg true), hb.trans (hg false), hab, hw⟩

/-- The receivers of a multicast: at most once each, and never its sender. -/
theorem count_rcv {O o : Nat} {os : Multiset Nat} (h : (O ::ₘ os).Nodup) :
    os.count O = 0 ∧ os.count o ≤ 1 := by
  rw [Multiset.nodup_cons] at h
  exact ⟨Multiset.count_eq_zero.2 h.1, Multiset.nodup_iff_count_le_one.1 h.2 o⟩

theorem nodes_cons {n : Node} {X : Multiset Item} : n ∈ nodesOf ({Item.node n} + X) := by
  rw [nodesOf_add, nodesOf_node]; exact Multiset.mem_add.2 (.inl (Multiset.mem_singleton_self n))

theorem nodes_tail {n n' : Node} {X : Multiset Item} (h : n ∈ nodesOf X) :
    n ∈ nodesOf ({Item.node n'} + X) := by
  rw [nodesOf_add]; exact Multiset.mem_add.2 (.inr h)

/-- The counting functions over sums of items and votes. -/
macro "count_simp" : tactic => `(tactic| simp only [nodesOf_add, nodesOf_zero, nodesOf_node,
  nodesOf_msg, pend_add, pend_node, pend_msg, casts_add, casts_one, voted_add, voted_node,
  voted_msg, zero_add, add_zero, Multiset.card_add, Multiset.card_singleton, Multiset.card_zero,
  Multiset.mem_add, Multiset.mem_singleton, cnt, cond_true, cond_false, ne_eq, reduceCtorEq,
  not_true_eq_false, not_false_eq_true, and_true, and_false, or_false] at *)

theorem nodes_mid {n : Node} {v : Bool} {r s : Nat} {os : OidSet} {X : Multiset Item}
    (h : n ∈ nodesOf X) : n ∈ nodesOf ({Item.msg v r s os} + X) := by
  rwa [nodesOf_add, nodesOf_msg, zero_add]

/-! ## Each rule preserves the invariant (on multisets) -/

theorem InvM.vote {TH O R VT VF VA : Nat} {v : Bool} {OS : OidSet} {X : Multiset Item}
    {g : Multiset Cast}
    (h : InvM TH ({O} + OS.toMultiset) ({Item.node ⟨O, R, .init, v, .undecided, VT, VF, VA⟩} + X) g) :
    InvM TH ({O} + OS.toMultiset)
      ({Item.node ⟨O, R, .wait, v, .undecided, VT + cond v 1 0, VF + cond v 0 1, VA + 1⟩} +
        ({Item.msg v R O OS} + X)) ({⟨O, R, v⟩} + g) := by
  have hO (o : Nat) := count_rcv (O := O) (o := o) (os := OS.toMultiset)
    (by simpa [Multiset.singleton_add] using h.ids)
  have hg : ∀ r w, casts g r w ≤ casts ({⟨O, R, v⟩} + g) r w := by
    intro r w; rw [casts_add]; omega
  have h0 := h.counted _ nodes_cons
  have hv0 := h.values _ nodes_cons
  refine ⟨?_, h.ids, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := h.th; count_simp; omega
  · intro n hn
    simp only [nodesOf_add, nodesOf_node, nodesOf_msg, zero_add, Multiset.mem_add,
      Multiset.mem_singleton] at hn
    rcases hn with rfl | hn
    · have := h.counters _ nodes_cons
      cases v <;> simp at this ⊢ <;> omega
    · exact h.counters n (nodes_tail hn)
  · intro o r w
    have := h.pending o r w
    have := (hO o).2
    simp only [pend_add, pend_node, pend_msg, casts_add, casts_one, zero_add] at *
    split_ifs at * <;> omega
  · intro n hn w
    simp only [nodesOf_add, nodesOf_node, nodesOf_msg, zero_add, Multiset.mem_add,
      Multiset.mem_singleton] at hn
    rcases hn with rfl | hn
    · have := h0 w
      have := (hO O).1
      cases v <;> cases w <;> simp only [cnt, pend_add, pend_node, pend_msg, casts_add,
        casts_one, zero_add] at * <;> split_ifs at * <;> simp_all <;> omega
    · have := h.counted n (nodes_tail hn) w
      have := (hO n.id).2
      simp only [pend_add, pend_node, pend_msg, casts_add, casts_one, zero_add] at *
      split_ifs at * <;> omega
  · intro r
    have := h.voters r
    simp only [voted_add, voted_node, voted_msg, casts_add, casts_one, zero_add] at *
    split_ifs at * <;> simp_all <;> omega
  · intro n hn w hd
    simp only [nodesOf_add, nodesOf_node, nodesOf_msg, zero_add, Multiset.mem_add,
      Multiset.mem_singleton] at hn
    rcases hn with rfl | hn
    · simp at hd
    · exact (h.decided n (nodes_tail hn) w hd).trans (hg _ _)
  · intro n hn r hr
    simp only [nodesOf_add, nodesOf_node, nodesOf_msg, zero_add, Multiset.mem_add,
      Multiset.mem_singleton] at hn
    rcases hn with rfl | hn
    · exact just_mono (hg r) (hv0 r hr)
    · exact just_mono (hg r) (h.values n (nodes_tail hn) r hr)
  · intro c hc r hr
    simp only [Multiset.mem_add, Multiset.mem_singleton] at hc
    rcases hc with rfl | hc
    · exact just_mono (hg r) (hv0 r hr)
    · exact just_mono (hg r) (h.votes c hc r hr)

theorem InvM.recv {TH O R VT VF VA S : Nat} {v V : Bool} {D : Dec} {ids : Multiset Nat}
    {OS : OidSet} {X : Multiset Item} {g : Multiset Cast}
    (h : InvM TH ids ({Item.node ⟨O, R, .wait, V, D, VT, VF, VA⟩} +
      ({Item.msg v R S ({O} + OS)} + X)) g) :
    InvM TH ids ({Item.node ⟨O, R, .wait, V, D, VT + cond v 1 0, VF + cond v 0 1, VA + 1⟩} +
      ({Item.msg v R S OS} + X)) g := by
  have h0 := h.counted _ nodes_cons
  refine ⟨?_, h.ids, ?_, ?_, ?_, ?_, ?_, ?_, h.votes⟩
  · have := h.th; count_simp; omega
  · intro n hn
    count_simp
    rcases hn with rfl | hn
    · have := h.counters _ nodes_cons
      cases v <;> simp at this ⊢ <;> omega
    · exact h.counters n (nodes_tail (nodes_mid hn))
  · intro o r w
    have := h.pending o r w
    count_simp
    simp only [ACU.toMultiset_plus, ACU.toMultiset_elem, Multiset.count_add,
      Multiset.count_singleton] at this
    split_ifs at * <;> omega
  · intro n hn w
    count_simp
    rcases hn with rfl | hn
    · have := h0 w
      simp only [ACU.toMultiset_plus, ACU.toMultiset_elem, Multiset.count_add,
        Multiset.count_singleton] at this
      cases v <;> cases w <;> count_simp <;> split_ifs at * <;> simp_all <;> omega
    · have := h.counted n (nodes_tail (nodes_mid hn)) w
      count_simp
      simp only [ACU.toMultiset_plus, ACU.toMultiset_elem, Multiset.count_add,
        Multiset.count_singleton] at this
      split_ifs at * <;> omega
  · intro r
    have := h.voters r
    count_simp
    exact this
  · intro n hn w hd
    count_simp
    rcases hn with rfl | hn
    · exact h.decided _ nodes_cons w hd
    · exact h.decided n (nodes_tail (nodes_mid hn)) w hd
  · intro n hn r hr
    count_simp
    rcases hn with rfl | hn
    · exact h.values _ nodes_cons r hr
    · exact h.values n (nodes_tail (nodes_mid hn)) r hr

theorem InvM.decide {TH O R VT VF VA : Nat} {v V : Bool} {ids : Multiset Nat}
    {X : Multiset Item} {g : Multiset Cast}
    (h : InvM TH ids ({Item.node ⟨O, R, .wait, V, .undecided, VT, VF, VA⟩} + X) g)
    (hc : TH ≤ cond v VT VF) :
    InvM TH ids ({Item.node ⟨O, R, .done, V, .decided v, VT, VF, VA⟩} + X) g := by
  have h0 := h.counted _ nodes_cons
  refine ⟨?_, h.ids, ?_, ?_, ?_, ?_, ?_, ?_, h.votes⟩
  · have := h.th; count_simp; omega
  · intro n hn
    count_simp
    rcases hn with rfl | hn
    · have := h.counters _ nodes_cons
      simp at this ⊢; omega
    · exact h.counters n (nodes_tail hn)
  · intro o r w
    have := h.pending o r w
    count_simp
    exact this
  · intro n hn w
    count_simp
    rcases hn with rfl | hn
    · have := h0 w; count_simp; exact this
    · have := h.counted n (nodes_tail hn) w; count_simp; exact this
  · intro r
    have := h.voters r
    count_simp
    split_ifs at * <;> omega
  · intro n hn w hd
    count_simp
    rcases hn with rfl | hn
    · simp only [Dec.decided.injEq] at hd
      subst hd
      have := h0 v
      cases v <;> count_simp <;> omega
    · exact h.decided n (nodes_tail hn) w hd
  · intro n hn r hr
    count_simp
    rcases hn with rfl | hn
    · exact h.values _ nodes_cons r hr
    · exact h.values n (nodes_tail hn) r hr

theorem InvM.update {TH O R VT VF VA : Nat} {v V : Bool} {ids : Multiset Nat}
    {X : Multiset Item} {g : Multiset Cast}
    (h : InvM TH ids ({Item.node ⟨O, R, .wait, V, .undecided, VT, VF, VA⟩} + X) g)
    (hTH : TH ≤ VA) (hv : v = true ↔ VF ≤ VT) :
    InvM TH ids ({Item.node ⟨O, R + 1, .init, v, .undecided, 0, 0, 0⟩} + X) g := by
  have h0 := h.counted _ nodes_cons
  refine ⟨?_, h.ids, ?_, ?_, ?_, ?_, ?_, ?_, h.votes⟩
  · have := h.th; count_simp; omega
  · intro n hn
    count_simp
    rcases hn with rfl | hn
    · simp
    · exact h.counters n (nodes_tail hn)
  · intro o r w
    have := h.pending o r w
    count_simp
    exact this
  · intro n hn w
    count_simp
    rcases hn with rfl | hn
    · have := h.pending O (R + 1) w
      count_simp
      cases w <;> dsimp only at * <;> omega
    · have := h.counted n (nodes_tail hn) w; count_simp; exact this
  · intro r
    have := h.voters r
    count_simp
    split_ifs at * <;> omega
  · intro n hn w hd
    count_simp
    rcases hn with rfl | hn
    · simp at hd
    · exact h.decided n (nodes_tail hn) w hd
  · intro n hn r hr
    count_simp
    rcases hn with rfl | hn
    · simp only [Nat.add_right_cancel_iff] at hr
      subst hr
      have := h.counters _ nodes_cons
      have ht := h0 true
      have hf := h0 false
      count_simp
      exact ⟨VT, VF, by omega, by omega, by simp at this; omega, hv⟩
    · exact h.values n (nodes_tail hn) r hr

theorem InvM.drop {TH : Nat} {ids : Multiset Nat} {P Q : Multiset Item} {g : Multiset Cast}
    (h : InvM TH ids P g) (hle : Q ≤ P) (hn : nodesOf Q = nodesOf P) : InvM TH ids Q g := by
  obtain ⟨Z, rfl⟩ := Multiset.le_iff_exists_add.1 hle
  have hv : ∀ r, voted Q r = voted (Q + Z) r := fun r => by simp only [voted, hn]
  refine ⟨hn ▸ h.th, h.ids, hn ▸ h.counters, ?_, ?_, ?_, hn ▸ h.decided, hn ▸ h.values, h.votes⟩
  · intro o r w; have := h.pending o r w; rw [pend_add] at this; omega
  · intro n hn' w
    have := h.counted n (hn ▸ hn') w; rw [pend_add] at this; omega
  · intro r; rw [hv]; exact h.voters r

/-! ## Each rule preserves the invariant -/

theorem inv_voteT {TH O R VT VF VA : Nat} {OS : OidSet} {CF : Items} {LG : Log}
    (h : Inv TH ({O} + OS) ({Item.node ⟨O, R, .init, true, .undecided, VT, VF, VA⟩} + CF) LG) :
    Inv TH ({O} + OS) ({Item.node ⟨O, R, .wait, true, .undecided, VT + 1, VF, VA + 1⟩} +
      ({Item.msg true R O OS} + CF)) ({Cast.mk O R true} + LG) := by
  unfold Inv at *; simp only [ACU.toMultiset_plus, ACU.toMultiset_elem] at *; exact h.vote

theorem inv_voteF {TH O R VT VF VA : Nat} {OS : OidSet} {CF : Items} {LG : Log}
    (h : Inv TH ({O} + OS) ({Item.node ⟨O, R, .init, false, .undecided, VT, VF, VA⟩} + CF) LG) :
    Inv TH ({O} + OS) ({Item.node ⟨O, R, .wait, false, .undecided, VT, VF + 1, VA + 1⟩} +
      ({Item.msg false R O OS} + CF)) ({Cast.mk O R false} + LG) := by
  unfold Inv at *; simp only [ACU.toMultiset_plus, ACU.toMultiset_elem] at *; exact h.vote

theorem inv_recvT {TH O R VT VF VA S : Nat} {IDS OS : OidSet} {V : Bool} {D : Dec} {CF : Items}
    {LG : Log}
    (h : Inv TH IDS ({Item.node ⟨O, R, .wait, V, D, VT, VF, VA⟩} +
      ({Item.msg true R S ({O} + OS)} + CF)) LG) :
    Inv TH IDS ({Item.node ⟨O, R, .wait, V, D, VT + 1, VF, VA + 1⟩} +
      ({Item.msg true R S OS} + CF)) LG := by
  unfold Inv at *; simp only [ACU.toMultiset_plus, ACU.toMultiset_elem] at h ⊢; exact h.recv

theorem inv_recvF {TH O R VT VF VA S : Nat} {IDS OS : OidSet} {V : Bool} {D : Dec} {CF : Items}
    {LG : Log}
    (h : Inv TH IDS ({Item.node ⟨O, R, .wait, V, D, VT, VF, VA⟩} +
      ({Item.msg false R S ({O} + OS)} + CF)) LG) :
    Inv TH IDS ({Item.node ⟨O, R, .wait, V, D, VT, VF + 1, VA + 1⟩} +
      ({Item.msg false R S OS} + CF)) LG := by
  unfold Inv at *; simp only [ACU.toMultiset_plus, ACU.toMultiset_elem] at h ⊢; exact h.recv

theorem inv_decideT {TH O R VT VF VA : Nat} {IDS : OidSet} {V : Bool} {CF : Items} {LG : Log}
    (h : Inv TH IDS ({Item.node ⟨O, R, .wait, V, .undecided, VT, VF, VA⟩} + CF) LG)
    (hc : TH ≤ VT) :
    Inv TH IDS ({Item.node ⟨O, R, .done, V, .decided true, VT, VF, VA⟩} + CF) LG := by
  unfold Inv at *; simp only [ACU.toMultiset_plus, ACU.toMultiset_elem] at *
  exact h.decide (v := true) hc

theorem inv_decideF {TH O R VT VF VA : Nat} {IDS : OidSet} {V : Bool} {CF : Items} {LG : Log}
    (h : Inv TH IDS ({Item.node ⟨O, R, .wait, V, .undecided, VT, VF, VA⟩} + CF) LG)
    (hc : TH ≤ VF) :
    Inv TH IDS ({Item.node ⟨O, R, .done, V, .decided false, VT, VF, VA⟩} + CF) LG := by
  unfold Inv at *; simp only [ACU.toMultiset_plus, ACU.toMultiset_elem] at *
  exact h.decide (v := false) hc

theorem inv_updateT {TH O R VT VF VA : Nat} {IDS : OidSet} {V : Bool} {CF : Items} {LG : Log}
    (h : Inv TH IDS ({Item.node ⟨O, R, .wait, V, .undecided, VT, VF, VA⟩} + CF) LG)
    (hc : VT < TH ∧ TH ≤ VA ∧ VF ≤ VT) :
    Inv TH IDS ({Item.node ⟨O, R + 1, .init, true, .undecided, 0, 0, 0⟩} + CF) LG := by
  unfold Inv at *; simp only [ACU.toMultiset_plus, ACU.toMultiset_elem] at *
  exact h.update hc.2.1 (by simp [hc.2.2])

theorem inv_updateF {TH O R VT VF VA : Nat} {IDS : OidSet} {V : Bool} {CF : Items} {LG : Log}
    (h : Inv TH IDS ({Item.node ⟨O, R, .wait, V, .undecided, VT, VF, VA⟩} + CF) LG)
    (hc : VF < TH ∧ TH ≤ VA ∧ VT < VF) :
    Inv TH IDS ({Item.node ⟨O, R + 1, .init, false, .undecided, 0, 0, 0⟩} + CF) LG := by
  unfold Inv at *; simp only [ACU.toMultiset_plus, ACU.toMultiset_elem] at *
  exact h.update hc.2.1 (by simp; omega)

/-- Dropping messages keeps the invariant (`loss`). -/
theorem inv_drop {TH : Nat} {IDS : OidSet} {P Q : Items} {LG : Log} (h : Inv TH IDS P LG)
    (hle : Q.toMultiset ≤ P.toMultiset) (hn : nodesOf Q.toMultiset = nodesOf P.toMultiset) :
    Inv TH IDS Q LG := by
  unfold Inv at *; exact h.drop hle hn

theorem inv_loss {TH R S : Nat} {IDS OS : OidSet} {V : Bool} {CF : Items} {LG : Log}
    (h : Inv TH IDS ({Item.msg V R S OS} + CF) LG) : Inv TH IDS CF LG :=
  inv_drop h (by simp [Multiset.le_cons_self]) (by simp only [ACU.toMultiset_plus, ACU.toMultiset_elem, nodesOf_add,
    nodesOf_msg, zero_add])

/-! ## Initial states -/

/-- Initially every node is in round 0, about to vote, with nothing counted or decided;
there are no messages and no votes cast; identifiers are distinct, and `TH > 2N/3`. -/
theorem inv_init {TH : Nat} {IDS : OidSet} {CF : Items}
    (hCF : ∀ it ∈ CF.toMultiset, ∃ n, it = .node n ∧ n.round = 0 ∧ n.step = .init ∧
      n.dec = .undecided ∧ n.vt = 0 ∧ n.vf = 0 ∧ n.va = 0)
    (hids : IDS.toMultiset.Nodup) (hth : 2 * Multiset.card (nodesOf CF.toMultiset) < 3 * TH) :
    Inv TH IDS CF ∅ := by
  have hn : ∀ n ∈ nodesOf CF.toMultiset, n.round = 0 ∧ n.step = .init ∧
      n.dec = .undecided ∧ n.vt = 0 ∧ n.vf = 0 ∧ n.va = 0 := by
    intro n hn
    obtain ⟨it, hit, hn⟩ := Multiset.mem_bind.1 hn
    obtain ⟨n', rfl, h'⟩ := hCF it hit
    simp only [Multiset.mem_singleton] at hn
    exact hn ▸ h'
  have hp : ∀ r v o, pend CF.toMultiset r v o = 0 := by
    intro r v o
    simp only [pend, Multiset.sum_eq_zero_iff, Multiset.mem_map]
    rintro _ ⟨it, hit, rfl⟩
    obtain ⟨n, rfl, -⟩ := hCF it hit
    rfl
  unfold Inv
  refine ⟨hth, hids, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n h; have := hn n h; simp [this]
  · intro o r v; simp [hp, casts]
  · intro n h v; have := hn n h; cases v <;> simp [cnt, hp, casts, this]
  · intro r; simp [casts]
  · intro n h v hd; simp [(hn n h).2.2.1] at hd
  · intro n h r hr; simp [(hn n h).1] at hr
  · intro c hc; simp at hc

/-! ## Agreement -/

theorem InvM.voted_le {TH : Nat} {ids : Multiset Nat} {m : Multiset Item} {g : Multiset Cast}
    (_ : InvM TH ids m g) (r : Nat) : voted m r ≤ Multiset.card (nodesOf m) :=
  Multiset.countP_le_card _ _

/-- Once `v` has a quorum in round `r`, every later round has few `!v` votes. -/
theorem InvM.lock {TH : Nat} {ids : Multiset Nat} {m : Multiset Item} {g : Multiset Cast}
    (h : InvM TH ids m g) {r : Nat} {v : Bool} (hv : TH ≤ casts g r v) :
    ∀ k, casts g (r + k) (!v) + TH ≤ Multiset.card (nodesOf m)
  | 0 => by
    have := h.voters r; have := h.voted_le r
    cases v <;> simp only [Nat.add_zero, Bool.not_true, Bool.not_false] at * <;> omega
  | k + 1 => by
    have ih := h.lock hv k
    have hz : casts g (r + (k + 1)) (!v) = 0 := by
      rw [casts, Multiset.countP_eq_zero]
      rintro c hc ⟨hr, hcv⟩
      obtain ⟨a, b, ha, hb, hab, hw⟩ := h.votes c hc (r + k) (by omega)
      have := h.voters (r + k); have := h.voted_le (r + k); have := h.th
      cases v <;> simp only [Bool.not_true, Bool.not_false] at hcv ih <;> rw [hcv] at hw <;>
        simp at hw <;> omega
    omega

theorem InvM.agreement {TH : Nat} {ids : Multiset Nat} {m : Multiset Item} {g : Multiset Cast}
    (h : InvM TH ids m g) {n₁ n₂ : Node} (h₁ : n₁ ∈ nodesOf m) (h₂ : n₂ ∈ nodesOf m)
    {v w : Bool} (hv : n₁.dec = .decided v) (hw : n₂.dec = .decided w) : v = w := by
  have d₁ := h.decided _ h₁ v hv
  have d₂ := h.decided _ h₂ w hw
  have := h.th
  rcases Nat.le_total n₁.round n₂.round with hr | hr
  · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hr
    have := h.lock d₁ k
    rw [← hk] at this
    cases v <;> cases w <;> simp only [Bool.not_true, Bool.not_false] at this ⊢ <;> omega
  · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hr
    have := h.lock d₂ k
    rw [← hk] at this
    cases v <;> cases w <;> simp only [Bool.not_true, Bool.not_false] at this ⊢ <;> omega

/-- Agreement: two decided nodes decided the same value. -/
theorem agreement {s : Conf} (h : InvS s) {n₁ n₂ : Node}
    (h₁ : Item.node n₁ ∈ s.items.toMultiset) (h₂ : Item.node n₂ ∈ s.items.toMultiset)
    {v w : Bool} (hv : n₁.dec = .decided v) (hw : n₂.dec = .decided w) : v = w := by
  unfold InvS Inv at h
  have mem : ∀ n, Item.node n ∈ s.items.toMultiset → n ∈ nodesOf s.items.toMultiset :=
    fun n hn => Multiset.mem_bind.2 ⟨_, hn, Multiset.mem_singleton_self n⟩
  exact h.agreement (mem _ h₁) (mem _ h₂) hv hw

/-! ## Rule images
`preserves r`: rule `r` sends states in `Inv` to states in `Inv`. Equivalently, its
`image` (its right-hand sides, from left-hand sides in `Inv`) lies in `inv`. -/

open Subsumption in
def preserves : Rule Conf → Prop
  | .bind body => ∀ x, InvS (body x).lhs → (body x).cond → InvS (body x).rhs

def image : Rule Conf → Patch Conf
  | .bind body => .bind fun x => ⟨(body x).rhs, InvS (body x).lhs ∧ (body x).cond⟩

theorem image_sub {r : Rule Conf} (h : preserves r) : subsumes [image r] inv := by
  cases r with
  | bind body =>
    unfold image inv invP
    exact Subsumption.subsumes_of_match
      (fun x => ((body x).rhs.th, (body x).rhs.ids, (body x).rhs.items, (body x).rhs.log))
      fun x hc => ⟨rfl, h x hc.1 hc.2⟩

theorem preserves_otr : ∀ r ∈ otr, preserves r := by
  simp only [otr, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rintro ⟨⟩ h hc
  · exact inv_voteT h
  · exact inv_voteF h
  · exact inv_recvT h
  · exact inv_recvF h
  · exact inv_decideT h hc
  · exact inv_decideF h hc
  · exact inv_updateT h hc
  · exact inv_updateF h hc
  · exact inv_loss h

end OTRA
