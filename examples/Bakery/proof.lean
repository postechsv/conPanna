import examples.Bakery.rule
import conPanna.Unification.Certification.Multiset
import conPanna.Narrowing.Narrowing
import conPanna.Unification.Tactics.maudeUnify
import conPanna.Later
import conPanna.Subsumption
import conPanna.Unification.Tactics.maudeMatch
import conPanna.narrow

/-!
Bakery: the invariant `invP` and the top-level proofs that the protocol (`bakery`) and its
abortable extension (`abortable`) preserve it. `narrow` computes each post with Maude's
filtered unifiers; its certification claims (`laterAx`, `laterSoundAx`) are discharged in
`cert.lean` and linked in `main.lean`.
-/

namespace Bakery

open Expresso Unification Narrowing Subsumption


def allIdle (PS : ProcSet) : Prop := ∀ m ∈ PS.toMultiset, m = .idle

def noCrit (PS : ProcSet) : Prop := ∀ m ∈ PS.toMultiset, ∀ t, m ≠ .crit t

/-- `⟨c, c, PS⟩ | allIdle(PS)` -/
def initialP : Patch Conf := .bind fun ((c, PS) : Nat × ProcSet) =>
  ⟨⟨c, c, PS⟩, allIdle PS⟩

/-- `⟨N, M, PS⟩ | M < N ∧ noCrit(PS) ∧ tickets(PS) ⊆ [M, N) ∧ nodup` -/
def waitingP : Patch Conf := .bind fun ((N, M, PS) : Nat × Nat × ProcSet) =>
  ⟨⟨N, M, PS⟩, M < N ∧ noCrit PS ∧ (∀ t ∈ tickets PS, M ≤ t ∧ t < N) ∧ (tickets PS).Nodup⟩

/-- `⟨N, M, crit(M) + PS⟩ | M < N ∧ noCrit(PS) ∧ tickets(PS) ⊆ (M, N) ∧ nodup` -/
def criticalP : Patch Conf := .bind fun ((N, M, PS) : Nat × Nat × ProcSet) =>
  ⟨⟨N, M, {Mode.crit M} + PS⟩,
    M < N ∧ noCrit PS ∧ (∀ t ∈ tickets PS, M < t ∧ t < N) ∧ (tickets PS).Nodup⟩

def invP : Pattern Conf := [initialP, waitingP, criticalP]

/-! ## Domain lemmas
How the predicates act on sums and single processes. Not `@[simp]`: they are passed
explicitly where the post is simplified (later, to `narrow`). -/

theorem tickets_plus (X Y : ProcSet) : tickets (X + Y) = tickets X + tickets Y := by
  simp only [tickets, ACU.toMultiset_plus]
  induction X.toMultiset, Y.toMultiset using Quotient.inductionOn₂ with
  | h l₁ l₂ => simp [List.filterMap_append]

theorem tickets_wait (n : Nat) : tickets {Mode.wait n} = {n} := by
  simp only [tickets, ACU.toMultiset_elem]
  exact Multiset.filterMap_cons_some _ _ 0 rfl

theorem allIdle_plus (X Y : ProcSet) : allIdle (X + Y) ↔ allIdle X ∧ allIdle Y := by
  simp [allIdle, or_imp, forall_and]

theorem allIdle_wait (n : Nat) : allIdle {Mode.wait n} ↔ False := by
  simp [allIdle]

theorem noCrit_plus (X Y : ProcSet) : noCrit (X + Y) ↔ noCrit X ∧ noCrit Y := by
  simp [noCrit, or_imp, forall_and]

theorem noCrit_wait (n : Nat) : noCrit {Mode.wait n} := by
  simp [noCrit]

theorem tickets_unit : tickets ∅ = 0 := by
  simp [tickets]

theorem noCrit_unit : noCrit ∅ := by
  simp [noCrit]

theorem tickets_idle : tickets {Mode.idle} = 0 := by
  simp only [tickets, ACU.toMultiset_elem]
  exact Multiset.filterMap_cons_none _ 0 rfl

theorem tickets_crit (n : Nat) : tickets {Mode.crit n} = {n} := by
  simp only [tickets, ACU.toMultiset_elem]
  exact Multiset.filterMap_cons_some _ _ 0 rfl

theorem allIdle_idle : allIdle {Mode.idle} := by
  simp [allIdle]

theorem allIdle_crit (n : Nat) : allIdle {Mode.crit n} ↔ False := by
  simp [allIdle]

theorem noCrit_idle : noCrit {Mode.idle} := by
  simp [noCrit]

theorem noCrit_crit (n : Nat) : noCrit {Mode.crit n} ↔ False := by
  simp [noCrit]

theorem noCrit_of_allIdle {PS : ProcSet} (h : allIdle PS) : noCrit PS :=
  fun m hm t ht => by cases (h m hm) ▸ ht

theorem tickets_of_allIdle {PS : ProcSet} (h : allIdle PS) : tickets PS = 0 := by
  refine Multiset.eq_zero_of_forall_notMem fun t ht => ?_
  obtain ⟨m, hm, hmt⟩ := (Multiset.mem_filterMap _ _).1 ht
  rw [h m hm] at hmt
  cases hmt

theorem allIdle_of_noCrit {PS : ProcSet} (hnc : noCrit PS) (ht : tickets PS = 0) :
    allIdle PS := by
  intro m hm
  cases m with
  | idle => rfl
  | wait t =>
    have h : t ∈ tickets PS := (Multiset.mem_filterMap Mode.ticket? _).2 ⟨_, hm, rfl⟩
    rw [ht] at h
    exact absurd h (Multiset.notMem_zero t)
  | crit t => exact absurd rfl (hnc _ hm t)

/-- `bakery(invP) ⊆ invP`: every step of the protocol preserves the invariant. -/
theorem bakery_preserves_inv : isOverPost bakery invP invP := by
  narrow bakery from invP
    using [ACU.plus_unit, ACU.unit_plus,                                -- the ACU theory
      Multiset.nodup_add, Multiset.disjoint_singleton,                  -- multisets
      tickets_plus, tickets_wait, tickets_idle, tickets_crit, tickets_unit,   -- the domain
      allIdle_plus, allIdle_wait, allIdle_idle, allIdle_crit,
      noCrit_plus, noCrit_wait, noCrit_idle, noCrit_crit, noCrit_unit]
    as post hpost
  -- post: wake from initialP, waitingP, criticalP (1–3), enter (4), exit (5)
  refine over_of_subsumes hpost.1 (subsumes_of_cover fun a ha => ?_)
  rw [← post_eq] at ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl
  · -- wake: ⟨c+1, c, {wait c} + R⟩ | allIdle R  ⊑  waitingP
    apply subsumes_one
    maude_match waitingP
    simp [noCrit_plus, noCrit_wait, noCrit_of_allIdle hc, tickets_plus, tickets_wait,
      tickets_of_allIdle hc]
  · -- wake: ⟨N+1, M, {wait N} + R⟩ | …  ⊑  waitingP: the new ticket N is above all of R's
    apply subsumes_one
    maude_match waitingP
    obtain ⟨hMN, hnc, ⟨hle, hlt⟩, hnd⟩ := hc
    simp only [noCrit_plus, noCrit_wait, tickets_plus, tickets_wait, Multiset.mem_add,
      Multiset.mem_singleton, Multiset.nodup_add, Multiset.nodup_singleton,
      Multiset.disjoint_singleton, and_true, true_and]
    refine ⟨by omega, hnc, fun t ht => ?_, hnd, fun hN => absurd (hlt _ hN) (lt_irrefl _)⟩
    rcases ht with ht | rfl
    · exact ⟨hle t ht, by have := hlt t ht; omega⟩
    · omega
  · -- wake: ⟨N+1, M, {wait N} + ({crit M} + Z)⟩ | …  ⊑  criticalP
    apply subsumes_one
    maude_match criticalP
    obtain ⟨hMN, hnc, ⟨hgt, hlt⟩, hnd⟩ := hc
    simp only [noCrit_plus, noCrit_wait, tickets_plus, tickets_wait, Multiset.mem_add,
      Multiset.mem_singleton, Multiset.nodup_add, Multiset.nodup_singleton,
      Multiset.disjoint_singleton, and_true, true_and]
    refine ⟨by omega, hnc, fun t ht => ?_, hnd, fun hN => absurd (hlt _ hN) (lt_irrefl _)⟩
    rcases ht with ht | rfl
    · exact ⟨hgt t ht, by have := hlt t ht; omega⟩
    · omega
  · -- enter: ⟨N, M, {crit M} + R⟩ | …  ⊑  criticalP
    apply subsumes_one
    maude_match criticalP
    obtain ⟨hMN, hnc, ⟨hle, -, hlt⟩, hnot, hnd⟩ := hc
    exact ⟨hMN, hnc, fun t ht => ⟨lt_of_le_of_ne (hle t ht) (fun h => hnot (h ▸ ht)), hlt t ht⟩,
      hnd⟩
  · -- exit: ⟨N, M+1, {idle} + R⟩ | …
    unfold bakery_preserves_inv.post_5
    refine subsumes_of_split (fun x => x.1 = x.2.1 + 1) (subsumes_one ?_) (subsumes_one ?_)
    · -- N = M + 1: no ticket fits in (M, M+1), so R is all idle: initialP
      refine ⟨initialP, by simp [invP], ?_⟩
      unfold initialP
      refine subsumes_of_match (fun x => (x.1, {Mode.idle} + x.2.2)) fun x hc => ⟨?_, ?_⟩
      · simp [hc.2]
      · obtain ⟨⟨-, hnc, ⟨hgt, hlt⟩, -⟩, hN⟩ := hc
        have ht : tickets x.2.2 = 0 := Multiset.eq_zero_of_forall_notMem fun t h => by
          have := hgt t h; have := hlt t h; omega
        simp [allIdle_plus, allIdle_idle, allIdle_of_noCrit hnc ht]
    · -- N ≠ M + 1: waitingP
      maude_match waitingP
      obtain ⟨⟨hMN, hnc, ⟨hgt, hlt⟩, hnd⟩, hN⟩ := hc
      simp only [noCrit_plus, noCrit_idle, tickets_plus, tickets_idle, Multiset.zero_add, true_and]
      refine ⟨by omega, hnc, fun t ht => ⟨by have := hgt t ht; omega, hlt t ht⟩, hnd⟩

/-- `abortable(invP) ⊆ invP`: abort and skip preserve the invariant too. -/
theorem abortable_preserves_inv : isOverPost abortable invP invP := by
  narrow abortable from invP
    using [ACU.plus_unit, ACU.unit_plus,                                -- the ACU theory
      Multiset.nodup_add, Multiset.disjoint_singleton,                  -- multisets
      tickets_plus, tickets_wait, tickets_idle, tickets_crit, tickets_unit,   -- the domain
      allIdle_plus, allIdle_wait, allIdle_idle, allIdle_crit,
      noCrit_plus, noCrit_wait, noCrit_idle, noCrit_crit, noCrit_unit]
    as post hpost
  -- post: abort from waitingP, from criticalP (1–2), skip (3)
  refine over_of_subsumes hpost.1 (subsumes_of_cover fun a ha => ?_)
  rw [← post_eq] at ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl
  · -- abort: ⟨N, M, {idle} + R⟩ | …  ⊑  waitingP
    apply subsumes_one
    maude_match waitingP
    obtain ⟨hMN, hnc, ⟨⟨-, hle⟩, -, hlt⟩, -, hnd⟩ := hc
    simp only [noCrit_plus, noCrit_idle, tickets_plus, tickets_idle, Multiset.zero_add, true_and]
    exact ⟨hMN, hnc, fun t ht => ⟨hle t ht, hlt t ht⟩, hnd⟩
  · -- abort: ⟨N, M, {idle} + ({crit M} + Z)⟩ | …  ⊑  criticalP
    apply subsumes_one
    maude_match criticalP
    obtain ⟨hMN, hnc, ⟨⟨-, hgt⟩, -, hlt⟩, -, hnd⟩ := hc
    simp only [noCrit_plus, noCrit_idle, tickets_plus, tickets_idle, Multiset.zero_add, true_and]
    exact ⟨hMN, hnc, fun t ht => ⟨hgt t ht, hlt t ht⟩, hnd⟩
  · -- skip: ⟨N, M+1, R⟩ | …, nobody holds M, so the tickets lie in [M+1, N)
    unfold abortable_preserves_inv.post_3
    refine subsumes_of_split (fun x => x.1 = x.2.1 + 1) (subsumes_one ?_) (subsumes_one ?_)
    · -- N = M + 1: no ticket fits, so R is all idle: initialP
      refine ⟨initialP, by simp [invP], ?_⟩
      unfold initialP
      refine subsumes_of_match (fun x => (x.1, x.2.2)) fun x hc => ⟨?_, ?_⟩
      · simp [hc.2]
      · obtain ⟨⟨⟨-, hnc, ⟨hge, hlt⟩, -⟩, -, hM⟩, hN⟩ := hc
        have ht : tickets x.2.2 = 0 := Multiset.eq_zero_of_forall_notMem fun t h => by
          have := hge t h; have := hlt t h
          exact hM (by rwa [show x.2.1 = t by omega])
        exact allIdle_of_noCrit hnc ht
    · -- N ≠ M + 1: waitingP
      maude_match waitingP
      obtain ⟨⟨⟨hMN, hnc, ⟨hge, hlt⟩, hnd⟩, -, hM⟩, hN⟩ := hc
      refine ⟨by omega, hnc, fun t ht => ⟨?_, hlt t ht⟩, hnd⟩
      have := hge t ht
      rcases Nat.lt_or_eq_of_le this with h | h
      · omega
      · exact absurd (h ▸ ht) hM

end Bakery
