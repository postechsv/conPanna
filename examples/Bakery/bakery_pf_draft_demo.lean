import examples.Bakery.model.bakery_sys
import conPanna.Unification.Certification.Multiset
import conPanna.Narrowing.Narrowing
import conPanna.Unification.Tactics.maudeUnify
import conPanna.Later
import conPanna.Subsumption
import conPanna.Unification.Tactics.maudeMatch
import conPanna.narrow

/-!
Bakery: `enter` preserves the invariant, proved top-down. Maude computes the
unifiers inside the proof (`maude_unify`); every certificate is deferred (`later`)
and proved in `bakery_obligation.lean`, and `bakery_pf.lean` links them.
Conditions are stated through `ACU.toMultiset`.
-/

namespace Bakery

open Expresso Unification Narrowing Subsumption

def Mode.ticket? : Mode → Option Nat
  | .idle => none
  | .wait t => some t
  | .crit t => some t

/-- Tickets of the waiting and critical processes. -/
def tickets (PS : ProcSet) : Multiset Nat := PS.toMultiset.filterMap Mode.ticket?

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

/-- `enterR(invP) ⊆ invP`: `enter` preserves the invariant. -/
theorem enter_preserves_inv : isOverPost [enterR] invP invP := by
  narrow [enterR] from invP
    using [ACU.plus_unit, ACU.unit_plus,                          -- the ACU theory
      Multiset.nodup_add, Multiset.disjoint_singleton,            -- multisets
      tickets_plus, tickets_wait, allIdle_plus, allIdle_wait,     -- the domain
      noCrit_plus, noCrit_wait]
    as post hpost
  -- simplification: 6 -> 2 patches

  --unfold enter_preserves_inv.post_1 at post_eq   -- post_1 spelled out, post_2 still folded
  --unfold enter_preserves_inv.post_2 at post_eq   -- both spelled out

  refine over_of_subsumes hpost.1 (subsumes_of_patches fun a ha => ?_)
  rw [← post_eq] at ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl
  · maude_match criticalP
    simpa [noCrit_unit, tickets_unit] using hc
  · maude_match criticalP
    obtain ⟨hMN, hnc, ⟨hle, hlt, -⟩, hnd, hnot⟩ := hc
    exact ⟨hMN, hnc, fun t ht => ⟨lt_of_le_of_ne (hle t ht) (fun h => hnot (h ▸ ht)), hlt t ht⟩,
      hnd⟩

/-- `wakeR(invP) ⊆ invP`: taking a ticket preserves the invariant. -/
theorem wake_preserves_inv : isOverPost [wakeR] invP invP := by
  narrow [wakeR] from invP
    using [ACU.plus_unit, ACU.unit_plus,                                -- the ACU theory
      Multiset.nodup_add, Multiset.disjoint_singleton,                  -- multisets
      tickets_plus, tickets_wait, tickets_idle, tickets_crit, tickets_unit,   -- the domain
      allIdle_plus, allIdle_wait, allIdle_idle, allIdle_crit,
      noCrit_plus, noCrit_wait, noCrit_idle, noCrit_crit, noCrit_unit]
    as post hpost
  -- simplification: 6 -> 6 patches

  refine over_of_subsumes hpost.1 (subsumes_of_patches fun a ha => ?_)
  rw [← post_eq] at ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl
  · -- ⟨c+1, c, {wait c}⟩  ⊑  waitingP
    maude_match waitingP
    simp [noCrit_wait, tickets_wait]
  · -- ⟨c+1, c, {wait c} + R⟩ | allIdle R  ⊑  waitingP
    maude_match waitingP
    simp [noCrit_plus, noCrit_wait, noCrit_of_allIdle hc, tickets_plus, tickets_wait,
      tickets_of_allIdle hc]
  · -- ⟨N+1, M, {wait N}⟩ | M < N  ⊑  waitingP
    maude_match waitingP
    simp [noCrit_wait, tickets_wait]
    omega
  · -- ⟨N+1, M, {wait N} + R⟩ | …  ⊑  waitingP: the new ticket N is above all of R's
    maude_match waitingP
    obtain ⟨hMN, hnc, ⟨hle, hlt⟩, hnd⟩ := hc
    simp only [noCrit_plus, noCrit_wait, tickets_plus, tickets_wait, Multiset.mem_add,
      Multiset.mem_singleton, Multiset.nodup_add, Multiset.nodup_singleton,
      Multiset.disjoint_singleton, and_true, true_and]
    refine ⟨by omega, hnc, fun t ht => ?_, hnd, fun hN => absurd (hlt _ hN) (lt_irrefl _)⟩
    rcases ht with ht | rfl
    · exact ⟨hle t ht, by have := hlt t ht; omega⟩
    · omega
  · -- ⟨N+1, M, {wait N} + {crit M}⟩ | M < N  ⊑  criticalP
    maude_match criticalP
    simp [noCrit_wait, tickets_wait]
    omega
  · -- ⟨N+1, M, {wait N} + (Z + {crit M})⟩ | …  ⊑  criticalP
    maude_match criticalP
    obtain ⟨hMN, hnc, ⟨hgt, hlt⟩, hnd⟩ := hc
    simp only [noCrit_plus, noCrit_wait, tickets_plus, tickets_wait, Multiset.mem_add,
      Multiset.mem_singleton, Multiset.nodup_add, Multiset.nodup_singleton,
      Multiset.disjoint_singleton, and_true, true_and]
    refine ⟨by omega, hnc, fun t ht => ?_, hnd, fun hN => absurd (hlt _ hN) (lt_irrefl _)⟩
    rcases ht with ht | rfl
    · exact ⟨hgt t ht, by have := hlt t ht; omega⟩
    · omega

/-- `exitR(invP) ⊆ invP`: leaving the critical section preserves the invariant. Each
patch lands in `initialP` when `N = M + 1` (every ticket served) and in `waitingP`
otherwise, so its condition is split first. -/
theorem exit_preserves_inv : isOverPost [exitR] invP invP := by
  narrow [exitR] from invP
    using [ACU.plus_unit, ACU.unit_plus,                                -- the ACU theory
      Multiset.nodup_add, Multiset.disjoint_singleton,                  -- multisets
      tickets_plus, tickets_wait, tickets_idle, tickets_crit, tickets_unit,   -- the domain
      allIdle_plus, allIdle_wait, allIdle_idle, allIdle_crit,
      noCrit_plus, noCrit_wait, noCrit_idle, noCrit_crit, noCrit_unit]
    as post hpost
  -- simplification: 8 -> 2 patches

  refine over_of_subsumes hpost.1 (subsumes_of_cover fun a ha => ?_)
  rw [← post_eq] at ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl
  · -- ⟨N, M+1, {idle}⟩ | M < N
    unfold exit_preserves_inv.post_1
    refine subsumes_of_split (fun x => x.1 = x.2 + 1) (subsumes_one ?_) (subsumes_one ?_)
    · -- N = M + 1: initialP
      refine ⟨initialP, by simp [invP], ?_⟩
      unfold initialP
      refine subsumes_of_match (fun x => (x.1, {Mode.idle})) fun x hc => ⟨?_, ?_⟩
      · simp [hc.2]
      · simp [allIdle_idle]
    · -- N ≠ M + 1: waitingP
      maude_match waitingP
      simp [noCrit_idle, tickets_idle]
      omega
  · -- ⟨N, M+1, {idle} + R⟩ | …
    unfold exit_preserves_inv.post_2
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

-- TODOs
-- user friendly syntax for patches
-- support A/C/AC + free/U 6 combinations as "basic theories" for maude_unify and dump
-- prevent .cache interference
-- check maude producer is deterministic (i.e. no rules, only equations)

--#print axioms enter_preserves_inv
--#obligations enter_preserves_inv



/- What `narrow` does, step by step: the theorem below with its narrowing written out.
Kept as an illustration (commented out).

example : isOverPost [enterR] invP invP := by
  -- narrowing start --
  let Us : unifiers_R_P [enterR] invP := by maude_unify  -- compactify Us
  let post : Pattern Conf := post_R_P [enterR] invP Us
  have hpost : isPost [enterR] invP post :=
    certifyPost_R_P _ _ Us
      ⟨⟨⟨by later, by later⟩,     -- initial:  complete, sound
        ⟨by later, by later⟩,     -- waiting:  complete, sound
        ⟨by later, by later⟩,     -- critical: complete, sound
        trivial⟩, trivial⟩
  -- compute the post: unfold the narrowing definitions and those of the rule and patterns
  conv at hpost =>
    arg 3
    simp only [post_R_P, post_r_P, post_r_p, List.map, post_r_p_u, List.cons_append,
      List.nil_append, List.append_nil, and_true, ACU.plus_unit, ACU.unit_plus,
      post, Us, invP, enterR, initialP, waitingP, criticalP]
  -- domain simplification: the domain lemmas, plus logic and multiset facts
  simp [tickets_plus, tickets_wait, allIdle_plus, allIdle_wait, noCrit_plus, noCrit_wait,
    or_imp, forall_and, Multiset.nodup_add, Multiset.disjoint_singleton] at hpost
  drop_empty at hpost
  -- narrowing end --

  -- what remains: the (simplified) post is contained in the invariant
  refine over_of_subsumes hpost.1 (subsumes_of_patches fun a ha => ?_)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl
  · -- ⟨N, M, {crit M}⟩ | M < N   ⊑  criticalP (Maude finds PS := ∅)
    maude_match criticalP
    simpa [noCrit_unit, tickets_unit] using hc
  · -- ⟨N, M, {crit M} + R⟩ | …   ⊑  criticalP (Maude finds PS := R)
    maude_match criticalP
    -- the one real step: M ≤ t and t ≠ M (M is not a ticket of R) give M < t
    obtain ⟨hMN, hnc, ⟨hle, hlt, -⟩, hnd, hnot⟩ := hc
    exact ⟨hMN, hnc, fun t ht => ⟨lt_of_le_of_ne (hle t ht) (fun h => hnot (h ▸ ht)), hlt t ht⟩,
      hnd⟩
-/

end Bakery
