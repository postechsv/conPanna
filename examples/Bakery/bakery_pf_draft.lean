import examples.Bakery.bakery_pf_draft_demo

/-!
Bakery: the whole system preserves the invariant, by narrowing all three rules at once.
`narrow` computes one post for `bakery` (its rules in order: `wake`, `enter`, `exit`);
every certificate is deferred (`later`).
-/

namespace Bakery

open Expresso Unification Narrowing Subsumption


/-- `bakery(invP) ⊆ invP`: every step of the protocol preserves the invariant. -/
theorem bakery_preserves_inv : isOverPost bakery invP invP := by
  narrow bakery from invP
    using [ACU.plus_unit, ACU.unit_plus,                                -- the ACU theory
      Multiset.nodup_add, Multiset.disjoint_singleton,                  -- multisets
      tickets_plus, tickets_wait, tickets_idle, tickets_crit, tickets_unit,   -- the domain
      allIdle_plus, allIdle_wait, allIdle_idle, allIdle_crit,
      noCrit_plus, noCrit_wait, noCrit_idle, noCrit_crit, noCrit_unit]
    as post hpost
  -- post : 10 patches, rule by rule: wake (1–6), enter (7–8), exit (9–10)
  refine over_of_subsumes hpost.1 (subsumes_of_cover fun a ha => ?_)
  rw [← post_eq] at ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  -- wake
  · -- ⟨c+1, c, {wait c}⟩  ⊑  waitingP
    apply subsumes_one
    maude_match waitingP
    simp [noCrit_wait, tickets_wait]
  · -- ⟨c+1, c, {wait c} + R⟩ | allIdle R  ⊑  waitingP
    apply subsumes_one
    maude_match waitingP
    simp [noCrit_plus, noCrit_wait, noCrit_of_allIdle hc, tickets_plus, tickets_wait,
      tickets_of_allIdle hc]
  · -- ⟨N+1, M, {wait N}⟩ | M < N  ⊑  waitingP
    apply subsumes_one
    maude_match waitingP
    simp [noCrit_wait, tickets_wait]
    omega
  · -- ⟨N+1, M, {wait N} + R⟩ | …  ⊑  waitingP: the new ticket N is above all of R's
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
  · -- ⟨N+1, M, {wait N} + {crit M}⟩ | M < N  ⊑  criticalP
    apply subsumes_one
    maude_match criticalP
    simp [noCrit_wait, tickets_wait]
    omega
  · -- ⟨N+1, M, {wait N} + (Z + {crit M})⟩ | …  ⊑  criticalP
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
  -- enter
  · apply subsumes_one
    maude_match criticalP
    simpa [noCrit_unit, tickets_unit] using hc
  · apply subsumes_one
    maude_match criticalP
    obtain ⟨hMN, hnc, ⟨hle, hlt, -⟩, hnd, hnot⟩ := hc
    exact ⟨hMN, hnc, fun t ht => ⟨lt_of_le_of_ne (hle t ht) (fun h => hnot (h ▸ ht)), hlt t ht⟩,
      hnd⟩
  -- exit
  · -- ⟨N, M+1, {idle}⟩ | M < N
    unfold bakery_preserves_inv.post_9
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
    unfold bakery_preserves_inv.post_10
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



#print bakery
#print invP
#print isOverPost
#check bakery_preserves_inv
--#print bakery_preserves_inv
end Bakery
