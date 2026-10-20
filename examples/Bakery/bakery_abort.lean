import examples.Bakery.bakery_pf_draft_demo

/-!
Bakery, abortable: a waiting process may give up its ticket (`abort`), and serving then
skips tickets nobody holds (`skip`, a rule with a side condition). The invariant `invP`
is unchanged: these two rules preserve it on their own (`abortable_preserves_inv`), and
`bakery_abort_pf.lean` combines this with `bakery_preserves_inv`.
-/

namespace Bakery

open Expresso Unification Narrowing Subsumption

/-- A waiting process gives up its ticket. -/
def abortR : Rule Conf := .bind fun ((N, M, T, R) : Nat × Nat × Nat × ProcSet) =>
  { lhs := ⟨N, M, {Mode.wait T} + R⟩, rhs := ⟨N, M, {Mode.idle} + R⟩ }

/-- Serving skips a ticket nobody holds (without the condition, it could skip past a
waiting process, or start serving a ticket while another process is critical). -/
def skipR : Rule Conf := .bind fun ((N, M, R) : Nat × Nat × ProcSet) =>
  { lhs := ⟨N, M, R⟩, rhs := ⟨N, M + 1, R⟩
    cond := M < N ∧ M ∉ tickets R }

def abortable : System Conf := [abortR, skipR]

theorem abortable_preserves_inv : isOverPost abortable invP invP := by
  narrow abortable from invP
    using [ACU.plus_unit, ACU.unit_plus,                                -- the ACU theory
      Multiset.nodup_add, Multiset.disjoint_singleton,                  -- multisets
      tickets_plus, tickets_wait, tickets_idle, tickets_crit, tickets_unit,   -- the domain
      allIdle_plus, allIdle_wait, allIdle_idle, allIdle_crit,
      noCrit_plus, noCrit_wait, noCrit_idle, noCrit_crit, noCrit_unit]
    as post hpost
  -- post : 5 patches: abort (1–4), skip (5); simplification already dropped `skip` from
  -- `initialP` (`M < N` fails) and from `criticalP` (`M ∉ tickets` fails: `crit M` holds M)
  refine over_of_subsumes hpost.1 (subsumes_of_cover fun a ha => ?_)
  rw [← post_eq] at ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl
  -- abort: one ticket fewer
  · -- ⟨N, M, {idle}⟩ | M < N  ⊑  waitingP
    apply subsumes_one
    maude_match waitingP
    simp [noCrit_idle, tickets_idle, hc.1]
  · -- ⟨N, M, {idle} + R⟩ | …  ⊑  waitingP
    apply subsumes_one
    maude_match waitingP
    obtain ⟨hMN, hnc, ⟨⟨hle, -⟩, hlt, -⟩, hnd, -⟩ := hc
    simp only [noCrit_plus, noCrit_idle, tickets_plus, tickets_idle, Multiset.zero_add, true_and]
    exact ⟨hMN, hnc, fun t ht => ⟨hle t ht, hlt t ht⟩, hnd⟩
  · -- ⟨N, M, {idle} + {crit M}⟩ | M < N  ⊑  criticalP
    apply subsumes_one
    maude_match criticalP
    simp [noCrit_idle, tickets_idle, hc.1]
  · -- ⟨N, M, {idle} + (Z + {crit M})⟩ | …  ⊑  criticalP
    apply subsumes_one
    maude_match criticalP
    obtain ⟨hMN, hnc, ⟨⟨hgt, -⟩, hlt, -⟩, hnd, -⟩ := hc
    simp only [noCrit_plus, noCrit_idle, tickets_plus, tickets_idle, Multiset.zero_add, true_and]
    exact ⟨hMN, hnc, fun t ht => ⟨hgt t ht, hlt t ht⟩, hnd⟩
  -- skip: nobody holds M, so the tickets lie in [M+1, N)
  · -- ⟨N, M+1, R⟩ | …
    unfold abortable_preserves_inv.post_5
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
