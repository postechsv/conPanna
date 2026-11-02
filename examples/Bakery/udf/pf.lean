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

/-! Test copy (udf branch): the Bakery definitions of bakery_pf_draft_demo.lean and the
narrowing of bakery_pf_draft.lean, up to `narrow`. -/

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

/-- `bakery(invP) ⊆ invP`: every step of the protocol preserves the invariant. -/
theorem bakery_preserves_inv : isOverPost bakery invP invP := by
  narrow bakery from invP
    using [ACU.plus_unit, ACU.unit_plus,                                -- the ACU theory
      Multiset.nodup_add, Multiset.disjoint_singleton,                  -- multisets
      tickets_plus, tickets_wait, tickets_idle, tickets_crit, tickets_unit,   -- the domain
      allIdle_plus, allIdle_wait, allIdle_idle, allIdle_crit,
      noCrit_plus, noCrit_wait, noCrit_idle, noCrit_crit, noCrit_unit]
    as post hpost
  -- the subsumption of the post (5 patches with filtered unifiers) is not part of this test
  sorry

end Bakery
