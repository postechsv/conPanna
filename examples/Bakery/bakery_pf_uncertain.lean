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

/- enterR(invP) ⊆ invP -/
theorem enter_preserves_inv : isOverPost [enterR] invP invP := by
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

/-- The same theorem, with `narrow` doing the narrowing. -/
theorem enter_preserves_inv' : isOverPost [enterR] invP invP := by
  narrow [enterR] from invP
    using [ACU.plus_unit, ACU.unit_plus,                          -- the ACU theory
      Multiset.nodup_add, Multiset.disjoint_singleton,            -- multisets
      tickets_plus, tickets_wait, allIdle_plus, allIdle_wait,     -- the domain
      noCrit_plus, noCrit_wait]
    as post hpost
  -- post : Pattern Conf,  post_eq : [post_1, post_2] = post,  hpost : isPost [enterR] invP post
  -- inspecting the post at will, in its definition:
  unfold enter_preserves_inv'.post_1 at post_eq   -- post_1 spelled out, post_2 still folded
  unfold enter_preserves_inv'.post_2 at post_eq   -- both spelled out



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

-- TODOs
-- user friendly syntax for patches
-- unfoldable defintions for patches so user can unfold state and cond at will
-- support A/C/AC + free/U 6 combinations as "basic theories" for maude_unify and dump
-- prevent .cache interference
-- check maude producer is deterministic (i.e. no rules, only equations)

#print axioms enter_preserves_inv

end Bakery
