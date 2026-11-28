import examples.PetriNet.ReadersWriters.rule
import conPanna.BaseTheory.Multiset
import conPanna.Narrowing.Narrowing
import conPanna.Unification.Tactics.maudeUnify
import conPanna.Later
import conPanna.Subsumption
import conPanna.Unification.Tactics.maudeMatch
import conPanna.narrow

/-!
Readers-writers: the invariant `invP` and the proof that the net preserves it. Every
reachable marking is one of four shapes, the other processes idle.
-/

namespace ReadersWriters

open Expresso Unification Narrowing Subsumption PetriNet Place

/-- Every process in `M` is idle (and `M` holds no token). -/
def allIdle (M : Marking Place) : Prop := ∀ p ∈ M.toMultiset, p = .idle

/-- `tok ⊗ tok ⊗ I`: nobody reads or writes. -/
def freeP : Patch (Marking Place) := .bind fun (I : Marking Place) => ⟨{tok} + {tok} + I, allIdle I⟩

/-- `reading ⊗ tok ⊗ I`: one reader. -/
def oneReaderP : Patch (Marking Place) := .bind fun (I : Marking Place) => ⟨{reading} + {tok} + I, allIdle I⟩

/-- `reading ⊗ reading ⊗ I`: two readers. -/
def twoReadersP : Patch (Marking Place) := .bind fun (I : Marking Place) =>
  ⟨{reading} + {reading} + I, allIdle I⟩

/-- `writing ⊗ I`: one writer. -/
def writerP : Patch (Marking Place) := .bind fun (I : Marking Place) => ⟨{writing} + I, allIdle I⟩

def invP : Pattern (Marking Place) := [freeP, oneReaderP, twoReadersP, writerP]

/-! ## Domain lemmas -/

theorem allIdle_plus (X Y : Marking Place) : allIdle (X + Y) ↔ allIdle X ∧ allIdle Y := by
  simp [allIdle, or_imp, forall_and]

theorem allIdle_unit : allIdle ∅ := by simp [allIdle]
theorem allIdle_idle : allIdle {idle} := by simp [allIdle]
theorem allIdle_reading : allIdle {reading} ↔ False := by simp [allIdle]
theorem allIdle_writing : allIdle {writing} ↔ False := by simp [allIdle]
theorem allIdle_tok : allIdle {tok} ↔ False := by simp [allIdle]

/-- `net(invP) ⊆ invP`: every transition preserves the invariant. -/
theorem net_preserves_inv : isOverPost net invP invP := by
  narrow net from invP
    using [ACU.plus_unit, ACU.unit_plus, allIdle_plus, allIdle_unit, allIdle_idle,
      allIdle_reading, allIdle_writing, allIdle_tok]
    as post hpost
  refine over_of_subsumes hpost.1 (subsumes_of_cover fun a ha => ?_)
  rw [← post_eq] at ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  -- post: start reading (1–2), stop reading (3–4), start writing (5), stop writing (6)
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl
  · -- reading ⊗ tok ⊗ I  ⊑  oneReaderP
    apply subsumes_one; maude_match oneReaderP; exact hc
  · -- reading ⊗ reading ⊗ I  ⊑  twoReadersP
    apply subsumes_one; maude_match twoReadersP; exact hc
  · -- idle ⊗ tok ⊗ tok ⊗ I  ⊑  freeP, with the reader back among the idle
    apply subsumes_one; maude_match freeP; simp [allIdle_plus, allIdle_idle, hc]
  · -- idle ⊗ tok ⊗ reading ⊗ I  ⊑  oneReaderP
    apply subsumes_one; maude_match oneReaderP; simp [allIdle_plus, allIdle_idle, hc]
  · -- writing ⊗ I  ⊑  writerP
    apply subsumes_one; maude_match writerP; exact hc
  · -- idle ⊗ tok ⊗ tok ⊗ I  ⊑  freeP
    apply subsumes_one; maude_match freeP; simp [allIdle_plus, allIdle_idle, hc]

end ReadersWriters
