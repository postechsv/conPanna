import Expresso.core

/-!
Proving subsumption `subsumes A B` (every state of pattern `A` is a state of `B`)
patch by patch, by matching.

* `subsumes_of_patches`: each patch of `A` is subsumed by some patch of `B`.
* `subsumes_of_match`: a patch `∃x. ⟨s x | c x⟩` is subsumed by `∃y. ⟨t y | d y⟩`
  if a matching substitution `σ` sends each `x` satisfying `c` to a `y = σ x` with
  `t y = s x` and `d y`.

Remark: these are sufficient conditions, not necessary ones. A patch can lie in the
union of several patches of `B` without lying in any single one (e.g. `n` arbitrary
is covered by `n` even ∪ `n` odd); such cases need a case split on the condition first.
-/

namespace Subsumption

open Expresso

universe u

variable {α : Type u}

/-- It suffices that each patch of `A` is subsumed by some patch of `B`. -/
theorem subsumes_of_patches {A B : Pattern α}
    (h : ∀ a ∈ A, ∃ b ∈ B, subsumes [a] [b]) : subsumes A B := by
  intro s ⟨a, ha, hs⟩
  obtain ⟨b, hb, hab⟩ := h a ha
  obtain ⟨b', hb', hs'⟩ := hab s ⟨a, List.mem_singleton_self a, hs⟩
  exact ⟨b, hb, (List.mem_singleton.1 hb') ▸ hs'⟩

/-- Matching: `∃x. ⟨s x | c x⟩ ⊑ ∃y. ⟨t y | d y⟩` if `σ` sends each `x` with `c x` to
`y = σ x` with `t y = s x` and `d y`. -/
theorem subsumes_of_match {A B : Type u} {f : A → PatchBody α} {g : B → PatchBody α}
    (σ : A → B) (h : ∀ x, (f x).cond → (g (σ x)).state = (f x).state ∧ (g (σ x)).cond) :
    subsumes [.bind f] [.bind g] := by
  intro s hs
  simp only [Pattern.holds_cons, Pattern.holds_nil, or_false, Patch.holds,
    PatchBody.holds] at hs ⊢
  obtain ⟨x, rfl, hc⟩ := hs
  exact ⟨σ x, h x hc⟩

end Subsumption
