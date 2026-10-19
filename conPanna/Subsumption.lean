import Expresso.core

/-!
Proving subsumption `subsumes A B` (every state of pattern `A` is a state of `B`)
patch by patch, by matching.

* `subsumes_of_patches`: each patch of `A` is subsumed by some patch of `B`.
* `subsumes_of_match`: a patch `∃x. ⟨s x | c x⟩` is subsumed by `∃y. ⟨t y | d y⟩`
  if a matching substitution `σ` sends each `x` satisfying `c` to a `y = σ x` with
  `t y = s x` and `d y`.
* `subsumes_of_empty`: a patch whose condition never holds is subsumed by anything.
* `subsumes_of_cover`, `subsumes_one`, `subsumes_of_split`: when a patch is covered
  by several patches of `B` together, split its condition on a predicate `q` and
  cover each half on its own.

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

/-- A patch whose condition never holds is subsumed by any pattern. -/
theorem subsumes_of_empty {A : Type u} {f : A → PatchBody α} {B : Pattern α}
    (h : ∀ x, ¬ (f x).cond) : subsumes [.bind f] B := by
  intro s hs
  simp only [Pattern.holds_cons, Pattern.holds_nil, or_false, Patch.holds,
    PatchBody.holds] at hs
  obtain ⟨x, -, hc⟩ := hs
  exact (h x hc).elim

/-- Each patch of `A` is subsumed by `B` (as a whole). -/
theorem subsumes_of_cover {A B : Pattern α} (h : ∀ a ∈ A, subsumes [a] B) : subsumes A B := by
  intro s ⟨a, ha, hs⟩
  exact h a ha s ⟨a, List.mem_singleton_self a, hs⟩

/-- A patch subsumed by one patch of `B` is subsumed by `B`. -/
theorem subsumes_one {a : Patch α} {B : Pattern α} (h : ∃ b ∈ B, subsumes [a] [b]) :
    subsumes [a] B := by
  obtain ⟨b, hb, hab⟩ := h
  intro s hs
  obtain ⟨b', hb', hs'⟩ := hab s hs
  exact ⟨b, hb, (List.mem_singleton.1 hb') ▸ hs'⟩

/-- Case split on `q`: the patch is subsumed if both halves, with `q` and with `¬ q`
added to its condition, are. -/
theorem subsumes_of_split {A : Type u} {f : A → PatchBody α} {B : Pattern α} (q : A → Prop)
    (h₁ : subsumes [.bind fun x => ⟨(f x).state, (f x).cond ∧ q x⟩] B)
    (h₂ : subsumes [.bind fun x => ⟨(f x).state, (f x).cond ∧ ¬ q x⟩] B) :
    subsumes [.bind f] B := by
  intro s hs
  simp only [Pattern.holds_cons, Pattern.holds_nil, or_false, Patch.holds,
    PatchBody.holds] at hs
  obtain ⟨x, hx, hc⟩ := hs
  by_cases hq : q x
  · exact h₁ s ⟨_, List.mem_singleton_self _, x, hx, hc, hq⟩
  · exact h₂ s ⟨_, List.mem_singleton_self _, x, hx, hc, hq⟩

end Subsumption
