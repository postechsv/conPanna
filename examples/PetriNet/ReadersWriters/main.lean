import examples.PetriNet.ReadersWriters.cert

/-!
Readers-writers: the finished theorem. The invariance proof of `proof.lean` is linked with
its certification obligations (`cert.lean`): `#link` replaces every deferred claim by the
theorem proving it, and the kernel re-checks the result. From the initial marking (two
tokens, everyone idle), never a writer together with a reader, and never two writers.
-/

namespace ReadersWriters

open Expresso PetriNet Place

#link net_preserves_inv

/-- The number of writers and of readers in a marking. -/
def writers (M : Marking Place) : Nat := M.toMultiset.count writing
def readers (M : Marking Place) : Nat := M.toMultiset.count reading

/-- At most one writer, and never a writer together with a reader. -/
def safeP : Pattern (Marking Place) :=
  [.bind fun (M : Marking Place) => ⟨M, writers M ≤ 1 ∧ (writers M = 0 ∨ readers M = 0)⟩]

theorem count_allIdle {I : Marking Place} (h : allIdle I) {p : Place} (hp : p ≠ idle) :
    I.toMultiset.count p = 0 :=
  Multiset.count_eq_zero.2 fun hm => hp (h p hm)

theorem init_inv : subsumes [freeP] invP := fun s h => by
  simp only [invP, Pattern.holds_cons, Pattern.holds_nil, or_false] at h ⊢
  exact .inl h

theorem inv_safe : subsumes invP safeP := fun s hs => by
  simp only [invP, safeP, freeP, oneReaderP, twoReadersP, writerP, Pattern.holds_cons,
    Pattern.holds_nil, or_false, Patch.holds, PatchBody.holds] at hs ⊢
  refine ⟨s, rfl, ?_⟩
  have hw {I : Marking Place} (h : allIdle I) := count_allIdle h (p := writing) (by decide)
  have hr {I : Marking Place} (h : allIdle I) := count_allIdle h (p := reading) (by decide)
  rcases hs with ⟨I, rfl, h⟩ | ⟨I, rfl, h⟩ | ⟨I, rfl, h⟩ | ⟨I, rfl, h⟩ <;>
    simp [writers, readers, ACU.toMultiset_plus, ACU.toMultiset_elem, hw h, hr h]

/-- Safety: from the initial marking, at most one writer and no writer beside a reader. -/
theorem net_safe {x y : Marking Place} (hx : Pattern.holds [freeP] x) (hxy : net.steps x y) :
    safeP.holds y :=
  invariant_safe init_inv net_preserves_inv.linked inv_safe hx hxy

#claims net_preserves_inv.linked
#print axioms net_safe

end ReadersWriters
