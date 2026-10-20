import examples.Bakery.bakery_obligation

/-!
Bakery: the proof of `bakery_preserves_inv` (the whole system) with its obligations linked in.
-/

namespace Bakery

#link bakery_preserves_inv

#print axioms bakery_preserves_inv.linked

#print bakery_preserves_inv.linked

/-! ## Mutual exclusion
`invP` contains the initial states and lies in `mutexP`; so does every reachable state. -/

open Expresso

def Mode.isCrit : Mode → Bool
  | .crit _ => true
  | _ => false

/-- The number of critical processes. -/
def crits (PS : ProcSet) : Nat := PS.toMultiset.countP (·.isCrit)

/-- At most one process is critical. -/
def mutexP : Pattern Conf := [.bind fun (s : Conf) => ⟨s, crits s.procs ≤ 1⟩]

theorem crits_noCrit {PS : ProcSet} (h : noCrit PS) : crits PS = 0 :=
  Multiset.countP_eq_zero.2 fun m hm => by
    cases m with
    | crit t => exact absurd rfl (h _ hm t)
    | _ => simp [Mode.isCrit]

theorem crits_plus (X Y : ProcSet) : crits (X + Y) = crits X + crits Y := by
  simp [crits, Multiset.countP_add]

theorem crits_crit (n : Nat) : crits {Mode.crit n} = 1 := by
  rw [crits, ACU.toMultiset_elem, ← Multiset.cons_zero, Multiset.countP_cons]; simp [Mode.isCrit]

theorem init_inv : subsumes [initialP] invP := fun s h => by
  simp only [invP, Pattern.holds_cons, Pattern.holds_nil, or_false] at h ⊢
  exact .inl h

theorem inv_mutex : subsumes invP mutexP := fun s hs => by
  simp only [invP, mutexP, initialP, waitingP, criticalP, Pattern.holds_cons,
    Pattern.holds_nil, or_false, Patch.holds, PatchBody.holds] at hs ⊢
  refine ⟨s, rfl, ?_⟩
  rcases hs with ⟨⟨c, PS⟩, rfl, h⟩ | ⟨⟨N, M, PS⟩, rfl, h⟩ | ⟨⟨N, M, PS⟩, rfl, h⟩
  · simp [crits_noCrit (noCrit_of_allIdle h)]
  · simp [crits_noCrit h.2.1]
  · simp [crits_plus, crits_crit, crits_noCrit h.2.1]

/-- Mutual exclusion: from an initial state, never two critical processes. -/
theorem bakery_mutex {x y : Conf} (hx : Pattern.holds [initialP] x) (hxy : bakery.steps x y) :
    mutexP.holds y :=
  invariant_safe init_inv bakery_preserves_inv.linked inv_mutex hx hxy

#print axioms bakery_mutex

end Bakery
