import examples.Bakery.model.bakery_sys
import conPanna.Unification.Certification.Multiset
import conPanna.Narrowing.Narrowing
import conPanna.Unification.Tactics.maudeUnify
import conPanna.Later

/-!
Bakery: `enter` preserves the invariant, proved top-down. Maude computes the
unifiers inside the proof (`maude_unify`); every certificate is deferred (`later`)
and proved in `bakery_obligation.lean`, and `bakery_pf.lean` links them.
Conditions are stated through `ACU.toMultiset`.
-/

/-! ## Simplifying a post
`post_simp [defs] at h` turns `h : isPost R S P` into the same statement about `P`
computed: the cells' posts concatenated, with `∧ True` and `+ ∅` dropped. Only `P`
is rewritten; `R` and `S` stay folded. `defs` are the definitions to unfold in `P`. -/

syntax "post_simp " "[" ident,* "]" " at " ident : tactic

open Expresso Narrowing Lean.Parser.Tactic in
macro_rules
  | `(tactic| post_simp [$defs,*] at $h) => do
    let defs ← defs.getElems.mapM fun d => `(simpLemma| $d:ident)
    `(tactic| conv at $h:ident =>
                arg 3
                simp only [post_R_P, post_r_P, post_r_p, List.map, post_r_p_u,
                  List.cons_append, List.nil_append, List.append_nil, and_true,
                  ACU.plus_unit, ACU.unit_plus, $defs,*])

namespace Bakery

open Expresso Unification Narrowing

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
How the predicates act on bags of no, one, or several processes. -/

@[simp] theorem tickets_plus (X Y : ProcSet) : tickets (X + Y) = tickets X + tickets Y := by
  simp only [tickets, ACU.toMultiset_plus]
  induction X.toMultiset, Y.toMultiset using Quotient.inductionOn₂ with
  | h l₁ l₂ => simp [List.filterMap_append]

@[simp] theorem tickets_wait (n : Nat) : tickets {Mode.wait n} = {n} := by
  simp only [tickets, ACU.toMultiset_elem]
  exact Multiset.filterMap_cons_some _ _ 0 rfl

@[simp] theorem allIdle_plus (X Y : ProcSet) : allIdle (X + Y) ↔ allIdle X ∧ allIdle Y := by
  simp [allIdle, or_imp, forall_and]

@[simp] theorem allIdle_wait (n : Nat) : allIdle {Mode.wait n} ↔ False := by
  simp [allIdle]

@[simp] theorem noCrit_plus (X Y : ProcSet) : noCrit (X + Y) ↔ noCrit X ∧ noCrit Y := by
  simp [noCrit, or_imp, forall_and]

@[simp] theorem noCrit_wait (n : Nat) : noCrit {Mode.wait n} := by
  simp [noCrit]

/-- The post has three candidates: from `initial` (refuted: `wait(c)` is not idle),
from `waiting` (lands in `critical`), and from `critical`: two processes in the
critical section, refuted by the ticket range. -/
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
  post_simp [post, Us, invP, enterR, initialP, waitingP, criticalP] at hpost
  simp [or_imp, forall_and, Multiset.nodup_add, Multiset.disjoint_singleton] at hpost  -- domain
  -- narrowing end --

  -- what remains: the (simplified) post is contained in the invariant
  refine over_of_subsumes hpost.1 ?_
  sorry -- TODO: completeness & soundness instead of 1 & 2

-- TODOs
-- filter bot
-- flatten disjunctions
-- user friendly syntax for patches
-- unfoldable defintions for patches so user can unfold state and cond at will
-- support A/C/AC + free/U 6 combinations as "basic theories" for maude_unify and dump
-- prevent .cache interference
-- certification obligation printing so user coulde copy-paste as lemmas
-- syntax highlighting error due to meta programming
-- check maude producer is deterministic (i.e. no rules, only equations)

#print axioms enter_preserves_inv

end Bakery
