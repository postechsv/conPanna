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

/-- The post has three candidates: from `initial` (refuted: `wait(c)` is not idle),
from `waiting` (lands in `critical`), and from `critical`: two processes in the
critical section, refuted by the ticket range. -/
theorem enter_preserves_inv : isOverPost [enterR] invP invP := by
  -- narrowing start --
  let Us : unifiers_R_P [enterR] invP := by maude_unify
  let post : Pattern Conf := post_R_P [enterR] invP Us
  have hpost : isPost [enterR] invP post :=
    certifyPost_R_P _ _ Us
      ⟨⟨⟨by later, by later⟩,     -- initial:  complete, sound
        ⟨by later, by later⟩,     -- waiting:  complete, sound
        ⟨by later, by later⟩,     -- critical: complete, sound
        trivial⟩, trivial⟩
  post_simp [post, Us, invP, enterR, initialP, waitingP, criticalP] at hpost
  -- compactify Us e.g. ...
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
