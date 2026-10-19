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
`Pattern.flatten` lists a pattern's disjuncts without `⊥`, right-associated. It is not
the same term, but it holds for the same states (`holds_flatten`), so `isPost` carries
over (`isPost_flatten`). `post_simp [defs] at h` turns `h : isPost R S P` into the same
statement about `P` computed, flattened, with `∧ True` and `+ ∅` dropped; only `P` is
rewritten, `R` and `S` stay folded. `defs` are the definitions to unfold in `P`. -/

namespace Expresso

universe u
variable {α : Type u}

/-- The disjuncts of a pattern, in order, without `⊥`. -/
def Pattern.disjuncts : Pattern α → List (Patch α)
  | .bott => []
  | .patch p => [p]
  | .disj l r => l.disjuncts ++ r.disjuncts

/-- A right-associated disjunction; `⊥` only when empty. -/
def Pattern.ofList : List (Patch α) → Pattern α
  | [] => .bott
  | [p] => .patch p
  | p :: ps => .disj (.patch p) (ofList ps)

def Pattern.flatten (P : Pattern α) : Pattern α := ofList P.disjuncts

theorem Pattern.holds_ofList (ps : List (Patch α)) (s : α) :
    (ofList ps).holds s ↔ ∃ p ∈ ps, p.holds s := by
  induction ps with
  | nil => simp [ofList, Pattern.holds]
  | cons p ps ih =>
    cases ps with
    | nil => simp [ofList, Pattern.holds]
    | cons q qs => simp only [ofList, Pattern.holds] at ih ⊢; simp [ih]

theorem Pattern.holds_disjuncts (P : Pattern α) (s : α) :
    P.holds s ↔ ∃ p ∈ P.disjuncts, p.holds s := by
  induction P with
  | bott => simp [disjuncts, Pattern.holds]
  | patch p => simp [disjuncts, Pattern.holds]
  | disj l r ihl ihr => simp [disjuncts, Pattern.holds, ihl, ihr, or_and_right, exists_or]

theorem Pattern.holds_flatten (P : Pattern α) (s : α) : P.flatten.holds s ↔ P.holds s := by
  rw [flatten, holds_ofList, holds_disjuncts]

theorem isPost_flatten {R : System α} {S P : Pattern α} (h : isPost R S P) :
    isPost R S P.flatten :=
  ⟨fun a b ha hs => (P.holds_flatten b).2 (h.1 a b ha hs),
   fun b hb => h.2 b ((P.holds_flatten b).1 hb)⟩

end Expresso

syntax "post_simp " "[" ident,* "]" " at " ident : tactic

open Expresso Narrowing Lean.Parser.Tactic in
macro_rules
  | `(tactic| post_simp [$defs,*] at $h) => do
    let defs ← defs.getElems.mapM fun d => `(simpLemma| $d:ident)
    `(tactic| (replace $h:ident := isPost_flatten $h:ident
               conv at $h:ident =>
                 arg 3
                 simp only [Pattern.flatten, Pattern.disjuncts, Pattern.ofList, post_R_P,
                   post_r_P, post_r_p, post_r_p_u, List.cons_append, List.nil_append,
                   List.append_nil, and_true, ACU.plus_unit, ACU.unit_plus, $defs,*]))

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

def invP : Pattern Conf :=
  .disj (.patch initialP) (.disj (.patch waitingP) (.patch criticalP))

/-- The post has three candidates: from `initial` (refuted: `wait(c)` is not idle),
from `waiting` (lands in `critical`), and from `critical`: two processes in the
critical section, refuted by the ticket range. -/
theorem enter_preserves_inv : isOverPost (.rule enterR) invP invP := by
  -- narrowing start --
  let Us : unifiers_R_P (.rule enterR) invP := by maude_unify
  let post : Pattern Conf := post_R_P (.rule enterR) invP Us
  have hpost : isPost (.rule enterR) invP (post) :=
    certifyPost_R_P _ _ Us
      ⟨⟨by later, by later⟩,     -- initial:  complete, sound
       ⟨by later, by later⟩,     -- waiting:  complete, sound
       ⟨by later, by later⟩⟩    -- critical: complete, sound
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
