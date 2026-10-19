import examples.Bakery.model.bakery_sys
import conPanna.Unification.Certification.Multiset
import conPanna.Narrowing.Narrowing
import conPanna.Unification.Tactics.maudeUnify
import conPanna.Later
import conPanna.Subsumption
import conPanna.Unification.Tactics.maudeMatch

/-!
Bakery: `enter` preserves the invariant, proved top-down. Maude computes the
unifiers inside the proof (`maude_unify`); every certificate is deferred (`later`)
and proved in `bakery_obligation.lean`, and `bakery_pf.lean` links them.
Conditions are stated through `ACU.toMultiset`.
-/

/-! ## Dropping empty patches
A patch whose condition is `False` holds for no state. `drop_empty at h` removes such
patches from the post of `h : isPost R S P`: the shorter list is a different term but
holds for the same states, so `isPost` carries over (`isPost_of_holds_iff`). -/

-- should appear near isPost at core.lean
-- used by drop_empty tactic
theorem Expresso.isPost_of_holds_iff {α : Type _} {R : Expresso.System α}
    {S P Q : Expresso.Pattern α} (h : Expresso.isPost R S P)
    (e : ∀ s, P.holds s ↔ Q.holds s) : Expresso.isPost R S Q :=
  ⟨fun a b ha hs => (e b).1 (h.1 a b ha hs), fun b hb => h.2 b ((e b).2 hb)⟩

open Lean Meta Elab Tactic in
/-- Remove the patches with condition `False` from the post of `h : isPost R S P`. -/
elab "drop_empty" " at " h:ident : tactic => withMainContext do
  let ty ← instantiateMVars (← getLocalDeclFromUserName h.getId).type
  unless ty.isAppOfArity ``Expresso.isPost 4 do
    throwError "drop_empty: {h} is not `isPost R S P`"
  let some (T, ps) := ty.appArg!.listLit? | throwError "drop_empty: the post is not a list"
  -- `Patch.bind fun x => { state := …, cond := False }`
  let empty (p : Expr) : Bool := p.isAppOfArity ``Expresso.Patch.bind 3 &&
    match p.appArg! with
    | .lam _ _ b _ => b.isAppOfArity ``Expresso.PatchBody.mk 3 && b.appArg!.isConstOf ``False
    | _ => false
  let keep := ps.filter (!empty ·)
  if keep.length == ps.length then return
  let Q ← Term.exprToSyntax (← mkListLit T keep)
  evalTactic (← `(tactic| replace $h:ident := Expresso.isPost_of_holds_iff $h:ident (Q := $Q)
    (fun _ => by simp only [Expresso.Pattern.holds_cons, Expresso.Pattern.holds_nil,
      Expresso.Patch.holds, Expresso.PatchBody.holds, and_false, exists_false, false_or])))

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

/-! ## `narrow`
The snippet between `narrowing start` and `narrowing end` above, as one tactic:

  `narrow R from S using [lemmas] as post hpost`

1. `maude_unify`: the unifier table `Us` for every (rule, patch) cell;
2. `certifyPost_R_P R S Us`, with every certificate deferred (`later`);
3. the post computed (the narrowing definitions and those of `R`, `S` and their
   elements unfolded) and simplified with `lemmas` plus a base set, on the post only;
4. `drop_empty`;
5. each remaining patch named `<theorem>.<post>_i` (a definition, so the context stays
   short), with `post`, its definition `post_eq : [post_1, …] = post`, and
   `hpost : isPost R S post`. `unfold <theorem>.post_i at post_eq` shows a patch. -/

open Lean Meta Elab Tactic in
/-- The elements of a list literal, after unfolding. -/
partial def narrowElems (l : Expr) : MetaM (List Expr) := do
  let l ← whnf l
  if l.isAppOfArity ``List.cons 3 then return l.appFn!.appArg! :: (← narrowElems l.appArg!)
  return []

syntax (name := narrowTac) "narrow " term " from " term
  (" using " "[" term,* "]")? (" as " ident ident)? : tactic

open Lean Meta Elab Tactic Expresso Narrowing in
@[tactic narrowTac] def evalNarrow : Tactic := fun stx => withMainContext do
  let `(tactic| narrow $Rs from $Ss $[using [$ls,*]]? $[as $pn $hn]?) := stx
    | throwUnsupportedSyntax
  let postId := pn.getD (mkIdent `post)
  let hId := hn.getD (mkIdent `hpost)
  let R ← Term.elabTerm Rs none
  let S ← Term.elabTerm Ss none
  let α := (← whnf (← whnf (← inferType R)).appArg!).appArg!
  -- 1. the unifiers
  let st ← Dumper.model α
  Dumper.write st
  let Us ← MaudeUnify.forSystem st (mkConst ``PUnit.unit [mkLevelSucc (← getLevel α)]) R S
  -- 2. the post, every certificate deferred
  let cert ← mkFreshExprSyntheticOpaqueMVar (← mkAppM ``certificates_R_P #[R, S, Us])
  let main ← getMainGoal
  setGoals [cert.mvarId!]
  evalTactic (← `(tactic| (
    simp only [certificates_R_P, certificates_r_P, certificates_r_p]
    repeat' (first | exact trivial | constructor)
    all_goals later)))
  setGoals [main]
  let h ← mkAppM ``certifyPost_R_P #[R, S, Us, ← instantiateMVars cert]
  let (_, main) ← (← main.assert hId.getId (← inferType h) h).intro1P
  replaceMainGoal [main]
  -- 3. compute the post (unfold), then simplify it
  let mut defs : Array (TSyntax ``Lean.Parser.Tactic.simpLemma) := #[]
  for e in [R, S] ++ (← narrowElems R) ++ (← narrowElems S) do
    if let some c := e.getAppFn.constName? then
      unless c == ``List.cons || c == ``List.nil do
        defs := defs.push (← `(Lean.Parser.Tactic.simpLemma| $(mkIdent c):ident))
  evalTactic (← `(tactic| conv at $hId:ident =>
    arg 3
    simp only [post_R_P, post_r_P, post_r_p, List.map, post_r_p_u, List.cons_append,
      List.nil_append, List.append_nil, $defs,*]))
  -- simplify with the given lemmas plus the logic ones (theory and domain lemmas come
  -- from the caller)
  let lemmas ← ((ls.map (·.getElems)).getD #[]).mapM fun t =>
    `(Lean.Parser.Tactic.simpLemma| $t:term)
  evalTactic (← `(tactic| try (conv at $hId:ident =>
    arg 3
    simp [and_true, or_imp, forall_and, $lemmas,*])))
  -- 4. drop the patches with condition `False`
  evalTactic (← `(tactic| drop_empty at $hId:ident))
  -- 5. name the patches `<theorem>.<post>_i`; `post` with its defining equation
  withMainContext do
    let some decl := (← getLCtx).findFromUserName? hId.getId | throwError "narrow: lost {hId}"
    let hty ← instantiateMVars decl.type
    let some (T, ps) := hty.appArg!.listLit?
      | throwError "narrow: the post is not a list{indentExpr hty}"
    let base := (← Term.getDeclName?).getD `narrow
    let mut names : Array Expr := #[]
    for (p, i) in ps.zipIdx do
      let n := base ++ .mkSimple s!"{postId.getId.eraseMacroScopes}_{i + 1}"
      names := names.push (← mkAuxDefinition n T p (compile := false))
    -- state `hpost` with the names (the same statement, by unfolding), then abstract the list
    let postList ← mkListLit T names.toList
    let main ← (← getMainGoal).replaceLocalDeclDefEq decl.fvarId
      (mkAppN hty.getAppFn (hty.getAppArgs.set! 3 postList))
    replaceMainGoal [main]
    let postVal ← Term.exprToSyntax postList
    let eqId := mkIdent (.mkSimple s!"{postId.getId.eraseMacroScopes}_eq")
    evalTactic (← `(tactic| generalize $eqId:ident : $postVal = $postId:ident at $hId:ident))

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
