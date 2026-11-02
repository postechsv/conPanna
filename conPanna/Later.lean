import Lean

/-!
Deferred obligations: prove a theorem top-down now, its obligations elsewhere later.

* `later` closes a goal like `sorry`, but first makes its statement self-contained:
  the proof's local `let`s are unfolded, so the hole states a closed obligation.
* `#obligations thm` prints `thm`'s holes as theorem statements
  `thm.obligation_k`, ready to be pasted into another file and proved.
* `#link thm` rebuilds `thm`'s proof as `thm.linked`, with each such hole replaced by
  the theorem proving it; holes without one stay open (with a warning). The kernel
  re-checks the result.

The holes are ordinary `sorry`s (Lean's warning applies); `#print axioms` shows
whether a theorem still depends on any. `narrow` leaves its certification claims as the
typed axioms `laterAx` (completeness) and `laterSoundAx` (soundness), which are holes in the
same sense; `#claims thm` lists those `thm` still depends on.
-/

namespace Later

open Lean Meta Elab Tactic Command

/-- Close the goal like `sorry`, with its statement made self-contained. -/
elab "later" : tactic => withMainContext do
  let goal ← getMainGoal
  let P ← zetaReduce (← instantiateMVars (← goal.getType))
  if P.hasFVar then
    throwError "later: the statement depends on local variables{indentExpr P}"
  goal.assign (← mkSorry P false)
  replaceMainGoal []

/-- A plain `sorry` written in a proof is labeled: `sorryAx (Name → P) _ tag`.
The statement without the label, if `T` is such a type. -/
def unlabel? (T : Expr) : Option Expr :=
  match T with
  | .forallE _ (.const ``Lean.Name []) P _ => if P.hasLooseBVars then none else some P
  | _ => none

/-- A deferred certification claim (`laterAx key P U`, `laterSoundAx P U`). -/
def isClaim (e : Expr) : Bool :=
  e.isAppOfArity `Unification.laterAx 5 || e.isAppOfArity `Unification.laterSoundAx 4

/-- The holes of proof term `v`, in order: each occurrence, with its statement. A statement
with loose bound variables is a plain `sorry` depending on the proof's context. -/
def holeTerms (v : Expr) : MetaM (Array (Expr × Expr)) := do
  let r ← IO.mkRef #[]
  v.forEach fun e => do
    if e.isAppOfArity ``sorryAx 2 then
      let T := e.appFn!.appArg!
      r.modify (·.push (e, (unlabel? T).getD T))
  let claims ← IO.mkRef #[]
  v.forEach fun e => do
    if isClaim e then claims.modify (·.push e)
  let mut out ← r.get
  for e in ← claims.get do
    out := out.push (e, ← inferType e)
  return out

/-- The statements of the holes of proof term `v`, in order. -/
def holes (v : Expr) : MetaM (Array Expr) := return (← holeTerms v).map (·.2)

def proofOf (n : Name) : MetaM Expr := do
  let some v := (← getConstInfo n).value? | throwError "{n} has no proof term"
  return v

/-- Print a theorem's holes as theorem statements `thm.obligation_k`. -/
elab "#obligations " id:ident : command => liftTermElabM do
  let n ← realizeGlobalConstNoOverloadWithInfo id
  let mut msg := m!""
  for (P, i) in (← holes (← proofOf n)).zipIdx do
    if P.hasLooseBVars then
      msg := msg ++ m!"-- hole {i + 1}: a plain `sorry`; its statement depends on the proof's context\n\n"
    else
      -- binder types are printed, so the statement parses back (`x.1` needs `x`'s type)
      let stmt ← withOptions (pp.funBinderTypes.set · true) (ppExpr P)
      msg := msg ++ m!"theorem {n}.obligation_{i + 1} :{Format.nest 4 (Format.line ++ stmt)} := by\n  sorry\n\n"
  logInfo msg

/-- Rebuild a theorem's proof as `thm.linked`, each self-contained hole replaced by the
theorem `thm.obligation_k` (or, failing that, a theorem of this file) stating it. -/
elab "#link " id:ident : command => liftTermElabM do
  let n ← realizeGlobalConstNoOverloadWithInfo id
  let info ← getConstInfo n
  let local_ := (← getEnv).constants.map₂.toList.filterMap fun (c, ci) =>
    if ci matches .thmInfo _ && c != n then some ci else none
  let mut v ← proofOf n
  let mut used : Array Name := #[]
  for ((occ, P), i) in (← holeTerms v).zipIdx do
    if P.hasLooseBVars then continue
    let named := (← getEnv).find? (n ++ .mkSimple s!"obligation_{i + 1}")
    let named ← match named with
      | some ci => pure (if ← isDefEq ci.type P then some ci else none)
      | none => pure none
    let some c ← (match named with
        | some ci => pure (some ci)
        | none => local_.findM? fun ci => isDefEq ci.type P)
      | logWarning m!"#link: hole {i + 1} stays open, no theorem proves{indentExpr P}"
        continue
    -- a deferred claim becomes `c`
    if isClaim occ then
      v := v.replace fun e => if e == occ then some (mkConst c.name) else none
      used := used.push c.name
      continue
    -- a labeled hole `sorryAx (Name → P) _` becomes `fun _ => c`
    v := v.replace fun e =>
      if !e.isAppOfArity ``sorryAx 2 then none
      else if e.appFn!.appArg! == P then some (mkConst c.name)
      else if unlabel? e.appFn!.appArg! == some P then
        some (.lam `tag (mkConst ``Lean.Name) (mkConst c.name) .default)
      else none
    used := used.push c.name
  addDecl <| .thmDecl
    { name := n ++ `linked, levelParams := info.levelParams, type := info.type, value := v }
  logInfo m!"{n ++ `linked}: {used.size} holes filled by {used.toList}"

/-- List the deferred certification claims (`laterAx`, `laterSoundAx`) a theorem's
proof still depends on: the theorem holds modulo exactly these. -/
elab "#claims " id:ident : command => liftTermElabM do
  let n ← realizeGlobalConstNoOverloadWithInfo id
  let mut msg := m!""
  let mut k : Nat := 0
  for (e, P) in ← holeTerms (← proofOf n) do
    if isClaim e then
      k := k + 1
      let key := if e.isAppOfArity `Unification.laterAx 5 then m!" (certificate {e.getArg! 0})" else m!""
      msg := msg ++ m!"claim {k}{key}:{indentExpr P}\n"
  logInfo (if k == 0 then m!"{n}: no deferred claims" else m!"{n}: {k} deferred claims\n" ++ msg)

end Later
