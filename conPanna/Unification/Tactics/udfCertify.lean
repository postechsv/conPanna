import conPanna.Unification.Tactics.udfStore
import conPanna.Unification.Certification.UdfTactics

/-!
`udf_certify` proves a goal `complete P U`, like `maude_certify_comp`, from a derivation
in the Unification Derivation Format (documentation/derivation-format.md).

1. The goal is restated in literal form and encoded (`UdfStore.prepare`).
2. The derivation is the one narrowing stored for this claim (udfStore.lean), if any;
   otherwise `producer/tools/udf.py` runs the instrumented Maude and extracts a UDF
   derivation whose leaves are covered by the unifiers `U`.
3. The derivation is parsed here, its states are recomputed, and each step becomes one
   rule of the calculus (Calculus.lean, AcuSolve.lean) with its obligations closed by
   the fixed tactics of Tactics.lean and UdfTactics.lean. The steps are elaborated
   against the goal. Nothing outside Lean is trusted, the derivation included.
-/

namespace UdfCertify

open Lean Meta Elab Tactic Unification MaudeAdapter

/-! ## S-expressions -/

inductive Sx where
  | atom (s : String)
  | list (xs : Array Sx)
deriving Inhabited

def tokenize (s : String) : Array String := Id.run do
  let mut out : Array String := #[]
  let mut cur := ""
  let mut comment := false
  for c in s.toList do
    if comment then
      if c == '\n' then comment := false
      continue
    if c == ';' || c == '(' || c == ')' || c.isWhitespace then
      if !cur.isEmpty then out := out.push cur; cur := ""
      if c == ';' then comment := true
      else if c == '(' || c == ')' then out := out.push c.toString
    else
      cur := cur.push c
  if !cur.isEmpty then out := out.push cur
  return out

partial def parseAt (toks : Array String) (i : Nat) : Except String (Sx × Nat) := do
  let some t := toks[i]? | throw "udf: unexpected end of file"
  if t == ")" then throw "udf: unexpected )"
  if t != "(" then return (.atom t, i + 1)
  let mut j := i + 1
  let mut xs : Array Sx := #[]
  while toks[j]? != some ")" do
    if j ≥ toks.size then throw "udf: unclosed ("
    let (x, j') ← parseAt toks j
    xs := xs.push x
    j := j'
  return (.list xs, j + 1)

def parseAll (s : String) : Except String (Array Sx) := do
  let toks := tokenize s
  let mut i := 0
  let mut out := #[]
  while i < toks.size do
    let (x, i') ← parseAt toks i
    out := out.push x
    i := i'
  return out

def Sx.atom! : Sx → String
  | .atom s => s
  | _ => ""

def Sx.items : Sx → Array Sx
  | .list xs => xs
  | _ => #[]

/-- The value after keyword `k` in a list of arguments. -/
def kw (xs : Array Sx) (k : String) : Option Sx := Id.run do
  for i in [0:xs.size] do
    if let .atom a := xs[i]! then
      if a == k then return xs[i + 1]?
  return none

def Sx.nat! (x : Sx) : Nat := x.atom!.toNat!

def Sx.int! (x : Sx) : Int := x.atom!.toInt!

/-! ## Derivations -/

inductive T where
  | var (n : String)
  | app (op : String) (args : Array T)
deriving Inhabited, BEq

structure Sig where
  ops : Array (String × Array String × String) := #[]
  acu : Array (String × String × String) := #[]     -- operator, sort, identity
  vars : Array (String × String) := #[]

def Sig.isOp (s : Sig) (n : String) : Bool :=
  s.ops.any (·.1 == n) || s.acu.any (·.1 == n) || s.acu.any (·.2.2 == n)

partial def Sig.term (s : Sig) : Sx → T
  | .atom a => if s.isOp a then .app a #[] else .var a
  | .list xs => .app xs[0]!.atom! (xs[1:].toArray.map s.term)

structure Step where
  rule : String
  args : Array Sx
  premises : Array String

structure Answer where
  binders : Array (String × String)
deriving Inhabited

structure Udf where
  sig : Sig
  problem : Array (T × T)
  answers : Array Answer
  steps : Std.HashMap String Step
  root : String

def Udf.parse (text : String) : Except String Udf := do
  let xs ← parseAll text
  let mut sig : Sig := {}
  let mut problem := #[]
  let mut answers := #[]
  let mut steps : Std.HashMap String Step := {}
  let mut root := ""
  for x in xs do
    let items := x.items
    match items[0]?.map (·.atom!) with
    | some "signature" =>
      for d in items[1:] do
        let d := d.items
        match d[0]!.atom! with
        | "op" => sig := { sig with ops := sig.ops.push (d[1]!.atom!, d[2]!.items.map (·.atom!), d[3]!.atom!) }
        | "acu" => sig := { sig with acu := sig.acu.push (d[1]!.atom!, d[2]!.atom!, d[3]!.atom!) }
        | "var" => sig := { sig with vars := sig.vars.push (d[1]!.atom!, d[2]!.atom!) }
        | _ => pure ()
    | some "problem" =>
      problem := items[1:].toArray.map fun e => (sig.term e.items[1]!, sig.term e.items[2]!)
    | some "answers" =>
      answers := items[1:].toArray.map fun a =>
        { binders := (a.items[2]!.items[1:].toArray.map fun b => (b.items[0]!.atom!, b.items[1]!.atom!)) }
    | some "step" =>
      let id := items[1]!.atom!
      if root.isEmpty then root := id
      let args := items[3:].toArray
      steps := steps.insert id
        { rule := items[2]!.atom!, args, premises := ((kw args ":premises").map (·.items.map (·.atom!))).getD #[] }
    | _ => pure ()
  return { sig, problem, answers, steps, root }

/-! ## Lean text -/

/-- A nested tuple shape over names (the request's `shape`). -/
inductive Shp where
  | leaf (n : String)
  | pair (l r : Shp)
deriving Inhabited

partial def Shp.ofJson : Json → Shp
  | .arr #[l, r] => .pair (Shp.ofJson l) (Shp.ofJson r)
  | .str s => .leaf s
  | _ => .leaf "_"

def Shp.render (s : Shp) (f : String → String) : String :=
  match s with
  | .leaf n => f n
  | .pair l r => s!"({l.render f}, {r.render f})"

def isIdent (s : String) : Bool :=
  !s.isEmpty && s.all fun c => c.isAlphanum || "_.?!'".contains c

/-- `s` is one `(...)` or `{...}` group. -/
def oneGroup (s : String) : Bool := Id.run do
  let cs := s.toList
  match cs.head?, cs.getLast? with
  | some '(', some ')' | some '{', some '}' =>
    let mut depth : Int := 0
    let mut i := 0
    for c in cs do
      if c == '(' || c == '{' then depth := depth + 1
      if c == ')' || c == '}' then depth := depth - 1
      i := i + 1
      if depth == 0 then return i == cs.length
    return false
  | _, _ => return false

def paren (s : String) : String := if isIdent s || oneGroup s then s else s!"({s})"

def tupleTerm (xs : List String) : String :=
  match xs with
  | [] => "()"
  | [x] => x
  | _ => "(" ++ ", ".intercalate xs ++ ")"

def vec (xs : List String) : String := "![" ++ ", ".intercalate xs ++ "]"

/-- The identifier-like tokens of a Lean text. -/
def tokens (s : String) : List String :=
  (s.split fun c => !(c.isAlphanum || "_.?!'".contains c)).filter (!·.isEmpty)

structure Gen where
  udf : Udf
  ops : Json                               -- Maude operator → Lean template
  bagType : Std.HashMap String String      -- sort → Lean type
  orig : Array String                      -- the problem's variables
  shape : Shp
  binders : Array Shp                      -- each answer's binder shape
  named : Std.HashMap String String := {}  -- variables named by a projection instead
  out : Array String := #[]
  sorts : Std.HashMap String String := {}

abbrev G := StateT Gen (Except String)

def emit (ind : Nat) (s : String) : G Unit :=
  modify fun g => { g with out := g.out ++ (s.splitOn "\n").toArray.map ("".pushn ' ' (2 * ind) ++ ·) }

def leanName (g : Gen) (n : String) : String :=
  if let some a := g.named[n]? then a else
  if n.startsWith "#" then "U" ++ (n.drop 1) ++ "!" else if g.orig.contains n then n ++ "?" else n

def acuOf (g : Gen) (op : String) : Option (String × String) :=
  (g.udf.sig.acu.find? (·.1 == op)).map (·.2)

def identOf (g : Gen) (c : String) : Option String :=
  (g.udf.sig.acu.find? (·.2.2 == c)).map (·.2.1)

partial def sortOf (g : Gen) : T → String
  | .var n => g.sorts.getD n ""
  | .app op args =>
    match acuOf g op, identOf g op with
    | some (s, _), _ => s
    | _, some s => s
    | _, _ => ((g.udf.sig.ops.find? fun (o, d, _) => o == op && d.size == args.size).map (·.2.2)).getD ""


def isBag (g : Gen) (s : String) : Bool := g.udf.sig.acu.any (·.2.1 == s)

partial def render (g : Gen) : T → Except String String
  | .var n => return leanName g n
  | .app op args => do
    if let some (s, _) := acuOf g op then
      let parts ← args.toList.mapM fun a => do
        let r ← render g a
        return if sortOf g a == s then r else "{" ++ r ++ "}"
      return " + ".intercalate parts
    if (identOf g op).isSome then return "∅"
    let some tmpl := (g.ops.getObjValAs? String op).toOption
      | throw s!"udf: no Lean name for Maude operator {op}"
    -- an argument of a bag sort that is one element (a subsort) is a singleton
    let dom := ((g.udf.sig.ops.find? fun (o, d, _) => o == op && d.size == args.size).map
      (·.2.1)).getD #[]
    let rs ← (List.range args.size).mapM fun i => do
      let r ← render g args[i]!
      let d := dom[i]?.getD ""
      return if isBag g d && sortOf g args[i]! != d then "{" ++ r ++ "}" else paren r
    if (tmpl.splitOn "{0}").length > 1 then
      let mut out := tmpl
      for i in [0:rs.length] do
        out := out.replace ("{" ++ toString i ++ "}") rs[i]!
      return out
    return " ".intercalate (tmpl :: rs)

partial def vars : T → List String
  | .var n => [n]
  | .app _ args => args.toList.flatMap vars

/-- A term at sort `s`: an element of a bag sort becomes a singleton; a variable-free bag
gets its type. -/
def renderAt (g : Gen) (s : String) (t : T) : Except String String := do
  let r ← render g t
  if isBag g s && sortOf g t != s then return "{" ++ r ++ "}"
  if isBag g s && vars t == [] then return s!"({r} : {g.bagType.getD s "_"})"
  return r

def renderEq (g : Gen) (e : T × T) : Except String String := do
  let (l, r) := e
  let s := if isBag g (sortOf g l) then sortOf g l else sortOf g r
  return s!"{← renderAt g s l} = {← renderAt g s r}"

def pat (g : Gen) (ctx : Array String) (used : Option (List String) := none) : String :=
  let name n := if used.all (·.contains (leanName g n)) then leanName g n else "_"
  if ctx == g.orig then g.shape.render (fun n => name n)
  else if ctx.isEmpty then "_" else tupleTerm (ctx.toList.map name)

def tupleOf (g : Gen) (ctx : Array String) (items : List String) : String :=
  if ctx == g.orig then g.shape.render fun n => items[ctx.idxOf n]! else tupleTerm items

def Shp.type (s : Shp) (f : String → String) : String :=
  match s with
  | .leaf n => f n
  | .pair l r => s!"({l.type f} × {r.type f})"

/-- The Lean type of a context. -/
def ctxType (g : Gen) (ctx : Array String) : String :=
  let ty (x : String) := g.bagType.getD (g.sorts.getD x "") "_"
  if ctx == g.orig then g.shape.type ty
  else if ctx.isEmpty then "Unit" else "(" ++ " × ".intercalate (ctx.toList.map ty) ++ ")"

def lam (g : Gen) (ctx : Array String) (body : String) : String :=
  s!"fun {pat g ctx (some (tokens body))} => {body}"

def lamEqs (g : Gen) (ctx : Array String) (E : Array (T × T)) : Except String String := do
  let ls ← E.toList.mapM fun e => return lam g ctx (← renderEq g e)
  return "[" ++ ", ".intercalate ls ++ "]"

partial def subst (σ : String → Option T) : T → T
  | .var n => (σ n).getD (.var n)
  | .app op args => .app op (args.map (subst σ))

/-- Restate the pending equations as `E`, in this text's form (`acu_solve` matches them
literally). -/
def front (i : Nat) (ind : Nat) : G Unit := do
  if i != 0 then
    emit ind s!"refine pick {i} (by decide) ?_"
    emit ind "udf_list"
    emit ind "checkpoint"

def injOf (g : Gen) (t : T) : List String :=
  match t with
  | .app op args =>
    if args.isEmpty then [] else
    match (g.ops.getObjValAs? String op).toOption with
    | some tmpl =>
      let name := (tmpl.splitOn " ").head!
      if isIdent name && name != "(" then [name ++ ".injEq"] else []
    | none => []
  | _ => []

def lookup (w : List (String × String)) (x : String) : String :=
  match w.find? (·.1 == x) with
  | some (_, t) => t
  | none => "()"

/-! ## Steps -/

partial def step (id : String) (ctx : Array String) (E : Array (T × T)) (ind : Nat) : G Unit := do
  let g ← get
  let some st := g.udf.steps[id]? | throw s!"udf: no step {id}"
  let eqIdx := ((kw st.args ":eq").map (·.nat!)).getD 0
  emit ind "checkpoint"
  match st.rule with
  | "delete" =>
    emit ind s!"-- {id} delete"
    front eqIdx ind
    emit ind "refine delete ?_"
    step st.premises[0]! ctx (E.eraseIdx! eqIdx) ind
  | "decomp" =>
    emit ind s!"-- {id} decomp"
    let (l, r) := E[eqIdx]!
    let rest := E.eraseIdx! eqIdx
    front eqIdx ind
    let (.app _ ls, .app _ rs) := (l, r) | throw "udf: decomp of a variable"
    let new := ls.zip rs
    emit ind s!"refine decomp {← lamEqs g ctx new}"
    emit (ind + 2) s!"(fun {pat g ctx} h => by acu_decomp [{", ".intercalate (injOf g l)}]) ?_"
    step st.premises[0]! ctx (new ++ rest) ind
  | "elim" =>
    emit ind s!"-- {id} elim"
    let v := ((kw st.args ":var").map (·.atom!)).getD ""
    let (l, r) := E[eqIdx]!
    let t := if l == .var v then r else l
    let rest := E.eraseIdx! eqIdx
    front eqIdx ind
    let new := ctx.filter (· != v)
    let tl ← renderAt g (g.sorts.getD v "") t
    let image := tupleOf g ctx (ctx.toList.map fun x => if x == v then tl else leanName g x)
    emit ind s!"refine elim (fun {pat g new} => {image})"
    emit (ind + 2) s!"(fun {pat g ctx} h => ⟨{tupleTerm (new.toList.map (leanName g))}, by acu_elim []⟩) ?_"
    step st.premises[0]! new (rest.map fun (a, b) =>
      (subst (fun x => if x == v then some t else none) a, subst (fun x => if x == v then some t else none) b)) ind
  | "clash" | "occurs" | "ground" =>
    emit ind s!"-- {id} {st.rule}"
    emit ind s!"exact clash fun {pat g ctx} h hD => by acu_free []"
  | "cover" =>
    let j := ((((kw st.args ":answer").map (·.atom!)).getD "a0").drop 1).toNat!
    let wit := ((kw st.args ":witness").map (·.items)).getD #[]
    let w : List (String × String) ← wit.toList.mapM fun b => do
      let x := b.items[0]!.atom!
      let t := g.udf.sig.term b.items[1]!
      let s := (g.udf.answers[j]!.binders.find? (·.1 == x)).map (·.2) |>.getD ""
      return (x, ← renderAt g s t)
    let shp := g.binders[j]!
    let tuple := match shp with
      | .leaf "_" => "()"
      | _ => shp.render (lookup w)
    emit ind s!"-- {id} cover a{j}"
    emit ind s!"refine cover _ (List.getElem_mem (by decide : {j} < _)) ?_"
    emit ind "simp only [List.getElem_cons_succ, List.getElem_cons_zero]"
    emit ind s!"exact fun {pat g ctx} _ _ => ⟨{tuple}, by udf_cover⟩"
  | "acu-solve" => acuSolve id st ctx E ind
  | r => throw s!"udf: rule {r} is not supported"

where
  acuSolve (id : String) (st : Step) (ctx : Array String) (E : Array (T × T)) (ind : Nat) :
      G Unit := do
    let g ← get
    let get! (k : String) : Sx := (kw st.args k).getD (.list #[])
    let op := (get! ":op").atom!
    let some (bagSort, _) := acuOf g op | throw s!"udf: {op} is not an ACU operator"
    let eqs := (get! ":eqs").items.map (·.nat!)
    let U := (get! ":unknowns").items.map g.udf.sig.term
    let bounds := (get! ":bounds").items.map (·.atom! == "inf")
    let rows := (get! ":rows").items.map (·.items.map (·.int!))
    let basis := (get! ":basis").items.map (·.items.map (·.nat!))
    let sels := (get! ":selections").items
    let bagIdx := (List.range U.size).filter (bounds[·]!)
    let alienIdx := (List.range U.size).filter (!bounds[·]!)
    let cols := bagIdx ++ alienIdx
    let n := bagIdx.length
    let m := alienIdx.length
    let isFree (v : Array Nat) := alienIdx.all (v[·]! == 0)
    let freeVs := (List.range basis.size).filter (isFree basis[·]!)
    let alienVs := (List.range basis.size).filter (!isFree basis[·]!)
    let k₀ := freeVs.length
    let k₁ := alienVs.length
    let rep (k : Nat) : Nat := (alienIdx.findIdx? ((basis[k]!)[·]! != 0)).getD 0
    let bagVars ← bagIdx.mapM fun j => match U[j]! with
      | .var x => pure x
      | _ => throw "udf: a bag unknown is not a variable"
    let rest := ctx.filter (!bagVars.contains ·)
    -- the equations solved, first
    let solved := eqs.map (E[·]!)
    let others := (List.range E.size).filter (!eqs.contains ·) |>.toArray.map (E[·]!)
    emit ind s!"-- {id} acu-solve"
    -- bring the solved equations to the front, in order (`pick`, last one first)
    let mut order := (List.range E.size).toArray
    for j in eqs.reverse do
      let p := (order.idxOf? j).getD 0
      front p ind
      order := #[j] ++ order.eraseIdx! p
    let col (v : Array Int) (sgn : Int) : String :=
      vec (cols.map fun j => toString (max (0 : Int) (sgn * v[j]!)).toNat)
    let rowsL := rows.toList.map fun r => s!"({col r 1}, {col r (-1)})"
    let headOp : T → String | .app o _ => o | .var x => "?" ++ x
    let clash := (List.range m).flatMap fun c => (List.range m).filterMap fun c' =>
      let (a, b) := (U[alienIdx[c]!]!, U[alienIdx[c']!]!)
      match a, b with
      | .app _ _, .app _ _ => if c < c' && headOp a != headOp b then some s!"({c}, {c'})" else none
      | _, _ => none
    let vecN (v : Array Nat) := vec (cols.map fun j => toString v[j]!)
    -- `glue` and the aliens take the rest of the context as `r`, by projections: a pattern
    -- would need its type before `rest` determines it
    let proj (i : Nat) : String :=
      if rest.size == 1 then "r" else
      "r" ++ String.join (List.replicate i ".2") ++ (if i + 1 < rest.size then ".1" else "")
    let gr := { g with
      named := (List.range rest.size).foldl (fun m i => m.insert rest[i]! (proj i)) {} }
    let aliens ← alienIdx.mapM fun j => renderAt gr "" U[j]!
    let glue := tupleOf g ctx (ctx.toList.map fun x =>
      match bagVars.idxOf? x with | some i => s!"V {i}" | none => leanName gr x)
    let selVec (sel : Array Nat) := vec (alienVs.map fun k => if sel.contains k then "true" else "false")
    let selsL := sels.toList.map fun s => selVec (s.items[1]!.items.map (·.nat!))
    let ncols := n + m
    let vnames := (List.range ncols).map (s!"v{·}")
    emit ind s!"refine acu_solve_take (Γ := {ctxType g ctx}) (Γr := {ctxType g rest}) {eqs.size}"
    emit (ind + 2) s!"(n := {n}) (m := {m}) (k₀ := {k₀}) (k₁ := {k₁})"
    emit (ind + 2) s!"\{ V := {lam g ctx (vec (bagVars.map (leanName g)))}, rest := {lam g ctx (tupleTerm (rest.toList.map (leanName g)))},"
    emit (ind + 3) s!"glue := fun r V => {glue} }"
    emit (ind + 2) s!"(fun r => {vec aliens})"
    emit (ind + 2) s!"\{ rows := [{", ".intercalate rowsL}], clash := [{", ".intercalate clash}] }"
    emit (ind + 2) s!"\{ free := {vec (freeVs.map (vecN basis[·]!))}, alien := {vec (alienVs.map (vecN basis[·]!))},"
    emit (ind + 3) s!"rep := {vec (alienVs.map (toString ∘ rep))} }"
    emit (ind + 2) s!"⟨by decide, by decide, by decide, by decide, by decide, by"
    emit (ind + 3) s!"intro v hv hne"
    emit (ind + 3) s!"obtain ⟨{", ".intercalate vnames}, rfl⟩ : ∃ {" ".intercalate vnames}, v = {vec vnames} :="
    emit (ind + 4) s!"⟨{", ".intercalate ((List.range ncols).map (s!"v {·}"))}, funext fun i => by fin_cases i <;> rfl⟩"
    -- S3′ split by alien patterns: each alien column is 0 or 1
    if m == 0 then emit (ind + 3) "udf_arith⟩"
    else
      emit (ind + 3) "udf_s3_unfold"
      let splits := (List.range m).map fun c =>
        s!"(rcases (show v{n + c} = 0 ∨ v{n + c} = 1 by omega) with rfl | rfl)"
      emit (ind + 3) (" <;>\n      ".intercalate splits)
      emit (ind + 3) "all_goals udf_s3_case⟩"
    emit (ind + 2) s!"(fun {pat g ctx} h => by udf_from h)"
    emit (ind + 2) "(fun _ => by udf_clash)"
    emit (ind + 2) s!"[{", ".intercalate selsL}] (by decide) ?_"
    -- one premise per selection (none: the system has no solution, the branch closes)
    if sels.isEmpty then emit ind "exact List.forall_mem_nil _"
    for i in [0:sels.size] do
      let s := sels[i]!.items
      let sel := s[1]!.items.map (·.nat!)
      let fresh := ((kw s ":fresh").map (·.items.map (·.atom!))).getD #[]
      let premise := st.premises[i]!
      modify fun g => { g with sorts := fresh.foldl (fun m z => m.insert z bagSort) g.sorts }
      let g ← get
      -- θ_S on the bag variables, and the pending equations of the merged aliens
      let mut zOf : Std.HashMap Nat T := {}
      let mut fi := 0
      for k in freeVs do
        if sel.contains k then
          zOf := zOf.insert k (.var fresh[fi]!)
          fi := fi + 1
      let mut pending : Array (T × T) := #[]
      for k in alienVs do
        if sel.contains k then
          let as := alienIdx.filter ((basis[k]!)[·]! != 0)
          let r := U[as.head!]!
          zOf := zOf.insert k r
          for j in as.tail do pending := pending.push (U[j]!, r)
      let θ (x : String) : Option T := do
        let i ← bagVars.idxOf? x
        let j := bagIdx[i]!
        return .app op (sel.toList.flatMap fun k =>
          (List.replicate (basis[k]!)[j]! (zOf.getD k (.var "?"))) ).toArray
      let E' := pending ++ others.map fun (a, b) => (subst θ a, subst θ b)
      let inner := rest ++ fresh
      emit ind s!"refine List.forall_mem_cons.2 ⟨?_, {if i + 1 == sels.size then "List.forall_mem_nil _⟩" else "?_⟩"}"
      emit ind s!"· -- {premise}: {selVec sel}"
      let k := k₀
      let cases := if k == 0 then "fun i => i.elim0" else if k == 1 then "fun i => by fin_cases i; rfl"
        else "fun i => by fin_cases i <;> rfl"
      let restT := tupleTerm (rest.toList.map (leanName g))
      let restP := if rest.isEmpty then "_" else tupleTerm (rest.toList.map (leanName g))
      emit (ind + 1) s!"refine rename (fun {if inner.isEmpty then "_" else tupleTerm (inner.toList.map (leanName g))} => ({restT}, {vec (fresh.toList)}))"
      emit (ind + 3) s!"(fun ({restP}, Z) => {tupleTerm (rest.toList.map (leanName g) ++ (List.range k).map (s!"Z {·}"))})"
      emit (ind + 3) s!"(fun ({restP}, Z) => Prod.ext rfl (funext {cases})) ?_"
      emit (ind + 1) "checkpoint"
      emit (ind + 1) "udf_list"
      step premise inner E' (ind + 1)

/-- The proof script of a goal `complete P U` from a UDF derivation. -/
def script (udfText : String) (request : Json) (table : Json) (bagType : Std.HashMap String String) :
    Except String String := do
  let udf ← Udf.parse udfText
  let ops ← match table.getObjVal? "ops" with
    | .ok o => pure o
    | _ => throw "udf: no ops in the model's table"
  -- the problem's variables, also those in no equation (the request lists them all)
  let reqVars := (request.getObjValAs? (Array Json) "vars").toOption.getD #[]
  let orig := reqVars.map fun v => (v.getObjValAs? String "name").toOption.getD ""
  let shape := Shp.ofJson ((request.getObjVal? "shape").toOption.getD .null)
  let answers := ((request.getObjValAs? (Array Json) "answers").toOption.getD #[])
  let binders := answers.map fun a => Shp.ofJson ((a.getObjVal? "binder").toOption.getD .null)
  let mut sorts : Std.HashMap String String := {}
  for v in reqVars do
    sorts := sorts.insert ((v.getObjValAs? String "name").toOption.getD "")
      ((v.getObjValAs? String "sort").toOption.getD "")
  for a in udf.answers do
    for (x, s) in a.binders do sorts := sorts.insert x s
  let g : Gen := { udf, ops, bagType, orig, shape, binders, sorts }
  let gen : G Unit := do
    emit 0 "rw [← start_iff]"
    step udf.root orig udf.problem 0
  let ((), g) ← gen.run g
  return "\n".intercalate g.out.toList

/-- The Python side, relative to the project root. -/
def tool : System.FilePath := "producer/tools/udf.py"

register_option udf_certify.trace : Bool := {
  defValue := false
  descr := "udf_certify: log the generated proof script" }


/-- Prove a goal `complete P U` from a UDF derivation produced by the instrumented Maude. -/
elab "udf_certify" : tactic => withMainContext do
  let goal ← getMainGoal
  let ty ← zetaReduce (← instantiateMVars (← goal.getType))
  unless ty.isAppOfArity ``Unification.complete 4 do
    throwError "udf_certify: the goal is not `complete P U`"
  let st ← Dumper.model ty.getAppArgs[0]!
  Dumper.write st
  let (target, request, key) ← UdfStore.claim st ty
  unless ← isDefEq ty target do
    throwError "udf_certify: could not restate the goal in literal form{indentExpr target}"
  let goal ← goal.replaceTargetDefEq target
  let udfText ← match ← UdfStore.load? key with
    | some text => pure text
    | none => do
      logInfo m!"udf_certify: no stored certificate for this claim; running Maude"
      let reply ← callTool tool request
      IO.ofExcept (reply.getObjValAs? String "udf")
  let table ← IO.ofExcept (Json.parse (Dumper.table st))
  let mut bagType : Std.HashMap String String := {}
  for s in st.sorts do
    bagType := bagType.insert s.name (toString (← ppExpr s.type))
  let script ← IO.ofExcept (script udfText request table bagType)
  let text := "set_option linter.unusedSimpArgs false in\n" ++
    "open Unification Unification.Certification in by\n" ++
    "\n".intercalate ((script.splitOn "\n").map ("  " ++ ·))
  if (← getOptions).getBool `udf_certify.trace then logInfo text
  let stx ← IO.ofExcept (Parser.runParserCategory (← getEnv) `term text)
  let info := SourceInfo.fromRef (← getRef)
  let stx := stx.rewriteBottomUp (·.setInfo info)
  replaceMainGoal [goal]
  goal.withContext do
    let pf ← withEnableInfoTree false <| elabTermEnsuringType stx (← goal.getType)
    goal.assign pf
  replaceMainGoal []

end UdfCertify
