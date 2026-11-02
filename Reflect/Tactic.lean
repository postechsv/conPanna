import Reflect.Sound
import conPanna.Unification.Tactics.udfCertify

/-!
`udf_reflect` proves a goal `complete P U` by reflection (documentation/reflection-design.md):

1. the model of the goal's sorts as data (`Reflect.Model`) with its laws, from the
   constructor model `#dump_model` writes (`Dumper.State`);
2. the problem and the unifiers as data terms mirroring the Lean terms node for node;
3. the stored UDF certificate as data;
4. one auxiliary lemma `complete P U`, by `complete_of_check` applied to `Eq.refl true` for
   the checker and `rfl` for the mirrors, checked by the kernel alone (as `decide +kernel`).
-/

namespace Reflect.Tac

open Lean Meta Elab Tactic Unification MaudeAdapter UdfCertify

/-! ## The model -/

structure OpInfo where
  maude : String
  args : Array Nat
  res : Nat
  /-- Lean text: the build function, the inverse, and the tag pattern. -/
  build : String
  unbuild : String
  pat : String
deriving Inhabited

structure Tbl where
  st : Dumper.State
  sortIdx : Std.HashMap String Nat := {}
  sortText : Array String := #[]
  ops : Array OpInfo := #[]
  ctorOf : Std.HashMap Name Nat := {}
  opIdx : Std.HashMap String Nat := {}
  /-- ACU operators: bag sort and element sort indices. -/
  acus : Array (Nat × Nat) := #[]
  acuOfSort : Std.HashMap Nat Nat := {}
  /-- Maude's union and unit names of each ACU operator. -/
  acuName : Std.HashMap String (Nat × Bool) := {}
  /-- The model and its laws, as constants. -/
  model : Expr := mkConst `none
  lawful : Expr := mkConst `none


def ppFull (e : Expr) : MetaM String := do
  return toString (← withOptions (fun o => o.setBool `pp.fullNames true |>.setBool `pp.funBinderTypes true) (ppExpr e))

/-- The `i`-th component of a right-nested `k`-tuple `x`, as text. -/
def comp (x : String) (i k : Nat) : String :=
  let snds := (List.range i).foldl (fun acc _ => s!"(Prod.snd {acc})") x
  if i + 1 == k then snds else s!"(Prod.fst {snds})"

def tupleText (xs : List String) : String :=
  match xs with
  | [] => "()"
  | [x] => x
  | _ => "(" ++ ", ".intercalate xs ++ ")"

def mkTbl (st : Dumper.State) : MetaM Tbl := do
  let mut t : Tbl := { st }
  for s in st.sorts do
    t := { t with sortIdx := t.sortIdx.insert s.name t.sortText.size,
                  sortText := t.sortText.push (← ppFull s.type) }
  let sidx (n : String) : MetaM Nat := do
    let some i := t.sortIdx[n]? | throwError "reflect: unknown sort {n}"
    return i
  let env ← getEnv
  for o in st.ops do
    if o.origin == "" then continue
    let ctor := o.origin.toName
    let k := o.args.length
    let xs := (List.range k).map fun i => comp "x" i k
    let build := if k == 0 then s!"fun _ => {ctor}" else s!"fun x => {ctor} {" ".intercalate xs}"
    let as := (List.range k).map (s!"a{·}")
    let some (.ctorInfo ci) := env.find? ctor | throwError "reflect: {ctor} is not a constructor"
    let some (.inductInfo ii) := env.find? ci.induct | throwError "reflect: {ctor}"
    let wild := if ii.ctors.length > 1 then " | _ => none" else ""
    let unbuild := s!"fun y => match y with | {ctor} {" ".intercalate as} => some {tupleText as}{wild}"
    let args ← o.args.toArray.mapM sidx
    t := { t with ctorOf := t.ctorOf.insert ctor t.ops.size, opIdx := t.opIdx.insert o.name t.ops.size,
                  ops := t.ops.push { maude := o.name, args, res := ← sidx o.result, build, unbuild,
                                      pat := s!"{ctor} .." } }
  for s in st.sorts do
    match s.kind with
    | .nat =>
      let n ← sidx s.name
      let z : OpInfo := { maude := "0", args := #[], res := n, build := "fun _ => Nat.zero", unbuild := "fun y => match y with | 0 => some () | _ => none", pat := "0" }
      let sc : OpInfo := { maude := "s_", args := #[n], res := n, build := "fun x => Nat.succ x", unbuild := "fun y => match y with | n + 1 => some n | _ => none", pat := "_ + 1" }
      for o in [z, sc] do
        t := { t with opIdx := t.opIdx.insert o.maude t.ops.size }
        t := { t with ops := t.ops.push o }
    | .bool =>
      let b ← sidx s.name
      for v in ["true", "false"] do
        let o : OpInfo := { maude := v, args := #[], res := b, build := s!"fun _ => {v}", unbuild := s!"fun y => match y with | {v} => some () | _ => none", pat := v }
        t := { t with opIdx := t.opIdx.insert v t.ops.size }
        t := { t with ops := t.ops.push o }
    | .acu e =>
      let i := t.acus.size
      let (u, z) := st.bagOps s.name
      t := { t with acus := t.acus.push (← sidx s.name, ← sidx e),
                    acuOfSort := t.acuOfSort.insert (← sidx s.name) i,
                    acuName := (t.acuName.insert u (i, true)).insert z (i, false) }
    | _ => pure ()
  return t

/-- Elaborate `text` at type `ty` and add it as an auxiliary definition. -/
def auxDef (text : String) (ty : Expr) : TermElabM Expr := do
  let stx ← IO.ofExcept (Parser.runParserCategory (← getEnv) `term text)
  let e ← Term.elabTermEnsuringType stx ty
  Term.synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e
  if e.hasMVar then throwError "reflect: could not elaborate{indentExpr e}"
  let name ← mkAuxDeclName `_reflect
  addDecl (.defnDecl { name, levelParams := [], type := ty, value := e,
                       hints := .regular 0, safety := .safe })
  return mkConst name

/-- The model as constants: `T`, `tag`, the model, its laws. -/
def mkModel (t : Tbl) : TermElabM Tbl := do
  let Tty ← mkArrow (mkConst ``Nat) (mkSort levelOne)
  let alts := (t.sortText.toList.zipIdx.map fun (s, i) => s!" | {i} => {s}")
  let T ← auxDef s!"fun s => match s with{String.join alts} | _ => Unit" Tty
  let tagTy ← withLocalDeclD `s (mkConst ``Nat) fun s => do
    mkForallFVars #[s] (← mkArrow (mkApp T s) (mkConst ``Nat))
  let mut tagAlts := ""
  for (_, si) in t.sortIdx.toList do
    let os := t.ops.toList.zipIdx.filter fun (o, _) => o.res == si
    if os.isEmpty then continue
    let inner := String.join (os.map fun (o, i) => s!" | {o.pat} => {i}")
    tagAlts := tagAlts ++ s!" | {si} => fun (y : {t.sortText[si]!}) => (match y with{inner})"
  let tag ← auxDef s!"fun s => match s with{tagAlts} | _ => fun _ => 0" tagTy
  let opTy ← mkAppM ``Reflect.Op #[T]
  let opsText := ", ".intercalate (t.ops.toList.map fun o =>
    let ub := o.unbuild.replace "fun y =>" s!"fun (y : {t.sortText[o.res]!}) =>"
    s!"\{ args := {o.args.toList}, res := {o.res}, build := {o.build}, unbuild := {ub} }")
  let ops ← auxDef s!"[{opsText}]" (← mkAppM ``List #[opTy])
  let acuTy ← mkAppM ``Reflect.AcuOp #[T]
  let acusText := ", ".intercalate (t.acus.toList.map fun (b, e) =>
    s!"\{ elem := {e}, bag := {b}, toBag := id, ofBag := id }")
  let acus ← auxDef s!"[{acusText}]" (← mkAppM ``List #[acuTy])
  let model := mkAppN (mkConst ``Reflect.Model.mk) #[T, tag, ops, acus]
  let mname ← mkAuxDeclName `_reflect
  addDecl (.defnDecl { name := mname, levelParams := [], type := mkConst ``Reflect.Model, value := model,
                       hints := .regular 0, safety := .safe })
  let model := mkConst mname
  let allL (n : Nat) (p : String) : String := String.join (List.replicate n s!"⟨{p}, ") ++ "trivial" ++ String.join (List.replicate n "⟩")
  let lawText := s!"⟨{allL t.ops.size "fun _ => rfl"}, {allL t.ops.size "fun _ => rfl"}, " ++
    s!"{allL t.acus.size "⟨fun _ => rfl, fun _ => rfl, by decide⟩"}⟩"
  let lawTy ← mkAppM ``Reflect.Model.Lawful #[model]
  let stx ← IO.ofExcept (Parser.runParserCategory (← getEnv) `term lawText)
  let pf ← Term.elabTermEnsuringType stx lawTy
  Term.synthesizeSyntheticMVarsNoPostponing
  let pf ← instantiateMVars pf
  let lname ← mkAuxLemma [] lawTy pf
  return { t with model, lawful := mkConst lname }

/-! ## Data terms -/

def nat (n : Nat) : Expr := mkRawNatLit n

def list (ty : Expr) (xs : List Expr) : MetaM Expr := mkListLit ty xs

def termTy : Expr := mkConst ``Reflect.Term

def tvar (i : Nat) : Expr := mkApp (mkConst ``Reflect.Term.var) (nat i)

def tapp (f : Nat) (ts : List Expr) : MetaM Expr :=
  return mkApp2 (mkConst ``Reflect.Term.app) (nat f) (← list termTy ts)

def tacu (f : Nat) (ts : List Expr) : MetaM Expr :=
  return mkApp2 (mkConst ``Reflect.Term.acu) (nat f) (← list termTy ts)

private def natLit? (e : Expr) : Option Nat :=
  if let some n := e.rawNatLit? then some n
  else if e.isAppOfArity ``OfNat.ofNat 3 then e.appFn!.appArg!.rawNatLit?
  else none

/-- The data term mirroring Lean term `e`, node for node; `names` numbers its variables. -/
partial def mirror (t : Tbl) (names : FVarId → Option Nat) (e : Expr) : MetaM Expr := do
  let e ← instantiateMVars e
  let go := mirror t names
  if let .fvar id := e then
    let some n := names id | throwError "reflect: unexpected variable {e}"
    return tvar n
  let s ← sortOfType t.st (← inferType e)
  let some si := t.sortIdx[s]? | throwError "reflect: unknown sort {s}"
  match (← sortInfo t.st s).kind with
  | .acu _ =>
    let some f := t.acuOfSort[si]? | throwError "reflect: {s}"
    if e.isAppOfArity ``HAdd.hAdd 6 || e.isAppOfArity ``ACU.plus 3 then
      return ← tacu f [← go e.appFn!.appArg!, ← go e.appArg!]
    if e.isAppOfArity ``Singleton.singleton 4 || e.isAppOfArity ``ACU.elem 2 then
      return ← tacu f [← go e.appArg!]
    if e.isAppOfArity ``EmptyCollection.emptyCollection 2 || e.isAppOfArity ``ACU.unit 1 then
      return ← tacu f []
  | .nat =>
    let z := t.opIdx["0"]!
    let sc := t.opIdx["s_"]!
    let succs (k : Nat) (b : Expr) : MetaM Expr := do
      let mut r := b
      for _ in [0:k] do r ← tapp sc [r]
      return r
    if let some k := natLit? e then return ← succs k (← tapp z [])
    if e.isAppOfArity ``HAdd.hAdd 6 || e.isAppOfArity ``Nat.add 2 then
      if let some k := natLit? e.appArg! then return ← succs k (← go e.appFn!.appArg!)
    if e.isAppOfArity ``Nat.succ 1 then return ← tapp sc [← go e.appArg!]
    if e.isConstOf ``Nat.zero then return ← tapp z []
  | .bool =>
    if e.isConstOf ``Bool.true then return ← tapp t.opIdx["true"]! []
    if e.isConstOf ``Bool.false then return ← tapp t.opIdx["false"]! []
  | .ind _ =>
    if let some c := e.getAppFn.constName? then
      if let some i := t.ctorOf[c]? then
        return ← tapp i (← e.getAppArgs.toList.mapM go)
  let e' ← whnfR e
  if e' != e then return ← go e'
  throwError "reflect: {e} is not a constructor term"

/-- The shape of a tuple type, over sort indices. -/
partial def shp (t : Tbl) : Shape → MetaM Expr
  | .leaf ty => do
    let s ← sortOfType t.st ty
    return mkApp (mkConst ``Reflect.Shp.leaf) (nat t.sortIdx[s]!)
  | .pair l r => return mkApp2 (mkConst ``Reflect.Shp.pair) (← shp t l) (← shp t r)

/-! ## The certificate -/

/-- A UDF term as data; `expect` is the sort expected at its position (a lone element
where a bag is expected becomes a singleton). -/
partial def udfTerm (t : Tbl) (vidx : String → MetaM (Nat × Nat)) (expect : Option Nat) :
    UdfCertify.T → MetaM Expr
  | .var n => do
    let (i, s) ← vidx n
    wrap s (tvar i)
  | .app op args => do
    if let some (f, isUnion) := t.acuName[op]? then
      let r ← if isUnion then tacu f (← args.toList.mapM (udfTerm t vidx none)) else tacu f []
      return r
    let some i := t.opIdx[op]? | throwError "reflect: unknown operator {op}"
    let o := t.ops[i]!
    let r ← tapp i (← (args.toList.zip o.args.toList).mapM fun (a, s) => udfTerm t vidx (some s) a)
    wrap o.res r
where
  wrap (s : Nat) (r : Expr) : MetaM Expr := do
    if let some e := expect then
      if let some f := t.acuOfSort[e]? then
        if t.acus[f]!.2 == s then return ← tacu f [r]
    return r

def intE (n : Int) : Expr :=
  if n ≥ 0 then mkApp (mkConst ``Int.ofNat) (nat n.toNat)
  else mkApp (mkConst ``Int.negSucc) (nat (n.natAbs - 1))

def natList (xs : List Nat) : MetaM Expr := list (mkConst ``Nat) (xs.map nat)

/-- Step ids in file order, and answer names. -/
def order (text : String) : Except String (Array String × Array String) := do
  let xs ← parseAll text
  let mut ids := #[]
  let mut ans := #[]
  for x in xs do
    let items := x.items
    match items[0]?.map (·.atom!) with
    | some "step" => ids := ids.push items[1]!.atom!
    | some "answers" => ans := items[1:].toArray.map fun a => a.items[1]!.atom!
    | _ => pure ()
  return (ids, ans)

/-- The certificate's steps as data. -/
def steps (t : Tbl) (udf : Udf) (ids ans : Array String) (vars : Std.HashMap String (Nat × Nat))
    (binderSorts : Array (Array Nat)) : MetaM (List Expr) := do
  let vidx (n : String) : MetaM (Nat × Nat) := do
    let some v := vars[n]? | throwError "reflect: unknown variable {n}"
    return v
  let sid (n : String) : MetaM Nat := do
    let some i := ids.findIdx? (· == n) | throwError "reflect: unknown step {n}"
    return i
  let term (e : Option Nat) (x : Sx) : MetaM Expr := udfTerm t vidx e (udf.sig.term x)
  ids.toList.mapM fun id => do
    let some st := udf.steps[id]? | throwError "reflect: no step {id}"
    let a := st.args
    let ps ← st.premises.toList.mapM sid
    let eq := ((kw a ":eq").map (·.nat!)).getD 0
    let C (n : Name) := mkConst (``Reflect.Rule ++ n)
    match st.rule with
    | "delete" => return mkApp2 (C `delete) (nat eq) (nat ps[0]!)
    | "decomp" => return mkApp2 (C `decomp) (nat eq) (nat ps[0]!)
    | "clash" | "occurs" => return mkApp (C `clash) (nat eq)
    | "ground" => return mkApp (C `ground) (nat eq)
    | "elim" =>
      let (x, _) ← vidx ((kw a ":var").get!.atom!)
      return mkApp3 (C `elim) (nat eq) (nat x) (nat ps[0]!)
    | "cover" =>
      let an := (kw a ":answer").get!.atom!
      let some ai := ans.findIdx? (· == an) | throwError "reflect: unknown answer {an}"
      let w := (kw a ":witness").get!.items
      let bs := binderSorts[ai]!
      let mut ws : Array Expr := #[]
      for j in [0:bs.size] do
        let some p := w.find? (·.items[0]!.atom! == s!"#{j + 1}")
          | throwError "reflect: no witness for #{j + 1}"
        ws := ws.push (← term (some bs[j]!) p.items[1]!)
      return mkApp2 (C `cover) (nat ai) (← list termTy ws.toList)
    | "acu-solve" =>
      let some (f, _) := t.acuName[(kw a ":op").get!.atom!]? | throwError "reflect: unknown ACU operator"
      let i := (kw a ":eqs").get!.items[0]!.nat!
      let unk ← (kw a ":unknowns").get!.items.toList.mapM (term none)
      let alien := (kw a ":bounds").get!.items.toList.map fun b =>
        if b.atom! == "1" then mkConst ``Bool.true else mkConst ``Bool.false
      let rows := (kw a ":rows").get!.items
      unless rows.size == 1 do throwError "reflect: only single-row systems"
      let row := rows[0]!.items.toList.map fun c => intE c.int!
      let basis ← (kw a ":basis").get!.items.toList.mapM fun v => natList (v.items.toList.map (·.nat!))
      let selTy ← mkAppM ``Prod #[← mkAppM ``List #[mkConst ``Nat], ← mkAppM ``List #[mkConst ``Nat]]
      let sels ← (kw a ":selections").get!.items.toList.mapM fun sel => do
        let S := (sel.items[1]!).items.toList.map (·.nat!)
        let fresh ← ((kw sel.items ":fresh").get!.items.toList.mapM fun z => do return (← vidx z.atom!).1)
        mkAppM ``Prod.mk #[← natList S, ← natList fresh]
      return mkAppN (C `acu) #[nat f, nat i, ← list termTy unk, ← list (mkConst ``Bool) alien,
        ← list (mkConst ``Int) row, ← list (← mkAppM ``List #[mkConst ``Nat]) basis,
        ← list selTy sels, ← natList ps]
    | r => throwError "reflect: rule {r} not supported"

/-- Prove `target = complete P U` (literal form) by reflection, from UDF text. -/
def prove (st : Dumper.State) (target : Expr) (udfText : String) : TermElabM Expr := do
  let t ← mkTbl st
  let t ← mkModel t
  let M := t.model
  let udf ← IO.ofExcept (Udf.parse udfText)
  let (ids, ans) ← IO.ofExcept (order udfText)
  let #[_, _, P, U] := target.getAppArgs | throwError "reflect: not `complete P U`"
  let us ← UdfStore.listElems U
  let Pw ← whnf P
  let body := Pw.appArg!
  openProblem P fun shape xs names lhs rhs => do
    let idx (id : FVarId) : Option Nat := xs.findIdx? (· == .fvar id)
    let _ := names
    let L ← mirror t idx lhs
    let R ← mirror t idx rhs
    let sh ← shp t shape
    let sα := t.sortIdx[← sortOfType st (← inferType lhs)]!
    -- variables: the problem's, then the certificate's others (fresh bags)
    let mut vars : Std.HashMap String (Nat × Nat) := {}
    let mut sorts : Array Nat := #[]
    for x in xs do
      let s := t.sortIdx[← sortOfType st (← inferType x)]!
      vars := vars.insert s!"X{sorts.size + 1}" (sorts.size, s)
      sorts := sorts.push s
    for id in ids do
      let some stp := udf.steps[id]? | throwError "reflect: no step {id}"
      if stp.rule == "acu-solve" then
        let some (f, _) := t.acuName[(kw stp.args ":op").get!.atom!]? | throwError "reflect: ACU operator"
        for sel in (kw stp.args ":selections").get!.items do
          for z in (kw sel.items ":fresh").get!.items do
            if !vars.contains z.atom! then
              vars := vars.insert z.atom! (sorts.size, t.acus[f]!.1)
              sorts := sorts.push t.acus[f]!.1
    -- answers
    let lansTy := mkApp2 (mkConst ``Reflect.LAns) M sh
    let mut lans : Array Expr := #[]
    let mut ansE : Array Expr := #[]
    let mut binderSorts : Array (Array Nat) := #[]
    for u in us do
      let (bsh, img, bs) ← openUnifier shape u fun binder zs images => do
        let zidx (id : FVarId) : Option Nat := zs.findIdx? (· == .fvar id)
        let img ← images.mapM (mirror t zidx)
        let bs ← binder.leaves.toArray.mapM fun ty => do return t.sortIdx[← sortOfType st ty]!
        return (← shp t binder, ← list termTy img, bs)
      let ub := (← whnf u).appArg!
      lans := lans.push (mkAppN (mkConst ``Reflect.LAns.mk) #[M, sh, bsh, img, ub])
      ansE := ansE.push (mkApp2 (mkConst ``Reflect.Ans.mk) bsh img)
      binderSorts := binderSorts.push bs
    let stepsE ← steps t udf ids ans vars binderSorts
    let c := mkAppN (mkConst ``Reflect.Cert.mk) #[sh, ← natList sorts.toList, L, R,
      ← list (mkConst ``Reflect.Ans) ansE.toList, ← list (mkConst ``Reflect.Rule) stepsE]
    let asE ← list lansTy lans.toList
    let valTy := mkApp (mkConst ``Option [levelZero]) (mkApp (mkConst ``Reflect.Model.Val) M)
    let refl (a : Expr) (ty : Expr) := mkApp2 (mkConst ``Eq.refl [levelOne]) ty a
    let ctxTy (sh : Expr) := mkApp2 (mkConst ``Reflect.Shp.Ty) (mkApp (mkConst ``Reflect.Model.T) M) sh
    let side (e : Expr) := Expr.lam `γ (ctxTy sh)
      (refl (mkAppN (mkConst ``Reflect.Model.eval) #[M, mkAppN (mkConst ``Reflect.Model.enc) #[M, sh, .bvar 0], e]) valTy) .default
    let hc := refl (mkConst ``Bool.true) (mkConst ``Bool)
    let pre := mkAppN (mkConst ``Reflect.complete_of_check) #[M, t.lawful, c, hc, nat sα, body,
      side L, side R, asE, refl (mkApp (mkConst ``Reflect.Cert.answers) c) (← mkAppM ``List #[mkConst ``Reflect.Ans])]
    let .forallE _ hUty _ _ ← inferType pre | throwError "reflect: theorem shape"
    let Pfun := hUty.appFn!.appArg!
    -- `AllL P as`, one `rfl` per answer
    let mut pf := mkConst ``True.intro
    let mut rest : List Expr := []
    let lansL := lans.toList
    for i in (List.range lansL.length).reverse do
      let a := lansL[i]!
      let tl ← list lansTy rest
      let bsh := a.getAppArgs[2]!
      let img := a.getAppArgs[3]!
      let hx := Expr.lam `x (ctxTy bsh)
        (refl (mkAppN (mkConst ``List.map [levelZero, levelZero])
          #[termTy, valTy, mkAppN (mkConst ``Reflect.Model.eval) #[M, mkAppN (mkConst ``Reflect.Model.enc) #[M, bsh, .bvar 0]], img])
          (← mkAppM ``List #[valTy])) .default
      pf := mkAppN (mkConst ``And.intro) #[mkApp Pfun a, mkApp3 (mkConst ``Reflect.AllL [levelZero]) lansTy Pfun tl, hx, pf]
      rest := a :: rest
    return mkApp pre pf

/-- Prove a goal `complete P U` by reflection, from the certificate narrowing stored. -/
elab "udf_reflect" : tactic => withMainContext do
  let goal ← getMainGoal
  let ty ← zetaReduce (← instantiateMVars (← goal.getType))
  unless ty.isAppOfArity ``Unification.complete 4 do
    throwError "udf_reflect: the goal is not `complete P U`"
  let st ← Dumper.model ty.getAppArgs[0]!
  let (target, _, key) ← UdfStore.claim st ty
  let some udfText ← UdfStore.load? key | throwError "udf_reflect: no stored certificate"
  let value ← prove st target udfText
  let name ← withOptions (Elab.async.set · false) do mkAuxLemma [] target value
  goal.assign (mkConst name)
  replaceMainGoal []

end Reflect.Tac
