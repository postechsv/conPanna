import conPanna.Dumper.Base
import conPanna.Reflect.Core

/-!
The reflection model of a state type (documentation/reflection-design.md, §5), generated
from its constructor model (`Dumper/Base.lean`): the sorts' types, one `Op` per constructor
with its inverse, a tag per constructor, and the ACU sorts; the laws hold by `rfl`.
-/

namespace Reflect.Tac

open Lean Meta Elab

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
def auxDef (text : String) (ty : Expr) (base : Option Name := none) (suffix : String := "") :
    TermElabM Expr := do
  let stx ← IO.ofExcept (Parser.runParserCategory (← getEnv) `term text)
  let e ← Term.elabTermEnsuringType stx ty
  Term.synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e
  if e.hasMVar then throwError "reflect: could not elaborate{indentExpr e}"
  let name ← match base with
    | some b => pure (b ++ suffix.toName)
    | none => mkAuxDeclName `_reflect
  addDecl (.defnDecl { name, levelParams := [], type := ty, value := e,
                       hints := .regular 0, safety := .safe })
  return mkConst name

/-- The model as constants: `T`, `tag`, the model, its laws. -/
def mkModel (t : Tbl) (base : Option Name := none) : TermElabM Tbl := do
  let Tty ← mkArrow (mkConst ``Nat) (mkSort levelOne)
  let alts := (t.sortText.toList.zipIdx.map fun (s, i) => s!" | {i} => {s}")
  let T ← auxDef s!"fun s => match s with{String.join alts} | _ => Unit" Tty base "T"
  let tagTy ← withLocalDeclD `s (mkConst ``Nat) fun s => do
    mkForallFVars #[s] (← mkArrow (mkApp T s) (mkConst ``Nat))
  let mut tagAlts := ""
  for (_, si) in t.sortIdx.toList do
    let os := t.ops.toList.zipIdx.filter fun (o, _) => o.res == si
    if os.isEmpty then continue
    let inner := String.join (os.map fun (o, i) => s!" | {o.pat} => {i}")
    tagAlts := tagAlts ++ s!" | {si} => fun (y : {t.sortText[si]!}) => (match y with{inner})"
  let tag ← auxDef s!"fun s => match s with{tagAlts} | _ => fun _ => 0" tagTy base "tag"
  let opTy ← mkAppM ``Reflect.Op #[T]
  let opsText := ", ".intercalate (t.ops.toList.map fun o =>
    let ub := o.unbuild.replace "fun y =>" s!"fun (y : {t.sortText[o.res]!}) =>"
    s!"\{ args := {o.args.toList}, res := {o.res}, build := {o.build}, unbuild := {ub} }")
  let ops ← auxDef s!"[{opsText}]" (← mkAppM ``List #[opTy]) base "ops"
  let acuTy ← mkAppM ``Reflect.AcuOp #[T]
  let acusText := ", ".intercalate (t.acus.toList.map fun (b, e) =>
    s!"\{ elem := {e}, bag := {b}, toBag := id, ofBag := id }")
  let acus ← auxDef s!"[{acusText}]" (← mkAppM ``List #[acuTy]) base "acus"
  let model := mkAppN (mkConst ``Reflect.Model.mk) #[T, tag, ops, acus]
  let mname ← match base with
    | some b => pure (b ++ `model)
    | none => mkAuxDeclName `_reflect
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
  let lname ← match base with
    | some b => do
      addDecl (.thmDecl { name := b ++ `lawful, levelParams := [], type := lawTy, value := pf })
      pure (b ++ `lawful)
    | none => mkAuxLemma [] lawTy pf
  return { t with model, lawful := mkConst lname }

/-- The reflection model's constants of state type `root`, `<root>.reflect.*`. -/
def baseOf (root : Expr) : Option Name := root.constName?.map (· ++ `reflect)

end Reflect.Tac
