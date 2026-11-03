import Lean

/-!
Parsing UDF derivations (documentation/derivation-format.md): s-expressions, terms, and the
derivation's signature, problem, answers and steps.
-/

namespace UdfCertify

open Lean

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

end UdfCertify
