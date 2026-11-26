import conPanna.Reflect.Check

/-!
# ACU-Solve, computed

The rule ACU-Solve (techrep §3) takes no data from the certificate: from the equation
`s ≟ t` it computes

* the *arguments* of both sides after cancellation, with their *multiplicities*
  (positive on the left, negative on the right);
* `Adm(s,t)`: the nonzero admissible solutions of the Diophantine equation whose entries
  sum to at most `2M`, `M` the largest multiplicity (`MinimalBound.total_le_of_minimal`);
* the *basis*: the minimal elements of `Adm(s,t)`;
* the *selections*: every element involving variable arguments only, plus a choice of
  elements that marks each non-variable argument exactly once.

A vector has one entry per argument, in the order of `arguments`. The arithmetic part
(`adm`, `basis`, `selections`) works on the multiplicities alone and is tested against
Maude's bases at the end of the file.
-/

namespace Reflect

open Term

/-! ## Arithmetic: solutions, the basis, the selections -/

/-- What the arithmetic needs to know about the arguments: the multiplicities, which
arguments are non-variable, and which pairs of them clash (different top constructors). -/
structure Shape where
  mults : List Int
  nonVar : List Bool
  clash : Nat → Nat → Bool

namespace Shape

variable (sh : Shape)

/-- The number of arguments. -/
def size : Nat := sh.mults.length

/-- `M`, the largest multiplicity. -/
def maxMult : Nat := sh.mults.foldl (fun m a => max m a.natAbs) 0

/-- All vectors of length `n` whose entries sum to at most `b`. -/
def vectorsUpTo : (n b : Nat) → List (List Nat)
  | 0, _ => [[]]
  | n + 1, b => (List.range (b + 1)).flatMap fun x => (vectorsUpTo n (b - x)).map (x :: ·)

/-- The positions of non-variable arguments where `v` is nonzero. -/
def marked (v : List Nat) : List Nat :=
  (List.range sh.size).filter fun j => nthD sh.nonVar j false && nthD v j 0 != 0

/-- `v` is an admissible solution: it solves the equation, is at most 1 at non-variable
arguments, and is never nonzero at two clashing ones. -/
def admissible (v : List Nat) : Bool :=
  dot sh.mults v == 0 &&
  (sh.marked v).all (fun j => nthD v j 0 == 1) &&
  (sh.marked v).all fun i => (sh.marked v).all fun j => !sh.clash i j

/-- `Adm(s,t)`: the nonzero admissible solutions with entries summing to at most `2M`. -/
def adm : List (List Nat) :=
  (vectorsUpTo sh.size (2 * sh.maxMult)).filter fun v => v.any (· != 0) && sh.admissible v

/-- The minimal elements of a list of vectors. -/
def minimal (vs : List (List Nat)) : List (List Nat) :=
  vs.filter fun v => !vs.any fun w => leV w v && w != v

/-- The basis: the minimal elements of `Adm(s,t)`. -/
def basis : List (List Nat) := minimal sh.adm

/-- Choices of basis elements (by index) covering the positions `todo` exactly once, each
element marking only positions still in `todo`. The first uncovered position is covered
first; `fuel` bounds the number of choices. -/
def covers (marks : List (Nat × List Nat)) : (fuel : Nat) → (todo : List Nat) → List (List Nat)
  | _, [] => [[]]
  | 0, _ :: _ => []
  | fuel + 1, p :: rest =>
    (marks.filter fun (_, m) => m.contains p && m.all (p :: rest).contains).flatMap
      fun (k, m) => (covers marks fuel ((p :: rest).filter (!m.contains ·))).map (k :: ·)

/-- The selections, as lists of indices into `basis`: every element marking no
non-variable argument, plus each exact cover of the non-variable arguments. -/
def selections : List (List Nat) :=
  let B := sh.basis
  let indexed := (List.range B.length).map fun k => (k, sh.marked (nthD B k []))
  let free := (indexed.filter fun (_, m) => m.isEmpty).map (·.1)
  let todo := (List.range sh.size).filter fun j => nthD sh.nonVar j false
  (covers (indexed.filter fun (_, m) => !m.isEmpty) todo.length todo).map (free ++ ·)

end Shape

/-! ## Terms: the arguments of an equation, and the premises -/

variable (M : Model)

/-- An argument of the equation and its multiplicity: positive on the left, negative on
the right. -/
structure Arg where
  term : Term
  mult : Int

/-- The distinct terms of a list, in order of first occurrence. -/
def distinctTerms (ts : List Term) : List Term :=
  ts.foldl (fun acc t => if memT t acc then acc else acc ++ [t]) []

/-- The arguments of `l ≟ r` after cancellation on both sides, left ones first: each
distinct summand with its occurrences on the left minus those on the right, if nonzero.
The terms of a state are in normal form, so this is syntactic. -/
def arguments (f : Nat) (l r : Term) : List Arg :=
  let L := summands f l
  let R := summands f r
  let net (t : Term) : Int := count t L - count t R
  let ts := distinctTerms (L ++ R)
  (ts.filter (net · > 0) ++ ts.filter (net · < 0)).map fun t => ⟨t, net t⟩

/-- Two arguments clash if both are constructor terms with different top constructors. -/
def clashT (t u : Term) : Bool :=
  match head? t, head? u with
  | some g, some h => g != h
  | _, _ => false

/-- The arithmetic shape of a list of arguments of the union `A`: an argument of the
element sort is non-variable (the element of a singleton). -/
def shapeOf (vs : List Nat) (A : AcuOp M.T) (args : List Arg) : Shape :=
  let unk := args.map (·.term)
  { mults := args.map (·.mult)
    nonVar := unk.map fun t => tsort M vs t == some A.elem
    clash := fun i j => clashT (nthD unk i (var 0)) (nthD unk j (var 0)) }

/-- ACU-Solve on equation `i` of the state, at the union `f`: the premise states, one per
selection, in the order of `Shape.selections`. The certificate names the new variables of
each selection (`fresh`). `none` if the equation does not have the form of the rule:
both sides of the bag sort, and every argument a singleton's element or a bag variable. -/
def acuSolve (vs : List Nat) (α : List Term) (E : List Eqn) (f i : Nat)
    (fresh : List (List Nat)) : Option (List (List Term × List Eqn)) :=
  match nth E i, M.acu? f with
  | some (l, r), some A =>
    let args := arguments f l r
    let unk := args.map (·.term)
    let sh := shapeOf M vs A args
    let B := sh.basis
    let sels := sh.selections
    let isBagVar : Term → Bool
      | var x => vs[x]? == some A.bag
      | _ => false
    let bagVars := (List.range unk.length).filterMap fun j =>
      if nthD sh.nonVar j false then none else match nthD unk j (var 0) with
        | var x => some x
        | _ => none
    if tsort M vs l == some A.bag && tsort M vs r == some A.bag &&
        (List.range unk.length).all (fun j => nthD sh.nonVar j false || isBagVar (nthD unk j (var 0))) &&
        sels.length == fresh.length &&
        (sels.zip fresh).all (fun (S, z) =>
          z.length == (S.filter (alienFree unk sh.nonVar B)).length && freshOk vs A.bag α E z) then
      some <| (sels.zip fresh).map fun (S, z) =>
        let θ := theta f unk sh.nonVar B S z
        let upd := acuUpd M vs bagVars θ
        (α.map upd, pendingOf unk sh.nonVar B S z ++ (E.eraseIdx i).map fun e => (upd e.1, upd e.2))
    else none
  | _, _ => none

/-! ## Tests against Maude's bases

The same sets as Maude's (the root step of the worked example, and a repeated-argument run),
listed in our order: the certificate's selections and premises follow this order. -/

private def noClash : Nat → Nat → Bool := fun _ _ => false

-- The root step of the worked example: X5 X6 ★ X4 ■ ▲, multiplicities -1 -1 -1 1 1 1.
private def rootShape : Shape :=
  ⟨[-1, -1, -1, 1, 1, 1], [false, false, true, false, true, true], noClash⟩

/-- info: [[0, 0, 1, 0, 0, 1], [0, 0, 1, 0, 1, 0], [0, 0, 1, 1, 0, 0], [0, 1, 0, 0, 0, 1],
  [0, 1, 0, 0, 1, 0], [0, 1, 0, 1, 0, 0], [1, 0, 0, 0, 0, 1], [1, 0, 0, 0, 1, 0],
  [1, 0, 0, 1, 0, 0]] -/
#guard_msgs (whitespace := lax) in
#eval rootShape.basis

/-- info: 8 -/
#guard_msgs in
#eval rootShape.selections.length

-- X X Y a b c ≟ b b b c Z: arguments b Z a X Y, multiplicities -2 -1 1 2 1; a and b clash.
private def dupShape : Shape :=
  ⟨[-2, -1, 1, 2, 1], [true, false, true, false, false],
   fun i j => (i == 0 && j == 2) || (i == 2 && j == 0)⟩

/-- info: [[0, 1, 0, 0, 1], [0, 1, 1, 0, 0], [0, 2, 0, 1, 0], [1, 0, 0, 0, 2], [1, 0, 0, 1, 0]] -/
#guard_msgs (whitespace := lax) in
#eval dupShape.basis

-- Elements 0 and 2 involve variable arguments only; `b` is covered by 3 or 4, `a` by 1.
/-- info: [[0, 2, 3, 1], [0, 2, 4, 1]] -/
#guard_msgs in
#eval dupShape.selections

end Reflect
