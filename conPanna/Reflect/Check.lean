import conPanna.Reflect.Core

/-!
The checker of UDF certificates over data terms (documentation/reflection-design.md).
`check M c` computes the states of the derivation itself and checks each step's side
conditions; `Reflect/Sound.lean` proves `check M c = true → complete P U`.
-/

namespace Reflect

open Term

variable (M : Model)

namespace Model

/-- Extra data a model needs for its laws: a constructor tag for each value. -/
def res? (f : Nat) : Option Nat := (M.op? f).map (·.res)

end Model

/-- The syntactic sort of a term: a variable's declared sort, a constructor's result
sort, an ACU operator's bag sort. -/
def tsort (vs : List Nat) : Term → Option Nat
  | var x => vs[x]?
  | app f _ => M.res? f
  | acu f _ => (M.acu? f).map (·.bag)

def flat (f : Nat) : List Term → List Term
  | [] => []
  | acu g bs :: as => if f == g then bs ++ flat f as else acu g bs :: flat f as
  | a :: as => a :: flat f as

/-- `acu f ts` in normal form: a single summand stands alone only if it is a bag. -/
def mkAcu (vs : List Nat) (f : Nat) (ts : List Term) : Term :=
  match Term.sort (flat f ts) with
  | [t] => match M.acu? f, tsort M vs t with
    | some A, some s => if s == A.bag then t else acu f [t]
    | _, _ => acu f [t]
  | ts => acu f ts

-- Normal form modulo ACU: flattened, `∅` dropped, sorted.
mutual
def norm (vs : List Nat) : Term → Term
  | var x => var x
  | app f as => app f (normL vs as)
  | acu f as => mkAcu M vs f (normL vs as)
def normL (vs : List Nat) : List Term → List Term
  | [] => []
  | a :: as => norm vs a :: normL vs as
end

abbrev Eqn := Term × Term

def normEq (vs : List Nat) (σ : Nat → Option Term) (e : Eqn) : Eqn :=
  (norm M vs (subst σ e.1), norm M vs (subst σ e.2))

/-- One answer: the binder's shape and the images of the problem's variables. -/
structure Ans where
  sh : Shp
  img : List Term

inductive Rule where
  | delete (i p : Nat)
  | decomp (i p : Nat)
  | elim (i x p : Nat)
  | clash (i : Nat)
  | ground (i : Nat)
  /-- `E = []`: the answer `a`, with the binder's variables `w`. -/
  | cover (a : Nat) (w : List Term)
  /-- ACU-Solve on equation `i` at union `f`: the arguments and their multiplicities; per
  selection, in the order of `Dio.selections`, its elements in the certificate's order and
  its new variables; and the step proving each premise. -/
  | acu (f i : Nat) (unk : List Term) (mults : List Int) (sels : List (List Nat × List Nat))
      (ps : List Nat)

/-- A claim about the problem `lhs = rhs` over the context `sh` (variables
`0 … sh.size - 1`) and its answers: their completeness, or their soundness. -/
structure Claim where
  sh : Shp
  lhs : Term
  rhs : Term
  answers : List Ans

/-- A completeness certificate: a UDF derivation for a claim. -/
structure Cert extends Claim where
  /-- The declared sort of every variable (the context's first, then fresh ones). -/
  sorts : List Nat
  steps : List Rule

/-! ## Helpers -/

def nth {β} : List β → Nat → Option β
  | [], _ => none
  | a :: _, 0 => some a
  | _ :: as, n + 1 => nth as n

def nthD {β} (l : List β) (n : Nat) (d : β) : β := (nth l n).getD d

def count (t : Term) : List Term → Nat
  | [] => 0
  | u :: us => (if beq t u then 1 else 0) + count t us

def memT (t : Term) (l : List Term) : Bool := l.any (beq t)

def summands (f : Nat) : Term → List Term
  | acu g ts => if f == g then ts else [acu g ts]
  | t => [t]

def head? : Term → Option Nat
  | app f _ => some f
  | _ => none

-- Refute `l = r` by a position where two constructors differ.
mutual
def refute : Term → Term → Bool
  | app f as, app g bs => f != g || (as.length == bs.length && refuteL as bs)
  | _, _ => false
def refuteL : List Term → List Term → Bool
  | a :: as, b :: bs => refute a b || refuteL as bs
  | _, _ => false
end

def dot (r : List Int) (v : List Nat) : Int :=
  match r, v with
  | c :: r, x :: v => c * x + dot r v
  | _, _ => 0

def leV : List Nat → List Nat → Bool
  | a :: as, b :: bs => Nat.ble a b && leV as bs
  | [], _ => true
  | _ :: _, [] => false

def natEqL : List Nat → List Nat → Bool
  | [], [] => true
  | a :: as, b :: bs => a == b && natEqL as bs
  | _, _ => false

/-! ## Arithmetic: solutions, the basis, the selections -/

/-- `Dio(s,t)` with its side conditions: the multiplicities of the arguments, which
arguments are non-variable, and which pairs of them clash (different top constructors). -/
structure Dio where
  mults : List Int
  nonVar : List Bool
  clash : Nat → Nat → Bool

namespace Dio

variable (sh : Dio)

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

/-- Choices among the candidates `cands` covering the positions `todo` exactly once, a
candidate `k` covering the positions `marks k`. The first uncovered position is covered
first; `fuel` bounds the number of choices. -/
def covers (cands : List Nat) (marks : Nat → List Nat) :
    (fuel : Nat) → (todo : List Nat) → List (List Nat)
  | _, [] => [[]]
  | 0, _ :: _ => []
  | fuel + 1, p :: rest =>
    (cands.filter fun k => (marks k).contains p && (marks k).all (p :: rest).contains).flatMap
      fun k => (covers cands marks fuel ((p :: rest).filter (!(marks k).contains ·))).map (k :: ·)

/-- The positions of non-variable arguments. -/
def nonVarPositions : List Nat := (List.range sh.size).filter fun j => nthD sh.nonVar j false

/-- The selections, as lists of indices into `basis`: every element marking no
non-variable argument, plus each exact cover of the non-variable arguments. -/
def selections : List (List Nat) :=
  let marks (k : Nat) := sh.marked (nthD sh.basis k [])
  let ks := List.range sh.basis.length
  (covers (ks.filter fun k => !(marks k).isEmpty) marks sh.nonVarPositions.length
    sh.nonVarPositions).map (ks.filter (fun k => (marks k).isEmpty) ++ ·)

end Dio

/-! ## ACU-solve -/

section Acu

variable (vs : List Nat) (f : Nat) (unk : List Term) (alien : List Bool) (row : List Int)
  (basis : List (List Nat))

def isAlien (j : Nat) : Bool := nthD alien j false

def bvec (k : Nat) : List Nat := nthD basis k []

def entry (k j : Nat) : Nat := nthD (bvec basis k) j 0

def alienFree (k : Nat) : Bool :=
  (List.range unk.length).all fun j => !isAlien alien j || entry basis k j == 0

/-- The aliens of vector `k`. -/
def aliensOf (k : Nat) : List Nat :=
  (List.range unk.length).filter fun j => isAlien alien j && entry basis k j != 0

/-- The representative of selected vector `k`: its fresh variable, or its first alien. -/
def rep (S fresh : List Nat) (k : Nat) : Term :=
  if alienFree unk alien basis k then var (nthD fresh ((S.filter (alienFree unk alien basis)).idxOf k) 0)
  else nthD unk ((aliensOf unk alien basis k).headD 0) (var 0)

/-- `θ_S`: each bag variable becomes the sum of its share of the selected vectors. -/
def theta (S fresh : List Nat) (x : Nat) : Option Term :=
  ((List.range unk.length).find? fun j => !isAlien alien j && beq (nthD unk j (var 0)) (var x)).map
    fun j => acu f (S.flatMap fun k =>
      List.replicate (entry basis k j) (rep unk alien basis S fresh k))

/-- The pending equations of a selection: the other aliens of a selected vector equal its
representative. -/
def pendingOf (S fresh : List Nat) : List Eqn :=
  S.flatMap fun k => ((aliensOf unk alien basis k).drop 1).map fun j =>
    (nthD unk j (var 0), rep unk alien basis S fresh k)

end Acu

mutual
def occursT (x : Nat) : Term → Bool
  | var y => x == y
  | app _ as => occursTL x as
  | acu _ as => occursTL x as
def occursTL (x : Nat) : List Term → Bool
  | [] => false
  | a :: as => occursT x a || occursTL x as
end

/-- Fresh variables: distinct, of the bag sort, and not in the state. -/
def freshOk (vs : List Nat) (bag : Nat) (α : List Term) (E : List Eqn) (fresh : List Nat) : Bool :=
  fresh.all fun z => vs[z]? == some bag && fresh.count z == 1 &&
    !(α.any (occursT z)) && !(E.any fun e => occursT z e.1 || occursT z e.2)

/-- ACU-SOLVE's substitution on a term of the state: only terms holding a bag variable of the
system change (and are normalized). -/
def acuUpd (vs bv : List Nat) (θ : Nat → Option Term) (t : Term) : Term :=
  if bv.any (occursT · t) then norm M vs (subst θ t) else t

/-! ## Terms: the arguments of an equation, and the premises -/

/-- The net count of a summand of `l ≟ r`: occurrences on the left minus on the right. -/
def net (f : Nat) (l r t : Term) : Int := count t (summands f l) - count t (summands f r)

/-- The multiplicity listed for `t`: the sum of the multiplicities `ms` at its positions in
`us`. -/
def weight (t : Term) : List Term → List Int → Int
  | u :: us, m :: ms => (if beq t u then m else 0) + weight t us ms
  | _, _ => 0

/-- `us`, with multiplicities `ms`, lists the arguments of `l ≟ r`: summands with nonzero
multiplicities, those of each summand adding up to its net count. A summand may be listed
more than once, e.g. on both sides (cancellation is not required). -/
def argumentsOk (f : Nat) (l r : Term) (us : List Term) (ms : List Int) : Bool :=
  us.length == ms.length && ms.all (· != 0) &&
    us.all (memT · (summands f l ++ summands f r)) &&
    (summands f l ++ summands f r).all fun t => weight t us ms == net f l r t

/-- Two arguments clash if both are constructor terms with different top constructors. -/
def clashT (t u : Term) : Bool :=
  match head? t, head? u with
  | some g, some h => g != h
  | _, _ => false

/-- `Dio(s,t)` for the arguments `us` of the union `A`, with multiplicities `ms`: an argument of the
element sort is non-variable (the element of a singleton). -/
def dioOf (vs : List Nat) (A : AcuOp M.T) (us : List Term) (ms : List Int) : Dio :=
  { mults := ms
    nonVar := us.map fun t => tsort M vs t == some A.elem
    clash := fun i j => clashT (nthD us i (var 0)) (nthD us j (var 0)) }

/-- ACU-Solve on equation `i` of the state, at the union `f`: the premise states, one per
selection, in the order of `Dio.selections`. The certificate lists the arguments (`unk`)
with their multiplicities (`mults`), which fixes their order, and each selection (`sels`):
its elements in its own order (a permutation of the computed one; the order of the pending
equations follows it), and its new variables. `none` if the listing is wrong, or the equation does not have the form of the rule: both
sides of the bag sort, and every argument a singleton's element or a bag variable. -/
def acuSolve (vs : List Nat) (α : List Term) (E : List Eqn) (f i : Nat) (unk : List Term)
    (mults : List Int) (sels : List (List Nat × List Nat)) : Option (List (List Term × List Eqn)) :=
  match nth E i, M.acu? f with
  | some (l, r), some A =>
    let sh := dioOf M vs A unk mults
    let B := sh.basis
    let isBagVar : Term → Bool
      | var x => vs[x]? == some A.bag
      | _ => false
    let bagVars := (List.range unk.length).filterMap fun j =>
      if nthD sh.nonVar j false then none else match nthD unk j (var 0) with
        | var x => some x
        | _ => none
    if argumentsOk f l r unk mults && tsort M vs l == some A.bag && tsort M vs r == some A.bag &&
        (List.range unk.length).all (fun j => nthD sh.nonVar j false || isBagVar (nthD unk j (var 0))) &&
        sh.selections.length == sels.length &&
        (sh.selections.zip sels).all (fun (C, S, z) => S.isPerm C &&
          z.length == (S.filter (alienFree unk sh.nonVar B)).length && freshOk vs A.bag α E z) then
      some <| sels.map fun (S, z) =>
        let θ := theta f unk sh.nonVar B S z
        let upd := acuUpd M vs bagVars θ
        (α.map upd, pendingOf unk sh.nonVar B S z ++ (E.eraseIdx i).map fun e => (upd e.1, upd e.2))
    else none
  | _, _ => none

/-! ## The derivation -/

/-- ELIM `x := t` on a term of the state: only terms holding `x` change (and are normalized). -/
def elimUpd (vs : List Nat) (x : Nat) (t u : Term) : Term :=
  if occursT x u then norm M vs (subst (fun y => if y == x then some t else none) u) else u

def run (c : Cert) : Nat → Nat → List Term → List Eqn → Bool
  | 0, _, _, _ => false
  | n + 1, id, α, E =>
    match nth c.steps id with
    | some (.delete i p) => match nth E i with
      | some (l, r) => beq l r && run c n p α (E.eraseIdx i)
      | none => false
    | some (.decomp i p) => match nth E i with
      | some (app f as, app g bs) => f == g && as.length == bs.length &&
          run c n p α (as.zip bs ++ E.eraseIdx i)
      | _ => false
    | some (.clash i) => match nth E i with
      | some (app f _, app g _) => f != g
      | _ => false
    | some (.ground i) => match nth E i with
      | some (l, r) => refute l r
      | none => false
    | some (.elim i x p) => match nth E i with
      | some (l, r) =>
        let t? := if beq l (var x) then some r else if beq r (var x) then some l else none
        match t? with
        | some t => !occursT x t &&
            run c n p (α.map (elimUpd M c.sorts x t))
              ((E.eraseIdx i).map fun e => (elimUpd M c.sorts x t e.1, elimUpd M c.sorts x t e.2))
        | none => false
      | none => false
    | some (.cover a w) => E.isEmpty && match nth c.answers a with
      | some A =>
        A.img.length == α.length && w.length == A.sh.size &&
        (A.img.all (varsBelow A.sh.size)) &&
        ((List.range A.sh.size).all fun j => A.img.any (occursT j)) &&
        ((List.range w.length).all fun j => tsort M c.sorts (nthD w j (var 0)) == nth A.sh.sorts j) &&
        (α.zip A.img).all fun (t, u) => beq t (norm M c.sorts (subst (nth w) u))
      | none => false
    | some (.acu f i unk mults sels ps) =>
      match acuSolve M c.sorts α E f i unk mults sels with
      | some states => states.length == ps.length &&
          (states.zip ps).all fun ((α', E'), p) => run c n p α' E'
      | none => false
    | none => false

/-- Completeness: the derivation checks, from the problem's initial state. -/
def check (c : Cert) : Bool :=
  natEqL (c.sorts.take c.sh.size) c.sh.sorts && c.sorts.length ≥ c.sh.size &&
  run M c (c.steps.length + 1) 0 ((List.range c.sh.size).map var)
    [(norm M c.sorts c.lhs, norm M c.sorts c.rhs)]

/-- Soundness: each answer, substituted into both sides, gives terms equal modulo ACU. -/
def checkSound (c : Claim) : Bool :=
  varsBelow c.sh.size c.lhs && varsBelow c.sh.size c.rhs &&
  c.answers.all fun A => A.img.length == c.sh.size &&
    beq (norm M A.sh.sorts (subst (nth A.img) c.lhs)) (norm M A.sh.sorts (subst (nth A.img) c.rhs))

/-! ## Tests against Maude's bases

The same sets as Maude's (the root step of the worked example, and a repeated-argument run),
listed in our order: the certificate's selections and premises follow this order. -/

private def noClash : Nat → Nat → Bool := fun _ _ => false

-- The root step of the worked example: X5 X6 ★ X4 ■ ▲, multiplicities -1 -1 -1 1 1 1.
private def rootShape : Dio :=
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
private def dupShape : Dio :=
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
