import Reflect.Core

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
  /-- ACU-solve equation `i` (one row) at operator `f`. -/
  | acu (f i : Nat) (unk : List Term) (alien : List Bool) (row : List Int)
      (basis : List (List Nat)) (sels : List (List Nat × List Nat)) (ps : List Nat)

structure Cert where
  /-- The problem's context: variables `0 … sh.size - 1`. -/
  sh : Shp
  /-- The declared sort of every variable (problem variables first). -/
  sorts : List Nat
  lhs : Term
  rhs : Term
  answers : List Ans
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

def insN (n : Nat) : List Nat → List Nat
  | [] => [n]
  | m :: ms => if Nat.blt m n then m :: insN n ms else n :: m :: ms

def sortN : List Nat → List Nat
  | [] => []
  | n :: ns => insN n (sortN ns)

def powerset : List Nat → List (List Nat)
  | [] => [[]]
  | k :: ks => let p := powerset ks; p.map (k :: ·) ++ p

/-- The unit vector `e_j` (plus `e_k`) of length `m`. -/
def unit2 (m j k : Nat) : List Nat :=
  (List.range m).map fun i => (if i == j then 1 else 0) + (if i == k then 1 else 0)

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

/-- Unknowns: bag variables of the bag sort, aliens of the element sort. -/
def unknownsOk : Bool :=
  unk.length == alien.length && row.length == unk.length &&
  match M.acu? f with
  | some A => (List.range unk.length).all fun j =>
      if isAlien alien j then tsort M vs (nthD unk j (var 0)) == some A.elem
      else match nthD unk j (var 0) with
        | var x => vs[x]? == some A.bag
        | _ => false
  | none => false

/-- 1. The row is the equation `l = r` read at its summands. -/
def rowOk (l r : Term) : Bool :=
  let L := summands f l
  let R := summands f r
  ((List.range unk.length).all fun j => nthD row j 0 == 0 || memT (nthD unk j (var 0)) (L ++ R)) &&
  ((L ++ R).all fun t =>
    ((List.range unk.length).foldl
      (fun acc j => if beq (nthD unk j (var 0)) t then acc + nthD row j 0 else acc) 0)
      == (count t L : Int) - (count t R : Int))

/-- 2. Basis vectors: nonzero solutions, at most one copy of each alien. -/
def basisOk : Bool :=
  basis.all fun v => v.length == unk.length && v.any (· != 0) && dot row v == 0 &&
    (List.range unk.length).all fun j => !isAlien alien j || Nat.ble (nthD v j 0) 1

/-- Two aliens clash: different top constructors. -/
def clashes (j k : Nat) : Bool :=
  isAlien alien j && isAlien alien k &&
  match head? (nthD unk j (var 0)), head? (nthD unk k (var 0)) with
  | some a, some b => a != b
  | _, _ => false

/-- 3. Completeness for one row with coefficients in {-1, 0, 1}: every minimal
admissible vector is above a basis vector. -/
def completeOk : Bool :=
  let m := unk.length
  let idx := List.range m
  let above (v : List Nat) := basis.any fun b => leV b v
  (idx.all fun j => nthD row j 0 == 0 || nthD row j 0 == 1 || nthD row j 0 == -1) &&
  (idx.all fun j => nthD row j 0 != 0 || above (unit2 m j m)) &&
  (idx.all fun j => idx.all fun k =>
    !(nthD row j 0 == 1 && nthD row k 0 == -1) || clashes unk alien j k || above (unit2 m j k))

/-- A selection: all alien-free vectors, and each alien exactly once. -/
def legal (S : List Nat) : Bool :=
  ((List.range basis.length).all fun k => !alienFree unk alien basis k || S.contains k) &&
  (List.range unk.length).all fun j =>
    !isAlien alien j || S.foldl (fun a k => a + entry basis k j) 0 == 1

/-- 4. Every legal selection is listed. -/
def selsOk (sels : List (List Nat × List Nat)) : Bool :=
  let ks := List.range basis.length
  let free := ks.filter (alienFree unk alien basis)
  let al := ks.filter fun k => !alienFree unk alien basis k
  (powerset al).all fun S =>
    !legal unk alien basis (free ++ S) ||
      sels.any fun (S', _) => natEqL (sortN (free ++ S)) (sortN S')

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

/-- The premise states of an ACU step, when its side conditions hold. -/
def acuPremises (vs : List Nat) (α : List Term) (E : List Eqn) (f i : Nat) (unk : List Term)
    (alien : List Bool) (row : List Int) (basis : List (List Nat))
    (sels : List (List Nat × List Nat)) : Option (List (List Term × List Eqn)) :=
  match nth E i, M.acu? f with
  | some (l, r), some A =>
    if unknownsOk M vs f unk alien row && rowOk f unk row l r && basisOk unk alien row basis &&
        completeOk unk alien row basis && selsOk unk alien basis sels &&
        (sels.all fun (S, fresh) =>
          freshOk vs A.bag α E fresh &&
          fresh.length == (S.filter (alienFree unk alien basis)).length &&
          S.all (· < basis.length)) then
      some <| sels.map fun (S, fresh) =>
        let θ := theta f unk alien basis S fresh
        (α.map fun t => norm M vs (subst θ t),
          pendingOf unk alien basis S fresh ++ (E.eraseIdx i).map (normEq M vs θ))
    else none
  | _, _ => none

/-! ## The derivation -/

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
            let θ : Nat → Option Term := fun y => if y == x then some t else none
            run c n p (α.map fun u => norm M c.sorts (subst θ u)) ((E.eraseIdx i).map (normEq M c.sorts θ))
        | none => false
      | none => false
    | some (.cover a w) => E.isEmpty && match nth c.answers a with
      | some A =>
        A.img.length == α.length && w.length == A.sh.size &&
        (A.img.all (varsBelow A.sh.size)) &&
        ((List.range w.length).all fun j => tsort M c.sorts (nthD w j (var 0)) == nth A.sh.sorts j) &&
        (α.zip A.img).all fun (t, u) => beq t (norm M c.sorts (subst (nth w) u))
      | none => false
    | some (.acu f i unk alien row basis sels ps) =>
      match acuPremises M c.sorts α E f i unk alien row basis sels with
      | some states => states.length == ps.length &&
          (states.zip ps).all fun ((α', E'), p) => run c n p α' E'
      | none => false
    | none => false

/-- The derivation checks, from the problem's initial state. -/
def check (c : Cert) : Bool :=
  natEqL (c.sorts.take c.sh.size) c.sh.sorts && c.sorts.length ≥ c.sh.size &&
  run M c (c.steps.length + 1) 0 ((List.range c.sh.size).map var)
    [(norm M c.sorts c.lhs, norm M c.sorts c.rhs)]

end Reflect
