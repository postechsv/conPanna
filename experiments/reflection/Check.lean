/-!
Doability test for proof by reflection: a Boolean checker of UDF certificates over a data
form of terms, evaluated by the kernel (`decide +kernel`). No correctness proof, no bridge
to the user's types: this only measures whether kernel evaluation is fast enough.

Proxy parts (to be made exact if the test succeeds): sorts are not checked, and basis
completeness (S3′) is checked by enumerating a small box instead of a proved bound.
-/

inductive Term where
  | var : Nat → Term
  | app : Nat → List Term → Term
  | acu : Nat → List Term → Term

namespace Term

def tag : Term → Nat
  | var _ => 0 | app _ _ => 1 | acu _ _ => 2

mutual
def beq : Term → Term → Bool
  | var a, var b => a == b
  | app f as, app g bs => f == g && beqL as bs
  | acu f as, acu g bs => f == g && beqL as bs
  | _, _ => false
def beqL : List Term → List Term → Bool
  | [], [] => true
  | a :: as, b :: bs => beq a b && beqL as bs
  | _, _ => false
end

-- `gt a b`: `a` comes strictly after `b` in a total order.
mutual
def gt : Term → Term → Bool
  | var a, var b => Nat.blt b a
  | app f as, app g bs => Nat.blt g f || (f == g && gtL as bs)
  | acu f as, acu g bs => Nat.blt g f || (f == g && gtL as bs)
  | a, b => Nat.blt b.tag a.tag
def gtL : List Term → List Term → Bool
  | [], _ => false
  | _ :: _, [] => true
  | a :: as, b :: bs => gt a b || (beq a b && gtL as bs)
end

def ins (t : Term) : List Term → List Term
  | [] => [t]
  | u :: us => if gt t u then u :: ins t us else t :: u :: us

def sort : List Term → List Term
  | [] => []
  | t :: ts => ins t (sort ts)

def flat (f : Nat) : List Term → List Term
  | [] => []
  | acu g bs :: as => if f == g then bs ++ flat f as else acu g bs :: flat f as
  | a :: as => a :: flat f as

def mkAcu (f : Nat) (ts : List Term) : Term :=
  match sort (flat f ts) with
  | [t] => t
  | ts => acu f ts

-- Normal form modulo ACU: flattened, identity removed, sorted.
mutual
def norm : Term → Term
  | var x => var x
  | app f as => app f (normL as)
  | acu f as => mkAcu f (normL as)
def normL : List Term → List Term
  | [] => []
  | a :: as => norm a :: normL as
end

def lookup (σ : List (Nat × Term)) (x : Nat) : Option Term :=
  match σ with
  | [] => none
  | (y, t) :: σ => if x == y then some t else lookup σ x

mutual
def subst (σ : List (Nat × Term)) : Term → Term
  | var x => (lookup σ x).getD (var x)
  | app f as => app f (substL σ as)
  | acu f as => acu f (substL σ as)
def substL (σ : List (Nat × Term)) : List Term → List Term
  | [] => []
  | a :: as => subst σ a :: substL σ as
end

mutual
def occurs (x : Nat) : Term → Bool
  | var y => x == y
  | app _ as => occursL x as
  | acu _ as => occursL x as
def occursL (x : Nat) : List Term → Bool
  | [] => false
  | a :: as => occurs x a || occursL x as
end

mutual
def hasVar : Term → Bool
  | var _ => true
  | app _ as => hasVarL as
  | acu _ as => hasVarL as
def hasVarL : List Term → Bool
  | [] => false
  | a :: as => hasVar a || hasVarL as
end

def summands (f : Nat) : Term → List Term
  | acu g ts => if f == g then ts else [acu g ts]
  | t => [t]

def head? : Term → Option Nat
  | app f _ => some f
  | _ => none

end Term

open Term

abbrev Subst := List (Nat × Term)
abbrev Eqn := Term × Term

def nth {β} : List β → Nat → Option β
  | [], _ => none
  | a :: _, 0 => some a
  | _ :: as, n + 1 => nth as n

def nthD {β} (l : List β) (n : Nat) (d : β) : β := (nth l n).getD d

def count (t : Term) : List Term → Nat
  | [] => 0
  | u :: us => (if beq t u then 1 else 0) + count t us

def memT (t : Term) (l : List Term) : Bool := l.any (beq t)

def powerset : List Nat → List (List Nat)
  | [] => [[]]
  | k :: ks => let p := powerset ks; p.map (k :: ·) ++ p

/-- All vectors with entry `j` in `0..bs[j]`. -/
def box : List Nat → List (List Nat)
  | [] => [[]]
  | b :: bs => let r := box bs; (List.range (b + 1)).flatMap fun i => r.map (i :: ·)

def dot (r : List Int) (v : List Nat) : Int :=
  match r, v with
  | c :: r, x :: v => c * x + dot r v
  | _, _ => 0

def leV : List Nat → List Nat → Bool
  | a :: as, b :: bs => Nat.ble a b && leV as bs
  | _, _ => true

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

inductive Rule where
  | delete (i p : Nat)
  | decomp (i p : Nat)
  | elim (i x p : Nat)
  | clash (i : Nat)
  | ground (i : Nat)
  | cover (a : Nat) (w : Subst)
  | acu (f : Nat) (eqs : List Nat) (unk : List Term) (alien : List Bool)
      (rows : List (List Int)) (basis : List (List Nat))
      (sels : List (List Nat × List Nat)) (ps : List Nat)

structure Cert where
  problem : List Eqn
  vars : List Nat
  answers : List Subst
  steps : List Rule

def normEq (σ : Subst) (e : Eqn) : Eqn := (norm (subst σ e.1), norm (subst σ e.2))

/-- The premise states of an ACU step, when its side conditions hold. -/
def acuPremises (α : Subst) (E : List Eqn) (f : Nat) (eqs : List Nat) (unk : List Term)
    (alien : List Bool) (rows : List (List Int)) (basis : List (List Nat))
    (sels : List (List Nat × List Nat)) : Option (List (Subst × List Eqn)) :=
  let solved := eqs.filterMap (nth E)
  let rest := ((List.range E.length).zip E).filterMap fun (i, e) =>
    if eqs.contains i then none else some e
  let m := unk.length
  let idx := List.range m
  let isAlien j := nthD alien j false
  -- 1. rows
  let rowsOk := solved.length == eqs.length && rows.length == solved.length &&
    (rows.zip solved).all fun (r, (l, s)) =>
      let L := summands f l; let R := summands f s
      (idx.all fun j => nthD r j 0 == 0 || memT (nthD unk j (var 0)) (L ++ R)) &&
      ((L ++ R).all fun t =>
        (idx.foldl (fun acc j => if beq (nthD unk j (var 0)) t then acc + nthD r j 0 else acc) 0)
          == (count t L : Int) - (count t R : Int))
  let solves (v : List Nat) := rows.all fun r => dot r v == 0
  -- 2. basis vectors
  let bounded (v : List Nat) := idx.all fun j => !isAlien j || Nat.ble (nthD v j 0) 1
  let basisOk := basis.all fun v => v.length == m && v.any (· != 0) && solves v && bounded v
  -- 3. basis completeness (proxy: a box)
  let clashFree (v : List Nat) := idx.all fun j => idx.all fun j' =>
    !(isAlien j && isAlien j' && nthD v j 0 == 1 && nthD v j' 0 == 1) ||
      match (nthD unk j (var 0)).head?, (nthD unk j' (var 0)).head? with
      | some a, some b => a == b
      | _, _ => true
  let complete := (box (idx.map fun j => if isAlien j then 1 else 2)).all fun v =>
    !(v.any (· != 0) && solves v && clashFree v) || basis.any (leV · v)
  -- 4. selections
  let ks := List.range basis.length
  let alienFree k := idx.all fun j => !isAlien j || nthD (nthD basis k []) j 0 == 0
  let legal (S : List Nat) := (ks.all fun k => !alienFree k || S.contains k) &&
    idx.all fun j => !isAlien j || S.foldl (fun a k => a + nthD (nthD basis k []) j 0) 0 == 1
  let selsOk := (sels.all fun (S, _) => legal S) &&
    (powerset ks).all fun S => !legal S || sels.any fun (S', _) => natEqL S (sortN S')
  if rowsOk && basisOk && complete && selsOk then
    some <| sels.map fun (S, fresh) =>
      let free := S.filter alienFree
      let rep k := if alienFree k then var (nthD fresh (free.idxOf k) 0) else
        nthD unk ((idx.filter fun j => isAlien j && nthD (nthD basis k []) j 0 == 1).headD 0) (var 0)
      let θ : Subst := idx.filterMap fun j =>
        if isAlien j then none else match nthD unk j (var 0) with
          | var n => some (n, acu f (S.flatMap fun k => List.replicate (nthD (nthD basis k []) j 0) (rep k)))
          | _ => none
      let new : List Eqn := S.flatMap fun k =>
        let A := idx.filter fun j => isAlien j && nthD (nthD basis k []) j 0 == 1
        (A.drop 1).map fun j => (nthD unk j (var 0), rep k)
      (α.map fun (x, t) => (x, norm (subst θ t)), new ++ rest.map (normEq θ))
  else none

def run (c : Cert) : Nat → Nat → Subst → List Eqn → Bool
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
      | some (l, r) => !hasVar l && !hasVar r && !beq l r
      | none => false
    | some (.elim i x p) => match nth E i with
      | some (l, r) =>
        let t? := if beq l (var x) then some r else if beq r (var x) then some l else none
        match t? with
        | some t => !occurs x t &&
            let θ := [(x, t)]
            run c n p (α.map fun (y, u) => (y, norm (subst θ u))) ((E.eraseIdx i).map (normEq θ))
        | none => false
      | none => false
    | some (.cover a w) => E.isEmpty && match nth c.answers a with
      | some σ => α.all fun (x, t) => beq t (norm (subst w ((lookup σ x).getD (var x))))
      | none => false
    | some (.acu f eqs unk alien rows basis sels ps) =>
      match acuPremises α E f eqs (normL unk) alien rows basis sels with
      | some states => states.length == ps.length &&
          (states.zip ps).all fun ((α', E'), p) => run c n p α' E'
      | none => false
    | none => false

def Cert.check (c : Cert) : Bool :=
  run c (c.steps.length + 1) 0 (c.vars.map fun x => (x, var x)) (c.problem.map (normEq []))
