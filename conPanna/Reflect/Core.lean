import Expresso.ACU

/-!
Certification by reflection (documentation/reflection-design.md): terms as data, models,
evaluation, and the checker of UDF certificates. Definitions only; the soundness proof is
in `Reflect/Sound.lean`. Everything here is computed by the kernel (`decide`), so the
definitions use structural recursion and `Nat` arithmetic only.
-/

namespace Reflect

universe u

/-! ## Terms -/

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

mutual
def subst (σ : Nat → Option Term) : Term → Term
  | var x => (σ x).getD (var x)
  | app f as => app f (substL σ as)
  | acu f as => acu f (substL σ as)
def substL (σ : Nat → Option Term) : List Term → List Term
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

-- All variables are below `n`.
mutual
def varsBelow (n : Nat) : Term → Bool
  | var y => Nat.blt y n
  | app _ as => varsBelowL n as
  | acu _ as => varsBelowL n as
def varsBelowL (n : Nat) : List Term → Bool
  | [] => true
  | a :: as => varsBelow n a && varsBelowL n as
end

end Term

/-! ## Signatures and models -/

/-- Shapes of variable tuples: `leaf s` a variable of sort `s`. -/
inductive Shp where
  | leaf (s : Nat)
  | pair (l r : Shp)

def Shp.size : Shp → Nat
  | .leaf _ => 1
  | .pair l r => l.size + r.size

def Shp.sorts : Shp → List Nat
  | .leaf s => [s]
  | .pair l r => l.sorts ++ r.sorts

def Shp.Ty (T : Nat → Type) : Shp → Type
  | .leaf s => T s
  | .pair l r => l.Ty T × r.Ty T

/-- The argument tuple of a constructor: `T s₁ × (T s₂ × …)`, `Unit` when empty. -/
def Tup (T : Nat → Type) : List Nat → Type
  | [] => Unit
  | [s] => T s
  | s :: ss => T s × Tup T ss

/-- A free constructor: argument sorts, result sort, and its Lean function. -/
structure Op (T : Nat → Type) where
  args : List Nat
  res : Nat
  build : Tup T args → T res
  /-- The arguments of a value built by this constructor. -/
  unbuild : T res → Option (Tup T args)

/-- An ACU operator: `T bag ≃ ACU (T elem)`. -/
structure AcuOp (T : Nat → Type) where
  elem : Nat
  bag : Nat
  toBag : T bag → ACU (T elem)
  ofBag : ACU (T elem) → T bag

/-- The Lean side of a signature. Sort `s` is the type `T s`; values carry their sort. -/
structure Model where
  T : Nat → Type
  /-- The constructor of a value: its position in `ops`. -/
  tag : (s : Nat) → T s → Nat
  ops : List (Op T)
  acus : List (AcuOp T)

def AllL {β : Type u} (P : β → Prop) : List β → Prop
  | [] => True
  | a :: as => P a ∧ AllL P as

def AllIdx {β : Type u} (P : Nat → β → Prop) : Nat → List β → Prop
  | _, [] => True
  | i, a :: as => P i a ∧ AllIdx P (i + 1) as

/-- The laws of a model, each closed by `rfl` per constructor: constructors are injective
(`unbuild` inverts `build`) and distinct (`tag` tells them apart); ACU sorts are bags. -/
structure Model.Lawful (M : Model) : Prop where
  unbuild : AllL (fun o : Op M.T => ∀ a, o.unbuild (o.build a) = some a) M.ops
  tag : AllIdx (fun i (o : Op M.T) => ∀ a, M.tag o.res (o.build a) = i) 0 M.ops
  acu : AllL (fun A : AcuOp M.T => (∀ X, A.toBag (A.ofBag X) = X) ∧
    (∀ y, A.ofBag (A.toBag y) = y) ∧ A.elem ≠ A.bag) M.acus

namespace Model

variable (M : Model)

abbrev Val := Σ s, M.T s

/-- The component of a value at sort `s`. -/
def get? (s : Nat) (v : M.Val) : Option (M.T s) :=
  if h : v.1 = s then some (h ▸ v.2) else none

def getTup? : (ss : List Nat) → List M.Val → Option (Tup M.T ss)
  | [], [] => some ()
  | [s], [v] => M.get? s v
  | s :: s' :: ss, v :: vs =>
    match M.get? s v, getTup? (s' :: ss) vs with
    | some a, some b => some (a, b)
    | _, _ => none
  | _, _ => none

def op? (f : Nat) : Option (Op M.T) := M.ops[f]?

def acu? (f : Nat) : Option (AcuOp M.T) := M.acus[f]?

def app (f : Nat) (vs : List M.Val) : Option M.Val :=
  match M.op? f with
  | some o => (M.getTup? o.args vs).map fun a => ⟨o.res, o.build a⟩
  | none => none

/-- What a summand contributes to a bag of `A`: an element, or a bag. -/
def contrib (A : AcuOp M.T) (v : M.Val) : Option (ACU (M.T A.elem)) :=
  match M.get? A.elem v with
  | some e => some {e}
  | none => (M.get? A.bag v).map A.toBag

/-! ## Evaluation -/

abbrev Valuation := Nat → Option M.Val

mutual
def eval (ρ : M.Valuation) : Term → Option M.Val
  | .var x => ρ x
  | .app f ts => (evalL ρ ts).bind (M.app f)
  | .acu f ts => match M.acu? f with
    | some A => (sumL ρ A ts).map fun X => ⟨A.bag, A.ofBag X⟩
    | none => none
def evalL (ρ : M.Valuation) : List Term → Option (List M.Val)
  | [] => some []
  | t :: ts => match eval ρ t, evalL ρ ts with
    | some v, some vs => some (v :: vs)
    | _, _ => none
def sumL (ρ : M.Valuation) (A : AcuOp M.T) : List Term → Option (ACU (M.T A.elem))
  | [] => some ∅
  | [t] => (eval ρ t).bind (M.contrib A)
  | t :: t' :: ts => match (eval ρ t).bind (M.contrib A), sumL ρ A (t' :: ts) with
    | some a, some b => some (a + b)
    | _, _ => none
end

/-- The valuation of a tuple: its leaves, in order. -/
def encL : (sh : Shp) → sh.Ty M.T → List M.Val
  | .leaf s, x => [⟨s, x⟩]
  | .pair l r, (a, b) => encL l a ++ encL r b

def enc (sh : Shp) (x : sh.Ty M.T) : M.Valuation := fun i => (M.encL sh x)[i]?

end Model

end Reflect
