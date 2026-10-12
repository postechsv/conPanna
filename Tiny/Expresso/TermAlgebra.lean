/-! Constructor-term algebra and its faithful native encoding. No pattern or rule dependency. -/
namespace TermAlgebra

universe u v w

/-! ## Constructor presentation and generated structural equality -/

-- Ctor: which constructors exist?
-- wait      : Ctor [ticket] mode
-- singleton : Ctor [mode] processes
-- union     : Ctor [processes, processes] processes
-- empty     : Ctor [] processes
structure CtorSig (Sorts : Type u) where -- Ctor
  Ctor : List Sorts → Sorts → Type v -- op (function operating on Sorts)

variable {Sorts : Type u} {sig : CtorSig.{u, v} Sorts}

-- CtorTerm and CtorTerms: well-typed constructor terms
mutual
  inductive CtorTerm (sig : CtorSig.{u, v} Sorts) : Sorts → Type (max u v) where
    | app {ss s} (head : sig.Ctor ss s) (args : CtorTerms sig ss) : CtorTerm sig s
  inductive CtorTerms (sig : CtorSig.{u, v} Sorts) : List Sorts → Type (max u v) where
    | nil : CtorTerms sig []
    | cons {s ss} (first : CtorTerm sig s) (rest : CtorTerms sig ss) : CtorTerms sig (s :: ss)
end

-- suppose (laws : Theory sig)
-- laws (union a b) (union b a) -- commutativity
-- laws (union (union a b) c) (union a (union b c) -- associativity
abbrev Theory (sig : CtorSig.{u, v} Sorts) :=
  {s : Sorts} → CtorTerm sig s → CtorTerm sig s → Prop

mutual
  /-- The LEAST equivalence closed under the declared equations and constructors. -/
  inductive EqUpto (laws : Theory sig) :
      {s : Sorts} → CtorTerm sig s → CtorTerm sig s → Prop where
    | refl {s} (a : CtorTerm sig s) : EqUpto laws a a
    | symm {s} {a b : CtorTerm sig s} : EqUpto laws a b → EqUpto laws b a
    | trans {s} {a b c : CtorTerm sig s} :
        EqUpto laws a b → EqUpto laws b c → EqUpto laws a c
    | law {s} {a b : CtorTerm sig s} : laws a b → EqUpto laws a b
    | congr {ss s} (head : sig.Ctor ss s) {a b : CtorTerms sig ss} :
        EqsUpto laws a b → EqUpto laws (.app head a) (.app head b)
  inductive EqsUpto (laws : Theory sig) :
      {ss : List Sorts} → CtorTerms sig ss → CtorTerms sig ss → Prop where
    | nil : EqsUpto laws .nil .nil
    | cons {s ss} {a b : CtorTerm sig s} {as bs : CtorTerms sig ss} :
        EqUpto laws a b → EqsUpto laws as bs → EqsUpto laws (.cons a as) (.cons b bs)
end

-- =[B] is an equivalence relation
theorem EqUpto.equivalence (laws : Theory sig) (s : Sorts) :
    Equivalence (EqUpto laws (s := s)) :=
  ⟨EqUpto.refl, EqUpto.symm, EqUpto.trans⟩

/-! ## Faithful interpretation using ordinary user-defined constructors
The two registration equations concern syntax, NOT literal commutativity of
Lean constructors. A generator may supply them later, outside this file.
-/

def Args (Carrier : Sorts → Type w) : List Sorts → Type w
  | [] => PUnit
  | s :: ss => Carrier s × Args Carrier ss

structure Algebra (sig : CtorSig.{u, v} Sorts) where
  Carrier : Sorts → Type w
  apply : ∀ {ss s}, sig.Ctor ss s → Args Carrier ss → Carrier s

mutual
  def CtorTerm.decode (A : Algebra sig) : {s : Sorts} → CtorTerm sig s → A.Carrier s
    | _, .app head args => A.apply head (args.decode A)
  def CtorTerms.decode (A : Algebra sig) : {ss : List Sorts} → CtorTerms sig ss → Args A.Carrier ss
    | _, .nil => PUnit.unit
    | _, .cons a as => (a.decode A, as.decode A)
end

def Args.encode {Carrier : Sorts → Type w} (encode : ∀ s, Carrier s → CtorTerm sig s) :
    (ss : List Sorts) → Args Carrier ss → CtorTerms sig ss
  | [], _ => .nil
  | s :: ss, (a, as) => .cons (encode s a) (Args.encode encode ss as)

structure Registration (sig : CtorSig.{u, v} Sorts) extends Algebra.{u, v, w} sig where
  encode : ∀ s, Carrier s → CtorTerm sig s
  decode_encode : ∀ s a, (encode s a).decode toAlgebra = a
  encode_apply : ∀ {ss s} (head : sig.Ctor ss s) (args : Args Carrier ss),
    encode s (apply head args) = .app head (Args.encode encode ss args)

mutual
  /-- Constructor compatibility also gives the other round trip. -/
  theorem Registration.encode_decode (reg : Registration sig) {s : Sorts} (a : CtorTerm sig s) :
      reg.encode s (a.decode reg.toAlgebra) = a :=
    match a with
    | .app head args =>
      (reg.encode_apply head (args.decode reg.toAlgebra)).trans
        (congrArg (CtorTerm.app head) (reg.encode_decode_args args))
  theorem Registration.encode_decode_args (reg : Registration sig) {ss : List Sorts}
      (args : CtorTerms sig ss) : Args.encode reg.encode ss (args.decode reg.toAlgebra) = args :=
    match args with
    | .nil => rfl
    | .cons a as => congr (congrArg CtorTerms.cons (reg.encode_decode a)) (reg.encode_decode_args as)
end

/-- One structural equality on native values; no legacy representation/bridge. -/
def NativeEq (laws : Theory sig) (reg : Registration sig) {s : Sorts}
    (a b : reg.Carrier s) : Prop :=
  EqUpto laws (reg.encode s a) (reg.encode s b)

theorem NativeEq.equivalence (laws : Theory sig) (reg : Registration sig) (s : Sorts) :
    Equivalence (NativeEq laws reg (s := s)) :=
  ⟨fun a => .refl (reg.encode s a), fun h => .symm h, fun h k => .trans h k⟩


end TermAlgebra
