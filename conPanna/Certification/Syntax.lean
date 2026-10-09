import conPanna.Certification.Enumeration

/-!
# Internal typed certificate data
This file owns constructor syntax, sorted variable positions, substitutions,
state snapshots and finite side-condition data. Read Calculus.lean for the
proof rules; these definitions are their implementation support, not a second
unification algorithm. No JSON, subprocess or native-semantic validity proof.
-/

namespace DirectCertification

open Structural.Indexed

variable {Sorts : Type} {sig : Signature Sorts}

namespace Substitution

inductive Variable : List Sorts → Sorts → Type where
  | here {s ss} : Variable (s :: ss) s
  | there {s t ss} : Variable ss s → Variable (t :: ss) s
  deriving DecidableEq

mutual
  inductive Term (sig : Signature Sorts) (Γ : List Sorts) : Sorts → Type where
    | var {s} : Variable Γ s → Term sig Γ s
    | app {ss s} : sig.Symbol ss s → Terms sig Γ ss → Term sig Γ s
  inductive Terms (sig : Signature Sorts) (Γ : List Sorts) : List Sorts → Type where
    | nil : Terms sig Γ []
    | cons {s ss} : Term sig Γ s → Terms sig Γ ss → Terms sig Γ (s :: ss)
end

def Terms.get {Γ ss s} : Terms sig Γ ss → Variable ss s → Term sig Γ s
  | .cons a _, .here => a
  | .cons _ rest, .there v => rest.get v

def Terms.variables (Γ : List Sorts) : (Δ : List Sorts) →
    (∀ {s}, Variable Δ s → Variable Γ s) → Terms sig Γ Δ
  | [], _ => .nil
  | _ :: ss, rename => .cons (.var (rename .here))
      (Terms.variables Γ ss (fun v => rename (.there v)))

def Terms.identity (Γ : List Sorts) : Terms sig Γ Γ := Terms.variables Γ Γ (fun v => v)

theorem Terms.variables_get {Γ Δ t} (rename : ∀ {s}, Variable Δ s → Variable Γ s)
    (v : Variable Δ t) : (Terms.variables Γ Δ rename : Terms sig Γ Δ).get v = .var (rename v) := by
  induction v with
  | here => rfl
  | there v ih => exact ih (fun v => rename (.there v))

mutual
  def Term.subst {Γ Δ s} (images : Terms sig Δ Γ) : Term sig Γ s → Term sig Δ s
    | .var v => images.get v
    | .app f args => .app f (args.subst images)
  def Terms.subst {Γ Δ ss} (terms : Terms sig Γ ss) (images : Terms sig Δ Γ) : Terms sig Δ ss :=
    match terms with
    | .nil => .nil
    | .cons a rest => .cons (a.subst images) (rest.subst images)
end

def add {Γ s} (op : sig.ACUOp s) (a b : Term sig Γ s) : Term sig Γ s :=
  .app (sig.add op) (.cons a (.cons b .nil))

def zero {Γ s} (op : sig.ACUOp s) : Term sig Γ s := .app (sig.zero op) .nil

def copies {Γ s} (op : sig.ACUOp s) : Nat → Term sig Γ s → Term sig Γ s
  | 0, _ => zero op
  | k + 1, a => add op a (copies op k a)

theorem copies_subst {Γ Δ s} (op : sig.ACUOp s) (k : Nat) (a : Term sig Γ s)
    (images : Terms sig Δ Γ) :
    (copies op k a).subst images = copies op k (a.subst images) := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [copies, add, Term.subst, Terms.subst, ih]

namespace Sharing

inductive Slots (s : Sorts) : List Sorts → Nat → Type where
  | nil : Slots s [] 0
  | skip {t Γ n} : Slots s Γ n → Slots s (t :: Γ) n
  | take {Γ n} : Slots s Γ n → Slots s (s :: Γ) (n + 1)

def Slots.variable {s} : {Γ : List Sorts} → {n : Nat} → Slots s Γ n → Fin n → Variable Γ s
  | _, _, .nil, i => Fin.elim0 i
  | _, _, .skip rest, i => .there (rest.variable i)
  | _, _, .take rest, i => Fin.cases .here (fun j => .there (rest.variable j)) i

def Slots.replace {s Δ} : {Γ : List Sorts} → {n : Nat} → Slots s Γ n →
    (Fin n → Term sig Δ s) → Terms sig Δ Γ → Terms sig Δ Γ
  | _, _, .nil, _, .nil => .nil
  | _, _, .skip rest, replacement, .cons a tail => .cons a (rest.replace replacement tail)
  | _, _, .take rest, replacement, .cons _ tail =>
      .cons (replacement 0) (rest.replace (fun i => replacement i.succ) tail)

theorem Slots.get_replace {s Γ n Δ} (slots : Slots s Γ n)
    (replacement : Fin n → Term sig Δ s) (others : Terms sig Δ Γ) (i : Fin n) :
    (slots.replace replacement others).get (slots.variable i) = replacement i := by
  induction slots with
  | nil => exact Fin.elim0 i
  | skip rest ih => cases others with | cons a tail => exact ih replacement tail i
  | take rest ih =>
    cases others with
    | cons a tail => exact Fin.cases rfl (fun j => ih _ tail j) i

def weaken (s : Sorts) : (k : Nat) → {Γ : List Sorts} → {t : Sorts} →
    Variable Γ t → Variable (List.replicate k s ++ Γ) t
  | 0, _, _, v => v
  | k + 1, _, _, v => .there (weaken s k v)

def parameter {Γ} (s : Sorts) : (k : Nat) → Fin k → Variable (List.replicate k s ++ Γ) s
  | 0, i => Fin.elim0 i
  | k + 1, i => Fin.cases .here (fun j => .there (parameter s k j)) i

def extend {C : Sorts → Type} {Γ s} : {k : Nat} →
    (Fin k → C s) → Args C Γ → Args C (List.replicate k s ++ Γ)
  | 0, _, values => values
  | _ + 1, parameters, values => (parameters 0, extend (fun i => parameters i.succ) values)

def lift {Γ s} (k : Nat) : Terms sig (List.replicate k s ++ Γ) Γ :=
  Terms.variables _ Γ (weaken s k)

def sum {Γ s} (op : sig.ACUOp s) : {n : Nat} → FiniteSharing.Vector n →
    (Fin n → Term sig Γ s) → Term sig Γ s
  | 0, _, _ => zero op
  | _ + 1, coeff, values => add op (copies op (coeff 0) (values 0))
      (sum op (fun i => coeff i.succ) (fun i => values i.succ))

def replacement {Γ s n} (op : sig.ACUOp s) (slots : Slots s Γ n)
    (left right : FiniteSharing.Vector n) (generators : List (FiniteSharing.Vector n)) :
    Fin n → Term sig (List.replicate generators.length s ++ Γ) s := fun i =>
  if left i = 0 ∧ right i = 0 then .var (weaken s generators.length (slots.variable i))
  else sum op (fun j => generators.get j i) (fun j => .var (parameter s generators.length j))

def substitution {Γ s n} (op : sig.ACUOp s) (slots : Slots s Γ n)
    (left right : FiniteSharing.Vector n) (generators : List (FiniteSharing.Vector n)) :
    Terms sig (List.replicate generators.length s ++ Γ) Γ :=
  slots.replace (replacement op slots left right generators) (lift generators.length)

end Sharing

structure Answer (sig : Signature Sorts) (inputs : List Sorts) where
  parameters : List Sorts
  images : Terms sig parameters inputs

structure Problem (sig : Signature Sorts) (inputs : List Sorts) where
  sort : Sorts
  left : Term sig inputs sort
  right : Term sig inputs sort

namespace Binding

inductive Removal (s : Sorts) : List Sorts → List Sorts → Type where
  | here {Γ} : Removal s (s :: Γ) Γ
  | there {t Γ Δ} : Removal s Γ Δ → Removal s (t :: Γ) (t :: Δ)

def Removal.variable {s} : {Γ Δ : List Sorts} → Removal s Γ Δ → Variable Γ s
  | _, _, .here => .here
  | _, _, .there rest => .there rest.variable

def Removal.weaken {s} : {Γ Δ : List Sorts} → Removal s Γ Δ →
    {t : Sorts} → Variable Δ t → Variable Γ t
  | _, _, .here, _, v => .there v
  | _, _, .there _, _, .here => .here
  | _, _, .there rest, _, .there v => .there (rest.weaken v)

def Removal.restrict {C : Sorts → Type} {s} : {Γ Δ : List Sorts} →
    Removal s Γ Δ → Args C Γ → Args C Δ
  | _, _, .here, values => values.2
  | _, _, .there rest, values => (values.1, rest.restrict values.2)

def tabulate (Δ : List Sorts) : (Γ : List Sorts) →
    (∀ {s}, Variable Γ s → Term sig Δ s) → Terms sig Δ Γ
  | [], _ => .nil
  | _ :: Γ, images => .cons (images .here) (tabulate Δ Γ (fun v => images (.there v)))

theorem tabulate_get {Γ Δ s} (images : ∀ {t}, Variable Γ t → Term sig Δ t) (v : Variable Γ s) :
    (tabulate Δ Γ images).get v = images v := by
  induction v with
  | here => rfl
  | there v ih => exact ih (fun v => images (.there v))

def Removal.replace {s Ω} : {Γ Δ : List Sorts} → Removal s Γ Δ → Term sig Ω s →
    (∀ {t}, Variable Δ t → Term sig Ω t) → ∀ {t}, Variable Γ t → Term sig Ω t
  | _, _, .here, term, _, _, .here => term
  | _, _, .here, _, others, _, .there v => others v
  | _, _, .there _, _, others, _, .here => others .here
  | _, _, .there rest, term, others, _, .there v =>
      rest.replace term (fun v => others (.there v)) v

theorem Removal.replace_variable {s Γ Δ Ω} (remove : Removal s Γ Δ) (term : Term sig Ω s)
    (others : ∀ {t}, Variable Δ t → Term sig Ω t) :
    remove.replace term others remove.variable = term := by
  induction remove with
  | here => rfl
  | there rest ih => exact ih (fun v => others (.there v))

theorem Removal.replace_weaken {s Γ Δ Ω t} (remove : Removal s Γ Δ) (term : Term sig Ω s)
    (others : ∀ {t}, Variable Δ t → Term sig Ω t) (v : Variable Δ t) :
    remove.replace term others (remove.weaken v) = others v := by
  induction remove with
  | here => rfl
  | there rest ih =>
    cases v with
    | here => rfl
    | there v => exact ih (fun v => others (.there v)) v

def Removal.embedding {s Γ Δ} (remove : Removal s Γ Δ) : Terms sig Γ Δ :=
  Terms.variables Γ Δ remove.weaken

def deletion {Γ : List Sorts} {s : Sorts} : Variable Γ s → Σ Δ, Removal s Γ Δ
  | .here => ⟨_, .here⟩
  | .there v => let ⟨Δ, remove⟩ := deletion v; ⟨_ :: Δ, .there remove⟩

theorem deletion_variable {Γ : List Sorts} {s : Sorts} (v : Variable Γ s) :
    (deletion v).2.variable = v := by
  induction v with
  | here => rfl
  | there v ih => exact congrArg Variable.there ih

def Removal.lowerVariable {s} : {Γ Δ : List Sorts} → Removal s Γ Δ →
    {t : Sorts} → Variable Γ t → Option (Variable Δ t)
  | _, _, .here, _, .here => none
  | _, _, .here, _, .there v => some v
  | _, _, .there _, _, .here => some .here
  | _, _, .there rest, _, .there v => (rest.lowerVariable v).map Variable.there

theorem Removal.lowerVariable_sound {s t : Sorts} {Γ Δ : List Sorts} (remove : Removal s Γ Δ)
    (v : Variable Γ t) (w : Variable Δ t) (found : remove.lowerVariable v = some w) :
    remove.weaken w = v := by
  induction remove with
  | here =>
    cases v with
    | here => cases found
    | there v => cases found; rfl
  | there rest ih =>
    cases v with
    | here => cases found; rfl
    | there v =>
      cases h : rest.lowerVariable v with
      | none => simp only [Removal.lowerVariable, h, Option.map_none] at found; cases found
      | some lower =>
        simp only [Removal.lowerVariable, h, Option.map_some, Option.some.injEq] at found
        cases found
        exact congrArg Variable.there (ih v lower h)

mutual
  def lower {s Γ Δ} (remove : Removal s Γ Δ) : {t : Sorts} → Term sig Γ t → Option (Term sig Δ t)
    | _, .var v => (remove.lowerVariable v).map Term.var
    | _, .app f args => (lowerArgs remove args).map (Term.app f)
  def lowerArgs {s Γ Δ} (remove : Removal s Γ Δ) :
      {ss : List Sorts} → Terms sig Γ ss → Option (Terms sig Δ ss)
    | _, .nil => some .nil
    | _, .cons first rest => do
        let first ← lower remove first
        let rest ← lowerArgs remove rest
        pure (.cons first rest)
end

theorem lower_sound {s Γ Δ t} (remove : Removal s Γ Δ)
    (term : Term sig Γ t) (reduced : Term sig Δ t) (found : lower remove term = some reduced) :
    reduced.subst remove.embedding = term := by
  refine Term.rec
    (motive_1 := fun {t} term => ∀ reduced : Term sig Δ t,
      lower remove term = some reduced → reduced.subst remove.embedding = term)
    (motive_2 := fun {ss} args => ∀ reduced : Terms sig Δ ss,
      lowerArgs remove args = some reduced → reduced.subst remove.embedding = args)
    ?_ ?_ ?_ ?_ term reduced found
  · intro t v reduced found
    cases h : remove.lowerVariable v with
    | none => simp only [lower, h, Option.map_none] at found; cases found
    | some w =>
      simp only [lower, h, Option.map_some, Option.some.injEq] at found
      cases found
      change (remove.embedding).get w = .var v
      rw [Removal.embedding, Terms.variables_get, remove.lowerVariable_sound v w h]
  · intro ss t f args ih reduced found
    cases h : lowerArgs remove args with
    | none => simp only [lower, h, Option.map_none] at found; cases found
    | some reducedArgs =>
      simp only [lower, h, Option.map_some, Option.some.injEq] at found
      cases found
      exact congrArg (Term.app f) (ih _ h)
  · intro reduced found
    cases found; rfl
  · intro t ss first rest hf hr reduced found
    cases hfirst : lower remove first with
    | none => simp only [lowerArgs, hfirst] at found; cases found
    | some first' =>
      cases hrest : lowerArgs remove rest with
      | none => simp only [lowerArgs, hfirst, hrest] at found; cases found
      | some rest' =>
        simp only [lowerArgs, hfirst, hrest, Option.pure_def] at found
        cases found
        simp only [Terms.subst, hf _ hfirst, hr _ hrest]

structure Prepared {Γ s} (selected : Variable Γ s) (rhs : Term sig Γ s) where
  context : List Sorts
  remove : Removal s Γ context
  position : remove.variable = selected
  replacement : Term sig context s
  reconstruction : replacement.subst remove.embedding = rhs

def prepare {Γ s} (selected : Variable Γ s) (rhs : Term sig Γ s) : Option (Prepared selected rhs) :=
  let remove := (deletion selected).2
  match found : lower remove rhs with
  | none => none
  | some replacement => some ⟨_, remove, deletion_variable selected, replacement,
      lower_sound remove rhs replacement found⟩

def Removal.substitution {s Γ Δ} (remove : Removal s Γ Δ) (term : Term sig Δ s) : Terms sig Δ Γ :=
  tabulate Δ Γ (remove.replace term (fun v => .var v))

theorem Removal.length {s : Sorts} {Γ Δ : List Sorts} (remove : Removal s Γ Δ) :
    Γ.length = Δ.length + 1 := by
  induction remove with
  | here => rfl
  | there rest ih => simp only [List.length_cons, ih, Nat.add_assoc]

def problem {s Γ Δ} (remove : Removal s Γ Δ) (term : Term sig Δ s) : Problem sig Γ :=
  ⟨s, .var remove.variable, term.subst remove.embedding⟩

def answer {s Γ Δ} (remove : Removal s Γ Δ) (term : Term sig Δ s) : Answer sig Γ :=
  ⟨Δ, remove.substitution term⟩

end Binding

namespace FreeOccurs

inductive Path (profile : Profile sig) {Γ s} (v : Variable Γ s) :
    {t : Sorts} → Term sig Γ t → Type where
  | root : Path profile v (.var v)
  | field {ss t u} (f : sig.Symbol ss t) (free : profile.view f = .atom f)
      (args : Terms sig Γ ss) (index : Variable ss u) (child : Path profile v (args.get index)) :
      Path profile v (.app f args)

inductive Proper (profile : Profile sig) {Γ s} (v : Variable Γ s) : Term sig Γ s → Type where
  | field {ss t} (f : sig.Symbol ss s) (free : profile.view f = .atom f)
      (args : Terms sig Γ ss) (index : Variable ss t) (child : Path profile v (args.get index)) :
      Proper profile v (.app f args)

mutual
  def findPath [DecidableEq Sorts] (profile : Profile sig) {Γ s}
      (v : Variable Γ s) : {t : Sorts} → (term : Term sig Γ t) → Option (Path profile v term)
    | t, .var w => if sameSort : s = t then by
        subst t
        exact if same : v = w then by subst w; exact some .root else none
      else none
    | _, .app f args => by
      cases free : profile.view f with
      | zero => exact none
      | add => exact none
      | atom f => exact (findArgs profile v args).map fun ⟨_, index, child⟩ => .field f free args index child
  def findArgs [DecidableEq Sorts] (profile : Profile sig) {Γ s}
      (v : Variable Γ s) : {ss : List Sorts} → (args : Terms sig Γ ss) →
        Option (Σ t, Σ index : Variable ss t, Path profile v (args.get index))
    | _, .nil => none
    | _, .cons first rest => match findPath profile v first with
      | some path => some ⟨_, .here, path⟩
      | none => (findArgs profile v rest).map fun ⟨t, index, path⟩ => ⟨t, .there index, path⟩
end

def findProper [DecidableEq Sorts] (profile : Profile sig) {Γ s}
    (v : Variable Γ s) : (term : Term sig Γ s) → Option (Proper profile v term)
  | .var _ => none
  | .app f args => by
    cases free : profile.view f with
    | zero => exact none
    | add => exact none
    | atom f => exact (findArgs profile v args).map fun ⟨_, index, child⟩ => .field f free args index child

end FreeOccurs

namespace FreePhase

inductive Action (profile : Profile sig) {Γ} : {s : Sorts} → Term sig Γ s → Term sig Γ s → Type where
  | delete {s} (term : Term sig Γ s) : Action profile term term
  | bind {s} (v : Variable Γ s) (rhs : Term sig Γ s) (entry : Binding.Prepared v rhs) :
      Action profile (.var v) rhs
  | occurs {s} (v : Variable Γ s) (rhs : Term sig Γ s) (path : FreeOccurs.Proper profile v rhs) :
      Action profile (.var v) rhs
  | orient {s a b} (action : Action profile (s := s) b a) : Action profile a b
  | decompose {ss s} (f : sig.Symbol ss s) (free : profile.view f = .atom f)
      (a b : Terms sig Γ ss) : Action profile (.app f a) (.app f b)
  | clash {ss tt s} (f : sig.Symbol ss s) (g : sig.Symbol tt s)
      (hf : profile.view f = .atom f) (hg : profile.view g = .atom g)
      (different : (⟨ss, f⟩ : Σ us, sig.Symbol us s) ≠ ⟨tt, g⟩)
      (a : Terms sig Γ ss) (b : Terms sig Γ tt) : Action profile (.app f a) (.app g b)
  | postpone {s a b} : Action profile (s := s) a b

def classifyVariable [DecidableEq Sorts] (profile : Profile sig) {Γ s} (v : Variable Γ s)
    (rhs : Term sig Γ s) : Action profile (.var v) rhs :=
  match rhs with
  | .var w => if same : v = w then by subst w; exact .delete _
      else match Binding.prepare v (.var w) with
        | some entry => .bind v _ entry
        | none => .postpone
  | .app f args => match Binding.prepare v (.app f args) with
      | some entry => .bind v _ entry
      | none => match FreeOccurs.findProper profile v (.app f args) with
        | some path => .occurs v _ path
        | none => .postpone

def classify [DecidableEq Sorts] [∀ ss s, DecidableEq (sig.Symbol ss s)]
    (profile : Profile sig) {Γ s} (left right : Term sig Γ s) : Action profile left right :=
  match left, right with
  | .var v, rhs => classifyVariable profile v rhs
  | lhs, .var v => .orient (classifyVariable profile v lhs)
  | @Term.app _ _ _ ss _ f a, @Term.app _ _ _ tt _ g b => by
      cases hf : profile.view f with
      | zero => exact .postpone
      | add => exact .postpone
      | atom f =>
        cases hg : profile.view g with
        | zero => exact .postpone
        | add => exact .postpone
        | atom g =>
          exact if sameSorts : ss = tt then by
            cases sameSorts
            exact if sameHead : f = g then by subst g; exact .decompose f hf a b
            else .clash f g hf hg (fun same => sameHead (eq_of_heq (Sigma.mk.inj same).2)) a b
          else .clash f g hf hg (fun same => sameSorts (Sigma.mk.inj same).1) a b

end FreePhase

namespace Sharing

def problem {Γ s n} (op : sig.ACUOp s) (slots : Slots s Γ n)
    (left right : FiniteSharing.Vector n) : Problem sig Γ :=
  ⟨s, sum op left (fun i => .var (slots.variable i)),
    sum op right (fun i => .var (slots.variable i))⟩

def answer {Γ s n} (op : sig.ACUOp s) (slots : Slots s Γ n)
    (left right : FiniteSharing.Vector n) (generators : List (FiniteSharing.Vector n)) : Answer sig Γ :=
  ⟨List.replicate generators.length s ++ Γ, substitution op slots left right generators⟩

end Sharing

namespace Worklist

def equation {Γ s} (a b : Term sig Γ s) : Problem sig Γ := ⟨s, a, b⟩

def lift4 {Γ s} : Terms sig (s :: s :: s :: s :: Γ) Γ :=
  Terms.variables _ Γ (fun v => .there (.there (.there (.there v))))

def liftEquations {Γ s} (eqs : List (Problem sig Γ)) : List (Problem sig (s :: s :: s :: s :: Γ)) :=
  eqs.map fun e => equation (e.left.subst lift4) (e.right.subst lift4)

def mutated {Γ s} (op : sig.ACUOp s) (a b c d : Term sig Γ s)
    (eqs : List (Problem sig Γ)) : List (Problem sig (s :: s :: s :: s :: Γ)) :=
  [equation (a.subst lift4) (add op (.var .here) (.var (.there .here))),
   equation (b.subst lift4) (add op (.var (.there (.there .here))) (.var (.there (.there (.there .here))))),
   equation (c.subst lift4) (add op (.var .here) (.var (.there (.there .here)))),
   equation (d.subst lift4) (add op (.var (.there .here)) (.var (.there (.there (.there .here)))))] ++
    liftEquations eqs

def substituteEquations {Γ Δ} (images : Terms sig Δ Γ) (eqs : List (Problem sig Γ)) :
    List (Problem sig Δ) := eqs.map fun e => equation (e.left.subst images) (e.right.subst images)

namespace Purification

def embedding {Γ : List Sorts} {s : Sorts} : Terms sig (s :: Γ) Γ :=
  Binding.Removal.embedding (.here : Binding.Removal s (s :: Γ) Γ)

def assignment {Γ s} (term : Term sig Γ s) : Terms sig Γ (s :: Γ) :=
  Binding.Removal.substitution .here term

def source {Γ s} (term : Term sig Γ s) (template : Problem sig (s :: Γ)) : Problem sig Γ :=
  equation (template.left.subst (assignment term)) (template.right.subst (assignment term))

def definition {Γ s} (term : Term sig Γ s) : Problem sig (s :: Γ) :=
  equation (.var .here) (term.subst embedding)

def state {Γ s} (term : Term sig Γ s) (template : Problem sig (s :: Γ))
    (rest : List (Problem sig Γ)) : List (Problem sig (s :: Γ)) :=
  definition term :: template :: substituteEquations embedding rest

end Purification

def zeroRequirements {Γ s n} (op : sig.ACUOp s) (coeff : FiniteSharing.Vector n)
    (terms : Fin n → Term sig Γ s) : List (Problem sig Γ) :=
  List.ofFn fun i => equation (terms i) (if coeff i = 0 then terms i else zero op)

def atomRequirements {Γ s n} (op : sig.ACUOp s) (coeff : FiniteSharing.Vector n)
    (terms : Fin n → Term sig Γ s) (target : Term sig Γ s) (chosen : Fin n) :
    List (Problem sig Γ) :=
  List.ofFn fun i => equation (terms i)
    (if coeff i = 0 then terms i else if i = chosen then target else zero op)

structure ReplayState (sig : Signature Sorts) (inputs Γ : List Sorts) where
  images : Terms sig Γ inputs
  equations : List (Problem sig Γ)

namespace ReplayState

def substitute {inputs Γ Δ} (state : ReplayState sig inputs Γ) (bindings : Terms sig Δ Γ) :
    ReplayState sig inputs Δ :=
  ⟨state.images.subst bindings, substituteEquations bindings state.equations⟩

def prepend {inputs Γ} (state : ReplayState sig inputs Γ) (extra : List (Problem sig Γ)) :
    ReplayState sig inputs Γ :=
  ⟨state.images, extra ++ state.equations⟩

def purify {inputs Γ s} (state : ReplayState sig inputs Γ) (term : Term sig Γ s)
    (template : Problem sig (s :: Γ)) (rest : List (Problem sig Γ)) :
    ReplayState sig inputs (s :: Γ) :=
  ⟨state.images.subst Purification.embedding, Purification.state term template rest⟩

end ReplayState

end Worklist

end Substitution

end DirectCertification
