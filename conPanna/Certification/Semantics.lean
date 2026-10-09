import conPanna.Certification.Calculus

/-!
# Semantic justification of the surface calculus
Every rule in Calculus.lean is justified against the existing registered
Structural.Indexed.NativeEq relation. Quotients, flattening, induction and
native-evaluation lemmas stay here or in Core/Sharing/Enumeration.
Certificate proofs do NOT repeat these arguments: they apply surface rules,
then exact_system (or exact for one equation) ONCE.

These theorems prove validity of accepted evidence, not search success.
There is no assumption trusting Maude and no new user registration obligation.
-/

namespace DirectCertification

open Structural.Indexed

variable {Sorts : Type} {sig : Signature Sorts}

theorem native_refl (reg : Registration sig) {s} (x : reg.Carrier s) :
    NativeEq sig reg x x :=
  .refl _

theorem native_symm (reg : Registration sig) {s} {x y : reg.Carrier s}
    (h : NativeEq sig reg x y) : NativeEq sig reg y x :=
  .symm h

theorem native_trans (reg : Registration sig) {s} {x y z : reg.Carrier s}
    (h : NativeEq sig reg x y) (k : NativeEq sig reg y z) : NativeEq sig reg x z :=
  .trans h k

theorem native_add_congr (reg : Registration sig) {s} (op : sig.ACUOp s)
    {x x' y y' : reg.Carrier s}
    (hx : NativeEq sig reg x x') (hy : NativeEq sig reg y y') :
    NativeEq sig reg (reg.apply (sig.add op) (x, y, PUnit.unit))
      (reg.apply (sig.add op) (x', y', PUnit.unit)) := by
  unfold NativeEq
  rw [reg.quote_apply, reg.quote_apply]
  exact .congr (sig.add op) (.cons hx (.cons hy .nil))

theorem native_unit (reg : Registration sig) {s} (op : sig.ACUOp s)
    (x : reg.Carrier s) :
    NativeEq sig reg
      (reg.apply (sig.add op) (reg.apply (sig.zero op) PUnit.unit, x, PUnit.unit)) x := by
  simp only [NativeEq, reg.quote_apply, Args.quote]
  exact .unit op _

theorem native_comm (reg : Registration sig) {s} (op : sig.ACUOp s)
    (x y : reg.Carrier s) :
    NativeEq sig reg (reg.apply (sig.add op) (x, y, PUnit.unit))
      (reg.apply (sig.add op) (y, x, PUnit.unit)) := by
  unfold NativeEq
  rw [reg.quote_apply, reg.quote_apply]
  exact .comm op _ _

theorem native_assoc (reg : Registration sig) {s} (op : sig.ACUOp s)
    (x y z : reg.Carrier s) :
    NativeEq sig reg
      (reg.apply (sig.add op) (reg.apply (sig.add op) (x, y, PUnit.unit), z, PUnit.unit))
      (reg.apply (sig.add op) (x, reg.apply (sig.add op) (y, z, PUnit.unit), PUnit.unit)) := by
  simp only [NativeEq, reg.quote_apply, Args.quote]
  exact .assoc op _ _ _

def nativeRepeat (reg : Registration sig) {s} (op : sig.ACUOp s) :
    Nat → reg.Carrier s → reg.Carrier s
  | 0, _ => reg.apply (sig.zero op) PUnit.unit
  | k + 1, a => reg.apply (sig.add op) (a, nativeRepeat reg op k a, PUnit.unit)

theorem quote_nativeRepeat (reg : Registration sig) {s} (op : sig.ACUOp s)
    (k : Nat) (a : reg.Carrier s) :
    reg.quote s (nativeRepeat reg op k a) = bagCopies op k (reg.quote s a) := by
  induction k with
  | zero => simp only [nativeRepeat, bagCopies, zero, reg.quote_apply, Args.quote]
  | succ k ih => simp only [nativeRepeat, bagCopies, add, reg.quote_apply, Args.quote, ih]

def nativeBagSum (reg : Registration sig) {s n} (op : sig.ACUOp s)
    (coeff : FiniteSharing.Vector n) (values : Fin n → reg.Carrier s) : reg.Carrier s :=
  (FiniteSharing.bagSum op coeff (fun i => reg.quote s (values i))).eval reg.toAlgebra

def nativeSharingImages (reg : Registration sig) {s n} (op : sig.ACUOp s)
    (left right : FiniteSharing.Vector n) (generators : List (FiniteSharing.Vector n))
    (parameters : Fin generators.length → reg.Carrier s)
    (passthrough : Fin n → reg.Carrier s) : Fin n → reg.Carrier s := fun i =>
  (FiniteSharing.sharingImages op left right generators (fun j => reg.quote s (parameters j))
    (fun j => reg.quote s (passthrough j)) i).eval reg.toAlgebra

theorem finiteSharing_native (profile : Profile sig) (reg : Registration sig) {s n rows cols}
    (op : sig.ACUOp s) (left right : FiniteSharing.Vector n)
    (rowLabels : Fin rows → Fin n) (colLabels : Fin cols → Fin n)
    (rowCounts : ∀ i, FiniteSharing.labelCount rowLabels i = left i)
    (colCounts : ∀ i, FiniteSharing.labelCount colLabels i = right i)
    (disjoint : FiniteSharing.Disjoint left right) (values : Fin n → reg.Carrier s) :
    NativeEq sig reg (nativeBagSum reg op left values) (nativeBagSum reg op right values) ↔
      ∃ parameters : Fin (FiniteSharing.supportGenerators rowLabels colLabels).length → reg.Carrier s,
        ∃ passthrough : Fin n → reg.Carrier s,
          ∀ i, NativeEq sig reg (values i)
            (nativeSharingImages reg op left right (FiniteSharing.supportGenerators rowLabels colLabels)
              parameters passthrough i) := by
  have exactRule := FiniteSharing.bags_generated profile op left right rowLabels colLabels
    rowCounts colCounts disjoint (fun i => reg.quote s (values i))
  constructor
  · intro equation
    obtain ⟨parameters, passthrough, images⟩ := exactRule.mp
      (by simpa only [NativeEq, nativeBagSum, reg.quote_eval] using equation)
    refine ⟨fun j => (parameters j).eval reg.toAlgebra,
      fun j => (passthrough j).eval reg.toAlgebra, fun i => ?_⟩
    simpa only [NativeEq, nativeSharingImages, reg.quote_eval] using images i
  · rintro ⟨parameters, passthrough, images⟩
    apply (show NativeEq sig reg (nativeBagSum reg op left values) (nativeBagSum reg op right values) ↔
        Structural.Indexed.Eq sig
          (FiniteSharing.bagSum op left (fun i => reg.quote s (values i)))
          (FiniteSharing.bagSum op right (fun i => reg.quote s (values i))) from
      by simp only [NativeEq, nativeBagSum, reg.quote_eval]).mpr
    apply exactRule.mpr
    refine ⟨fun j => reg.quote s (parameters j), fun j => reg.quote s (passthrough j), fun i => ?_⟩
    simpa only [NativeEq, nativeSharingImages, reg.quote_eval] using images i

theorem multiplicity_native (profile : Profile sig) (reg : Registration sig) {s}
    (op : sig.ACUOp s) (k : Nat) (positive : 0 < k) (a b : reg.Carrier s) :
    NativeEq sig reg (nativeRepeat reg op k a) (nativeRepeat reg op k b) ↔
      NativeEq sig reg a b := by
  simp only [NativeEq, quote_nativeRepeat]
  exact multiplicity_cancel profile op k positive _ _

theorem quote_args_iff (reg : Registration sig) {ss}
    (a b : Args reg.Carrier ss) :
    Eqs sig (Args.quote sig reg.quote ss a) (Args.quote sig reg.quote ss b) ↔
      ArgsRel (fun s => NativeEq sig reg (s := s)) ss a b := by
  induction ss with
  | nil =>
      cases a; cases b
      exact ⟨fun _ => True.intro, fun _ => .nil⟩
  | cons s ss ih =>
      rcases a with ⟨x, rest⟩
      rcases b with ⟨y, tail⟩
      constructor
      · intro h
        cases h with
        | cons hx ht => exact ⟨hx, (ih rest tail).mp ht⟩
      · rintro ⟨hx, ht⟩
        exact .cons hx ((ih rest tail).mpr ht)

theorem decompose_native (profile : Profile sig) (reg : Registration sig) {ss s}
    (f : sig.Symbol ss s) (free : profile.view f = .atom f)
    (a b : Args reg.Carrier ss) :
    NativeEq sig reg (reg.apply f a) (reg.apply f b) ↔
      ArgsRel (fun s => NativeEq sig reg (s := s)) ss a b := by
  unfold NativeEq
  rw [reg.quote_apply, reg.quote_apply]
  exact (decompose profile f free _ _).trans (quote_args_iff reg a b)

theorem clash_native (profile : Profile sig) (reg : Registration sig) {ss tt s}
    (f : sig.Symbol ss s) (g : sig.Symbol tt s)
    (hf : profile.view f = .atom f) (hg : profile.view g = .atom g)
    (different : (⟨ss, f⟩ : Σ us, sig.Symbol us s) ≠ ⟨tt, g⟩)
    (a : Args reg.Carrier ss) (b : Args reg.Carrier tt) :
    ¬ NativeEq sig reg (reg.apply f a) (reg.apply g b) := by
  unfold NativeEq
  rw [reg.quote_apply, reg.quote_apply]
  exact clash profile f g hf hg different _ _

theorem rigid_native (profile : Profile sig) (reg : Registration sig) {s}
    (rigid : profile.rigid s = true) (a b : reg.Carrier s) :
    NativeEq sig reg a b ↔ a = b := by
  constructor
  · intro h
    have same := eq_of_rigid profile rigid h
    simpa only [reg.eval_quote] using congrArg (fun t => t.eval reg.toAlgebra) same
  · intro h
    cases h
    exact .refl _

theorem share_literal {α : Type} (x y : α) : x = y ↔ ∃ u : α, x = u ∧ y = u :=
  ⟨fun h => ⟨x, rfl, h.symm⟩, fun ⟨_u, hx, hy⟩ => hx.trans hy.symm⟩

theorem share_native (reg : Registration sig) {s} (x y : reg.Carrier s) :
    NativeEq sig reg x y ↔ ∃ u : reg.Carrier s,
      NativeEq sig reg x u ∧ NativeEq sig reg y u :=
  ⟨fun h => ⟨x, .refl _, .symm h⟩,
    fun ⟨_u, hx, hy⟩ => .trans hx (.symm hy)⟩

theorem split_native (profile : Profile sig) (reg : Registration sig) {s}
    (op : sig.ACUOp s) (x y a : reg.Carrier s)
    (ha : mass profile (reg.quote s a) = 1) :
    NativeEq sig reg (reg.apply (sig.add op) (x, y, PUnit.unit)) a ↔
      (NativeEq sig reg x (reg.apply (sig.zero op) PUnit.unit) ∧ NativeEq sig reg y a) ∨
      (NativeEq sig reg x a ∧ NativeEq sig reg y (reg.apply (sig.zero op) PUnit.unit)) := by
  unfold NativeEq
  rw [reg.quote_apply, reg.quote_apply]
  exact split_atom profile op _ _ _ ha

namespace NativeRules

theorem singletonCases (profile : Profile sig) (reg : Registration sig) {s ss}
    (op : sig.ACUOp s) (f : sig.Symbol ss s) (free : profile.view f = .atom f)
    (args : Args reg.Carrier ss) (x y : reg.Carrier s) :
    NativeEq sig reg (reg.apply (sig.add op) (x, y, PUnit.unit)) (reg.apply f args) ↔
      (NativeEq sig reg x (reg.apply (sig.zero op) PUnit.unit) ∧
        NativeEq sig reg y (reg.apply f args)) ∨
      (NativeEq sig reg x (reg.apply f args) ∧
        NativeEq sig reg y (reg.apply (sig.zero op) PUnit.unit)) := by
  apply split_native profile reg op x y (reg.apply f args)
  simp [reg.quote_apply, mass, Tree.eval, measure, free]

theorem rightUnit (reg : Registration sig) {s} (op : sig.ACUOp s)
    (x : reg.Carrier s) :
    NativeEq sig reg
      (reg.apply (sig.add op) (x, reg.apply (sig.zero op) PUnit.unit, PUnit.unit)) x :=
  native_trans reg (native_comm reg op _ _) (native_unit reg op x)

theorem unaryCongruence (reg : Registration sig) {s t}
    (f : sig.Symbol [s] t) {x y : reg.Carrier s} (same : NativeEq sig reg x y) :
    NativeEq sig reg (reg.apply f (x, PUnit.unit)) (reg.apply f (y, PUnit.unit)) := by
  unfold NativeEq
  rw [reg.quote_apply, reg.quote_apply]
  exact .congr f (.cons same .nil)

end NativeRules

theorem mutate_native (profile : Profile sig) (reg : Registration sig) {s}
    (op : sig.ACUOp s) (x y a rest : reg.Carrier s) :
    NativeEq sig reg (reg.apply (sig.add op) (x, y, PUnit.unit))
      (reg.apply (sig.add op) (a, rest, PUnit.unit)) ↔
      ∃ p q r t : reg.Carrier s,
        NativeEq sig reg x (reg.apply (sig.add op) (p, q, PUnit.unit)) ∧
        NativeEq sig reg y (reg.apply (sig.add op) (r, t, PUnit.unit)) ∧
        NativeEq sig reg a (reg.apply (sig.add op) (p, r, PUnit.unit)) ∧
        NativeEq sig reg rest (reg.apply (sig.add op) (q, t, PUnit.unit)) := by
  have rule := mutate profile op (reg.quote s x) (reg.quote s y)
    (reg.quote s a) (reg.quote s rest)
  constructor
  · intro input
    unfold NativeEq at input
    rw [reg.quote_apply, reg.quote_apply] at input
    obtain ⟨p, q, r, t, hx, hy, ha, hr⟩ := rule.mp input
    refine ⟨p.eval reg.toAlgebra, q.eval reg.toAlgebra,
      r.eval reg.toAlgebra, t.eval reg.toAlgebra, ?_, ?_, ?_, ?_⟩
    · simpa only [NativeEq, reg.quote_apply, Args.quote, reg.quote_eval] using hx
    · simpa only [NativeEq, reg.quote_apply, Args.quote, reg.quote_eval] using hy
    · simpa only [NativeEq, reg.quote_apply, Args.quote, reg.quote_eval] using ha
    · simpa only [NativeEq, reg.quote_apply, Args.quote, reg.quote_eval] using hr
  · rintro ⟨p, q, r, t, hx, hy, ha, hr⟩
    unfold NativeEq
    rw [reg.quote_apply, reg.quote_apply]
    apply rule.mpr
    refine ⟨reg.quote s p, reg.quote s q, reg.quote s r, reg.quote s t, ?_, ?_, ?_, ?_⟩
    · simpa only [NativeEq, reg.quote_apply, Args.quote] using hx
    · simpa only [NativeEq, reg.quote_apply, Args.quote] using hy
    · simpa only [NativeEq, reg.quote_apply, Args.quote] using ha
    · simpa only [NativeEq, reg.quote_apply, Args.quote] using hr

theorem cancel_native (profile : Profile sig) (reg : Registration sig) {s}
    (op : sig.ACUOp s) (a x y : reg.Carrier s) :
    NativeEq sig reg (reg.apply (sig.add op) (a, x, PUnit.unit))
      (reg.apply (sig.add op) (a, y, PUnit.unit)) ↔ NativeEq sig reg x y := by
  unfold NativeEq
  rw [reg.quote_apply, reg.quote_apply]
  exact cancel profile op _ _ _

theorem exchange_native (profile : Profile sig) (reg : Registration sig) {s}
    (op : sig.ACUOp s) (a b x y : reg.Carrier s)
    (ha : mass profile (reg.quote s a) = 1)
    (hb : mass profile (reg.quote s b) = 1) :
    NativeEq sig reg (reg.apply (sig.add op) (a, x, PUnit.unit))
      (reg.apply (sig.add op) (b, y, PUnit.unit)) ↔
      (NativeEq sig reg a b ∧ NativeEq sig reg x y) ∨
      ∃ n : reg.Carrier s,
        NativeEq sig reg x (reg.apply (sig.add op) (b, n, PUnit.unit)) ∧
        NativeEq sig reg y (reg.apply (sig.add op) (a, n, PUnit.unit)) := by
  have rule := exchange profile op (reg.quote s a) (reg.quote s b)
    (reg.quote s x) (reg.quote s y) ha hb
  constructor
  · intro input
    unfold NativeEq at input
    rw [reg.quote_apply, reg.quote_apply] at input
    rcases rule.mp input with matched | ⟨n, hx, hy⟩
    · exact .inl matched
    · refine .inr ⟨n.eval reg.toAlgebra, ?_, ?_⟩
      · simpa only [NativeEq, reg.quote_apply, Args.quote, reg.quote_eval] using hx
      · simpa only [NativeEq, reg.quote_apply, Args.quote, reg.quote_eval] using hy
  · intro output
    unfold NativeEq
    rw [reg.quote_apply, reg.quote_apply]
    rcases output with matched | ⟨n, hx, hy⟩
    · exact rule.mpr (.inl matched)
    · apply rule.mpr (.inr ⟨reg.quote s n, ?_, ?_⟩)
      · simpa only [NativeEq, reg.quote_apply, Args.quote] using hx
      · simpa only [NativeEq, reg.quote_apply, Args.quote] using hy

namespace Substitution

def Variable.eval {C : Sorts → Type} {Γ s} : Variable Γ s → Args C Γ → C s
  | .here, values => values.1
  | .there v, values => v.eval values.2

mutual
  def Term.eval (reg : Registration sig) {Γ s} (values : Args reg.Carrier Γ) :
      Term sig Γ s → reg.Carrier s
    | .var v => v.eval values
    | .app f args => reg.apply f (args.eval reg values)
  def Terms.eval (reg : Registration sig) {Γ ss} (values : Args reg.Carrier Γ) :
      Terms sig Γ ss → Args reg.Carrier ss
    | .nil => PUnit.unit
    | .cons a rest => (a.eval reg values, rest.eval reg values)
end

theorem variables_eval (reg : Registration sig) {Γ Δ}
    (rename : ∀ {s}, Variable Δ s → Variable Γ s)
    (old : Args reg.Carrier Δ) (fresh : Args reg.Carrier Γ)
    (same : ∀ {s} (v : Variable Δ s), (rename v).eval fresh = v.eval old) :
    (Terms.variables Γ Δ rename : Terms sig Γ Δ).eval reg fresh = old := by
  induction Δ with
  | nil => cases old; rfl
  | cons s ss ih =>
    exact Prod.ext (same .here) (ih (fun v => rename (.there v)) old.2
      (fun v => same (.there v)))

theorem Variable.eval_get (reg : Registration sig) {Γ Δ s} (v : Variable Γ s)
    (images : Terms sig Δ Γ) (values : Args reg.Carrier Δ) :
    v.eval (images.eval reg values) = (images.get v).eval reg values := by
  induction v with
  | here => cases images; rfl
  | there v ih => cases images with | cons a rest => exact ih rest

theorem Term.eval_subst (reg : Registration sig) {Γ Δ s} (term : Term sig Γ s)
    (images : Terms sig Δ Γ) (values : Args reg.Carrier Δ) :
    (term.subst images).eval reg values = term.eval reg (images.eval reg values) := by
  refine Term.rec
    (motive_1 := fun {s} a => (a.subst images).eval reg values = a.eval reg (images.eval reg values))
    (motive_2 := fun {ss} as => (as.subst images).eval reg values = as.eval reg (images.eval reg values))
    ?_ ?_ ?_ ?_ term
  · intro s v; exact (Variable.eval_get reg v images values).symm
  · intro ss s f args ih; exact congrArg (reg.apply f) ih
  · rfl
  · intro s ss a rest ha hr; simp only [Terms.subst, Terms.eval, ha, hr]

theorem Terms.eval_subst (reg : Registration sig) {Γ Δ ss} (terms : Terms sig Γ ss)
    (images : Terms sig Δ Γ) (values : Args reg.Carrier Δ) :
    (terms.subst images).eval reg values = terms.eval reg (images.eval reg values) := by
  refine Terms.rec
    (motive_1 := fun {_} _ => True)
    (motive_2 := fun {ss} as => (as.subst images).eval reg values = as.eval reg (images.eval reg values))
    ?_ ?_ ?_ ?_ terms
  · intros; trivial
  · intros; trivial
  · rfl
  · intro s ss a rest _ hr
    simp only [Terms.subst, Terms.eval, Term.eval_subst, hr]

theorem copies_eval (reg : Registration sig) {Γ s} (op : sig.ACUOp s)
    (k : Nat) (a : Term sig Γ s) (values : Args reg.Carrier Γ) :
    (copies op k a).eval reg values = nativeRepeat reg op k (a.eval reg values) := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [copies, add, Term.eval, Terms.eval, nativeRepeat, ih]

namespace Sharing

theorem weaken_eval {C : Sorts → Type} {Γ s t k} (v : Variable Γ t)
    (parameters : Fin k → C s) (values : Args C Γ) :
    (weaken s k v).eval (extend parameters values) = v.eval values := by
  induction k with
  | zero => rfl
  | succ k ih => exact ih (fun i => parameters i.succ)

theorem parameter_eval {C : Sorts → Type} {Γ s k} (i : Fin k)
    (parameters : Fin k → C s) (values : Args C Γ) :
    (parameter (Γ := Γ) s k i).eval (extend parameters values) = parameters i := by
  induction k with
  | zero => exact Fin.elim0 i
  | succ k ih => exact Fin.cases rfl (fun j => ih j (fun i => parameters i.succ)) i

theorem lift_eval (reg : Registration sig) {Γ s k} (parameters : Fin k → reg.Carrier s)
    (values : Args reg.Carrier Γ) :
    (lift (sig := sig) (Γ := Γ) (s := s) k).eval reg (extend parameters values) = values :=
  variables_eval reg _ values _ (fun v => weaken_eval v parameters values)

theorem sum_quote (reg : Registration sig) {Γ s n} (op : sig.ACUOp s)
    (coeff : FiniteSharing.Vector n) (terms : Fin n → Term sig Γ s) (values : Args reg.Carrier Γ) :
    reg.quote s ((sum op coeff terms).eval reg values) =
      FiniteSharing.bagSum op coeff (fun i => reg.quote s ((terms i).eval reg values)) := by
  induction n with
  | zero =>
    simp only [sum, zero, Term.eval, Terms.eval, reg.quote_apply, Args.quote, FiniteSharing.bagSum]
    rfl
  | succ n ih =>
    simp only [sum, add, Term.eval, Terms.eval, copies_eval, reg.quote_apply, Args.quote,
      quote_nativeRepeat, FiniteSharing.bagSum, ih]
    rfl

theorem sum_eval (reg : Registration sig) {Γ s n} (op : sig.ACUOp s)
    (coeff : FiniteSharing.Vector n) (terms : Fin n → Term sig Γ s) (values : Args reg.Carrier Γ) :
    (sum op coeff terms).eval reg values = nativeBagSum reg op coeff (fun i => (terms i).eval reg values) :=
  (reg.eval_quote _ _).symm.trans (congrArg (fun tree => tree.eval reg.toAlgebra)
    (sum_quote reg op coeff terms values))

theorem Slots.replace_congr (reg : Registration sig) {Γ s n Δ} (slots : Slots s Γ n)
    (replacement : Fin n → Term sig Δ s) (others : Terms sig Δ Γ)
    (values : Args reg.Carrier Γ) (fresh : Args reg.Carrier Δ)
    (preserved : ArgsRel (fun t => NativeEq sig reg (s := t)) Γ values (others.eval reg fresh))
    (selected : ∀ i, NativeEq sig reg ((slots.variable i).eval values) ((replacement i).eval reg fresh)) :
    ArgsRel (fun t => NativeEq sig reg (s := t)) Γ values
      ((slots.replace replacement others).eval reg fresh) := by
  induction slots with
  | nil => trivial
  | skip rest ih =>
    cases others with
    | cons a tail => exact ⟨preserved.1, ih replacement tail values.2 preserved.2
        (fun i => selected i)⟩
  | take rest ih =>
    cases others with
    | cons a tail => exact ⟨selected 0, ih (fun i => replacement i.succ) tail values.2 preserved.2
        (fun i => selected i.succ)⟩

theorem replacement_eval (reg : Registration sig) {Γ s n} (op : sig.ACUOp s) (slots : Slots s Γ n)
    (left right : FiniteSharing.Vector n) (generators : List (FiniteSharing.Vector n))
    (fresh : Args reg.Carrier (List.replicate generators.length s ++ Γ)) (i : Fin n) :
    ((replacement op slots left right generators) i).eval reg fresh =
      nativeSharingImages reg op left right generators
        (fun j => (parameter s generators.length j).eval fresh)
        (fun j => (weaken s generators.length (slots.variable j)).eval fresh) i := by
  unfold replacement nativeSharingImages FiniteSharing.sharingImages
  split
  · exact (reg.eval_quote _ _).symm
  · exact sum_eval reg op _ _ fresh

end Sharing

theorem apply_congr (reg : Registration sig) {ss s} (f : sig.Symbol ss s)
    {a b : Args reg.Carrier ss}
    (h : ArgsRel (fun s => NativeEq sig reg (s := s)) ss a b) :
    NativeEq sig reg (reg.apply f a) (reg.apply f b) := by
  unfold NativeEq
  rw [reg.quote_apply, reg.quote_apply]
  exact .congr f ((quote_args_iff reg a b).mpr h)

theorem Equality.sound (reg : Registration sig) {Γ s} {a b : Term sig Γ s}
    (proof : Equality sig Γ a b) (values : Args reg.Carrier Γ) :
    NativeEq sig reg (a.eval reg values) (b.eval reg values) := by
  refine Equality.rec
    (motive_1 := fun {s} a b _ => NativeEq sig reg (a.eval reg values) (b.eval reg values))
    (motive_2 := fun {ss} as bs _ =>
      ArgsRel (fun s => NativeEq sig reg (s := s)) ss (as.eval reg values) (bs.eval reg values))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ proof
  · intro s a; exact .refl _
  · intro s a b h ih; exact .symm ih
  · intro s a b c h k ih ik; exact .trans ih ik
  · intro ss s f as bs h ih; exact apply_congr reg f ih
  · intro s op a b; exact native_comm reg op _ _
  · intro s op a b c
    simp only [NativeEq, Term.eval, Terms.eval, add, reg.quote_apply, Args.quote]
    exact .assoc op _ _ _
  · intro s op a; exact native_unit reg op _
  · trivial
  · intro s ss a b as bs h k ih ik; exact ⟨ih, ik⟩

theorem Equalities.sound (reg : Registration sig) {Γ ss} {a b : Terms sig Γ ss}
    (proof : Equalities sig Γ a b) (values : Args reg.Carrier Γ) :
    ArgsRel (fun s => NativeEq sig reg (s := s)) ss (a.eval reg values) (b.eval reg values) :=
  match proof with
  | .nil => True.intro
  | .cons h rest => ⟨h.sound reg values, rest.sound reg values⟩

theorem args_trans (reg : Registration sig) {ss} {a b c : Args reg.Carrier ss}
    (h : ArgsRel (fun s => NativeEq sig reg (s := s)) ss a b)
    (k : ArgsRel (fun s => NativeEq sig reg (s := s)) ss b c) :
    ArgsRel (fun s => NativeEq sig reg (s := s)) ss a c := by
  induction ss with
  | nil => trivial
  | cons s ss ih => exact ⟨.trans h.1 k.1, ih h.2 k.2⟩

theorem args_refl (reg : Registration sig) {Γ} (values : Args reg.Carrier Γ) :
    ArgsRel (fun s => NativeEq sig reg (s := s)) Γ values values := by
  induction Γ with
  | nil => trivial
  | cons s ss ih => exact ⟨.refl _, ih values.2⟩

def Answer.Holds (reg : Registration sig) {inputs} (answer : Answer sig inputs)
    (values : Args reg.Carrier inputs) : Prop :=
  ∃ fresh : Args reg.Carrier answer.parameters,
    ArgsRel (fun s => NativeEq sig reg (s := s)) inputs values (answer.images.eval reg fresh)

def Solutions (reg : Registration sig) {inputs} (proposed : List (Answer sig inputs))
    (values : Args reg.Carrier inputs) : Prop :=
  ∃ answer, answer ∈ proposed ∧ answer.Holds reg values

theorem Factor.sound (reg : Registration sig) {inputs} {source target : Answer sig inputs}
    (factor : Factor source target) {values} (input : source.Holds reg values) :
    target.Holds reg values := by
  rcases input with ⟨fresh, images⟩
  refine ⟨factor.parameters.eval reg fresh, ?_⟩
  have matched := factor.images.sound reg fresh
  rw [Terms.eval_subst] at matched
  exact args_trans reg images matched

theorem Coverage.sound (reg : Registration sig) {inputs}
    {proposed reference : List (Answer sig inputs)} (proof : Coverage proposed reference)
    {values} : Solutions reg reference values → Solutions reg proposed values := by
  induction proof with
  | nil => rintro ⟨_, impossible, _⟩; cases impossible
  | @cons source rest index factor tail ih =>
      rintro ⟨answer, member, input⟩
      rcases List.mem_cons.mp member with same | member
      · cases same
        exact ⟨_, List.get_mem _ _, factor.sound reg input⟩
      · exact ih ⟨answer, member, input⟩

def Problem.Holds (reg : Registration sig) {inputs} (problem : Problem sig inputs)
    (values : Args reg.Carrier inputs) : Prop :=
  NativeEq sig reg (problem.left.eval reg values) (problem.right.eval reg values)

theorem Variable.eval_congr (reg : Registration sig) {Γ s} (v : Variable Γ s)
    {a b : Args reg.Carrier Γ}
    (h : ArgsRel (fun s => NativeEq sig reg (s := s)) Γ a b) :
    NativeEq sig reg (v.eval a) (v.eval b) := by
  induction v with
  | here => exact h.1
  | there v ih => exact ih h.2

theorem Term.eval_congr (reg : Registration sig) {Γ s} (term : Term sig Γ s)
    {a b : Args reg.Carrier Γ}
    (h : ArgsRel (fun s => NativeEq sig reg (s := s)) Γ a b) :
    NativeEq sig reg (term.eval reg a) (term.eval reg b) := by
  refine Term.rec
    (motive_1 := fun {s} term => NativeEq sig reg (term.eval reg a) (term.eval reg b))
    (motive_2 := fun {ss} terms =>
      ArgsRel (fun s => NativeEq sig reg (s := s)) ss (terms.eval reg a) (terms.eval reg b))
    ?_ ?_ ?_ ?_ term
  · intro s v; exact v.eval_congr reg h
  · intro ss s f args ih; exact apply_congr reg f ih
  · trivial
  · intro s ss first rest ih ir; exact ⟨ih, ir⟩

theorem Terms.eval_congr (reg : Registration sig) {Γ ss} (terms : Terms sig Γ ss)
    {a b : Args reg.Carrier Γ}
    (h : ArgsRel (fun s => NativeEq sig reg (s := s)) Γ a b) :
    ArgsRel (fun s => NativeEq sig reg (s := s)) ss (terms.eval reg a) (terms.eval reg b) := by
  induction ss with
  | nil => cases terms; trivial
  | cons s ss ih =>
    cases terms with
    | cons a rest => exact ⟨a.eval_congr reg h, ih rest⟩

namespace Binding

theorem Removal.weaken_eval {C : Sorts → Type} {s Γ Δ t} (remove : Removal s Γ Δ)
    (v : Variable Δ t) (values : Args C Γ) :
    (remove.weaken v).eval values = v.eval (remove.restrict values) := by
  induction remove with
  | here => rfl
  | there rest ih =>
    cases v with
    | here => rfl
    | there v => exact ih v values.2

theorem tabulate_congr (reg : Registration sig) {Γ Δ}
    (images : ∀ {s}, Variable Γ s → Term sig Δ s)
    (old : Args reg.Carrier Γ) (fresh : Args reg.Carrier Δ)
    (same : ∀ {s} (v : Variable Γ s), NativeEq sig reg (v.eval old) ((images v).eval reg fresh)) :
    ArgsRel (fun s => NativeEq sig reg (s := s)) Γ old ((tabulate Δ Γ images).eval reg fresh) := by
  induction Γ with
  | nil => trivial
  | cons s Γ ih => exact ⟨same .here, ih (fun v => images (.there v)) old.2
      (fun v => same (.there v))⟩

theorem Removal.embedding_eval (reg : Registration sig) {s Γ Δ} (remove : Removal s Γ Δ)
    (values : Args reg.Carrier Γ) : remove.embedding.eval reg values = remove.restrict values :=
  variables_eval reg _ _ _ (fun v => remove.weaken_eval v values)

theorem Removal.embedding_substitution_eval (reg : Registration sig) {s Γ Δ}
    (remove : Removal s Γ Δ) (term : Term sig Δ s) (fresh : Args reg.Carrier Δ) :
    remove.embedding.eval reg (remove.substitution term |>.eval reg fresh) = fresh := by
  apply variables_eval reg
  intro t v
  rw [Variable.eval_get, Removal.substitution, tabulate_get, Removal.replace_weaken]
  rfl

theorem Removal.replace_congr (reg : Registration sig) {s Γ Δ Ω}
    (remove : Removal s Γ Δ) (term : Term sig Ω s)
    (others : ∀ {t}, Variable Δ t → Term sig Ω t)
    (old : Args reg.Carrier Γ) (fresh : Args reg.Carrier Ω)
    (chosen : NativeEq sig reg (remove.variable.eval old) (term.eval reg fresh))
    (same : ∀ {t} (v : Variable Δ t), NativeEq sig reg ((remove.weaken v).eval old)
      ((others v).eval reg fresh)) : ∀ {t} (v : Variable Γ t),
      NativeEq sig reg (v.eval old) ((remove.replace term others v).eval reg fresh) := by
  induction remove with
  | here =>
    intro t v
    cases v with
    | here => exact chosen
    | there v => exact same v
  | there rest ih =>
    intro t v
    cases v with
    | here => exact same .here
    | there v => exact ih (fun v => others (.there v)) old.2 chosen (fun v => same (.there v)) v

theorem complete (reg : Registration sig) {s Γ Δ} (remove : Removal s Γ Δ)
    (term : Term sig Δ s) (values : Args reg.Carrier Γ)
    (input : NativeEq sig reg (remove.variable.eval values)
      ((term.subst remove.embedding).eval reg values)) :
    ArgsRel (fun s => NativeEq sig reg (s := s)) Γ values
      ((remove.substitution term).eval reg (remove.restrict values)) := by
  apply tabulate_congr reg
  apply remove.replace_congr reg
  · simpa only [Term.eval_subst, Removal.embedding_eval] using input
  · intro t v
    rw [remove.weaken_eval]
    exact .refl _

theorem sound (reg : Registration sig) {s Γ Δ} (remove : Removal s Γ Δ)
    (term : Term sig Δ s) (fresh : Args reg.Carrier Δ) :
    NativeEq sig reg (remove.variable.eval ((remove.substitution term).eval reg fresh))
      ((term.subst remove.embedding).eval reg ((remove.substitution term).eval reg fresh)) := by
  rw [Variable.eval_get, Removal.substitution, tabulate_get, Removal.replace_variable,
    Term.eval_subst, ← Removal.substitution, Removal.embedding_substitution_eval]
  exact .refl _

end Binding

namespace FreeOccurs

def argsDepth (profile : Profile sig) (reg : Registration sig) {ss}
    (values : Args reg.Carrier ss) : Nat :=
  FreeDepth.maxArgs ((Args.quote sig reg.quote ss values).eval (FreeDepth.algebra profile))

theorem field_le (profile : Profile sig) (reg : Registration sig) {ss s}
    (field : Variable ss s) (values : Args reg.Carrier ss) :
    FreeDepth.depth profile (reg.quote s (field.eval values)) ≤ argsDepth profile reg values := by
  induction field with
  | here => exact Nat.le_max_left _ _
  | there field ih => exact Nat.le_trans (ih values.2) (Nat.le_max_right _ _)

theorem field_lt (profile : Profile sig) (reg : Registration sig) {ss s t}
    (f : sig.Symbol ss s) (free : profile.view f = .atom f)
    (field : Variable ss t) (values : Args reg.Carrier ss) :
    FreeDepth.depth profile (reg.quote t (field.eval values)) <
      FreeDepth.depth profile (reg.quote s (reg.apply f values)) := by
  rw [reg.quote_apply]
  have head : FreeDepth.depth profile (.app f (Args.quote sig reg.quote ss values)) =
      argsDepth profile reg values + 1 := by
    simp only [FreeDepth.depth, Tree.eval, FreeDepth.algebra, free, argsDepth]
  rw [head]
  exact Nat.lt_succ_of_le (field_le profile reg field values)

theorem Path.le (profile : Profile sig) (reg : Registration sig) {Γ s t}
    (v : Variable Γ s) (term : Term sig Γ t) (path : Path profile v term)
    (values : Args reg.Carrier Γ) :
    FreeDepth.depth profile (reg.quote s (v.eval values)) ≤
      FreeDepth.depth profile (reg.quote t (term.eval reg values)) := by
  induction path with
  | root => exact Nat.le_refl _
  | field f free args index child ih =>
    apply Nat.le_of_lt (Nat.lt_of_le_of_lt ih _)
    simpa only [Variable.eval_get, Term.eval] using field_lt profile reg f free index (args.eval reg values)

theorem Proper.sound (profile : Profile sig) (reg : Registration sig) {Γ s}
    (v : Variable Γ s) (term : Term sig Γ s) (path : Proper profile v term)
    (values : Args reg.Carrier Γ) : ¬ NativeEq sig reg (v.eval values) (term.eval reg values) := by
  intro same
  cases path with
  | field f free args index child =>
    have lower := child.le profile reg v (args.get index) values
    have upper := field_lt profile reg f free index (args.eval reg values)
    rw [Variable.eval_get] at upper
    have different := Nat.ne_of_lt (Nat.lt_of_le_of_lt lower upper)
    exact different (FreeDepth.congr profile same)

end FreeOccurs

namespace Sharing

theorem image_eval (reg : Registration sig) {Γ s n} (op : sig.ACUOp s) (slots : Slots s Γ n)
    (left right : FiniteSharing.Vector n) (generators : List (FiniteSharing.Vector n))
    (fresh : Args reg.Carrier (List.replicate generators.length s ++ Γ)) (i : Fin n) :
    (slots.variable i).eval ((substitution op slots left right generators).eval reg fresh) =
      nativeSharingImages reg op left right generators
        (fun j => (parameter s generators.length j).eval fresh)
        (fun j => (weaken s generators.length (slots.variable j)).eval fresh) i := by
  rw [Variable.eval_get]
  simp only [substitution, Slots.get_replace, replacement_eval]

theorem complete (profile : Profile sig) (reg : Registration sig) {Γ s n rows cols}
    (op : sig.ACUOp s) (slots : Slots s Γ n) (left right : FiniteSharing.Vector n)
    (rowLabels : Fin rows → Fin n) (colLabels : Fin cols → Fin n)
    (rowCounts : ∀ i, FiniteSharing.labelCount rowLabels i = left i)
    (colCounts : ∀ i, FiniteSharing.labelCount colLabels i = right i)
    (disjoint : FiniteSharing.Disjoint left right) (values : Args reg.Carrier Γ)
    (input : (problem op slots left right).Holds reg values) :
    (answer op slots left right (FiniteSharing.supportGenerators rowLabels colLabels)).Holds reg values := by
  have equation : NativeEq sig reg
      (nativeBagSum reg op left (fun i => (slots.variable i).eval values))
      (nativeBagSum reg op right (fun i => (slots.variable i).eval values)) := by
    simpa only [problem, Problem.Holds, sum_eval, Term.eval] using input
  obtain ⟨parameters, passthrough, images⟩ := (finiteSharing_native profile reg op left right
    rowLabels colLabels rowCounts colCounts disjoint _).mp equation
  refine ⟨extend parameters values, ?_⟩
  apply slots.replace_congr reg
  · rw [lift_eval]
    exact args_refl reg values
  · intro i
    rw [replacement_eval]
    simp only [parameter_eval, weaken_eval]
    by_cases inactive : left i = 0 ∧ right i = 0
    · simp only [nativeSharingImages, FiniteSharing.sharingImages, if_pos inactive, reg.eval_quote]
      exact .refl _
    · simpa only [nativeSharingImages, FiniteSharing.sharingImages, if_neg inactive] using images i

theorem sound (profile : Profile sig) (reg : Registration sig) {Γ s n rows cols}
    (op : sig.ACUOp s) (slots : Slots s Γ n) (left right : FiniteSharing.Vector n)
    (rowLabels : Fin rows → Fin n) (colLabels : Fin cols → Fin n)
    (rowCounts : ∀ i, FiniteSharing.labelCount rowLabels i = left i)
    (colCounts : ∀ i, FiniteSharing.labelCount colLabels i = right i)
    (disjoint : FiniteSharing.Disjoint left right)
    (fresh : Args reg.Carrier (List.replicate (FiniteSharing.supportGenerators rowLabels colLabels).length s ++ Γ)) :
    (problem op slots left right).Holds reg
      ((substitution op slots left right (FiniteSharing.supportGenerators rowLabels colLabels)).eval reg fresh) := by
  simp only [problem, Problem.Holds, sum_eval, Term.eval, image_eval]
  apply (finiteSharing_native profile reg op left right rowLabels colLabels rowCounts colCounts disjoint _).mpr
  exact ⟨_, _, fun _ => .refl _⟩

end Sharing

theorem Soundness.sound (reg : Registration sig) {inputs} {problem : Problem sig inputs}
    {proposed : List (Answer sig inputs)} (proof : Soundness problem proposed) :
    ∀ values, Solutions reg proposed values → problem.Holds reg values := by
  induction proof with
  | nil => rintro _ ⟨_, impossible, _⟩; cases impossible
  | @cons problem answer rest equality tail ih =>
      rintro values ⟨candidate, member, fresh, images⟩
      rcases List.mem_cons.mp member with same | member
      · cases same
        have equation := equality.sound reg fresh
        rw [Term.eval_subst, Term.eval_subst] at equation
        exact .trans (problem.left.eval_congr reg images)
          (.trans equation (.symm (problem.right.eval_congr reg images)))
      · exact ih values ⟨candidate, member, fresh, images⟩
  | sharing profile op slots left right rows cols rowCounts colCounts disjoint tail ih =>
      rintro values ⟨candidate, member, fresh, images⟩
      rcases List.mem_cons.mp member with same | member
      · cases same
        have equation := Sharing.sound profile reg op slots left right rows cols rowCounts colCounts disjoint fresh
        exact .trans ((Sharing.problem op slots left right).left.eval_congr reg images)
          (.trans equation (.symm ((Sharing.problem op slots left right).right.eval_congr reg images)))
      · exact ih values ⟨candidate, member, fresh, images⟩
  | binding remove term tail ih =>
      rintro values ⟨candidate, member, fresh, images⟩
      rcases List.mem_cons.mp member with same | member
      · cases same
        exact .trans ((Binding.problem remove term).left.eval_congr reg images)
          (.trans (Binding.sound reg remove term fresh)
            (.symm ((Binding.problem remove term).right.eval_congr reg images)))
      · exact ih values ⟨candidate, member, fresh, images⟩

theorem exact_of_coverage (reg : Registration sig) {inputs} (problem : Problem sig inputs)
    (reference proposed : List (Answer sig inputs))
    (complete : ∀ values, problem.Holds reg values → Solutions reg reference values)
    (sound : Soundness problem proposed)
    (cover : Coverage proposed reference) :
    ∀ values, problem.Holds reg values ↔ Solutions reg proposed values :=
  fun values => ⟨fun h => cover.sound reg (complete values h), sound.sound reg values⟩

namespace Worklist

def Holds (reg : Registration sig) {Γ} (eqs : List (Problem sig Γ))
    (values : Args reg.Carrier Γ) : Prop := ∀ p ∈ eqs, p.Holds reg values

theorem Derives.sound (reg : Registration sig) {profile : Profile sig} {Γ eqs s a b}
    (proof : Derives profile (Γ := Γ) eqs (s := s) a b) (values : Args reg.Carrier Γ)
    (input : Holds reg eqs values) : NativeEq sig reg (a.eval reg values) (b.eval reg values) := by
  refine Derives.rec
    (motive_1 := fun {s} a b _ => NativeEq sig reg (a.eval reg values) (b.eval reg values))
    (motive_2 := fun {ss} as bs _ =>
      ArgsRel (fun s => NativeEq sig reg (s := s)) ss (as.eval reg values) (bs.eval reg values))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ proof
  · intro s a b h; exact h.sound reg values
  · intro index; exact input _ (List.get_mem _ _)
  · intro s a b h ih; exact .symm ih
  · intro s a b c h k ih ik; exact .trans ih ik
  · intro ss s f as bs h ih; exact apply_congr reg f ih
  · intro s op common a b h ih
    exact (cancel_native profile reg op _ _ _).mp ih
  · intro s op k positive a b h ih
    apply (multiplicity_native profile reg op k positive _ _).mp
    simpa only [copies_eval] using ih
  · intro ss s t f free a b field h ih
    have args := (decompose_native profile reg f free _ _).mp ih
    have selected := Variable.eval_congr reg field args
    simpa only [Variable.eval_get] using selected
  · trivial
  · intro s ss a b as bs h k ih ik; exact ⟨ih, ik⟩

theorem DerivesArgs.sound (reg : Registration sig) {profile : Profile sig} {Γ eqs ss a b}
    (proof : DerivesArgs profile (Γ := Γ) eqs (ss := ss) a b) (values : Args reg.Carrier Γ)
    (input : Holds reg eqs values) :
    ArgsRel (fun s => NativeEq sig reg (s := s)) ss (a.eval reg values) (b.eval reg values) :=
  match proof with
  | .nil => True.intro
  | .cons h rest => ⟨h.sound reg values input, rest.sound reg values input⟩

theorem lift4_eval (reg : Registration sig) {Γ s} (p q r t : reg.Carrier s)
    (values : Args reg.Carrier Γ) :
    (lift4 (sig := sig) (Γ := Γ) (s := s)).eval (Γ := s :: s :: s :: s :: Γ)
      reg (p, q, r, t, values) = values :=
  variables_eval reg _ values _ (fun _ => rfl)

theorem identity_eval (reg : Registration sig) {Γ} (values : Args reg.Carrier Γ) :
    (Terms.identity Γ : Terms sig Γ Γ).eval reg values = values :=
  variables_eval reg _ values values (fun _ => rfl)

theorem substituteEquations_holds (reg : Registration sig) {Γ Δ}
    (images : Terms sig Δ Γ) (eqs : List (Problem sig Γ))
    (old : Args reg.Carrier Γ) (fresh : Args reg.Carrier Δ)
    (same : ArgsRel (fun s => NativeEq sig reg (s := s)) Γ old (images.eval reg fresh))
    (input : Holds reg eqs old) : Holds reg (substituteEquations images eqs) fresh := by
  intro e member
  obtain ⟨original, inOriginal, rfl⟩ := List.mem_map.mp member
  simp only [Problem.Holds, equation, Term.eval_subst]
  exact .trans (.symm (original.left.eval_congr reg same))
    (.trans (input original inOriginal) (original.right.eval_congr reg same))

namespace Purification

theorem embedding_eval (reg : Registration sig) {Γ s} (fresh : Args reg.Carrier (s :: Γ)) :
    (embedding (sig := sig) (Γ := Γ) (s := s)).eval reg fresh = fresh.2 :=
  Binding.Removal.embedding_eval reg .here fresh

theorem assignment_eval (reg : Registration sig) {Γ s} (term : Term sig Γ s)
    (values : Args reg.Carrier Γ) :
    (assignment term).eval reg values = (term.eval reg values, values) := by
  apply Prod.ext
  · rfl
  · simpa only [assignment, Binding.Removal.embedding_eval, Binding.Removal.restrict] using
      Binding.Removal.embedding_substitution_eval reg .here term values

theorem complete (reg : Registration sig) {Γ s} (term : Term sig Γ s)
    (template : Problem sig (s :: Γ)) (rest : List (Problem sig Γ))
    (values : Args reg.Carrier Γ) (selected : (source term template).Holds reg values)
    (input : Holds reg rest values) :
    Holds reg (state term template rest) (term.eval reg values, values) := by
  intro e member
  rcases List.mem_cons.mp member with rfl | member
  · simp only [Problem.Holds, definition, equation, Term.eval, Variable.eval,
      Term.eval_subst, embedding_eval]
    exact .refl _
  rcases List.mem_cons.mp member with rfl | member
  · simpa only [source, equation, Problem.Holds, Term.eval_subst, assignment_eval] using selected
  · obtain ⟨original, inOriginal, rfl⟩ := List.mem_map.mp member
    simpa only [Problem.Holds, equation, Term.eval_subst, embedding_eval] using input original inOriginal

theorem sound (reg : Registration sig) {Γ s} (term : Term sig Γ s)
    (template : Problem sig (s :: Γ)) (fresh : Args reg.Carrier (s :: Γ))
    (named : (definition term).Holds reg fresh) (selected : template.Holds reg fresh) :
    (source term template).Holds reg fresh.2 := by
  have same : ArgsRel (fun s => NativeEq sig reg (s := s)) (s :: Γ) fresh
      ((assignment term).eval reg fresh.2) := by
    rw [assignment_eval]
    exact ⟨by simpa only [definition, equation, Problem.Holds, Term.eval, Variable.eval,
      Term.eval_subst, embedding_eval] using named, args_refl reg fresh.2⟩
  simp only [source, equation, Problem.Holds, Term.eval_subst]
  exact .trans (.symm (template.left.eval_congr reg same))
    (.trans selected (template.right.eval_congr reg same))

theorem exact (reg : Registration sig) {Γ s} (term : Term sig Γ s)
    (template : Problem sig (s :: Γ)) (rest : List (Problem sig Γ))
    (values : Args reg.Carrier Γ) :
    Holds reg (source term template :: rest) values ↔
      ∃ fresh : Args reg.Carrier (s :: Γ),
        ArgsRel (fun s => NativeEq sig reg (s := s)) Γ values fresh.2 ∧
          Holds reg (state term template rest) fresh := by
  constructor
  · intro input
    exact ⟨(term.eval reg values, values), args_refl reg values,
      complete reg term template rest values (input _ (List.mem_cons_self))
        (fun e member => input e (List.mem_cons_of_mem _ member))⟩
  · rintro ⟨fresh, same, input⟩ e member
    have projected : Holds reg (source term template :: rest) fresh.2 := by
      intro p member
      rcases List.mem_cons.mp member with rfl | member
      · exact sound reg term template fresh (input _ List.mem_cons_self)
          (input _ (List.mem_cons_of_mem _ List.mem_cons_self))
      · have h := input _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_map.mpr ⟨p, member, rfl⟩)))
        simpa only [Problem.Holds, equation, Term.eval_subst, embedding_eval] using h
    exact .trans (e.left.eval_congr reg same)
      (.trans (projected e member) (.symm (e.right.eval_congr reg same)))

end Purification

theorem zeroRequirements_holds (reg : Registration sig) {Γ s n} (op : sig.ACUOp s)
    (coeff : FiniteSharing.Vector n) (terms : Fin n → Term sig Γ s)
    (values : Args reg.Carrier Γ)
    (empty : ∀ i, coeff i ≠ 0 → NativeEq sig reg ((terms i).eval reg values)
      ((zero op).eval reg values)) : Holds reg (zeroRequirements op coeff terms) values := by
  intro e member
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp member
  by_cases h : coeff i = 0
  · simp only [Problem.Holds, equation, if_pos h]; exact .refl _
  · simpa only [Problem.Holds, equation, if_neg h] using empty i h

theorem atomRequirements_holds (reg : Registration sig) {Γ s n} (op : sig.ACUOp s)
    (coeff : FiniteSharing.Vector n) (terms : Fin n → Term sig Γ s)
    (target : Term sig Γ s) (chosen : Fin n) (values : Args reg.Carrier Γ)
    (same : NativeEq sig reg ((terms chosen).eval reg values) (target.eval reg values))
    (empty : ∀ i, i ≠ chosen → coeff i ≠ 0 → NativeEq sig reg ((terms i).eval reg values)
      ((zero op).eval reg values)) : Holds reg (atomRequirements op coeff terms target chosen) values := by
  intro e member
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp member
  by_cases h : coeff i = 0
  · simp only [Problem.Holds, equation, if_pos h]; exact .refl _
  · by_cases selected : i = chosen
    · subst i; simpa only [Problem.Holds, equation, if_neg h, if_true] using same
    · simpa only [Problem.Holds, equation, if_neg h, if_neg selected] using empty i selected h

theorem Complete.sound (reg : Registration sig) {profile : Profile sig} {inputs proposed Γ images eqs}
    (proof : Complete profile (inputs := inputs) proposed (Γ := Γ) images eqs) :
    ∀ values, Holds reg eqs values → Solutions reg proposed (images.eval reg values) := by
  induction proof with
  | cover index bindings derived =>
    intro values input
    refine ⟨_, List.get_mem _ _, bindings.eval reg values, ?_⟩
    simpa only [Terms.eval_subst] using derived.sound reg values input
  | @bind Γ Δ images eqs s remove term selected child ih =>
    intro values input
    have same := Binding.complete reg remove term values (selected.sound reg values input)
    obtain ⟨answer, member, parameters, covered⟩ := ih (remove.restrict values)
      (substituteEquations_holds reg (remove.substitution term) _ values _ same input)
    refine ⟨answer, member, parameters, ?_⟩
    rw [Terms.eval_subst] at covered
    exact args_trans reg (images.eval_congr reg same) covered
  | occurs v rhs path selected =>
    intro values input
    exact False.elim (path.sound profile reg v rhs values (selected.sound reg values input))
  | @purify Γ images s term template before after child ih =>
    intro values input
    have selected := input _ (List.mem_append.mpr (.inr List.mem_cons_self))
    have residual : Holds reg (before ++ after) values := by
      intro e member
      rcases List.mem_append.mp member with member | member
      · exact input e (List.mem_append.mpr (.inl member))
      · exact input e (List.mem_append.mpr (.inr (List.mem_cons_of_mem _ member)))
    have covered := ih (term.eval reg values, values)
      (Purification.complete reg term template _ values selected residual)
    simpa only [Terms.eval_subst, Purification.embedding_eval] using covered
  | @atom Γ images eqs s n ss op coeff terms f free args selected children ih =>
    intro values input
    have count : mass profile (reg.quote s ((Term.app f args).eval reg values)) = 1 := by
      simp [Term.eval, reg.quote_apply, mass, Tree.eval, measure, free]
    have selected := selected.sound reg values input
    rw [NativeEq, Sharing.sum_quote] at selected
    obtain ⟨j, degree, same, empty⟩ := (AtomProcessing.sum_atom profile op coeff
      (fun i => reg.quote s ((terms i).eval reg values)) _ count).mp selected
    have constraints := atomRequirements_holds reg op coeff terms (.app f args) j values
      same (fun i different positive => by
        simpa only [NativeEq, Substitution.zero, Structural.Indexed.zero,
          Term.eval, Terms.eval, reg.quote_apply, Args.quote]
          using empty i different positive)
    apply ih j degree values
    intro e member
    rcases List.mem_append.mp member with member | member
    · exact constraints e member
    · exact input e member
  | @zero Γ images eqs s n op coeff terms selected child ih =>
    intro values input
    have selected := selected.sound reg values input
    simp only [NativeEq, Sharing.sum_quote, Substitution.zero, Term.eval, Terms.eval,
      reg.quote_apply, Args.quote] at selected
    have empty := (AtomProcessing.sum_zero profile op coeff
      (fun i => reg.quote s ((terms i).eval reg values))).mp selected
    have constraints := zeroRequirements_holds reg op coeff terms values (fun i positive => by
      simpa only [NativeEq, Substitution.zero, Structural.Indexed.zero,
        Term.eval, Terms.eval, reg.quote_apply, Args.quote] using empty i positive)
    apply ih values
    intro e member
    rcases List.mem_append.mp member with member | member
    · exact constraints e member
    · exact input e member
  | nonempty op f free args selected =>
    intro values input
    have count := mass_congr profile (selected.sound reg values input)
    simp [Substitution.zero, Term.eval, Terms.eval, reg.quote_apply, mass, Tree.eval,
      measure, free, profile.view_zero] at count
  | @sharing Γ images eqs s n nr nc op slots left right rows cols rowCounts colCounts disjoint selected child ih =>
    intro values input
    obtain ⟨fresh, imagesSame⟩ := Sharing.complete profile reg op slots left right rows cols
      rowCounts colCounts disjoint values (selected.sound reg values input)
    have residual := substituteEquations_holds reg (Sharing.substitution op slots left right
      (FiniteSharing.supportGenerators rows cols)) eqs values fresh imagesSame input
    obtain ⟨answer, member, parameters, covered⟩ := ih fresh residual
    refine ⟨answer, member, parameters, ?_⟩
    rw [Terms.eval_subst] at covered
    exact args_trans reg (images.eval_congr reg imagesSame) covered
  | @mutate Γ images eqs s op a b c d selected child ih =>
    intro values input
    have selected := selected.sound reg values input
    rcases (mutate_native profile reg op (a.eval reg values) (b.eval reg values)
      (c.eval reg values) (d.eval reg values)).mp selected with ⟨p, q, r, t, ha, hb, hc, hd⟩
    have lifted : Holds reg (liftEquations (s := s) eqs) (p, q, r, t, values) := by
      intro e member
      simp only [liftEquations] at member
      rcases List.mem_map.mp member with ⟨original, horiginal, heq⟩
      rw [← heq]
      simpa only [Problem.Holds, equation, Term.eval_subst, lift4_eval] using input original horiginal
    have result := ih (p, q, r, t, values) (by
      intro e member
      simp only [mutated, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with (rfl | rfl | rfl | rfl) | member
      · simpa only [Problem.Holds, equation, Term.eval_subst, lift4_eval, add,
          Term.eval, Terms.eval, Variable.eval] using ha
      · simpa only [Problem.Holds, equation, Term.eval_subst, lift4_eval, add,
          Term.eval, Terms.eval, Variable.eval] using hb
      · simpa only [Problem.Holds, equation, Term.eval_subst, lift4_eval, add,
          Term.eval, Terms.eval, Variable.eval] using hc
      · simpa only [Problem.Holds, equation, Term.eval_subst, lift4_eval, add,
          Term.eval, Terms.eval, Variable.eval] using hd
      · exact lifted e member)
    simpa only [Terms.eval_subst, lift4_eval] using result
  | @split Γ images eqs ss s op x y f free args selected left right il ir =>
    intro values input
    have atom : mass profile (reg.quote s ((Term.app f args).eval reg values)) = 1 := by
      simp [Term.eval, reg.quote_apply, mass, Tree.eval, measure, free]
    rcases (split_native profile reg op (x.eval reg values) (y.eval reg values)
      ((Term.app f args).eval reg values) atom).mp (selected.sound reg values input) with
      ⟨hx, hy⟩ | ⟨hx, hy⟩
    · apply il values
      intro e member
      rcases List.mem_cons.mp member with rfl | member
      · exact hx
      rcases List.mem_cons.mp member with rfl | member
      · exact hy
      exact input e member
    · apply ir values
      intro e member
      rcases List.mem_cons.mp member with rfl | member
      · exact hx
      rcases List.mem_cons.mp member with rfl | member
      · exact hy
      exact input e member
  | clash f g hf hg different a b selected =>
    intro values input
    exact False.elim ((clash_native profile reg f g hf hg different _ _)
      (selected.sound reg values input))

theorem SystemSoundness.sound (reg : Registration sig) {inputs proposed eqs}
    (proof : SystemSoundness (sig := sig) (inputs := inputs) proposed eqs)
    (values : Args reg.Carrier inputs) (solution : Solutions reg proposed values) :
    Holds reg eqs values := by
  induction proof with
  | nil => intro e member; cases member
  | @cons e rest head tail ih =>
    intro p member
    rcases List.mem_cons.mp member with same | member
    · cases same; exact head.sound reg values solution
    · exact ih p member

theorem exact_system (reg : Registration sig) {profile : Profile sig} {inputs}
    (eqs : List (Problem sig inputs)) (proposed : List (Answer sig inputs))
    (complete : Complete profile proposed (Terms.identity inputs) eqs)
    (sound : SystemSoundness proposed eqs) :
    ∀ values, Holds reg eqs values ↔ Solutions reg proposed values :=
  fun values => ⟨fun input =>
    (identity_eval reg values) ▸ complete.sound reg values input,
    sound.sound reg values⟩

theorem exact (reg : Registration sig) {profile : Profile sig} {inputs}
    (problem : Problem sig inputs) (proposed : List (Answer sig inputs))
    (complete : Complete profile proposed (Terms.identity inputs) [problem])
    (sound : Soundness problem proposed) :
    ∀ values, problem.Holds reg values ↔ Solutions reg proposed values :=
  fun values => ⟨fun input =>
    (identity_eval reg values) ▸ complete.sound reg values
      (fun _p member => (List.mem_singleton.mp member) ▸ input),
    sound.sound reg values⟩

end Worklist

end Substitution

end DirectCertification
