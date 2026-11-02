import Reflect.Check
import conPanna.Unification.Certification.Solve

/-!
Facts about evaluation (documentation/reflection-design.md, §1): Boolean equality of terms,
typing, locality, substitution.
-/

namespace Reflect

open Term

/-! ## Boolean equality -/

mutual
theorem beq_eq : ∀ {a b : Term}, beq a b = true → a = b
  | .var x, .var y, h => by simp only [beq, beq_iff_eq] at h; rw [h]
  | .app f as, .app g bs, h => by
    simp only [beq, Bool.and_eq_true, beq_iff_eq] at h
    rw [h.1, beqL_eq h.2]
  | .acu f as, .acu g bs, h => by
    simp only [beq, Bool.and_eq_true, beq_iff_eq] at h
    rw [h.1, beqL_eq h.2]
  | .var _, .app _ _, h | .var _, .acu _ _, h | .app _ _, .var _, h | .app _ _, .acu _ _, h
  | .acu _ _, .var _, h | .acu _ _, .app _ _, h => by simp [beq] at h
theorem beqL_eq : ∀ {as bs : List Term}, beqL as bs = true → as = bs
  | [], [], _ => rfl
  | a :: as, b :: bs, h => by
    simp only [beqL, Bool.and_eq_true] at h
    rw [beq_eq h.1, beqL_eq h.2]
  | [], _ :: _, h | _ :: _, [], h => by simp [beqL] at h
end

mutual
theorem beq_refl : ∀ a : Term, beq a a = true
  | .var x => by simp [beq]
  | .app f as => by simp [beq, beqL_refl as]
  | .acu f as => by simp [beq, beqL_refl as]
theorem beqL_refl : ∀ as : List Term, beqL as as = true
  | [] => rfl
  | a :: as => by simp [beqL, beq_refl a, beqL_refl as]
end

theorem beq_iff {a b : Term} : beq a b = true ↔ a = b :=
  ⟨beq_eq, fun h => h ▸ beq_refl a⟩

instance : DecidableEq Term := fun a b => decidable_of_iff _ beq_iff

namespace Model

variable (M : Model)

/-! ## Values -/

theorem get?_eq_some {s : Nat} {v : M.Val} {y : M.T s} (h : M.get? s v = some y) : v = ⟨s, y⟩ := by
  unfold get? at h
  split at h
  · next h' =>
    obtain ⟨s', v⟩ := v
    simp only at h'
    subst h'
    simp only [Option.some.injEq] at h
    subst h
    rfl
  · simp at h

@[simp] theorem get?_mk (s : Nat) (y : M.T s) : M.get? s ⟨s, y⟩ = some y := by
  simp [get?]

theorem get?_ne {s : Nat} {v : M.Val} (h : v.1 ≠ s) : M.get? s v = none := by
  simp [get?, h]

/-- A valuation respects the declared sorts `vs`. -/
def WS (vs : List Nat) (ρ : M.Valuation) : Prop := ∀ x v, ρ x = some v → vs[x]? = some v.1

/-! ## Constructors -/

theorem app_eq_some {f : Nat} {xs : List M.Val} {v : M.Val} (h : M.app f xs = some v) :
    ∃ o a, M.op? f = some o ∧ M.getTup? o.args xs = some a ∧ v = ⟨o.res, o.build a⟩ := by
  unfold app at h
  split at h
  · next o ho =>
    cases ha : M.getTup? o.args xs with
    | none => simp [ha] at h
    | some a => simp only [ha, Option.map_some, Option.some.injEq] at h; exact ⟨o, a, ho, ha, h.symm⟩
  · simp at h

/-! ## Typing -/

theorem tsort_eval {vs : List Nat} {ρ : M.Valuation} (hρ : M.WS vs ρ) :
    ∀ {t : Term} {v : M.Val}, M.eval ρ t = some v → tsort M vs t = some v.1
  | .var x, v, h => by simp only [eval] at h; simp [tsort, hρ x v h]
  | .app f ts, v, h => by
    simp only [eval] at h
    cases hl : M.evalL ρ ts with
    | none => simp [hl] at h
    | some xs =>
      simp only [hl, Option.bind_some] at h
      obtain ⟨o, a, ho, -, rfl⟩ := M.app_eq_some h
      simp [tsort, res?, ho]
  | .acu f ts, v, h => by
    simp only [eval] at h
    split at h
    · next A hA =>
      cases hs : M.sumL ρ A ts with
      | none => simp [hs] at h
      | some X => simp only [hs, Option.map_some, Option.some.injEq] at h; subst h; simp [tsort, hA]
    · simp at h

/-! ## Locality and substitution -/

variable {M}

mutual
theorem eval_congr {ρ ρ' : M.Valuation} :
    ∀ (t : Term), (∀ x, occursT x t = true → ρ x = ρ' x) → M.eval ρ t = M.eval ρ' t
  | .var x, h => by simp only [eval]; exact h x (by simp [occursT])
  | .app f ts, h => by
    simp only [eval]
    rw [evalL_congr ts (fun x hx => h x (by simp [occursT, hx]))]
  | .acu f ts, h => by
    simp only [eval]
    split
    · rw [sumL_congr _ ts (fun x hx => h x (by simp [occursT, hx]))]
    · rfl
theorem evalL_congr {ρ ρ' : M.Valuation} :
    ∀ (ts : List Term), (∀ x, occursTL x ts = true → ρ x = ρ' x) → M.evalL ρ ts = M.evalL ρ' ts
  | [], _ => rfl
  | t :: ts, h => by
    simp only [evalL]
    rw [eval_congr t (fun x hx => h x (by simp [occursTL, hx])),
      evalL_congr ts (fun x hx => h x (by simp [occursTL, hx]))]
theorem sumL_congr {ρ ρ' : M.Valuation} (A : AcuOp M.T) :
    ∀ (ts : List Term), (∀ x, occursTL x ts = true → ρ x = ρ' x) → M.sumL ρ A ts = M.sumL ρ' A ts
  | [], _ => rfl
  | [t], h => by
    simp only [sumL]
    rw [eval_congr t (fun x hx => h x (by simp [occursTL, hx]))]
  | t :: t' :: ts, h => by
    simp only [sumL]
    rw [eval_congr t (fun x hx => h x (by simp [occursTL, hx])),
      sumL_congr A (t' :: ts) (fun x hx => h x (by simp only [occursTL] at hx ⊢; simp [hx]))]
end

/-- The valuation a substitution produces: `σ x` evaluated, or `ρ x` outside its domain. -/
def substV (ρ : M.Valuation) (σ : Nat → Option Term) : M.Valuation := fun x =>
  match σ x with
  | some u => M.eval ρ u
  | none => ρ x

mutual
theorem eval_subst (ρ : M.Valuation) (σ : Nat → Option Term) :
    ∀ t, M.eval ρ (subst σ t) = M.eval (substV ρ σ) t
  | .var x => by
    simp only [subst, eval, substV]
    cases σ x <;> rfl
  | .app f ts => by simp only [subst, eval]; rw [evalL_subst ρ σ ts]
  | .acu f ts => by
    simp only [subst, eval]
    split
    · rw [sumL_subst ρ σ _ ts]
    · rfl
theorem evalL_subst (ρ : M.Valuation) (σ : Nat → Option Term) :
    ∀ ts, M.evalL ρ (substL σ ts) = M.evalL (substV ρ σ) ts
  | [] => rfl
  | t :: ts => by simp only [substL, evalL]; rw [eval_subst ρ σ t, evalL_subst ρ σ ts]
theorem sumL_subst (ρ : M.Valuation) (σ : Nat → Option Term) (A : AcuOp M.T) :
    ∀ ts, M.sumL ρ A (substL σ ts) = M.sumL (substV ρ σ) A ts
  | [] => rfl
  | [t] => by simp only [substL, sumL]; rw [eval_subst ρ σ t]
  | t :: t' :: ts => by
    simp only [substL, sumL]
    rw [eval_subst ρ σ t, ← sumL_subst ρ σ A (t' :: ts)]
    rfl
end

-- A term that evaluates has all its variables defined.
mutual
theorem eval_def {ρ : M.Valuation} :
    ∀ {t : Term} {v : M.Val}, M.eval ρ t = some v → ∀ x, occursT x t = true → (ρ x).isSome
  | .var y, v, h, x, hx => by
    simp only [occursT, beq_iff_eq] at hx; subst hx; simp only [eval] at h; simp [h]
  | .app f ts, v, h, x, hx => by
    simp only [eval] at h
    cases hl : M.evalL ρ ts with
    | none => simp [hl] at h
    | some xs => exact evalL_def hl x (by simpa [occursT] using hx)
  | .acu f ts, v, h, x, hx => by
    simp only [eval] at h
    split at h
    · next A _ =>
      cases hs : M.sumL ρ A ts with
      | none => simp [hs] at h
      | some X => exact sumL_def A hs x (by simpa [occursT] using hx)
    · simp at h
theorem evalL_def {ρ : M.Valuation} :
    ∀ {ts : List Term} {vs : List M.Val}, M.evalL ρ ts = some vs → ∀ x, occursTL x ts = true → (ρ x).isSome
  | [], _, _, x, hx => by simp [occursTL] at hx
  | t :: ts, vs, h, x, hx => by
    simp only [evalL] at h
    cases ht : M.eval ρ t with
    | none => simp [ht] at h
    | some v =>
      cases hl : M.evalL ρ ts with
      | none => simp [ht, hl] at h
      | some ws =>
        simp only [occursTL, Bool.or_eq_true] at hx
        rcases hx with hx | hx
        · exact eval_def ht x hx
        · exact evalL_def hl x hx
theorem sumL_def {ρ : M.Valuation} (A : AcuOp M.T) :
    ∀ {ts : List Term} {X}, M.sumL ρ A ts = some X → ∀ x, occursTL x ts = true → (ρ x).isSome
  | [], _, _, x, hx => by simp [occursTL] at hx
  | [t], X, h, x, hx => by
    simp only [sumL] at h
    cases ht : M.eval ρ t with
    | none => simp [ht] at h
    | some v => exact eval_def ht x (by simpa [occursTL] using hx)
  | t :: t' :: ts, X, h, x, hx => by
    simp only [sumL] at h
    cases ht : M.eval ρ t with
    | none => simp [ht] at h
    | some v =>
      cases hs : M.sumL ρ A (t' :: ts) with
      | none => simp [ht, hs] at h
      | some Y =>
        simp only [occursTL, Bool.or_eq_true] at hx
        rcases hx with hx | hx
        · exact eval_def ht x hx
        · exact sumL_def A hs x (by simpa [occursTL] using hx)
end

/-! ## Laws -/

theorem allL_mem {β : Type u} {P : β → Prop} : ∀ {l : List β}, AllL P l → ∀ x ∈ l, P x
  | [], _, _, hx => by simp at hx
  | a :: l, h, x, hx => by
    rcases List.mem_cons.1 hx with rfl | hx
    · exact h.1
    · exact allL_mem h.2 x hx

theorem allIdx_get {β : Type u} {P : Nat → β → Prop} :
    ∀ {i : Nat} {l : List β}, AllIdx P i l → ∀ j x, l[j]? = some x → P (i + j) x
  | _, [], _, j, x, hx => by simp at hx
  | i, a :: l, h, 0, x, hx => by simp only [List.getElem?_cons_zero, Option.some.injEq] at hx; subst hx; exact h.1
  | i, a :: l, h, j + 1, x, hx => by
    have := allIdx_get h.2 j x (by simpa using hx)
    rwa [show i + 1 + j = i + (j + 1) by omega] at this

theorem acu_law (hM : M.Lawful) {f : Nat} {A : AcuOp M.T} (hA : M.acu? f = some A) :
    (∀ X, A.toBag (A.ofBag X) = X) ∧ (∀ y, A.ofBag (A.toBag y) = y) ∧ A.elem ≠ A.bag :=
  allL_mem hM.acu A (List.mem_of_getElem? hA)

theorem contrib_bag (hM : M.Lawful) {f : Nat} {A : AcuOp M.T} (hA : M.acu? f = some A)
    (X : ACU (M.T A.elem)) : M.contrib A ⟨A.bag, A.ofBag X⟩ = some X := by
  obtain ⟨h1, -, h3⟩ := acu_law hM hA
  simp [contrib, M.get?_ne (s := A.elem) (v := ⟨A.bag, A.ofBag X⟩) (Ne.symm h3), h1]

/-! ## Bags as multisets -/

/-- A summand's contribution, as a multiset. -/
def cval (A : AcuOp M.T) (ρ : M.Valuation) (t : Term) : Option (Multiset (M.T A.elem)) :=
  ((M.eval ρ t).bind (M.contrib A)).map ACU.toMultiset

def msum (A : AcuOp M.T) (ρ : M.Valuation) : List Term → Option (Multiset (M.T A.elem))
  | [] => some 0
  | t :: ts => (cval A ρ t).bind fun a => (msum A ρ ts).map (a + ·)

theorem sumL_msum (A : AcuOp M.T) (ρ : M.Valuation) :
    ∀ ts, (M.sumL ρ A ts).map ACU.toMultiset = msum A ρ ts
  | [] => by simp [sumL, msum]
  | [t] => by
    simp only [sumL, msum, cval]
    cases (M.eval ρ t).bind (M.contrib A) <;> simp
  | t :: t' :: ts => by
    have ih := sumL_msum A ρ (t' :: ts)
    rw [msum, ← ih]
    simp only [sumL, cval]
    cases hc : (M.eval ρ t).bind (M.contrib A) <;>
      cases hs : M.sumL ρ A (t' :: ts) <;> simp [ACU.toMultiset_plus]

theorem msum_append (A : AcuOp M.T) (ρ : M.Valuation) :
    ∀ ts us, msum A ρ (ts ++ us) = (msum A ρ ts).bind fun a => (msum A ρ us).map (a + ·)
  | [], us => by cases h : msum A ρ us <;> simp [msum, h]
  | t :: ts, us => by
    simp only [List.cons_append, msum, msum_append A ρ ts us]
    cases cval A ρ t <;> cases msum A ρ ts <;> cases msum A ρ us <;> simp [add_assoc]

theorem msum_perm (A : AcuOp M.T) (ρ : M.Valuation) {ts us : List Term} (h : ts.Perm us) :
    msum A ρ ts = msum A ρ us := by
  induction h with
  | nil => rfl
  | cons t _ ih => simp only [msum, ih]
  | swap t u ts =>
    simp only [msum]
    cases cval A ρ t <;> cases cval A ρ u <;> cases msum A ρ ts <;> simp [add_left_comm]
  | trans _ _ ih1 ih2 => rw [ih1, ih2]

theorem eval_acu_of_msum {A : AcuOp M.T} {f : Nat} (hA : M.acu? f = some A) {ρ : M.Valuation}
    {ts us : List Term} (h : msum A ρ ts = msum A ρ us) :
    M.eval ρ (.acu f ts) = M.eval ρ (.acu f us) := by
  simp only [eval, hA]
  rw [← sumL_msum, ← sumL_msum] at h
  have : M.sumL ρ A ts = M.sumL ρ A us :=
    Option.map_injective ACU.toMultiset_injective h
  rw [this]

theorem cval_acu (hM : M.Lawful) {A : AcuOp M.T} {f : Nat} (hA : M.acu? f = some A)
    (ρ : M.Valuation) (bs : List Term) : cval A ρ (.acu f bs) = msum A ρ bs := by
  rw [← sumL_msum]
  simp only [cval, eval, hA]
  cases M.sumL ρ A bs <;> simp [contrib_bag hM hA]

theorem msum_flat (hM : M.Lawful) {A : AcuOp M.T} {f : Nat} (hA : M.acu? f = some A)
    (ρ : M.Valuation) : ∀ ts, msum A ρ (flat f ts) = msum A ρ ts
  | [] => rfl
  | .acu g bs :: as => by
    simp only [flat]
    split
    · next hfg =>
      simp only [beq_iff_eq] at hfg; subst hfg
      rw [msum_append, msum_flat hM hA ρ as]
      simp only [msum, cval_acu hM hA]
    · simp only [msum, msum_flat hM hA ρ as]
  | .var x :: as => by simp only [flat, msum, msum_flat hM hA ρ as]
  | .app g bs :: as => by simp only [flat, msum, msum_flat hM hA ρ as]

theorem perm_ins (t : Term) : ∀ us, (Term.ins t us).Perm (t :: us)
  | [] => List.Perm.refl _
  | u :: us => by
    simp only [Term.ins]
    split
    · exact ((perm_ins t us).cons u).trans (List.Perm.swap t u us)
    · exact List.Perm.refl _

theorem perm_sort : ∀ ts, (Term.sort ts).Perm ts
  | [] => List.Perm.refl _
  | t :: ts => (perm_ins t _).trans ((perm_sort ts).cons t)

/-- A bag-sorted term is its own sum. -/
theorem eval_acu_single (hM : M.Lawful) {vs : List Nat} {ρ : M.Valuation} (hρ : M.WS vs ρ)
    {A : AcuOp M.T} {f : Nat} (hA : M.acu? f = some A) {t : Term}
    (ht : tsort M vs t = some A.bag) : M.eval ρ (.acu f [t]) = M.eval ρ t := by
  obtain ⟨-, h2, h3⟩ := acu_law hM hA
  simp only [eval, hA, sumL]
  cases he : M.eval ρ t with
  | none => simp
  | some v =>
    have hs := M.tsort_eval hρ he
    rw [ht, Option.some.injEq] at hs
    obtain ⟨s, y⟩ := v
    simp only at hs
    subst hs
    simp [contrib, M.get?_ne (s := A.elem) (v := ⟨A.bag, y⟩) (Ne.symm h3), h2]

theorem eval_mkAcu (hM : M.Lawful) {vs : List Nat} {ρ : M.Valuation} (hρ : M.WS vs ρ)
    (f : Nat) (ts : List Term) : M.eval ρ (mkAcu M vs f ts) = M.eval ρ (.acu f ts) := by
  cases hA : M.acu? f with
  | none =>
    have hnone : ∀ us, M.eval ρ (.acu f us) = none := fun us => by simp [eval, hA]
    unfold mkAcu
    split
    · simp only [hA]; rw [hnone, hnone]
    · rw [hnone, hnone]
  | some A =>
    have hperm : msum A ρ (Term.sort (flat f ts)) = msum A ρ ts := by
      rw [msum_perm A ρ (perm_sort _), msum_flat hM hA]
    unfold mkAcu
    generalize Term.sort (flat f ts) = l at hperm ⊢
    rcases l with _ | ⟨t, _ | ⟨t', l⟩⟩
    · exact eval_acu_of_msum hA hperm
    · simp only [hA]
      cases hs : tsort M vs t with
      | none => exact eval_acu_of_msum hA hperm
      | some s =>
        simp only
        by_cases hb : s = A.bag
        · subst hb
          simp only [beq_self_eq_true, ite_true]
          rw [← eval_acu_single hM hρ hA hs]
          exact eval_acu_of_msum hA hperm
        · simp only [beq_iff_eq, hb, ite_false]
          exact eval_acu_of_msum hA hperm
    · exact eval_acu_of_msum hA hperm

mutual
theorem eval_norm (hM : M.Lawful) {vs : List Nat} {ρ : M.Valuation} (hρ : M.WS vs ρ) :
    ∀ t, M.eval ρ (norm M vs t) = M.eval ρ t
  | .var x => rfl
  | .app f ts => by simp only [norm, eval]; rw [evalL_norm hM hρ ts]
  | .acu f ts => by
    simp only [norm]
    rw [eval_mkAcu hM hρ]
    cases hA : M.acu? f with
    | none => simp [eval, hA]
    | some A => exact eval_acu_of_msum hA (msum_norm hM hρ A ts)
theorem evalL_norm (hM : M.Lawful) {vs : List Nat} {ρ : M.Valuation} (hρ : M.WS vs ρ) :
    ∀ ts, M.evalL ρ (normL M vs ts) = M.evalL ρ ts
  | [] => rfl
  | t :: ts => by simp only [normL, evalL]; rw [eval_norm hM hρ t, evalL_norm hM hρ ts]
theorem msum_norm (hM : M.Lawful) {vs : List Nat} {ρ : M.Valuation} (hρ : M.WS vs ρ) (A : AcuOp M.T) :
    ∀ ts, msum A ρ (normL M vs ts) = msum A ρ ts
  | [] => rfl
  | t :: ts => by simp only [normL, msum, cval]; rw [eval_norm hM hρ t, msum_norm hM hρ A ts]
end

/-! ## Constructors are injective and distinct -/

/-- The values of a tuple of arguments. -/
def encTup : (ss : List Nat) → Tup M.T ss → List M.Val
  | [], _ => []
  | [s], x => [⟨s, x⟩]
  | s :: s' :: ss, x => ⟨s, x.1⟩ :: encTup (s' :: ss) x.2

theorem getTup?_eq : ∀ {ss : List Nat} {xs : List M.Val} {a : Tup M.T ss},
    M.getTup? ss xs = some a → xs = encTup ss a
  | [], [], a, _ => rfl
  | [s], [v], a, h => by simp only [getTup?] at h; simp [encTup, M.get?_eq_some h]
  | s :: s' :: ss, v :: vs, a, h => by
    simp only [getTup?] at h
    cases hv : M.get? s v with
    | none => simp [hv] at h
    | some x =>
      cases hs : M.getTup? (s' :: ss) vs with
      | none => simp [hv, hs] at h
      | some y =>
        simp only [hv, hs, Option.some.injEq] at h
        subst h
        simp [encTup, M.get?_eq_some hv, getTup?_eq hs]
  | [], _ :: _, _, h | [_], [], _, h | [_], _ :: _ :: _, _, h | _ :: _ :: _, [], _, h => by
    simp [getTup?] at h

theorem app_inj (hM : M.Lawful) {f g : Nat} {xs ys : List M.Val} {v : M.Val}
    (h1 : M.app f xs = some v) (h2 : M.app g ys = some v) : f = g ∧ xs = ys := by
  obtain ⟨o, a, ho, ha, rfl⟩ := M.app_eq_some h1
  obtain ⟨o', a', ho', ha', hv⟩ := M.app_eq_some h2
  have t1 := allIdx_get hM.tag f o ho a
  have t2 := allIdx_get hM.tag g o' ho' a'
  obtain ⟨hr, hb⟩ := Sigma.mk.inj_iff.1 hv
  have hfg : f = g := by
    simp only [Nat.zero_add] at t1 t2
    rw [← t1, ← t2]
    revert hb
    generalize o.build a = x
    generalize o'.build a' = y
    revert x y
    rw [hr]
    intro x y hxy
    rw [eq_of_heq hxy]
  subst hfg
  rw [ho] at ho'
  cases ho'
  have hab : o.build a = o.build a' := eq_of_heq hb
  have u1 := allL_mem hM.unbuild o (List.mem_of_getElem? ho) a
  have u2 := allL_mem hM.unbuild o (List.mem_of_getElem? ho) a'
  rw [hab, u2, Option.some.injEq] at u1
  subst u1
  exact ⟨rfl, (getTup?_eq ha).trans (getTup?_eq ha').symm⟩

theorem eval_app_some {ρ : M.Valuation} {f : Nat} {ts : List Term} {v : M.Val}
    (h : M.eval ρ (.app f ts) = some v) : ∃ xs, M.evalL ρ ts = some xs ∧ M.app f xs = some v := by
  simp only [eval] at h
  cases hl : M.evalL ρ ts with
  | none => simp [hl] at h
  | some xs => exact ⟨xs, rfl, by simpa [hl] using h⟩

theorem evalL_cons_some {ρ : M.Valuation} {t : Term} {ts : List Term} {xs : List M.Val}
    (h : M.evalL ρ (t :: ts) = some xs) :
    ∃ x xs', xs = x :: xs' ∧ M.eval ρ t = some x ∧ M.evalL ρ ts = some xs' := by
  simp only [evalL] at h
  cases ht : M.eval ρ t with
  | none => simp [ht] at h
  | some x =>
    cases hl : M.evalL ρ ts with
    | none => simp [ht, hl] at h
    | some xs' => simp only [ht, hl, Option.some.injEq] at h; exact ⟨x, xs', h.symm, rfl, rfl⟩

theorem evalL_zip {ρ : M.Valuation} : ∀ {as bs : List Term} {xs : List M.Val},
    M.evalL ρ as = some xs → M.evalL ρ bs = some xs →
    ∀ e ∈ as.zip bs, ∃ v, M.eval ρ e.1 = some v ∧ M.eval ρ e.2 = some v
  | [], _, _, _, _, e, he => by simp at he
  | _ :: _, [], _, _, _, e, he => by simp at he
  | a :: as, b :: bs, xs, ha, hb, e, he => by
    obtain ⟨x, xs', rfl, hx, hxs⟩ := evalL_cons_some ha
    obtain ⟨y, ys', hy, hy1, hys⟩ := evalL_cons_some hb
    simp only [List.cons.injEq] at hy
    obtain ⟨rfl, rfl⟩ := hy
    rcases List.mem_cons.1 (by simpa using he) with rfl | he
    · exact ⟨x, hx, hy1⟩
    · exact evalL_zip hxs hys e he

mutual
theorem refute_sound (hM : M.Lawful) {ρ : M.Valuation} :
    ∀ {l r : Term}, refute l r = true → ∀ v, M.eval ρ l = some v → M.eval ρ r = some v → False
  | .app f as, .app g bs, h, v, hl, hr => by
    obtain ⟨xs, hxs, hf⟩ := eval_app_some hl
    obtain ⟨ys, hys, hg⟩ := eval_app_some hr
    obtain ⟨rfl, rfl⟩ := app_inj hM hf hg
    simp only [refute, bne_self_eq_false, Bool.false_or, Bool.and_eq_true] at h
    exact refuteL_sound hM h.2 xs hxs hys
  | .var _, _, h, _, _, _ | .acu _ _, _, h, _, _, _ | .app _ _, .var _, h, _, _, _
  | .app _ _, .acu _ _, h, _, _, _ => by simp [refute] at h
theorem refuteL_sound (hM : M.Lawful) {ρ : M.Valuation} :
    ∀ {as bs : List Term}, refuteL as bs = true → ∀ xs, M.evalL ρ as = some xs → M.evalL ρ bs = some xs → False
  | a :: as, b :: bs, h, xs, ha, hb => by
    obtain ⟨x, xs', rfl, hx, hxs⟩ := evalL_cons_some ha
    obtain ⟨y, ys', hy, hy1, hys⟩ := evalL_cons_some hb
    simp only [List.cons.injEq] at hy
    obtain ⟨rfl, rfl⟩ := hy
    simp only [refuteL, Bool.or_eq_true] at h
    rcases h with h | h
    · exact refute_sound hM h x hx hy1
    · exact refuteL_sound hM h xs' hxs hys
  | [], _, h, _, _, _ | _ :: _, [], h, _, _, _ => by simp [refuteL] at h
end

/-! ## Tuples of values -/

theorem encL_length : ∀ (sh : Shp) (x : sh.Ty M.T), (M.encL sh x).length = sh.size
  | .leaf _, _ => rfl
  | .pair l r, (a, b) => by simp [encL, Shp.size, encL_length l a, encL_length r b]

theorem encL_sorts : ∀ (sh : Shp) (x : sh.Ty M.T), (M.encL sh x).map (·.1) = sh.sorts
  | .leaf _, _ => rfl
  | .pair l r, (a, b) => by simp [encL, Shp.sorts, encL_sorts l a, encL_sorts r b]

theorem encL_inj : ∀ (sh : Shp) {x y : sh.Ty M.T}, M.encL sh x = M.encL sh y → x = y
  | .leaf s, x, y, h => by
    simp only [encL, List.cons.injEq, and_true] at h
    exact eq_of_heq (Sigma.mk.inj_iff.1 h).2
  | .pair l r, (a, b), (a', b'), h => by
    simp only [encL] at h
    obtain ⟨h1, h2⟩ := List.append_inj h (by rw [encL_length, encL_length])
    rw [encL_inj l h1, encL_inj r h2]

theorem Shp.sorts_length : ∀ sh : Shp, sh.sorts.length = sh.size
  | .leaf _ => rfl
  | .pair l r => by simp [Shp.sorts, Shp.size, Shp.sorts_length l, Shp.sorts_length r]

/-- A valuation that holds values of the right sorts at `off, off + 1, …` is a tuple's. -/
theorem decode : ∀ (sh : Shp) (ν : M.Valuation) (off : Nat),
    (∀ j < sh.size, ∃ v, ν (off + j) = some v ∧ sh.sorts[j]? = some v.1) →
    ∃ a : sh.Ty M.T, ∀ j < sh.size, ν (off + j) = (M.encL sh a)[j]?
  | .leaf s, ν, off, h => by
    obtain ⟨⟨s', y⟩, hv, hs⟩ := h 0 (by simp [Shp.size])
    simp only [Shp.sorts, List.getElem?_cons_zero, Option.some.injEq] at hs
    subst hs
    refine ⟨y, fun j hj => ?_⟩
    simp only [Shp.size, Nat.lt_one_iff] at hj
    subst hj
    simpa [encL] using hv
  | .pair l r, ν, off, h => by
    obtain ⟨a, ha⟩ := decode l ν off fun j hj => by
      obtain ⟨v, hv, hs⟩ := h j (by simp [Shp.size]; omega)
      refine ⟨v, hv, ?_⟩
      rwa [Shp.sorts, List.getElem?_append_left (by rw [Shp.sorts_length]; exact hj)] at hs
    obtain ⟨b, hb⟩ := decode r ν (off + l.size) fun j hj => by
      obtain ⟨v, hv, hs⟩ := h (l.size + j) (by simp [Shp.size]; omega)
      refine ⟨v, by rwa [Nat.add_assoc], ?_⟩
      rwa [Shp.sorts, List.getElem?_append_right (by rw [Shp.sorts_length]; omega),
        Shp.sorts_length, Nat.add_sub_cancel_left] at hs
    refine ⟨(a, b), fun j hj => ?_⟩
    simp only [encL]
    by_cases hjl : j < l.size
    · rw [List.getElem?_append_left (by rw [encL_length]; exact hjl)]
      exact ha j hjl
    · rw [List.getElem?_append_right (by rw [encL_length]; omega), encL_length]
      have := hb (j - l.size) (by simp [Shp.size] at hj; omega)
      rwa [show off + l.size + (j - l.size) = off + j by omega] at this

end Model

end Reflect
