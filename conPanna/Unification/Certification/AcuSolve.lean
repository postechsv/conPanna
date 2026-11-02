import conPanna.Unification.Certification.Calculus

/-!
ACU-SOLVE on a system of bag equations (documentation/acu-solve-design.md), the rule
`acu-solve` of the derivation format (documentation/derivation-format.md, §5).

The columns of a system are its bag variables `X : Fin n → ACU El` and its aliens
`a : Fin m → El`, bags first: `Fin (n + m)`. Two alien columns may hold the same term.
The data is one basis of the whole system, split into its alien-free vectors (each
gets a fresh bag) and its alien vectors (each selected or not). One premise per legal
selection: every alien in exactly one selected vector.

Validity asks only that the basis covers the *admissible* solutions: at most one copy of
each alien, and no two clashing aliens (different top symbols). This is what Maude's
bases satisfy. The proof peels basis vectors with `decompose`, as SOLVE does.
-/

namespace Unification.Certification

open ACU

universe v w w' x y

variable {El : Type y} {n m k₀ k₁ : ℕ}

/-! ## Data -/

/-- A system of bag equations over `n` bag variables and `m` aliens. Each row `(L, R)`
reads `Σ_j L j • col j = Σ_j R j • col j`. `clash` lists pairs of aliens with different
top symbols. -/
structure System (n m : ℕ) where
  rows : List ((Fin (n + m) → ℕ) × (Fin (n + m) → ℕ))
  clash : List (Fin m × Fin m) := []

/-- The columns as bags: the bag variables, then each alien as a singleton. -/
def columns (X : Fin n → ACU El) (a : Fin m → El) : Fin (n + m) → ACU El :=
  Fin.append X fun c => {a c}

/-- The system holds for the bags `X` and aliens `a`: each row in SOLVE's `side` form,
bags then aliens (`Fin.castAdd`, `Fin.natAdd` evaluate at numerals). -/
def System.Holds (q : System n m) (X : Fin n → ACU El) (a : Fin m → El) : Prop :=
  ∀ r ∈ q.rows,
    side (fun i => r.1 (Fin.castAdd m i)) X (fun c => r.1 (Fin.natAdd n c)) a =
      side (fun i => r.2 (Fin.castAdd m i)) X (fun c => r.2 (Fin.natAdd n c)) a

/-- The count vectors the basis must cover: solutions of every row with at most one
copy of each alien and no two clashing aliens. -/
def System.Admissible (q : System n m) (v : Fin (n + m) → ℕ) : Prop :=
  (∀ r ∈ q.rows, dot r.1 v = dot r.2 v) ∧ (∀ c, v (Fin.natAdd n c) ≤ 1) ∧
    ∀ p ∈ q.clash, v (Fin.natAdd n p.1) + v (Fin.natAdd n p.2) ≤ 1

/-- The basis: alien-free vectors, alien vectors, and a representative alien of each
alien vector. -/
structure Basis (n m k₀ k₁ : ℕ) where
  free : Fin k₀ → Fin (n + m) → ℕ
  alien : Fin k₁ → Fin (n + m) → ℕ
  rep : Fin k₁ → Fin m

/-- All basis vectors, the alien-free ones first. -/
def Basis.all (B : Basis n m k₀ k₁) : Fin (k₀ + k₁) → Fin (n + m) → ℕ :=
  Fin.append B.free B.alien

/-- The side conditions: closed arithmetic facts about the system and the basis, stated
for the two kinds of vectors separately (no `Fin.append` to evaluate). -/
structure Basis.Valid (q : System n m) (B : Basis n m k₀ k₁) : Prop where
  nonzero : ∀ t, ∃ j, B.free t j ≠ 0
  solvesFree : ∀ t, ∀ r ∈ q.rows, dot r.1 (B.free t) = dot r.2 (B.free t)
  solvesAlien : ∀ t, ∀ r ∈ q.rows, dot r.1 (B.alien t) = dot r.2 (B.alien t)
  free : ∀ t c, B.free t (Fin.natAdd n c) = 0
  rep : ∀ t, B.alien t (Fin.natAdd n (B.rep t)) ≠ 0
  complete : ∀ v, q.Admissible v → (∃ j, v j ≠ 0) →
    (∃ t, Below (B.free t) v) ∨ ∃ t, Below (B.alien t) v

/-- Every subset of `Fin k`, as a Boolean function. -/
def selections : (k : ℕ) → List (Fin k → Bool)
  | 0 => [Fin.elim0]
  | k + 1 => (selections k).flatMap fun S => [Matrix.vecCons false S, Matrix.vecCons true S]

/-- A selection of alien vectors is legal if it holds every alien exactly once. -/
def Basis.Legal (B : Basis n m k₀ k₁) (S : Fin k₁ → Bool) : Bool :=
  (List.finRange m).all fun c =>
    ((List.finRange k₁).map fun t => if S t then B.alien t (Fin.natAdd n c) else 0).sum == 1

/-- The legal selections: one premise each. -/
def Basis.legal (B : Basis n m k₀ k₁) : List (Fin k₁ → Bool) :=
  (selections k₁).filter B.Legal

/-- `θ_S`: `X i := Σ_t free t i • Z t + Σ_{t ∈ S} alien t i • {a (rep t)}`. -/
def Basis.theta (B : Basis n m k₀ k₁) (a : Fin m → El) (S : Fin k₁ → Bool)
    (Z : Fin k₀ → ACU El) : Fin n → ACU El := fun i =>
  sum (fun t => copies (B.free t (Fin.castAdd m i)) (Z t)) +
    sum (fun t => if S t then copies (B.alien t (Fin.castAdd m i)) {a (B.rep t)} else ∅)

/-- The pending equations of a selection: the aliens of a selected vector equal its
representative. -/
def Basis.pending {Γr : Type w'} (B : Basis n m k₀ k₁) (a : Γr → Fin m → El)
    (S : Fin k₁ → Bool) : List (Γr × (Fin k₀ → ACU El) → Prop) :=
  (List.ofFn fun t => (List.ofFn fun c =>
    if S t ∧ B.alien t (Fin.natAdd n c) ≠ 0 ∧ c ≠ B.rep t then
      [fun p : Γr × (Fin k₀ → ACU El) => a p.1 c = a p.1 (B.rep t)] else []).flatten).flatten

/-! ## Facts -/

theorem mem_selections : ∀ {k : ℕ} (S : Fin k → Bool), S ∈ selections k
  | 0, S => List.mem_singleton.2 (funext fun i => i.elim0)
  | k + 1, S => by
    simp only [selections, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false]
    refine ⟨Fin.tail S, mem_selections _, ?_⟩
    have h : S = Matrix.vecCons (S 0) (Fin.tail S) := (Fin.cons_self_tail S).symm
    cases h0 : S 0 <;> rw [h0] at h
    · exact Or.inl h
    · exact Or.inr h

theorem eqs_iff {Γ : Type w} (E : List (Γ → Prop)) (ρ : Γ) : Eqs E ρ ↔ ∀ e ∈ E, e ρ := by
  induction E with
  | nil => simp [Eqs]
  | cons e E ih =>
    change e ρ ∧ Eqs E ρ ↔ _
    rw [ih]
    simp

/-- A singleton written as a sum: each summand with a nonzero coefficient is empty or the
singleton, and the coefficients of the nonempty summands add up to one. -/
theorem singleton_eq_sum [DecidableEq El] {k : ℕ} (e : El) (w : Fin k → ℕ)
    (M : Fin k → Multiset El) (h : ({e} : Multiset El) = ∑ t, w t • M t) :
    (∀ t, w t ≠ 0 → M t = 0 ∨ M t = {e}) ∧ ∑ t, (if M t ≠ 0 then w t else 0) = 1 := by
  have hle : ∀ t, w t ≠ 0 → M t ≤ {e} := by
    intro t ht
    calc M t ≤ w t • M t := Multiset.le_iff_count.mpr fun x => by
            rw [Multiset.count_nsmul]; exact Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero ht)
      _ ≤ ∑ t, w t • M t := Finset.single_le_sum (f := fun t => w t • M t)
            (fun _ _ => zero_le _) (Finset.mem_univ t)
      _ = {e} := h.symm
  have h1 : ∀ t, w t ≠ 0 → M t = 0 ∨ M t = {e} := fun t ht => Multiset.le_singleton.mp (hle t ht)
  refine ⟨h1, ?_⟩
  have hc := congrArg Multiset.card h
  rw [Multiset.card_singleton, Multiset.card_sum] at hc
  rw [hc]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Multiset.card_nsmul]
  by_cases hw : w t = 0
  · simp [hw]
  · rcases h1 t hw with h0 | h0 <;> simp [h0]

/-! ## Validity -/

/-- Every solution of a valid system has the form `θ_S Z` for a legal selection `S`, with
the aliens of each selected vector equal to its representative. -/
theorem acu_decomp (q : System n m) (B : Basis n m k₀ k₁) (valid : B.Valid q)
    (X : Fin n → ACU El) (a : Fin m → El) (heq : q.Holds X a)
    (hclash : ∀ p ∈ q.clash, a p.1 ≠ a p.2) :
    ∃ S ∈ B.legal, ∃ Z : Fin k₀ → ACU El, X = B.theta a S Z ∧
      ∀ t, S t → ∀ c, B.alien t (Fin.natAdd n c) ≠ 0 → a c = a (B.rep t) := by
  classical
  let x : Fin (n + m) → Multiset El := fun j => (columns X a j).toMultiset
  have hxb : ∀ i, x (Fin.castAdd m i) = (X i).toMultiset := fun i => by simp [x, columns]
  have hxa : ∀ c, x (Fin.natAdd n c) = {a c} := fun c => by simp [x, columns]
  -- Every element's count vector is admissible.
  have hx : ∀ e, q.Admissible (counts x e) := by
    intro e
    refine ⟨fun r hr => ?_, fun c => ?_, fun p hp => ?_⟩
    · have hm := congrArg (fun X => Multiset.count e (toMultiset X)) (heq r hr)
      simp only [side, toMultiset_plus, toMultiset_sum, toMultiset_copies, toMultiset_elem,
        Multiset.count_add, Multiset.count_sum', Multiset.count_nsmul] at hm
      rw [dot_eq, dot_eq, Fin.sum_univ_add, Fin.sum_univ_add]
      simpa [counts, hxb, hxa] using hm
    · simp only [counts, hxa, Multiset.count_singleton]; split <;> omega
    · have hne := hclash p hp
      simp only [counts, hxa, Multiset.count_singleton]
      split <;> split <;> first | omega | (exfalso; apply hne; simp_all)
  -- Peel basis vectors.
  have hnz : ∀ t, ∃ j, B.all t j ≠ 0 := by
    intro t
    refine Fin.addCases (fun t => ?_) (fun t => ?_) t
    · simpa [Basis.all] using valid.nonzero t
    · exact ⟨_, by simpa [Basis.all] using valid.rep t⟩
  have hsol : ∀ t, ∀ r ∈ q.rows, dot r.1 (B.all t) = dot r.2 (B.all t) := by
    intro t
    refine Fin.addCases (fun t => ?_) (fun t => ?_) t
    · simpa [Basis.all] using valid.solvesFree t
    · simpa [Basis.all] using valid.solvesAlien t
  have hcomp : ∀ v, q.Admissible v → (∃ j, v j ≠ 0) → ∃ t, Below (B.all t) v := by
    intro v hv hne
    rcases valid.complete v hv hne with ⟨t, ht⟩ | ⟨t, ht⟩
    · exact ⟨Fin.castAdd k₁ t, by simpa [Basis.all] using ht⟩
    · exact ⟨Fin.natAdd k₀ t, by simpa [Basis.all] using ht⟩
  obtain ⟨U, hU⟩ := decompose q.Admissible B.all
    (fun t h => by obtain ⟨j, hj⟩ := hnz t; exact hj (congrFun h j))
    (fun v hv hne => by
      have hne' : ∃ j, v j ≠ 0 := by
        by_contra hc; push_neg at hc; exact hne (funext hc)
      obtain ⟨t, ht⟩ := hcomp v hv hne'
      refine ⟨t, fun j => ht j, fun r hr => ?_, fun c => ?_, fun p hp => ?_⟩
      · rw [dot_sub _ ht, dot_sub _ ht, hv.1 r hr, hsol t r hr]
      · have := hv.2.1 c; simp only [Pi.sub_apply]; omega
      · have := hv.2.2 p hp; simp only [Pi.sub_apply]; omega)
    x hx
  -- The sums split into alien-free and alien vectors.
  have hsplit : ∀ j, x j = (∑ t, B.free t j • U (Fin.castAdd k₁ t)) +
      ∑ t, B.alien t j • U (Fin.natAdd k₀ t) := fun j => by
    rw [hU j, Fin.sum_univ_add]; simp [Basis.all]
  -- Alien columns: each selected alien vector holds exactly the alien's element.
  have halien : ∀ c, (∀ t, B.alien t (Fin.natAdd n c) ≠ 0 →
        U (Fin.natAdd k₀ t) = 0 ∨ U (Fin.natAdd k₀ t) = {a c}) ∧
      ∑ t, (if U (Fin.natAdd k₀ t) ≠ 0 then B.alien t (Fin.natAdd n c) else 0) = 1 := by
    intro c
    have h := hsplit (Fin.natAdd n c)
    simp only [valid.free, zero_nsmul, Finset.sum_const_zero, zero_add, hxa] at h
    exact singleton_eq_sum (a c) _ _ h
  let S : Fin k₁ → Bool := fun t => decide (U (Fin.natAdd k₀ t) ≠ 0)
  have hsel : ∀ t, S t → U (Fin.natAdd k₀ t) = {a (B.rep t)} := by
    intro t ht
    have ht' : U (Fin.natAdd k₀ t) ≠ 0 := of_decide_eq_true ht
    exact ((halien (B.rep t)).1 t (valid.rep t)).resolve_left ht'
  have hunsel : ∀ t, S t = false → U (Fin.natAdd k₀ t) = 0 := by
    intro t ht
    simpa [S] using ht
  refine ⟨S, ?_, fun t => ofMultiset (U (Fin.castAdd k₁ t)), ?_, ?_⟩
  · -- legality
    refine List.mem_filter.2 ⟨mem_selections S, ?_⟩
    simp only [Basis.Legal, List.all_eq_true, beq_iff_eq]
    intro c _
    rw [← finSum_eq_list]
    have := (halien c).2
    convert this using 2 with t
    simp [S]
  · -- the bag columns
    funext i
    rw [eq_iff]
    simp only [Basis.theta, toMultiset_plus, toMultiset_sum, toMultiset_copies,
      toMultiset_ofMultiset, ← hxb, hsplit]
    congr 1
    refine Finset.sum_congr rfl fun t _ => ?_
    cases h : S t
    · simp [hunsel t h]
    · simp [hsel t h]
  · -- the pending equations
    intro t ht c hc
    have h1 := ((halien c).1 t hc).resolve_left (by simpa [S] using ht)
    rw [hsel t ht] at h1
    exact (Multiset.singleton_inj.mp h1).symm

/-! ## The rule -/

variable {Γ₀ : Type v} {Γ : Type w} {unifiers : UnifierSet.{v, x} Γ₀}
  {α : Γ → Γ₀} {E : List (Γ → Prop)} {D : Γ → Prop}

/-- ACU-SOLVE the system `q`, which the first equations `es` of the state describe.
One premise per legal selection `S`: the bag variables become `θ_S`, over the rest of
the context plus fresh bags `Z : Fin k₀ → ACU El`, and the aliens of each selected
vector become equal to its representative.

Given by the certificate: `sp` (the bag variables), `a` (the aliens, which depend only on
the rest of the context), `q` (the rows and the clashing pairs) and `B` (the basis).
Checked in Lean: `valid` (closed arithmetic), `heq` (the equations are the rows, modulo
AC), `hclash` (clashing aliens differ, by their top symbols), `hsels` (the listed
selections `sels` include every legal one, by evaluation) and `next`, one premise per
listed selection. -/
theorem acu_solve {Γr : Type w'} (sp : Split El Γ Γr n) (a : Γr → Fin m → El)
    (q : System n m) (B : Basis n m k₀ k₁) (valid : B.Valid q) {es : List (Γ → Prop)}
    (heq : ∀ ρ, Eqs es ρ → q.Holds (sp.V ρ) (a (sp.rest ρ)))
    (hclash : ∀ r, ∀ p ∈ q.clash, a r p.1 ≠ a r p.2)
    (sels : List (Fin k₁ → Bool)) (hsels : ∀ S, B.Legal S = true → S ∈ sels)
    (next : ∀ S ∈ sels,
      (⟨α ∘ fun p => sp.glue p.1 (B.theta (a p.1) S p.2),
        B.pending a S ++ E.map (· ∘ fun p => sp.glue p.1 (B.theta (a p.1) S p.2)),
        D ∘ fun p => sp.glue p.1 (B.theta (a p.1) S p.2)⟩ : State Γ₀ _) ⊩ unifiers) :
    ⟨α, es ++ E, D⟩ ⊩ unifiers := by
  intro ρ hE hD
  rw [eqs_append] at hE
  obtain ⟨S, hS, Z, hX, hpend⟩ :=
    acu_decomp q B valid (sp.V ρ) (a (sp.rest ρ)) (heq ρ hE.1) (hclash (sp.rest ρ))
  have hρ : ρ = sp.glue (sp.rest ρ) (B.theta (a (sp.rest ρ)) S Z) := by
    rw [← hX, sp.hglue]
  have h := next S (hsels S (List.mem_filter.1 hS).2) (sp.rest ρ, Z)
    (by
      rw [eqs_append, eqs_map]
      refine ⟨(eqs_iff _ _).2 fun e he => ?_, by show Eqs E (sp.glue _ _); rw [← hρ]; exact hE.2⟩
      simp only [Basis.pending, List.mem_flatten, List.mem_ofFn] at he
      obtain ⟨_, ⟨t, rfl⟩, he⟩ := he
      simp only [List.mem_flatten, List.mem_ofFn] at he
      obtain ⟨_, ⟨c, rfl⟩, he⟩ := he
      split at he
      · next hc =>
        simp only [List.mem_singleton] at he
        subst he
        exact hpend t hc.1 c hc.2.1
      · simp at he)
    (by change D (sp.glue _ _); rw [← hρ]; exact hD)
  change ∃ σ ∈ unifiers, covers σ (α ρ)
  rw [hρ]
  exact h

/-- Not a rule of the paper: restate the pending equations as `E'`, implied by them. Used
to bring the equations a step works on to the front, and to evaluate `Basis.pending`. -/
theorem restate {s : State Γ₀ Γ} (E' : List (Γ → Prop)) (h : ∀ ρ, Eqs s.E ρ → Eqs E' ρ)
    (next : (⟨s.α, E', s.D⟩ : State Γ₀ Γ) ⊩ unifiers) : s ⊩ unifiers :=
  fun ρ hE hD => next ρ (h ρ hE) hD

end Unification.Certification
