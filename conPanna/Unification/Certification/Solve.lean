import conPanna.Unification.Certification.Multiset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.List.Sublists
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Ring.Basic
import Mathlib.Data.Fin.VecNotation

/-!
The data of SOLVE and its validity, proved once.

One bag equation over bag variables `X : Fin n → ACU El` and alien classes
`a : Fin m → El` is written with coefficients:
  `Σᵢ L i • X i + Σ_c La c • {a c}  =  Σᵢ R i • X i + Σ_c Ra c • {a c}`.
`solve_decomp` shows that every such `X` has the form `θ_π U` for some choice `π`
of particular solutions and fresh bags `U`, given the side conditions S0–S3.
-/

namespace Unification.Certification

open ACU

universe y

variable {El : Type y}

/-! ## Data -/

/-- `k • X`: `k` copies of `X`. -/
def copies : ℕ → ACU El → ACU El
  | 0, _ => ∅
  | k + 1, X => X + copies k X

/-- `Σ_j f j`. -/
def sum {k : ℕ} (f : Fin k → ACU El) : ACU El :=
  (List.ofFn f).foldr (· + ·) ∅

/-- One side of a bag equation: `Σᵢ L i • X i + Σ_c La c • {a c}`. -/
def side {n m : ℕ} (L : Fin n → ℕ) (X : Fin n → ACU El)
    (La : Fin m → ℕ) (a : Fin m → El) : ACU El :=
  sum (fun i => copies (L i) (X i)) + sum (fun c => copies (La c) {a c})

/-- `L · v`. -/
def dot {n : ℕ} (L v : Fin n → ℕ) : ℕ := (List.ofFn fun i => L i * v i).sum

/-- Component-wise `p ≤ v`. -/
def Below {n : ℕ} (p v : Fin n → ℕ) : Prop := ∀ i, p i ≤ v i

/-- All choices of one particular solution per alien class. -/
def choices {n : ℕ} : {m : ℕ} → (Fin m → List (Fin n → ℕ)) → List (Fin m → Fin n → ℕ)
  | 0, _ => [Fin.elim0]
  | _ + 1, P => (P 0).flatMap fun p => (choices (fun c => P c.succ)).map fun π => Matrix.vecCons p π

/-- The substitution `θ_π`: `X i := Σ_c π c i • {a c} + Σ_j B j i • U j`. -/
def theta {n m k : ℕ} (a : Fin m → El) (π : Fin m → Fin n → ℕ)
    (B : Fin k → Fin n → ℕ) (U : Fin k → ACU El) : Fin n → ACU El :=
  fun i => sum (fun c => copies (π c i) {a c}) + sum (fun j => copies (B j i) (U j))

/-- The nonempty cliques of a compatibility relation on alien classes. -/
def cliques {m : ℕ} (cp : Fin m → Fin m → Bool) : List (List (Fin m)) :=
  (List.finRange m).sublists.filter fun G =>
    !G.isEmpty && G.all fun c => G.all fun c' => c == c' || cp c c'

/-! ## Basic facts -/

variable {n m k : ℕ}

theorem sum_succ (f : Fin (k + 1) → ACU El) : sum f = f 0 + sum (fun j => f j.succ) := by
  simp [sum, List.ofFn_succ]

@[simp] theorem toMultiset_copies (j : ℕ) (X : ACU El) :
    (copies j X).toMultiset = j • X.toMultiset := by
  induction j with
  | zero => simp [copies]
  | succ j ih => simp [copies, ih, succ_nsmul, add_comm]

@[simp] theorem toMultiset_sum (f : Fin k → ACU El) :
    (sum f).toMultiset = ∑ j, (f j).toMultiset := by
  induction k with
  | zero => simp [sum]
  | succ k ih => rw [sum_succ, toMultiset_plus, ih, Fin.sum_univ_succ]

theorem dot_eq (L v : Fin n → ℕ) : dot L v = ∑ i, L i * v i := by
  simp [dot, List.sum_ofFn]

theorem dot_add (L u v : Fin n → ℕ) : dot L (u + v) = dot L u + dot L v := by
  simp [dot_eq, mul_add, Finset.sum_add_distrib]

theorem dot_le (L : Fin n → ℕ) {u v : Fin n → ℕ} (h : Below u v) : dot L u ≤ dot L v := by
  simp only [dot_eq]
  exact Finset.sum_le_sum fun i _ => Nat.mul_le_mul_left _ (h i)

theorem dot_sub (L : Fin n → ℕ) {u v : Fin n → ℕ} (h : Below u v) :
    dot L (v - u) = dot L v - dot L u := by
  have : v = (v - u) + u := funext fun i => by simp [Nat.sub_add_cancel (h i)]
  conv_rhs => rw [this, dot_add]
  omega

theorem dot_listSum {α : Type} (L : Fin n → ℕ) (G : List α) (f : α → Fin n → ℕ) :
    dot L (fun i => (G.map fun c => f c i).sum) = (G.map fun c => dot L (f c)).sum := by
  induction G with
  | nil => simp [dot_eq]
  | cons c G ih =>
    have : (fun i => ((c :: G).map fun c => f c i).sum) = f c + fun i => (G.map fun c => f c i).sum := by
      funext i; simp
    rw [this, dot_add, ih]; simp

theorem listSum_ite {α : Type} (l : List α) (p : α → Prop) [DecidablePred p] (f : α → ℕ) :
    (l.map fun c => if p c then f c else 0).sum = ((l.filter p).map f).sum := by
  induction l with
  | nil => rfl
  | cons c l ih => by_cases h : p c <;> simp [List.filter_cons, h, ih]

theorem finSum_eq_list (f : Fin m → ℕ) : ∑ c, f c = ((List.finRange m).map f).sum := by
  rw [← List.sum_ofFn, List.ofFn_eq_map]

theorem mem_choices (P : Fin m → List (Fin n → ℕ)) (π : Fin m → Fin n → ℕ)
    (h : ∀ c, π c ∈ P c) : π ∈ choices P := by
  induction m with
  | zero => simp [choices]; funext c; exact c.elim0
  | succ m ih =>
    simp only [choices, List.mem_flatMap, List.mem_map]
    refine ⟨π 0, h 0, fun c => π c.succ, ih _ _ fun c => h c.succ, ?_⟩
    funext c; cases c using Fin.cases <;> rfl

/-! ## Peeling basis vectors (BASIS) -/

section Peel

variable [DecidableEq El]

/-- The count vector of one element across the bag variables. -/
def counts (x : Fin n → Multiset El) (e : El) : Fin n → ℕ := fun i => (x i).count e

/-- Every multiset solution of a homogeneous system is a combination of basis
vectors with fresh multiset coefficients, if every nonzero solution dominates a
nonzero basis vector and stays a solution after subtracting it. -/
theorem decompose (H : (Fin n → ℕ) → Prop) (B : Fin k → Fin n → ℕ)
    (nonzero : ∀ j, B j ≠ 0)
    (dom : ∀ v, H v → v ≠ 0 → ∃ j, B j ≤ v ∧ H (v - B j))
    (x : Fin n → Multiset El) (hx : ∀ e, H (counts x e)) :
    ∃ U : Fin k → Multiset El, ∀ i, x i = ∑ j, B j i • U j := by
  induction h : ∑ i, Multiset.card (x i) using Nat.strong_induction_on generalizing x with
  | _ N ih =>
  by_cases hz : ∀ i, x i = 0
  · exact ⟨0, fun i => by simp [hz i]⟩
  push_neg at hz
  obtain ⟨i₀, hi₀⟩ := hz
  obtain ⟨e, he⟩ := Multiset.exists_mem_of_ne_zero hi₀
  have hv : counts x e ≠ 0 := fun h0 => by
    have := congrFun h0 i₀
    simp only [counts, Pi.zero_apply, Multiset.count_eq_zero] at this
    exact this he
  obtain ⟨j, hle, hH⟩ := dom _ (hx e) hv
  let x' : Fin n → Multiset El := fun i => x i - Multiset.replicate (B j i) e
  have hrep : ∀ i, Multiset.replicate (B j i) e ≤ x i :=
    fun i => Multiset.le_count_iff_replicate_le.mp (hle i)
  have hx' : ∀ e', H (counts x' e') := by
    intro e'
    by_cases he' : e' = e
    · subst he'
      convert hH using 1
      funext i
      simp [counts, x', Multiset.count_sub]
    · convert hx e' using 1
      funext i
      simp [counts, x', Multiset.count_sub, Multiset.count_replicate, Ne.symm he']
  have hlt : ∑ i, Multiset.card (x' i) < N := by
    rw [← h]
    obtain ⟨i₁, hi₁⟩ := Function.ne_iff.mp (nonzero j)
    apply Finset.sum_lt_sum
    · intro i _
      simp [x', Multiset.card_sub (hrep i)]
    · refine ⟨i₁, Finset.mem_univ _, ?_⟩
      have hc := Multiset.card_le_card (hrep i₁)
      simp only [Multiset.card_replicate] at hc
      simp only [x', Multiset.card_sub (hrep i₁), Multiset.card_replicate]
      simp only [Pi.zero_apply] at hi₁
      omega
  obtain ⟨U', hU'⟩ := ih _ hlt x' hx' rfl
  refine ⟨fun j' => U' j' + if j' = j then {e} else 0, fun i => ?_⟩
  simp only [nsmul_add, Finset.sum_add_distrib, smul_ite, nsmul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, ← hU' i, Multiset.nsmul_singleton, x']
  exact (tsub_add_cancel_of_le (hrep i)).symm

end Peel

/-! ## Validity of SOLVE -/

/-- Every solution of one bag equation has the form `θ_π U`, given the side
conditions. `cp` is the compatibility relation: incompatible classes denote
different elements; S2 is required for every clique of compatible classes. -/
theorem solve_decomp (X : Fin n → ACU El) (a : Fin m → El) (L R : Fin n → ℕ)
    (La Ra : Fin m → ℕ) (cp : Fin m → Fin m → Bool)
    (heq : side L X La a = side R X Ra a)
    (hinc : ∀ c c', c ≠ c' → cp c c' = false → a c ≠ a c')
    (P : Fin m → List (Fin n → ℕ)) (B : Fin k → Fin n → ℕ)
    (S0 : ∀ j, ∃ i, B j i ≠ 0)
    (S1p : ∀ c, ∀ p ∈ P c, dot L p + La c = dot R p + Ra c)
    (S1b : ∀ j, dot L (B j) = dot R (B j))
    (S2 : ∀ G ∈ cliques cp, ∀ v, dot L v + (G.map La).sum = dot R v + (G.map Ra).sum →
      ∃ π : Fin m → Fin n → ℕ, (∀ c ∈ G, π c ∈ P c) ∧
        Below (fun i => (G.map fun c => π c i).sum) v)
    (S3 : ∀ v, dot L v = dot R v → (∃ i, v i ≠ 0) → ∃ j, Below (B j) v) :
    ∃ π ∈ choices P, ∃ U : Fin k → ACU El, X = theta a π B U := by
  classical
  -- The multiset view and the count equation at every element.
  let x : Fin n → Multiset El := fun i => (X i).toMultiset
  let Ge : El → List (Fin m) := fun e => (List.finRange m).filter fun c => e = a c
  have hm := congrArg toMultiset heq
  simp only [side, toMultiset_plus, toMultiset_sum, toMultiset_copies] at hm
  have helem : ∀ e, dot L (counts x e) + ((Ge e).map La).sum =
      dot R (counts x e) + ((Ge e).map Ra).sum := by
    intro e
    have := congrArg (Multiset.count e) hm
    simp only [toMultiset_elem, Multiset.count_add, Multiset.count_sum', Multiset.count_nsmul,
      Multiset.count_singleton, mul_ite, mul_one, mul_zero] at this
    have hG : ∀ f : Fin m → ℕ, ((Ge e).map f).sum = ∑ c, if e = a c then f c else 0 :=
      fun f => by rw [finSum_eq_list, listSum_ite]
    rw [dot_eq, dot_eq, hG, hG]
    exact this
  -- Each nonempty Ge e is a clique.
  have hclique : ∀ e, Ge e ≠ [] → Ge e ∈ cliques cp := by
    intro e hne
    simp only [cliques, List.mem_filter, List.mem_sublists]
    refine ⟨List.filter_sublist, ?_⟩
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff, List.all_eq_true,
      Bool.or_eq_true, beq_iff_eq]
    refine ⟨hne, fun c hc c' hc' => ?_⟩
    by_cases hcc : c = c'
    · exact Or.inl hcc
    · right
      by_contra hf
      simp only [Ge, List.mem_filter, decide_eq_true_eq] at hc hc'
      exact hinc c c' hcc (by simpa using hf) (hc.2.symm.trans hc'.2)
  -- S2 at every element, as a choice function.
  have hS : ∀ e, ∃ π : Fin m → Fin n → ℕ, Ge e ≠ [] →
      (∀ c ∈ Ge e, π c ∈ P c) ∧ Below (fun i => ((Ge e).map fun c => π c i).sum) (counts x e) := by
    intro e
    by_cases hne : Ge e = []
    · exact ⟨fun _ _ => 0, fun h => (h hne).elim⟩
    · obtain ⟨π, h1, h2⟩ := S2 _ (hclique e hne) _ (helem e)
      exact ⟨π, fun _ => ⟨h1, h2⟩⟩
  choose pick hpick using hS
  let π : Fin m → Fin n → ℕ := fun c => pick (a c) c
  have hmemG : ∀ c, c ∈ Ge (a c) := fun c => by simp [Ge]
  have hπP : ∀ c, π c ∈ P c := fun c =>
    (hpick (a c) (List.ne_nil_of_mem (hmemG c))).1 c (hmemG c)
  -- On Ge e, π agrees with pick e.
  have hπG : ∀ e, ∀ c ∈ Ge e, π c = pick e c := by
    intro e c hc
    simp only [Ge, List.mem_filter, decide_eq_true_eq] at hc
    simp [π, ← hc.2]
  -- The particular part Q and its counts.
  let Q : Fin n → Multiset El := fun i => ∑ c, π c i • ({a c} : Multiset El)
  have hQcount : ∀ e i, (Q i).count e = ((Ge e).map fun c => pick e c i).sum := by
    intro e i
    simp only [Q, Multiset.count_sum', Multiset.count_nsmul, Multiset.count_singleton,
      mul_ite, mul_one, mul_zero]
    rw [finSum_eq_list, listSum_ite]
    exact congrArg List.sum (List.map_congr_left fun c hc => congrFun (hπG e c hc) i)
  have hQle : ∀ e, Below (fun i => (Q i).count e) (counts x e) := by
    intro e i
    show (Q i).count e ≤ counts x e i
    rw [hQcount]
    by_cases hne : Ge e = []
    · simp [hne]
    · exact (hpick e hne).2 i
  -- The remainder is homogeneous at every element.
  let Y : Fin n → Multiset El := fun i => x i - Q i
  have hQx : ∀ i, Q i ≤ x i := fun i => Multiset.le_iff_count.mpr fun e => hQle e i
  have hY : ∀ e, dot L (counts Y e) = dot R (counts Y e) := by
    intro e
    have hcY : counts Y e = counts x e - fun i => (Q i).count e := by
      funext i; simp [counts, Y, Multiset.count_sub]
    rw [hcY, dot_sub _ (hQle e), dot_sub _ (hQle e)]
    have hw : (fun i => (Q i).count e) = fun i => ((Ge e).map fun c => pick e c i).sum :=
      funext fun i => hQcount e i
    rw [hw, dot_listSum, dot_listSum]
    have hsum : ((Ge e).map fun c => dot L (pick e c)).sum + ((Ge e).map La).sum =
        ((Ge e).map fun c => dot R (pick e c)).sum + ((Ge e).map Ra).sum := by
      rw [← List.sum_map_add, ← List.sum_map_add]
      congr 1
      refine List.map_congr_left fun c hc => ?_
      have := S1p c (pick e c) (by rw [← hπG e c hc]; exact hπP c)
      exact this
    have hle1 := dot_le L (hQle e)
    have hle2 := dot_le R (hQle e)
    rw [hw, dot_listSum] at hle1
    rw [hw, dot_listSum] at hle2
    have := helem e
    omega
  -- Peel basis vectors from the remainder.
  obtain ⟨U, hU⟩ := decompose (fun v => dot L v = dot R v) B
    (fun j h => by obtain ⟨i, hi⟩ := S0 j; exact hi (congrFun h i))
    (fun v hv hne => by
      have hne' : ∃ i, v i ≠ 0 := by
        by_contra hc; push_neg at hc; exact hne (funext hc)
      obtain ⟨j, hj⟩ := S3 v hv hne'
      refine ⟨j, fun i => hj i, ?_⟩
      have hb : Below (B j) v := hj
      show dot L (v - B j) = dot R (v - B j)
      rw [dot_sub _ hb, dot_sub _ hb, hv, S1b j])
    Y hY
  refine ⟨π, mem_choices P π hπP, fun j => ofMultiset (U j), funext fun i => ?_⟩
  rw [eq_iff]
  simp only [theta, toMultiset_plus, toMultiset_sum, toMultiset_copies, toMultiset_elem,
    toMultiset_ofMultiset, ← hU i, Multiset.nsmul_singleton]
  show x i = _
  simp only [← Multiset.nsmul_singleton]
  exact (add_tsub_cancel_of_le (hQx i)).symm

theorem mem_of_choices {P : Fin m → List (Fin n → ℕ)} {π : Fin m → Fin n → ℕ}
    (h : π ∈ choices P) : ∀ c, π c ∈ P c := by
  induction m with
  | zero => intro c; exact c.elim0
  | succ m ih =>
    simp only [choices, List.mem_flatMap, List.mem_map] at h
    obtain ⟨p, hp, π', hπ', rfl⟩ := h
    intro c
    cases c using Fin.cases with
    | zero => simpa using hp
    | succ c => simpa using ih hπ' c

/-- S2 stated over the finite list of choices: the form a certificate proves,
since it unfolds to a closed Presburger formula. -/
theorem S2_of_choices (cp : Fin m → Fin m → Bool) (L R : Fin n → ℕ) (La Ra : Fin m → ℕ)
    (P : Fin m → List (Fin n → ℕ))
    (h : ∀ G ∈ cliques cp, ∀ v, dot L v + (G.map La).sum = dot R v + (G.map Ra).sum →
      ∃ π ∈ choices P, Below (fun i => (G.map fun c => π c i).sum) v) :
    ∀ G ∈ cliques cp, ∀ v, dot L v + (G.map La).sum = dot R v + (G.map Ra).sum →
      ∃ π : Fin m → Fin n → ℕ, (∀ c ∈ G, π c ∈ P c) ∧
        Below (fun i => (G.map fun c => π c i).sum) v := by
  intro G hG v hv
  obtain ⟨π, hπ, hb⟩ := h G hG v hv
  exact ⟨π, fun c _ => mem_of_choices hπ c, hb⟩

/-- All ways of picking one element from each list. -/
def prodL {α : Type} : List (List α) → List (List α)
  | [] => [[]]
  | l :: ls => l.flatMap fun x => (prodL ls).map (x :: ·)

/-- The component-wise sum of a list of vectors. -/
def vsum (ps : List (Fin n → ℕ)) : Fin n → ℕ := fun i => (ps.map (· i)).sum

/-- A pick from the lists `P c` (`c ∈ G`) is a choice function on `G`. -/
theorem choice_of_prodL [DecidableEq (Fin m)] (P : Fin m → List (Fin n → ℕ)) :
    ∀ (G : List (Fin m)), G.Nodup → ∀ ps ∈ prodL (G.map P),
      ∃ π : Fin m → Fin n → ℕ, (∀ c ∈ G, π c ∈ P c) ∧
        ∀ i, (G.map fun c => π c i).sum = vsum ps i
  | [], _, ps, hps => by
    simp only [List.map_nil, prodL, List.mem_singleton] at hps
    subst hps
    exact ⟨fun _ _ => 0, by simp, fun i => by simp [vsum]⟩
  | c :: G, hnd, ps, hps => by
    simp only [List.map_cons, prodL, List.mem_flatMap, List.mem_map] at hps
    obtain ⟨p, hp, ps', hps', rfl⟩ := hps
    have hc : c ∉ G := (List.nodup_cons.mp hnd).1
    obtain ⟨π, hπ, hsum⟩ := choice_of_prodL P G (List.nodup_cons.mp hnd).2 ps' hps'
    refine ⟨Function.update π c p, fun c' hc' => ?_, fun i => ?_⟩
    · rcases List.mem_cons.mp hc' with rfl | h
      · simpa using hp
      · have hne : c' ≠ c := fun e => hc (e ▸ h)
        rw [Function.update_of_ne hne]; exact hπ c' h
    · have : (G.map fun c' => Function.update π c p c' i) = G.map fun c' => π c' i :=
        List.map_congr_left fun c' h => by
          have hne : c' ≠ c := fun e => hc (e ▸ h)
          rw [Function.update_of_ne hne]
      simp only [List.map_cons, List.sum_cons, Function.update_self, this, hsum, vsum]

/-- S2 over an explicit list of cliques, each stated as a closed Presburger
formula over the sums of picks from the clique's particular solutions: the
form a certificate states. -/
theorem S2_of_list (cp : Fin m → Fin m → Bool) (L R : Fin n → ℕ) (La Ra : Fin m → ℕ)
    (P : Fin m → List (Fin n → ℕ)) (Gs : List (List (Fin m))) (hGs : ∀ G ∈ cliques cp, G ∈ Gs)
    (h : ∀ G ∈ Gs, ∀ v, dot L v + (G.map La).sum = dot R v + (G.map Ra).sum →
      ∃ ps ∈ prodL (G.map P), Below (vsum ps) v) :
    ∀ G ∈ cliques cp, ∀ v, dot L v + (G.map La).sum = dot R v + (G.map Ra).sum →
      ∃ π : Fin m → Fin n → ℕ, (∀ c ∈ G, π c ∈ P c) ∧
        Below (fun i => (G.map fun c => π c i).sum) v := by
  intro G hG v hv
  obtain ⟨ps, hps, hb⟩ := h G (hGs G hG) v hv
  have hnd : G.Nodup := by
    simp only [cliques, List.mem_filter, List.mem_sublists] at hG
    exact (List.nodup_finRange m).sublist hG.1
  obtain ⟨π, hπ, hsum⟩ := choice_of_prodL P G hnd ps hps
  exact ⟨π, hπ, fun i => by show (G.map fun c => π c i).sum ≤ v i; rw [hsum]; exact hb i⟩

/-- S2 for an all-incompatible relation reduces to one class at a time. -/
theorem S2_single (L R : Fin n → ℕ) (La Ra : Fin m → ℕ) (P : Fin m → List (Fin n → ℕ))
    (h : ∀ c v, dot L v + La c = dot R v + Ra c → ∃ p ∈ P c, Below p v) :
    ∀ G ∈ cliques (fun _ _ => false), ∀ v, dot L v + (G.map La).sum = dot R v + (G.map Ra).sum →
      ∃ π : Fin m → Fin n → ℕ, (∀ c ∈ G, π c ∈ P c) ∧
        Below (fun i => (G.map fun c => π c i).sum) v := by
  intro G hG v hv
  simp only [cliques, List.mem_filter, List.mem_sublists, Bool.and_eq_true, Bool.not_eq_true',
    List.isEmpty_eq_false_iff, List.all_eq_true, Bool.or_false, beq_iff_eq] at hG
  obtain ⟨hsub, hne, hall⟩ := hG
  obtain ⟨c, hc⟩ := List.exists_mem_of_ne_nil G hne
  have hnd : G.Nodup := (List.nodup_finRange m).sublist (by assumption)
  have heq : ∀ c' ∈ G, c' = c := fun c' hc' => by simpa using hall c' hc' c hc
  have hG : G = [c] := by
    match G, hnd, heq, hc with
    | [], _, _, hc => simp at hc
    | d :: G', hnd, heq, _ =>
      have hd := heq d (by simp)
      subst hd
      cases G' with
      | nil => rfl
      | cons d' G'' =>
        have := heq d' (by simp)
        subst this
        simp at hnd
  subst hG
  obtain ⟨p, hp, hb⟩ := h c v (by simpa using hv)
  exact ⟨fun _ => p, by simpa using hp, fun i => by simpa using hb i⟩

end Unification.Certification
