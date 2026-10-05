import conPanna.Certification.Core

/-! General finite-sharing arithmetic and its semantic proof. -/

namespace DirectCertification
open Structural.Indexed
variable {Sorts : Type} {sig : Signature Sorts}
variable (profile : Profile sig)
namespace FiniteSharing
/-!
## General multiplicity lemmas for the future FiniteSharing rule

This is a once-for-all PROOF auxiliary, not a Diophantine search backend,
a user registration interface, or a claim that ACU certification is complete.
For one atom class, a bag assignment induces a vector of multiplicities.
The balance coefficients retain repeated occurrences of the original variables.

The two established steps are:
  Balanced(v) ==> v = m1 + ... + mk, with every mi minimal and nonzero.
  Every minimal vector belongs to G, and every vector in G is balanced
  ==================================================================
                   Balanced(v) <==> Generated(G,v)

Below, boolean_supports_exact proves the numerical exactness: every balanced
active vector is a sum of nonempty Boolean support degrees, and every such sum
is balanced. Minimal occurrence-level rounding is fully proved, not assumed.
supportGenerators_exact additionally proves exactness of the EXECUTABLE exhaustive
support list. bags_generated and finiteSharing_native lift this to tree/native
bag images. Sharing generates typed open substitutions and checked replay nodes.
General certificate search remains pending.

The decomposition uses classical existence and strong induction. It is not
executable certificate search, and no domain constraints or Bakery symbols
occur in the statements.
-/

abbrev Vector (n : Nat) := Fin n → Nat
def zeroVector {n} : Vector n := fun _ => 0
def plus {n} (v w : Vector n) : Vector n := fun i => v i + w i
def minus {n} (v w : Vector n) : Vector n := fun i => v i - w i
def Below {n} (v w : Vector n) : Prop := ∀ i, v i ≤ w i
def size : {n : Nat} → Vector n → Nat
  | 0, _ => 0
  | _ + 1, v => v 0 + size (fun i => v i.succ)
theorem size_zero (n : Nat) : size (zeroVector (n := n)) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [size, zeroVector] using ih
theorem size_plus {n} (v w : Vector n) :
    size (plus v w) = size v + size w := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [size, plus]
    have ht := ih (fun i => v i.succ) (fun i => w i.succ)
    change size (fun i => v i.succ + w i.succ) = _ at ht
    rw [ht]
    omega
theorem size_mono {n} {v w : Vector n} (h : Below v w) : size v ≤ size w := by
  induction n with
  | zero => exact Nat.le_refl _
  | succ n ih =>
    exact Nat.add_le_add (h 0) (ih (fun i => h i.succ))
theorem eq_of_below_size_eq {n} {v w : Vector n}
    (h : Below v w) (hs : size v = size w) : v = w := by
  induction n with
  | zero => funext i; exact Fin.elim0 i
  | succ n ih =>
    have ht : size (fun i => v i.succ) ≤ size (fun i => w i.succ) :=
      size_mono (fun i => h i.succ)
    have h0 := h 0
    simp only [size] at hs
    have first : v 0 = w 0 := by omega
    have tail : size (fun i => v i.succ) = size (fun i => w i.succ) := by omega
    have same := ih (fun i => h i.succ) tail
    funext i
    exact Fin.cases first (fun j => congrFun same j) i
theorem size_pos {n} {v : Vector n} (h : v ≠ zeroVector) : 0 < size v := by
  apply Nat.pos_of_ne_zero
  intro hs
  have same : zeroVector = v :=
    eq_of_below_size_eq (fun _ => Nat.zero_le _) ((size_zero n).trans hs.symm)
  exact h same.symm
theorem split_below {n} {w v : Vector n} (h : Below w v) :
    v = plus w (minus v w) :=
  funext fun i => (Nat.add_sub_of_le (h i)).symm
def dot {n} (coeff v : Vector n) : Nat := size (fun i => coeff i * v i)
def Balanced {n} (left right v : Vector n) : Prop := dot left v = dot right v
theorem dot_plus {n} (coeff v w : Vector n) :
    dot coeff (plus v w) = dot coeff v + dot coeff w := by
  unfold dot plus
  simp only [Nat.mul_add]
  exact size_plus _ _
theorem balanced_minus {n} {left right v w : Vector n}
    (hv : Balanced left right v) (hw : Balanced left right w) (hle : Below w v) :
    Balanced left right (minus v w) := by
  unfold Balanced at *
  rw [split_below hle, dot_plus, dot_plus, hw] at hv
  exact Nat.add_left_cancel hv
/-- Minimality is componentwise: there is no smaller nonzero balanced vector.
Zero is deliberately excluded; the empty decomposition accounts for it. -/
def Minimal {n} (left right v : Vector n) : Prop :=
  v ≠ zeroVector ∧ Balanced left right v ∧
    ∀ w, Below w v → Balanced left right w → w ≠ zeroVector → w = v
def total {n} : List (Vector n) → Vector n
  | [] => zeroVector
  | v :: rest => plus v (total rest)
theorem total_append {n} (xs ys : List (Vector n)) :
    total (xs ++ ys) = plus (total xs) (total ys) := by
  induction xs with
  | nil => funext i; simp [total, plus, zeroVector]
  | cons x xs ih =>
    simp only [List.cons_append, total, ih]
    funext i
    exact (Nat.add_assoc _ _ _).symm
/-- Every balance solution is a finite sum of minimal balance solutions.
Split off a proper balanced subvector when one exists. Both summands have
strictly smaller total multiplicity, so the induction retains every solution.
No positivity or linearity restriction on the coefficient vectors is needed. -/
theorem decompose_minimal {n} (left right v : Vector n) (hv : Balanced left right v) :
    ∃ parts : List (Vector n),
      (∀ w ∈ parts, Minimal left right w) ∧ total parts = v := by
  classical
  refine Nat.strongRecOn (motive := fun k => ∀ v : Vector n,
    size v = k → Balanced left right v →
      ∃ parts : List (Vector n),
        (∀ w ∈ parts, Minimal left right w) ∧ total parts = v)
    (size v) ?_ v rfl hv
  intro k ih current hk hc
  by_cases hz : current = zeroVector
  · exact ⟨[], fun _ h => False.elim (List.not_mem_nil h), hz.symm⟩
  by_cases smaller : ∃ w, Below w current ∧ Balanced left right w ∧
      w ≠ zeroVector ∧ w ≠ current
  · obtain ⟨w, hle, hw, hnz, hne⟩ := smaller
    have wlt : size w < k := by
      have hleSize := size_mono hle
      have hneSize : size w ≠ size current :=
        fun h => hne (eq_of_below_size_eq hle h)
      have hlt := Nat.lt_of_le_of_ne hleSize hneSize
      omega
    have sumSplit : size current = size w + size (minus current w) := by
      exact (congrArg size (split_below hle)).trans (size_plus _ _)
    have dlt : size (minus current w) < k := by
      have positive := size_pos hnz
      omega
    obtain ⟨ws, hws, ews⟩ := ih (size w) wlt w rfl hw
    obtain ⟨ds, hds, eds⟩ := ih (size (minus current w)) dlt
      (minus current w) rfl (balanced_minus hc hw hle)
    refine ⟨ws ++ ds, ?_, ?_⟩
    · intro u member
      rcases List.mem_append.mp member with member | member
      · exact hws u member
      · exact hds u member
    · rw [total_append, ews, eds]
      exact (split_below hle).symm
  · refine ⟨[current], ?_, ?_⟩
    · intro w member
      have same : w = current := by simpa using member
      subst w
      refine ⟨hz, hc, ?_⟩
      intro w hle hw hnz
      exact Classical.byContradiction (fun hne => smaller ⟨w, hle, hw, hnz, hne⟩)
    · funext i
      simp [total, plus, zeroVector]


def Generated {n} (generators : List (Vector n)) (v : Vector n) : Prop :=
  ∃ parts : List (Vector n), (∀ w ∈ parts, w ∈ generators) ∧ total parts = v
theorem balanced_zero {n} (left right : Vector n) :
    Balanced left right zeroVector := by
  unfold Balanced dot zeroVector
  simp only [Nat.mul_zero]
theorem balanced_plus {n} {left right v w : Vector n}
    (hv : Balanced left right v) (hw : Balanced left right w) :
    Balanced left right (plus v w) := by
  unfold Balanced at *
  rw [dot_plus, dot_plus, hv, hw]
theorem total_balanced {n} (left right : Vector n) (parts : List (Vector n))
    (h : ∀ w ∈ parts, Balanced left right w) :
    Balanced left right (total parts) := by
  induction parts with
  | nil => exact balanced_zero left right
  | cons w rest ih =>
    exact balanced_plus (h w (List.mem_cons_self))
      (ih (fun u hu => h u (List.mem_cons_of_mem w hu)))
theorem generated_of_minimal_coverage {n} (left right : Vector n)
    (generators : List (Vector n))
    (covers : ∀ w, Minimal left right w → w ∈ generators)
    {v : Vector n} (hv : Balanced left right v) : Generated generators v := by
  obtain ⟨parts, minimal, sum⟩ := decompose_minimal left right v hv
  exact ⟨parts, fun w member => covers w (minimal w member), sum⟩
/-- General reduction of exact generation to coverage of minimal vectors.
The hypotheses are proof obligations for the GENERAL grid metatheorem, not
a per-model registration or a certificate supplied by the user/Maude. -/
theorem generated_iff_balanced {n} (left right : Vector n)
    (generators : List (Vector n))
    (sound : ∀ w ∈ generators, Balanced left right w)
    (covers : ∀ w, Minimal left right w → w ∈ generators)
    (v : Vector n) : Generated generators v ↔ Balanced left right v := by
  constructor
  · rintro ⟨parts, member, rfl⟩
    exact total_balanced left right parts (fun w hw => sound w (member w hw))
  · exact generated_of_minimal_coverage left right generators covers

/-!
### Minimal vectors and finite sharing capacities

The next lemmas retain the arbitrary coefficients and variable repetitions.
A transport matrix distributes the weighted multiplicities from left variables
to right variables. It has the required row/column totals, without any bound
on the size of the input problem.

If a minimal vector had BOTH v_i > b_j and v_j > a_i, the elementary solution
    X_i := b_j, Y_j := a_i, all other variables := 0
would be a proper nonzero balanced subvector. Minimality forbids this.
Consequently each transport block is bounded by a_i*b_j, exactly the number
of cells between the occurrences of those two variables.

IMPORTANT: bounded block totals alone do not prove that individual occurrence
rows have equal degrees. The later Boolean-grid section proves that stronger
representation separately; none of the capacity lemmas silently assume it.

The repair argument for that final theorem is:
* Expand the variable labels to occurrence rows/columns with degrees v_i/v_j.
  The transport existence lemma gives a natural-entry matrix with these margins.
* Suppose a cell (u,z) contains a >= 2. Minimality gives either rowDegree(u)
  <= number of columns with z's label, or the transposed inequality.
* In the first case, some column z' with the same label has entry 0 in row u.
  Its column total equals that of z, so some other row u' has
  d := M[u',z'] > c := M[u',z].
* Replace the rectangle (a,0;c,d) by (a-1,1;c+1,d-1). Margins are unchanged;
  switch_cost_lt proves its squared-entry cost strictly decreases.
* Use strong induction on the whole matrix's squared-entry cost. Eventually
  every cell is 0 or 1, and its selected cells preserve every occurrence margin.
  boolean_transport_exists proves this argument in Lean below.

Matrix rounding, exhaustive support enumeration, and native bag instantiation
are now proved below. Typed replay is connected; general search remains pending. No new
search control or user registration is introduced by these metatheorems.
-/

def spike {n} (index : Fin n) (value : Nat) : Vector n :=
  fun i => if i = index then value else 0

theorem size_spike {n} (index : Fin n) (value : Nat) : size (spike index value) = value := by
  induction n with
  | zero => exact Fin.elim0 index
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) index
    · have tail : (fun i : Fin n => spike (0 : Fin (n+1)) value i.succ) = zeroVector := by
        funext i
        simp [spike, zeroVector, Fin.succ_ne_zero]
      change spike (0 : Fin (n+1)) value 0 + size _ = value
      rw [tail, size_zero]
      simp [spike]
    · have tail : (fun i : Fin n => spike j.succ value i.succ) = spike j value := by
        funext i
        simp [spike, Fin.succ_inj]
      change spike j.succ value 0 + size _ = value
      rw [tail, ih j]
      simp [spike, Ne.symm (Fin.succ_ne_zero j)]

theorem dot_spike {n} (coeff : Vector n) (index : Fin n) (value : Nat) :
    dot coeff (spike index value) = coeff index * value := by
  have image : (fun i => coeff i * spike index value i) = spike index (coeff index * value) := by
    funext i
    by_cases hi : i = index
    · subst i; simp [spike]
    · simp [spike, hi]
  unfold dot
  rw [image]
  exact size_spike _ _

def pairVector {n} (left right : Vector n) (i j : Fin n) : Vector n :=
  plus (spike i (right j)) (spike j (left i))

theorem pair_balanced {n} (left right : Vector n) (i j : Fin n)
    (hi : right i = 0) (hj : left j = 0) :
    Balanced left right (pairVector left right i j) := by
  unfold Balanced pairVector
  rw [dot_plus, dot_plus, dot_spike, dot_spike, dot_spike, dot_spike, hi, hj]
  simp only [Nat.zero_mul, Nat.add_zero, Nat.zero_add]
  exact Nat.mul_comm _ _

/-- Opposite-side minimal multiplicities cannot both exceed the elementary
two-variable solution. The hypotheses locate two distinct variable indices
after cancellation; no occurrence is treated as an independent variable. -/
theorem minimal_pair_bound {n} {left right v : Vector n} (minimal : Minimal left right v)
    (i j : Fin n) (hr : 0 < right j)
    (hi : right i = 0) (hj : left j = 0) :
    v i ≤ right j ∨ v j ≤ left i := by
  classical
  have different : i ≠ j := by
    intro same
    subst j
    omega
  by_cases first : v i ≤ right j
  · exact Or.inl first
  by_cases second : v j ≤ left i
  · exact Or.inr second
  have below : Below (pairVector left right i j) v := by
    intro k
    by_cases ki : k = i
    · subst k
      simp [pairVector, plus, spike, different]
      omega
    by_cases kj : k = j
    · subst k
      simp [pairVector, plus, spike, Ne.symm different]
      omega
    · simp [pairVector, plus, spike, ki, kj]
  have nonzero : pairVector left right i j ≠ zeroVector := by
    intro equal
    have atI := congrFun equal i
    simp [pairVector, plus, spike, zeroVector, different] at atI
    omega
  have same := minimal.2.2 (pairVector left right i j) below (pair_balanced left right i j hi hj) nonzero
  have atI := congrFun same i
  simp [pairVector, plus, spike, different] at atI
  omega

/-- One rectangle exchange strictly decreases squared-entry cost. The zero
entry is explicit in the formula; the other diagonal entry d exceeds c.
This is a general arithmetic metatheorem, not problem-specific automation. -/
theorem switch_cost_lt (a c d : Nat) (ha : 2 ≤ a) (hd : c < d) :
    (a-1)*(a-1) + 1 + (c+1)*(c+1) + (d-1)*(d-1) <
      a*a + c*c + d*d := by
  obtain ⟨x, rfl⟩ := Nat.exists_eq_add_of_le ha
  obtain ⟨y, rfl⟩ := Nat.exists_eq_add_of_le (Nat.succ_le_of_lt hd)
  simp only [Nat.succ_eq_add_one]
  have hx : 2 + x - 1 = 1 + x := by omega
  have hy : c + 1 + y - 1 = c + y := by omega
  simp only [hx, hy, Nat.mul_add, Nat.mul_comm]
  omega



theorem size_split {n} {small large : Vector n} (h : Below small large) :
    size large = size small + size (minus large small) :=
  (congrArg size (split_below h)).trans (size_plus _ _)

theorem coordinate_le_size {n} (v : Vector n) (index : Fin n) : v index ≤ size v := by
  have below : Below (spike index (v index)) v := by
    intro i
    by_cases same : i = index
    · subst i; simp [spike]
    · simp [spike, same]
  have bound := size_mono below
  rw [size_spike] at bound
  exact bound

/-- Allocate any requested amount no larger than the available finite total. -/
theorem allocate {n} (available : Vector n) (amount : Nat) (h : amount ≤ size available) :
    ∃ chosen : Vector n, Below chosen available ∧ size chosen = amount := by
  induction n generalizing amount with
  | zero =>
    exact ⟨zeroVector, fun i => Fin.elim0 i, by simpa [size] using (Nat.eq_zero_of_le_zero h).symm⟩
  | succ n ih =>
    by_cases fits : amount ≤ available 0
    · refine ⟨spike 0 amount, ?_, size_spike _ _⟩
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa [spike] using fits
      · simp [spike, Fin.succ_ne_zero]
    · have remaining : amount - available 0 ≤ size (fun i => available i.succ) := by
        simp only [size] at h
        omega
      obtain ⟨tail, below, enough⟩ := ih (fun i => available i.succ)
        (amount - available 0) remaining
      refine ⟨Fin.cases (available 0) tail, ?_, ?_⟩
      · intro i
        exact Fin.cases (Nat.le_refl _) (fun j => below j) i
      · change available 0 + size tail = amount
        rw [enough]
        omega

abbrev Matrix (rows cols : Nat) := Fin rows → Fin cols → Nat

/-- Every pair of finite natural margin vectors with equal totals admits a
transport matrix. The proof fills one row and recurses, retaining all margins. -/
theorem transport_exists {rows cols} (rowTotals : Vector rows) (colTotals : Vector cols)
    (same : size rowTotals = size colTotals) :
    ∃ matrix : Matrix rows cols,
      (∀ i, size (matrix i) = rowTotals i) ∧
      (∀ j, size (fun i => matrix i j) = colTotals j) := by
  induction rows generalizing colTotals with
  | zero =>
    have allZero : colTotals = zeroVector :=
      (eq_of_below_size_eq (fun _ => Nat.zero_le _)
        ((size_zero cols).trans same)).symm
    refine ⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i, ?_⟩
    intro j
    rw [allZero]
    rfl
  | succ rows ih =>
    have enough : rowTotals 0 ≤ size colTotals := by
      simp only [size] at same
      omega
    obtain ⟨first, below, firstTotal⟩ := allocate colTotals (rowTotals 0) enough
    have remaining : size (fun i => rowTotals i.succ) = size (minus colTotals first) := by
      have split := size_split below
      simp only [size] at same
      omega
    obtain ⟨rest, restRows, restCols⟩ := ih (fun i => rowTotals i.succ)
      (minus colTotals first) remaining
    refine ⟨Fin.cases first rest, ?_, ?_⟩
    · intro i
      exact Fin.cases firstTotal (fun j => restRows j) i
    · intro j
      change first j + size (fun i => rest i j) = colTotals j
      rw [restCols]
      exact Nat.add_sub_of_le (below j)

/-- Syntactic cancellation puts each active variable on at most one side.
Variables canceled completely are handled separately as passthrough parameters. -/
def Disjoint {n} (left right : Vector n) : Prop :=
  ∀ i, left i = 0 ∨ right i = 0

/-- General finite-capacity transport for ANY minimal balance vector.
This proves the variable-pair bounds, NOT yet Boolean occurrence-grid coverage. -/
theorem minimal_bounded_transport {n} {left right v : Vector n}
    (disjoint : Disjoint left right) (minimal : Minimal left right v) :
    ∃ matrix : Matrix n n,
      (∀ i, size (matrix i) = left i * v i) ∧
      (∀ j, size (fun i => matrix i j) = right j * v j) ∧
      (∀ i j, matrix i j ≤ left i * right j) := by
  obtain ⟨matrix, rows, cols⟩ := transport_exists
    (fun i => left i * v i) (fun j => right j * v j) minimal.2.1
  refine ⟨matrix, rows, cols, ?_⟩
  intro i j
  have rowBound : matrix i j ≤ left i * v i :=
    by rw [← rows i]; exact coordinate_le_size (matrix i) j
  have colBound : matrix i j ≤ right j * v j :=
    by rw [← cols j]; exact coordinate_le_size (fun k => matrix k j) i
  by_cases li : left i = 0
  · simpa [li] using rowBound
  by_cases rj : right j = 0
  · simpa [rj] using colBound
  have hr : 0 < right j := Nat.pos_of_ne_zero rj
  have ri : right i = 0 := (disjoint i).resolve_left li
  have lj : left j = 0 := (disjoint j).resolve_right rj
  rcases minimal_pair_bound minimal i j hr ri lj with first | second
  · exact Nat.le_trans rowBound (Nat.mul_le_mul_left (left i) first)
  · exact Nat.le_trans colBound (by simpa [Nat.mul_comm] using Nat.mul_le_mul_left (right j) second)

/-! ### Boolean occurrence-grid rounding (CERTIFICATION.md, Lemma 5.4)

The lemmas below work on arbitrary finite matrices. A row/column total records
the multiplicity of its variable, not an independently chosen occurrence.
Rectangle exchanges preserve ALL margins and strictly decrease squared cost.
No coefficient bound, linearity assumption, Bakery symbol, or solver is used.
-/

private def erase {n} (v : Vector n) (index : Fin n) : Vector n :=
  fun i => if i = index then 0 else v i

theorem size_erase {n} (v : Vector n) (index : Fin n) :
    size v = v index + size (erase v index) := by
  have split : v = plus (spike index (v index)) (erase v index) := by
    funext i
    by_cases same : i = index
    · subst i; simp [plus, spike, erase]
    · simp [plus, spike, erase, same]
  have sum := congrArg size split
  simpa only [size_plus, size_spike] using sum

/-- Compare finite sums when exactly two coordinates may change. The additive
form avoids assuming that subtraction commutes with finite sums. -/
theorem size_compare_pair {n} (v w : Vector n) (i j : Fin n)
    (different : i ≠ j) (outside : ∀ k, k ≠ i → k ≠ j → v k = w k) :
    size w + v i + v j = size v + w i + w j := by
  have same : erase (erase v i) j = erase (erase w i) j := by
    funext k
    by_cases first : k = i
    · subst k; simp [erase]
    by_cases second : k = j
    · subst k; simp [erase]
    · simp [erase, first, second, outside k first second]
  have hv := size_erase v i
  have hw := size_erase w i
  have hv' := size_erase (erase v i) j
  have hw' := size_erase (erase w i) j
  simp only [erase, if_neg (Ne.symm different)] at hv' hw'
  rw [same] at hv'
  omega

theorem size_strict {n} {v w : Vector n} (below : Below v w)
    (index : Fin n) (strict : v index < w index) : size v < size w := by
  have bound := size_mono below
  have different : size v ≠ size w := by
    intro same
    have values := congrFun (eq_of_below_size_eq below same) index
    omega
  omega

def transpose {rows cols} (matrix : Matrix rows cols) : Matrix cols rows :=
  fun j i => matrix i j

def Margins {rows cols} (matrix : Matrix rows cols)
    (rowTotals : Vector rows) (colTotals : Vector cols) : Prop :=
  (∀ i, size (matrix i) = rowTotals i) ∧
  (∀ j, size (fun i => matrix i j) = colTotals j)

def cost {rows cols} (matrix : Matrix rows cols) : Nat :=
  size (fun i => size (fun j => matrix i j * matrix i j))

theorem size_swap {rows cols} (matrix : Matrix rows cols) :
    size (fun i => size (matrix i)) = size (fun j => size (fun i => matrix i j)) := by
  induction rows with
  | zero =>
    change 0 = size (zeroVector (n := cols))
    exact (size_zero cols).symm
  | succ rows ih =>
    change size (matrix 0) + size (fun i => size (matrix i.succ)) =
      size (fun j => matrix 0 j + size (fun i => matrix i.succ j))
    rw [ih]
    exact (size_plus (matrix 0) (fun j => size (fun i => matrix i.succ j))).symm

theorem cost_transpose {rows cols} (matrix : Matrix rows cols) :
    cost (transpose matrix) = cost matrix :=
  (size_swap (fun i j => matrix i j * matrix i j)).symm

theorem zero_in_column_class {rows cols} (matrix : Matrix rows cols)
    (colTotals : Vector cols) (r : Fin rows) (c : Fin cols)
    (bound : size (matrix r) ≤ size (fun j => if colTotals j = colTotals c then 1 else 0))
    (large : 2 ≤ matrix r c) :
    ∃ c', colTotals c' = colTotals c ∧ matrix r c' = 0 := by
  classical
  apply Classical.byContradiction
  intro none
  have below : Below (fun j => if colTotals j = colTotals c then 1 else 0) (matrix r) := by
    intro j
    by_cases same : colTotals j = colTotals c
    · have positive : matrix r j ≠ 0 := fun zero => none ⟨j, same, zero⟩
      simp only [if_pos same]
      omega
    · simp [same]
  have strict := size_strict below c (by simp; omega)
  omega

theorem crossing_row {rows cols} (matrix : Matrix rows cols)
    (r : Fin rows) (c c' : Fin cols)
    (same : size (fun i => matrix i c) = size (fun i => matrix i c'))
    (strict : matrix r c' < matrix r c) :
    ∃ r', matrix r' c < matrix r' c' := by
  classical
  apply Classical.byContradiction
  intro none
  have below : Below (fun i => matrix i c') (fun i => matrix i c) := by
    intro i
    change matrix i c' ≤ matrix i c
    have notLess : ¬ matrix i c < matrix i c' := fun lt => none ⟨i, lt⟩
    omega
  have smaller := size_strict below r strict
  omega

/-- One rectangle exchange: (A,0;C,D) becomes (A-1,1;C+1,D-1). -/
def rectangle {rows cols} (matrix : Matrix rows cols)
    (r r' : Fin rows) (c c' : Fin cols) : Matrix rows cols :=
  fun i j => if i = r then
    if j = c then matrix i j - 1 else if j = c' then matrix i j + 1 else matrix i j
  else if i = r' then
    if j = c then matrix i j + 1 else if j = c' then matrix i j - 1 else matrix i j
  else matrix i j

theorem rectangle_improves {rows cols} (matrix : Matrix rows cols)
    (r r' : Fin rows) (c c' : Fin cols)
    (large : 2 ≤ matrix r c) (empty : matrix r c' = 0)
    (cross : matrix r' c < matrix r' c') :
    (∀ i, size (rectangle matrix r r' c c' i) = size (matrix i)) ∧
    (∀ j, size (fun i => rectangle matrix r r' c c' i j) = size (fun i => matrix i j)) ∧
    cost (rectangle matrix r r' c c') < cost matrix := by
  have dr : r ≠ r' := by intro same; subst r'; omega
  have dc : c ≠ c' := by intro same; subst c'; omega
  have at₁ : rectangle matrix r r' c c' r c = matrix r c - 1 := by simp [rectangle]
  have at₂ : rectangle matrix r r' c c' r c' = 1 := by simp [rectangle, Ne.symm dc, empty]
  have at₃ : rectangle matrix r r' c c' r' c = matrix r' c + 1 := by
    simp [rectangle, Ne.symm dr]
  have at₄ : rectangle matrix r r' c c' r' c' = matrix r' c' - 1 := by
    simp [rectangle, Ne.symm dr, Ne.symm dc]
  have row₁ := size_compare_pair (matrix r) (rectangle matrix r r' c c' r) c c' dc
    (fun j first second => by simp [rectangle, first, second])
  have row₂ := size_compare_pair (matrix r') (rectangle matrix r r' c c' r') c c' dc
    (fun j first second => by simp [rectangle, first, second])
  have col₁ := size_compare_pair (fun i => matrix i c)
    (fun i => rectangle matrix r r' c c' i c) r r' dr
    (fun i first second => by simp [rectangle, first, second])
  have col₂ := size_compare_pair (fun i => matrix i c')
    (fun i => rectangle matrix r r' c c' i c') r r' dr
    (fun i first second => by simp [rectangle, first, second])
  dsimp only at row₁ row₂ col₁ col₂
  rw [at₁, at₂, empty] at row₁
  rw [at₃, at₄] at row₂
  rw [at₁, at₃] at col₁
  rw [at₂, at₄, empty] at col₂
  refine ⟨?_, ?_, ?_⟩
  · intro i
    by_cases first : i = r
    · subst i; omega
    by_cases second : i = r'
    · subst i; omega
    · have unchanged : rectangle matrix r r' c c' i = matrix i := by
        funext j
        simp [rectangle, first, second]
      exact congrArg size unchanged
  · intro j
    by_cases first : j = c
    · subst j; omega
    by_cases second : j = c'
    · subst j; omega
    · have unchanged : (fun i => rectangle matrix r r' c c' i j) = (fun i => matrix i j) := by
        funext i
        simp [rectangle, first, second]
      exact congrArg size unchanged
  · have squares₁ := size_compare_pair (fun j => matrix r j * matrix r j)
      (fun j => rectangle matrix r r' c c' r j * rectangle matrix r r' c c' r j) c c' dc
      (fun j first second => by simp [rectangle, first, second])
    have squares₂ := size_compare_pair (fun j => matrix r' j * matrix r' j)
      (fun j => rectangle matrix r r' c c' r' j * rectangle matrix r r' c c' r' j) c c' dc
      (fun j first second => by simp [rectangle, first, second])
    have whole := size_compare_pair
      (fun i => size (fun j => matrix i j * matrix i j))
      (fun i => size (fun j => rectangle matrix r r' c c' i j * rectangle matrix r r' c c' i j))
      r r' dr (fun i first second => by simp [rectangle, first, second])
    dsimp only at squares₁ squares₂ whole
    rw [at₁, at₂, empty] at squares₁
    rw [at₃, at₄] at squares₂
    simp only [Nat.zero_mul, Nat.one_mul, Nat.add_zero] at squares₁
    have decreased := switch_cost_lt (matrix r c) (matrix r' c) (matrix r' c') large cross
    unfold cost
    omega

/-- Number of occurrences having the same required multiplicity as this one.
Grouping by totals may combine several variable labels; that only enlarges the
class. Thus the document's label-count bounds imply these weaker bounds. -/
def classCount {n} (totals : Vector n) (index : Fin n) : Nat :=
  size (fun j => if totals j = totals index then 1 else 0)

def PairBound {rows cols} (rowTotals : Vector rows) (colTotals : Vector cols) : Prop :=
  ∀ r c, rowTotals r ≤ classCount colTotals c ∨ colTotals c ≤ classCount rowTotals r

theorem row_improvement {rows cols} (matrix : Matrix rows cols)
    (rowTotals : Vector rows) (colTotals : Vector cols)
    (margins : Margins matrix rowTotals colTotals) (r : Fin rows) (c : Fin cols)
    (large : 2 ≤ matrix r c) (bound : rowTotals r ≤ classCount colTotals c) :
    ∃ updated : Matrix rows cols,
      Margins updated rowTotals colTotals ∧ cost updated < cost matrix := by
  obtain ⟨c', same, empty⟩ := zero_in_column_class matrix colTotals r c
    (by rw [margins.1 r]; exact bound) large
  have equalColumns : size (fun i => matrix i c) = size (fun i => matrix i c') := by
    rw [margins.2 c, margins.2 c', same]
  obtain ⟨r', cross⟩ := crossing_row matrix r c c' equalColumns (by omega)
  obtain ⟨rowsSame, colsSame, decreased⟩ := rectangle_improves matrix r r' c c' large empty cross
  exact ⟨rectangle matrix r r' c c',
    ⟨fun i => (rowsSame i).trans (margins.1 i), fun j => (colsSame j).trans (margins.2 j)⟩,
    decreased⟩

/-- A least-cost witness exists for any nonempty family of finite matrices.
This is an internal classical metaproof, NOT an executable optimizer/certificate
search, and introduces no axiom requiring a solver or a model author's proof. -/
theorem least_cost {rows cols} (P : Matrix rows cols → Prop)
    (witness : ∃ matrix, P matrix) :
    ∃ matrix, P matrix ∧ ∀ other, P other → cost matrix ≤ cost other := by
  classical
  obtain ⟨seed, valid⟩ := witness
  refine Nat.strongRecOn (motive := fun k => ∀ seed : Matrix rows cols,
    cost seed = k → P seed →
      ∃ matrix, P matrix ∧ ∀ other, P other → cost matrix ≤ cost other)
    (cost seed) ?_ seed rfl valid
  intro k ih seed same valid
  by_cases smaller : ∃ other, P other ∧ cost other < k
  · obtain ⟨other, validOther, lower⟩ := smaller
    exact ih (cost other) lower other rfl validOther
  · refine ⟨seed, valid, ?_⟩
    intro other validOther
    have notLower : ¬ cost other < k := fun lower => smaller ⟨other, validOther, lower⟩
    omega

/-- GENERAL BOOLEAN-GRID THEOREM (the rounding step of Lemma 5.4).

Equal finite margin totals plus the opposite-pair bound imply a zero/one matrix
with EXACTLY those margins. Dimensions, degrees, and repetitions are arbitrary.
Choose a least squared-cost transport. Any entry >=2 admits a decreasing
rectangle, directly or after transposition, contradicting minimality.

This proves existence of the Boolean support. Relating label-count bounds to
minimal balance vectors and lifting their generated sums to native bags remain
separate steps; this theorem alone is NOT an ACU certification algorithm.
-/
theorem boolean_transport_exists {rows cols} (rowTotals : Vector rows) (colTotals : Vector cols)
    (same : size rowTotals = size colTotals) (bound : PairBound rowTotals colTotals) :
    ∃ matrix : Matrix rows cols,
      Margins matrix rowTotals colTotals ∧ ∀ i j, matrix i j ≤ 1 := by
  obtain ⟨matrix, margins, minimal⟩ := least_cost
    (fun matrix => Margins matrix rowTotals colTotals) (transport_exists rowTotals colTotals same)
  refine ⟨matrix, margins, ?_⟩
  intro r c
  apply Classical.byContradiction
  intro tooLarge
  have large : 2 ≤ matrix r c := by omega
  rcases bound r c with rowBound | colBound
  · obtain ⟨updated, valid, lower⟩ := row_improvement matrix rowTotals colTotals margins r c large rowBound
    have impossible := minimal updated valid
    omega
  · have swapped : Margins (transpose matrix) colTotals rowTotals := ⟨margins.2, margins.1⟩
    obtain ⟨updated, valid, lower⟩ := row_improvement
      (transpose matrix) colTotals rowTotals swapped c r large colBound
    have restored : Margins (transpose updated) rowTotals colTotals := ⟨valid.2, valid.1⟩
    have impossible := minimal (transpose updated) restored
    rw [cost_transpose] at impossible lower
    omega

/-- Count occurrence positions carrying a given variable label. -/
def labelCount {n positions} (labels : Fin positions → Fin n) (label : Fin n) : Nat :=
  size (fun i => if labels i = label then 1 else 0)

theorem size_scale {n} (k : Nat) (v : Vector n) :
    size (fun i => k * v i) = k * size v := by
  induction n with
  | zero => simp [size]
  | succ n ih => simp only [size, ih, Nat.mul_add]

/-- Expanding each variable into its occurrences preserves its weighted total.
This connects actual coefficient vectors to the occurrence-grid margins. -/
theorem size_labels {n positions} (labels : Fin positions → Fin n) (v : Vector n) :
    size (fun i => v (labels i)) = dot (labelCount labels) v := by
  have row : ∀ i, size (fun j => if labels i = j then v j else 0) = v (labels i) := by
    intro i
    have same : (fun j => if labels i = j then v j else 0) = spike (labels i) (v (labels i)) := by
      funext j
      by_cases equal : j = labels i
      · subst j; simp [spike]
      · simp [spike, equal, Ne.symm equal]
    rw [same, size_spike]
  have col : ∀ j, size (fun i => if labels i = j then v j else 0) = labelCount labels j * v j := by
    intro j
    have same : (fun i => if labels i = j then v j else 0) =
        (fun i => v j * (if labels i = j then 1 else 0)) := by
      funext i
      by_cases equal : labels i = j <;> simp [equal]
    rw [same, size_scale, Nat.mul_comm]
    rfl
  have swapped := size_swap (fun i j => if labels i = j then v j else 0)
  simp only [row, col] at swapped
  exact swapped

theorem label_count_positive {n positions} (labels : Fin positions → Fin n) (index : Fin positions) :
    0 < labelCount labels (labels index) := by
  have bound := coordinate_le_size (fun i => if labels i = labels index then 1 else 0) index
  simpa [labelCount] using bound

theorem label_count_le_class_count {n positions}
    (labels : Fin positions → Fin n) (v : Vector n) (index : Fin positions) :
    labelCount labels (labels index) ≤ classCount (fun i => v (labels i)) index := by
  apply size_mono
  intro i
  change (if labels i = labels index then 1 else 0) ≤
    (if v (labels i) = v (labels index) then 1 else 0)
  by_cases same : labels i = labels index <;> simp [same]

/-- A minimal balance vector is represented by a Boolean occurrence matrix.

The label counts are the original coefficients (e.g. two positions labelled X
for 2X), while every such position has degree v(X). These GENERAL hypotheses
describe the automatically constructed grid, not per-model/user registration.
No occurrence is mistaken for an independent unification variable.
-/
theorem minimal_boolean_support {n rows cols} (left right v : Vector n)
    (rowLabels : Fin rows → Fin n) (colLabels : Fin cols → Fin n)
    (rowCounts : ∀ i, labelCount rowLabels i = left i)
    (colCounts : ∀ i, labelCount colLabels i = right i)
    (disjoint : Disjoint left right) (minimal : Minimal left right v) :
    ∃ matrix : Matrix rows cols,
      Margins matrix (fun r => v (rowLabels r)) (fun c => v (colLabels c)) ∧
      ∀ r c, matrix r c ≤ 1 := by
  have same : size (fun r => v (rowLabels r)) = size (fun c => v (colLabels c)) := by
    rw [size_labels, size_labels]
    have rowsSame : labelCount rowLabels = left := funext rowCounts
    have colsSame : labelCount colLabels = right := funext colCounts
    rw [rowsSame, colsSame]
    exact minimal.2.1
  apply boolean_transport_exists _ _ same
  intro r c
  have lp : 0 < left (rowLabels r) := by
    rw [← rowCounts]
    exact label_count_positive rowLabels r
  have rp : 0 < right (colLabels c) := by
    rw [← colCounts]
    exact label_count_positive colLabels c
  have rz : right (rowLabels r) = 0 := (disjoint _).resolve_left (Nat.ne_of_gt lp)
  have lz : left (colLabels c) = 0 := (disjoint _).resolve_right (Nat.ne_of_gt rp)
  rcases minimal_pair_bound minimal (rowLabels r) (colLabels c) rp rz lz with first | second
  · left
    have count := label_count_le_class_count colLabels v c
    rw [colCounts] at count
    exact Nat.le_trans first count
  · right
    have count := label_count_le_class_count rowLabels v r
    rw [rowCounts] at count
    exact Nat.le_trans second count

theorem label_count_exists {n positions} (labels : Fin positions → Fin n)
    (label : Fin n) (positive : 0 < labelCount labels label) : ∃ i, labels i = label := by
  classical
  apply Classical.byContradiction
  intro none
  have zero : (fun i => if labels i = label then 1 else 0) = zeroVector := by
    funext i
    have different : labels i ≠ label := fun same => none ⟨i, same⟩
    simp [different, zeroVector]
  unfold labelCount at positive
  rw [zero, size_zero] at positive
  omega

/-- COMPLETE OCCURRENCE REPRESENTATION of an active minimal balance vector.

Every minimal vector has a NONEMPTY Boolean support with its exact degrees.
The final hypothesis merely excludes inactive coordinates from this active
vector; canceled/inactive unification variables are separate passthrough images,
not silently forced to empty by the eventual unification rule.

This is Lemma 5.4, for arbitrary finite coefficient vectors after cancellation.
Combined with decompose_minimal, it represents EVERY balanced active vector as
a finite sum of support-degree vectors. The later supportGenerators and Sharing
sections enumerate that family and rebuild checked symbolic/native substitutions.
-/
theorem minimal_nonempty_boolean_support {n rows cols} (left right v : Vector n)
    (rowLabels : Fin rows → Fin n) (colLabels : Fin cols → Fin n)
    (rowCounts : ∀ i, labelCount rowLabels i = left i)
    (colCounts : ∀ i, labelCount colLabels i = right i)
    (disjoint : Disjoint left right) (minimal : Minimal left right v)
    (active : ∀ i, left i = 0 → right i = 0 → v i = 0) :
    ∃ matrix : Matrix rows cols,
      Margins matrix (fun r => v (rowLabels r)) (fun c => v (colLabels c)) ∧
      (∀ r c, matrix r c ≤ 1) ∧ ∃ r c, matrix r c = 1 := by
  obtain ⟨matrix, margins, boolean⟩ := minimal_boolean_support
    left right v rowLabels colLabels rowCounts colCounts disjoint minimal
  refine ⟨matrix, margins, boolean, ?_⟩
  apply Classical.byContradiction
  intro none
  have allZero : ∀ r c, matrix r c = 0 := by
    intro r c
    have small := boolean r c
    have notOne : matrix r c ≠ 1 := fun one => none ⟨r, c, one⟩
    omega
  have rowZero : ∀ r, v (rowLabels r) = 0 := by
    intro r
    have zero : matrix r = zeroVector := funext (allZero r)
    have same := margins.1 r
    rw [zero, size_zero] at same
    exact same.symm
  have colZero : ∀ c, v (colLabels c) = 0 := by
    intro c
    have zero : (fun r => matrix r c) = zeroVector := funext (fun r => allZero r c)
    have same := margins.2 c
    rw [zero, size_zero] at same
    exact same.symm
  apply minimal.1
  funext i
  change v i = 0
  by_cases leftZero : left i = 0
  · by_cases rightZero : right i = 0
    · exact active i leftZero rightZero
    · obtain ⟨c, same⟩ := label_count_exists colLabels i
        (by rw [colCounts]; exact Nat.pos_of_ne_zero rightZero)
      simpa only [same] using colZero c
  · obtain ⟨r, same⟩ := label_count_exists rowLabels i
      (by rw [rowCounts]; exact Nat.pos_of_ne_zero leftZero)
    simpa only [same] using rowZero r

theorem member_below_total {n} {parts : List (Vector n)} {v : Vector n}
    (member : v ∈ parts) : Below v (total parts) := by
  induction parts with
  | nil => cases member
  | cons first rest ih =>
    rcases List.mem_cons.mp member with same | member
    · subst v
      intro i
      exact Nat.le_add_right _ _
    · intro i
      exact Nat.le_trans (ih member i) (Nat.le_add_left _ _)

/-- Soundness of support-degree vectors: each cell contributes once to each
side. Uniform label margins therefore satisfy the original balance equation.
Boolean/nonempty conditions are not needed for this direction. -/
theorem balanced_of_margins {n rows cols} (left right v : Vector n)
    (rowLabels : Fin rows → Fin n) (colLabels : Fin cols → Fin n)
    (rowCounts : ∀ i, labelCount rowLabels i = left i)
    (colCounts : ∀ i, labelCount colLabels i = right i)
    (matrix : Matrix rows cols)
    (margins : Margins matrix (fun r => v (rowLabels r)) (fun c => v (colLabels c))) :
    Balanced left right v := by
  have same := size_swap matrix
  simp only [margins.1, margins.2] at same
  rw [size_labels, size_labels] at same
  have rowsSame : labelCount rowLabels = left := funext rowCounts
  have colsSame : labelCount colLabels = right := funext colCounts
  rw [rowsSame, colsSame] at same
  exact same

/-- NUMERIC FINITE-SHARING COMPLETENESS, uniformly for arbitrary repetitions.

Every balanced ACTIVE vector is a finite sum of degree vectors of nonempty
Boolean supports, including the zero vector via the empty sum. The same input
labels/coefficients are used by every summand. Inactive coordinates are handled
outside this active balance by independent passthrough parameters.

This establishes the multiplicity argument needed by Proposition 5.5. It is a
general metatheorem, not a certificate-search implementation or an assumption
that a particular enumerated support list is exhaustive.
-/
theorem decompose_boolean_supports {n rows cols} (left right v : Vector n)
    (rowLabels : Fin rows → Fin n) (colLabels : Fin cols → Fin n)
    (rowCounts : ∀ i, labelCount rowLabels i = left i)
    (colCounts : ∀ i, labelCount colLabels i = right i)
    (disjoint : Disjoint left right) (balanced : Balanced left right v)
    (active : ∀ i, left i = 0 → right i = 0 → v i = 0) :
    ∃ parts : List (Vector n), total parts = v ∧
      ∀ w ∈ parts, ∃ matrix : Matrix rows cols,
        Margins matrix (fun r => w (rowLabels r)) (fun c => w (colLabels c)) ∧
        (∀ r c, matrix r c ≤ 1) ∧ ∃ r c, matrix r c = 1 := by
  obtain ⟨parts, minimal, same⟩ := decompose_minimal left right v balanced
  refine ⟨parts, same, ?_⟩
  intro w member
  have below := member_below_total member
  rw [same] at below
  have activePart : ∀ i, left i = 0 → right i = 0 → w i = 0 := by
    intro i hl hr
    have bound := below i
    rw [active i hl hr] at bound
    exact Nat.eq_zero_of_le_zero bound
  exact minimal_nonempty_boolean_support left right w rowLabels colLabels
    rowCounts colCounts disjoint (minimal w member) activePart


end FiniteSharing
end DirectCertification
