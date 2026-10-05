import conPanna.Certification.Sharing

/-! Exhaustive sharing enumeration and singleton/zero metatheorems. -/

namespace DirectCertification
open Structural.Indexed
variable {Sorts : Type} {sig : Signature Sorts}
variable (profile : Profile sig)
namespace FiniteSharing
/-- Both directions of the multiplicity-level finite-sharing rule.
The representation is a solution SET; minimality is not required of the
submitted supports, and redundant/overlapping generators do not invalidate it.
This theorem supplies the once-for-all numeric foundation for the later computed
support family, native image reconstruction, and typed sharing replay constructors.
-/
theorem boolean_supports_exact {n rows cols} (left right v : Vector n)
    (rowLabels : Fin rows → Fin n) (colLabels : Fin cols → Fin n)
    (rowCounts : ∀ i, labelCount rowLabels i = left i)
    (colCounts : ∀ i, labelCount colLabels i = right i)
    (disjoint : Disjoint left right)
    (active : ∀ i, left i = 0 → right i = 0 → v i = 0) :
    Balanced left right v ↔
      ∃ parts : List (Vector n), total parts = v ∧
        ∀ w ∈ parts, ∃ matrix : Matrix rows cols,
          Margins matrix (fun r => w (rowLabels r)) (fun c => w (colLabels c)) ∧
          (∀ r c, matrix r c ≤ 1) ∧ ∃ r c, matrix r c = 1 := by
  constructor
  · intro balanced
    exact decompose_boolean_supports left right v rowLabels colLabels
      rowCounts colCounts disjoint balanced active
  · rintro ⟨parts, same, represented⟩
    rw [← same]
    apply total_balanced
    intro w member
    obtain ⟨matrix, margins, _boolean, _nonempty⟩ := represented w member
    exact balanced_of_margins left right w rowLabels colLabels rowCounts colCounts matrix margins

/-! ### Executable exhaustive support family

The grid dimensions come from the input occurrences, not a search bound.
Enumerate every zero/one grid; retain precisely the nonempty grids whose row
and column degrees agree at repeated labels. Equal degree vectors from different
grids may remain duplicated. No supplied support table is trusted complete.
-/

def booleanVectors : (n : Nat) → List (Vector n)
  | 0 => [zeroVector]
  | n + 1 => (booleanVectors n).flatMap fun tail =>
      [Fin.cases 0 tail, Fin.cases 1 tail]

theorem mem_booleanVectors {n} (v : Vector n) :
    v ∈ booleanVectors n ↔ ∀ i, v i ≤ 1 := by
  induction n with
  | zero =>
    have same : v = zeroVector := funext fun i => Fin.elim0 i
    subst v
    simp [booleanVectors]
  | succ n ih =>
    constructor
    · intro member
      obtain ⟨tail, member, same⟩ := List.mem_flatMap.mp member
      have small := (ih tail).mp member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at same
      rcases same with same | same
      · subst v
        exact Fin.cases (Nat.zero_le _) small
      · subst v
        exact Fin.cases (Nat.le_refl _) small
    · intro small
      let tail : Vector n := fun i => v i.succ
      have member := (ih tail).mpr (fun i => small i.succ)
      apply List.mem_flatMap.mpr
      refine ⟨tail, member, ?_⟩
      have head := small 0
      have shape : v = Fin.cases (v 0) tail :=
        funext (Fin.cases rfl (fun _ => rfl))
      rw [shape]
      have cases : v 0 = 0 ∨ v 0 = 1 := by omega
      rcases cases with zero | one
      · rw [zero]
        exact List.mem_cons_self
      · rw [one]
        exact List.mem_cons_of_mem _ List.mem_cons_self

def booleanMatrices : (rows cols : Nat) → List (Matrix rows cols)
  | 0, _ => [fun i => Fin.elim0 i]
  | rows + 1, cols => (booleanVectors cols).flatMap fun first =>
      (booleanMatrices rows cols).map fun rest => Fin.cases first rest

theorem mem_booleanMatrices {rows cols} (matrix : Matrix rows cols) :
    matrix ∈ booleanMatrices rows cols ↔ ∀ r c, matrix r c ≤ 1 := by
  induction rows with
  | zero =>
    have same : matrix = fun i => Fin.elim0 i := funext fun i => Fin.elim0 i
    subst matrix
    simp [booleanMatrices]
  | succ rows ih =>
    constructor
    · intro member
      obtain ⟨first, firstMember, member⟩ := List.mem_flatMap.mp member
      obtain ⟨rest, restMember, same⟩ := List.mem_map.mp member
      subst matrix
      exact Fin.cases ((mem_booleanVectors first).mp firstMember)
        ((ih rest).mp restMember)
    · intro small
      let rest : Matrix rows cols := fun r => matrix r.succ
      refine List.mem_flatMap.mpr ⟨matrix 0,
        (mem_booleanVectors _).mpr (small 0), List.mem_map.mpr ⟨rest,
          (ih rest).mpr (fun r => small r.succ), ?_⟩⟩
      exact funext (Fin.cases rfl (fun _ => rfl))

private def peak : {n : Nat} → Vector n → Nat
  | 0, _ => 0
  | _ + 1, v => max (v 0) (peak (fun i => v i.succ))

theorem peak_le {n} (v : Vector n) (bound : Nat) (small : ∀ i, v i ≤ bound) :
    peak v ≤ bound := by
  induction n with
  | zero => exact Nat.zero_le _
  | succ n ih =>
    exact Nat.max_le.mpr ⟨small 0, ih _ (fun i => small i.succ)⟩

theorem coordinate_le_peak {n} (v : Vector n) (i : Fin n) : v i ≤ peak v := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    exact Fin.cases (Nat.le_max_left _ _)
      (fun j => Nat.le_trans (ih (fun i => v i.succ) j) (Nat.le_max_right _ _)) i

/-- Recover a variable's degree from its occurrences. Max is only a convenient
computable projection: the subsequent margin check requires ALL its occurrences
to have that same degree. Absent variables have degree zero here, and are later
represented by separate passthrough parameters in the native substitution. -/
def supportDegrees {n rows cols}
    (rowLabels : Fin rows → Fin n) (colLabels : Fin cols → Fin n)
    (matrix : Matrix rows cols) : Vector n := fun i =>
  max (peak (fun r => if rowLabels r = i then size (matrix r) else 0))
    (peak (fun c => if colLabels c = i then size (fun r => matrix r c) else 0))

theorem supportDegrees_eq {n rows cols} (v : Vector n)
    (rowLabels : Fin rows → Fin n) (colLabels : Fin cols → Fin n)
    (matrix : Matrix rows cols)
    (margins : Margins matrix (fun r => v (rowLabels r)) (fun c => v (colLabels c)))
    (active : ∀ i, labelCount rowLabels i = 0 → labelCount colLabels i = 0 → v i = 0) :
    supportDegrees rowLabels colLabels matrix = v := by
  funext i
  have upper : supportDegrees rowLabels colLabels matrix i ≤ v i := by
    apply Nat.max_le.mpr
    constructor
    · apply peak_le
      intro r
      split
      · rename_i same
        simpa only [same] using Nat.le_of_eq (margins.1 r)
      · exact Nat.zero_le _
    · apply peak_le
      intro c
      split
      · rename_i same
        simpa only [same] using Nat.le_of_eq (margins.2 c)
      · exact Nat.zero_le _
  apply Nat.le_antisymm upper
  by_cases rowZero : labelCount rowLabels i = 0
  · by_cases colZero : labelCount colLabels i = 0
    · rw [active i rowZero colZero]
      exact Nat.zero_le _
    · obtain ⟨c, same⟩ := label_count_exists colLabels i (Nat.pos_of_ne_zero colZero)
      have bound := coordinate_le_peak
        (fun c => if colLabels c = i then size (fun r => matrix r c) else 0) c
      simp only [margins.2 c, same] at bound
      exact Nat.le_trans bound (Nat.le_max_right _ _)
  · obtain ⟨r, same⟩ := label_count_exists rowLabels i (Nat.pos_of_ne_zero rowZero)
    have bound := coordinate_le_peak
      (fun r => if rowLabels r = i then size (matrix r) else 0) r
    simp only [margins.1 r, same] at bound
    exact Nat.le_trans bound (Nat.le_max_left _ _)

def ValidSupport {n rows cols}
    (rowLabels : Fin rows → Fin n) (colLabels : Fin cols → Fin n)
    (matrix : Matrix rows cols) : Prop :=
  Margins matrix
    (fun r => supportDegrees rowLabels colLabels matrix (rowLabels r))
    (fun c => supportDegrees rowLabels colLabels matrix (colLabels c)) ∧
  ∃ r c, matrix r c = 1

instance {n rows cols} (rowLabels : Fin rows → Fin n) (colLabels : Fin cols → Fin n)
    (matrix : Matrix rows cols) : Decidable (ValidSupport rowLabels colLabels matrix) :=
  inferInstanceAs (Decidable ((_ ∧ _) ∧ ∃ r c, matrix r c = 1))

/-- All finite balanced supports, computed from occurrence labels only. -/
def supportGenerators {n rows cols}
    (rowLabels : Fin rows → Fin n) (colLabels : Fin cols → Fin n) : List (Vector n) :=
  ((booleanMatrices rows cols).filter
    (fun matrix => decide (ValidSupport rowLabels colLabels matrix))).map
      (supportDegrees rowLabels colLabels)

theorem supportGenerators_sound {n rows cols} (left right : Vector n)
    (rowLabels : Fin rows → Fin n) (colLabels : Fin cols → Fin n)
    (rowCounts : ∀ i, labelCount rowLabels i = left i)
    (colCounts : ∀ i, labelCount colLabels i = right i)
    (v : Vector n) (member : v ∈ supportGenerators rowLabels colLabels) :
    Balanced left right v := by
  obtain ⟨matrix, member, same⟩ := List.mem_map.mp member
  have valid := of_decide_eq_true (List.mem_filter.mp member).2
  rw [← same]
  exact balanced_of_margins left right _ rowLabels colLabels rowCounts colCounts matrix valid.1

theorem supportGenerators_cover {n rows cols} (v : Vector n)
    (rowLabels : Fin rows → Fin n) (colLabels : Fin cols → Fin n)
    (active : ∀ i, labelCount rowLabels i = 0 → labelCount colLabels i = 0 → v i = 0)
    (matrix : Matrix rows cols)
    (margins : Margins matrix (fun r => v (rowLabels r)) (fun c => v (colLabels c)))
    (boolean : ∀ r c, matrix r c ≤ 1) (nonempty : ∃ r c, matrix r c = 1) :
    v ∈ supportGenerators rowLabels colLabels := by
  have same := supportDegrees_eq v rowLabels colLabels matrix margins active
  apply List.mem_map.mpr
  refine ⟨matrix, List.mem_filter.mpr ⟨(mem_booleanMatrices matrix).mpr boolean, ?_⟩, same⟩
  apply decide_eq_true
  exact ⟨by simpa only [same] using margins, nonempty⟩

/-- EXACTNESS OF THE COMPUTED LIST. No completeness hypothesis about a proposed
list remains: Boolean enumeration and its filter are proved exhaustive. This is
numeric exactness, not yet a native bag rule or a general certification solver.
All coefficients and dimensions are arbitrary; repetitions are not bounded. -/
theorem supportGenerators_exact {n rows cols} (left right v : Vector n)
    (rowLabels : Fin rows → Fin n) (colLabels : Fin cols → Fin n)
    (rowCounts : ∀ i, labelCount rowLabels i = left i)
    (colCounts : ∀ i, labelCount colLabels i = right i)
    (disjoint : Disjoint left right)
    (active : ∀ i, left i = 0 → right i = 0 → v i = 0) :
    Generated (supportGenerators rowLabels colLabels) v ↔ Balanced left right v := by
  constructor
  · rintro ⟨parts, members, same⟩
    rw [← same]
    exact total_balanced left right parts (fun w member =>
      supportGenerators_sound left right rowLabels colLabels rowCounts colCounts w (members w member))
  · intro balanced
    obtain ⟨parts, same, supports⟩ := decompose_boolean_supports left right v
      rowLabels colLabels rowCounts colCounts disjoint balanced active
    refine ⟨parts, ?_, same⟩
    intro w member
    obtain ⟨matrix, margins, boolean, nonempty⟩ := supports w member
    apply supportGenerators_cover w rowLabels colLabels _ matrix margins boolean nonempty
    intro i hl hr
    have bound := member_below_total member i
    rw [same, active i (by rw [← rowCounts]; exact hl)
      (by rw [← colCounts]; exact hr)] at bound
    exact Nat.eq_zero_of_le_zero bound

/-- Convert a generated sum to one multiplicity per PARAMETER POSITION.
Positions, not vector equality, are essential: duplicate support vectors must
not duplicate an element's assigned multiplicity. -/
theorem generated_weights {n} (generators : List (Vector n)) (v : Vector n)
    (generated : Generated generators v) :
    ∃ weights : Vector generators.length,
      ∀ i, dot (fun j => generators.get j i) weights = v i := by
  obtain ⟨parts, members, same⟩ := generated
  have build : ∀ parts : List (Vector n), (∀ w ∈ parts, w ∈ generators) →
      ∃ weights : Vector generators.length,
        ∀ i, dot (fun j => generators.get j i) weights = total parts i := by
    intro parts
    induction parts with
    | nil =>
      intro _
      refine ⟨zeroVector, fun i => ?_⟩
      simp only [dot, zeroVector, Nat.mul_zero, total]
      exact size_zero _
    | cons first rest ih =>
      intro members
      obtain ⟨index, atIndex⟩ := List.mem_iff_get.mp (members first List.mem_cons_self)
      obtain ⟨weights, sum⟩ := ih (fun w member => members w (List.mem_cons_of_mem _ member))
      refine ⟨plus (spike index 1) weights, fun i => ?_⟩
      rw [dot_plus, dot_spike, Nat.mul_one, atIndex, sum]
      rfl
  obtain ⟨weights, sum⟩ := build parts members
  exact ⟨weights, fun i => (sum i).trans (congrFun same i)⟩

/-- Exchange finite sums: applying coefficients to reconstructed parameter
images is the same as applying each generator's balance to the parameters. -/
theorem dot_images {n m} (coeff : Vector n) (generators : Fin m → Vector n)
    (weights : Vector m) :
    dot coeff (fun i => dot (fun j => generators j i) weights) =
      dot (fun j => dot coeff (generators j)) weights := by
  unfold dot
  calc
    _ = size (fun i => size (fun j => coeff i * generators j i * weights j)) := by
      apply congrArg size
      funext i
      simpa only [Nat.mul_assoc] using
        (size_scale (coeff i) (fun j => generators j i * weights j)).symm
    _ = size (fun j => size (fun i => coeff i * generators j i * weights j)) :=
      size_swap _
    _ = _ := by
      apply congrArg size
      funext j
      simpa only [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
        size_scale (weights j) (fun i => coeff i * generators j i)

theorem balanced_images {n m} (left right : Vector n)
    (generators : Fin m → Vector n) (sound : ∀ j, Balanced left right (generators j))
    (weights : Vector m) :
    Balanced left right (fun i => dot (fun j => generators j i) weights) := by
  unfold Balanced
  rw [dot_images, dot_images]
  exact congrArg (fun coeff => dot coeff weights) (funext sound)

/-! ### Collect multiplicity witnesses into actual finite bags

Lists here are INTERNAL bags of atom classes, not a new model representation.
For every class a, generated_weights supplies one number per support POSITION.
Put that many copies of a into the corresponding parameter bag. The dictionary
is finite because the input bags are finite; arbitrary payload values are kept.
Permutation, not literal list equality, is the reconstruction guarantee.
-/

def listCopies {α : Type} : Nat → List α → List α
  | 0, _ => []
  | k + 1, xs => xs ++ listCopies k xs

def listSum {α : Type} : {n : Nat} → Vector n → (Fin n → List α) → List α
  | 0, _, _ => []
  | _ + 1, coeff, bags => listCopies (coeff 0) (bags 0) ++
      listSum (fun i => coeff i.succ) (fun i => bags i.succ)

theorem count_listCopies {α : Type} [DecidableEq α] (a : α) (k : Nat) (xs : List α) :
    List.count a (listCopies k xs) = k * List.count a xs := by
  induction k with
  | zero => simp [listCopies]
  | succ k ih => simp only [listCopies, List.count_append, ih, Nat.succ_mul, Nat.add_comm]

theorem count_listSum {α : Type} [DecidableEq α] {n} (a : α)
    (coeff : Vector n) (bags : Fin n → List α) :
    List.count a (listSum coeff bags) = dot coeff (fun i => List.count a (bags i)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [listSum, List.count_append, count_listCopies, dot, size]
    exact congrArg (fun tail => coeff 0 * List.count a (bags 0) + tail)
      (ih (fun i => coeff i.succ) (fun i => bags i.succ))

private def dictionary {α : Type} [DecidableEq α] : List α → List α
  | [] => []
  | a :: rest => let tail := dictionary rest
      if a ∈ tail then tail else a :: tail

theorem dictionary_mem {α : Type} [DecidableEq α] (a : α) (xs : List α) :
    a ∈ dictionary xs ↔ a ∈ xs := by
  induction xs generalizing a with
  | nil => rfl
  | cons first rest ih =>
    simp only [dictionary]
    split
    · rename_i present
      have present := (ih first).mp present
      simpa only [List.mem_cons, ih] using
        (show a ∈ rest ↔ a = first ∨ a ∈ rest from
          ⟨Or.inr, fun h => h.elim (fun same => same ▸ present) id⟩)
    · simp only [List.mem_cons, ih]

theorem dictionary_nodup {α : Type} [DecidableEq α] (xs : List α) :
    (dictionary xs).Nodup := by
  induction xs with
  | nil => exact List.nodup_nil
  | cons first rest ih =>
    simp only [dictionary]
    split
    · exact ih
    · exact List.nodup_cons.mpr ⟨‹_›, ih⟩

theorem count_dictionary {α : Type} [DecidableEq α] (xs : List α)
    (nodup : xs.Nodup) (weights : α → Nat) (a : α) :
    List.count a (xs.flatMap (fun b => List.replicate (weights b) b)) =
      if a ∈ xs then weights a else 0 := by
  induction xs with
  | nil => simp
  | cons first rest ih =>
    have distinct := List.nodup_cons.mp nodup
    simp only [List.flatMap_cons, List.count_append, ih distinct.2]
    by_cases same : a = first
    · subst a
      simp [distinct.1]
    · simp [List.count_replicate, same, Ne.symm same]

/-- Lift numeric generation to finite bags of ANY element type. Duplicated
generator vectors are assigned by index, preserving one shared parameter scope.
This classical witness construction belongs to the general metatheorem, not
runtime search and not a per-model registration obligation. -/
theorem lists_generated {α : Type} [DecidableEq α] {n} (generators : List (Vector n))
    (bags : Fin n → List α)
    (generated : ∀ a, Generated generators (fun i => List.count a (bags i))) :
    ∃ parameters : Fin generators.length → List α,
      ∀ i, (bags i).Perm (listSum (fun j => generators.get j i) parameters) := by
  classical
  let atoms := dictionary ((List.finRange n).flatMap bags)
  have contains : ∀ a i, a ∈ bags i → a ∈ atoms := by
    intro a i member
    apply (dictionary_mem a _).mpr
    exact List.mem_flatMap.mpr ⟨i, List.mem_ofFn.mpr ⟨i, rfl⟩, member⟩
  have witnesses := fun a => generated_weights generators _ (generated a)
  let weights := fun a => Classical.choose (witnesses a)
  have sums : ∀ a i, dot (fun j => generators.get j i) (weights a) = List.count a (bags i) :=
    fun a => Classical.choose_spec (witnesses a)
  let parameters := fun j => atoms.flatMap (fun a => List.replicate (weights a j) a)
  refine ⟨parameters, fun i => List.perm_iff_count.mpr (fun a => ?_)⟩
  rw [count_listSum]
  have counts : ∀ j, List.count a (parameters j) = if a ∈ atoms then weights a j else 0 :=
    fun j => count_dictionary atoms (dictionary_nodup _) (fun a => weights a j) a
  by_cases member : a ∈ atoms
  · simp only [counts, if_pos member]
    exact (sums a i).symm
  · have zero : List.count a (bags i) = 0 :=
      List.count_eq_zero.mpr (fun present => member (contains a i present))
    simp only [counts, if_neg member, dot, Nat.mul_zero, zero]
    exact (size_zero _).symm

/-! ### Finite sharing in the EXISTING indexed structural semantics

Each support gets ONE bag parameter, shared by every original variable image.
Flattening/counts are internal proof auxiliaries; the conclusion relates ordinary
registered constructor trees by Structural.Indexed.Eq, without new axioms.
-/

def bagSum {s} (op : sig.ACUOp s) :
    {n : Nat} → Vector n → (Fin n → Tree sig s) → Tree sig s
  | 0, _, _ => zero sig op
  | _ + 1, coeff, values => add sig op (bagCopies op (coeff 0) (values 0))
      (bagSum op (fun i => coeff i.succ) (fun i => values i.succ))

theorem count_bagSum (profile : Profile sig) {s n} (op : sig.ACUOp s)
    (coeff : Vector n) (values : Fin n → Tree sig s) (a : QTree sig s)
    [DecidableEq (QTree sig s)] :
    List.count a (flatten profile (bagSum op coeff values)) =
      dot coeff (fun i => List.count a (flatten profile (values i))) := by
  induction n with
  | zero => simp [bagSum, flatten_zero, dot, size]
  | succ n ih =>
    simp only [bagSum, flatten_add, List.count_append, count_flatten_repeat, dot, size]
    exact congrArg (fun tail => coeff 0 * List.count a (flatten profile (values 0)) + tail)
      (ih (fun i => coeff i.succ) (fun i => values i.succ))

theorem bagSum_balance (profile : Profile sig) {s n} (op : sig.ACUOp s)
    (left right : Vector n) (values : Fin n → Tree sig s) [DecidableEq (QTree sig s)] :
    Structural.Indexed.Eq sig (bagSum op left values) (bagSum op right values) ↔
      ∀ a : QTree sig s, Balanced left right
        (fun i => List.count a (flatten profile (values i))) := by
  classical
  constructor
  · intro same a
    have counts := (flatten_congr profile same).count_eq a
    simpa only [count_bagSum] using counts
  · intro balanced
    apply eq_of_flatten_perm profile op
    apply List.perm_iff_count.mpr
    intro a
    simpa only [count_bagSum] using balanced a

theorem qtree_bagCopies {s} (op : sig.ACUOp s) (k : Nat)
    (value : Tree sig s) (atoms : List (QTree sig s)) (folded : qtree value = qfold op atoms) :
    qtree (bagCopies op k value) = qfold op (listCopies k atoms) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change qadd op (qtree value) (qtree (bagCopies op k value)) = _
    rw [folded, ih]
    exact (qfold_append op atoms (listCopies k atoms)).symm

theorem qtree_bagSum {s n} (op : sig.ACUOp s) (coeff : Vector n)
    (values : Fin n → Tree sig s) (atoms : Fin n → List (QTree sig s))
    (folded : ∀ i, qtree (values i) = qfold op (atoms i)) :
    qtree (bagSum op coeff values) = qfold op (listSum coeff atoms) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change qadd op (qtree (bagCopies op (coeff 0) (values 0)))
      (qtree (bagSum op (fun i => coeff i.succ) (fun i => values i.succ))) = _
    rw [qtree_bagCopies op _ _ _ (folded 0),
      ih (fun i => coeff i.succ) (fun i => values i.succ) (fun i => atoms i.succ)
        (fun i => folded i.succ)]
    exact (qfold_append op _ _).symm

/-- Exact finite sharing for active bags. The unit condition concerns only
inactive coordinates of this intermediate balance, NOT original canceled inputs.
The public tree rule below restores those inputs as independent passthroughs. -/
theorem bags_generated_active (profile : Profile sig) {s n rows cols}
    (op : sig.ACUOp s) (left right : Vector n)
    (rowLabels : Fin rows → Fin n) (colLabels : Fin cols → Fin n)
    (rowCounts : ∀ i, labelCount rowLabels i = left i)
    (colCounts : ∀ i, labelCount colLabels i = right i)
    (disjoint : Disjoint left right) (values : Fin n → Tree sig s)
    (active : ∀ i, left i = 0 → right i = 0 →
      Structural.Indexed.Eq sig (values i) (zero sig op)) :
    Structural.Indexed.Eq sig (bagSum op left values) (bagSum op right values) ↔
      ∃ parameters : Fin (supportGenerators rowLabels colLabels).length → Tree sig s,
        ∀ i, Structural.Indexed.Eq sig (values i)
          (bagSum op (fun j => (supportGenerators rowLabels colLabels).get j i) parameters) := by
  classical
  let generators := supportGenerators rowLabels colLabels
  constructor
  · intro equation
    have balanced := (bagSum_balance profile op left right values).mp equation
    have generated : ∀ a : QTree sig s, Generated generators
        (fun i => List.count a (flatten profile (values i))) := by
      intro a
      apply (supportGenerators_exact left right _ rowLabels colLabels rowCounts colCounts disjoint ?_).mpr
        (balanced a)
      intro i hl hr
      have count := (flatten_congr profile (active i hl hr)).count_eq a
      simpa only [flatten_zero, List.count_nil] using count
    obtain ⟨pieces, represented⟩ := lists_generated generators (fun i => flatten profile (values i)) generated
    have reps := fun j => Quotient.exists_rep (qfold op (pieces j))
    let parameters := fun j => Classical.choose (reps j)
    have folded : ∀ j, qtree (parameters j) = qfold op (pieces j) :=
      fun j => Classical.choose_spec (reps j)
    refine ⟨parameters, fun i => (qtree_eq_iff _ _).mp ?_⟩
    exact (qfold_flatten profile op (values i)).symm.trans
      ((qfold_perm op (represented i)).trans
        (qtree_bagSum op _ parameters pieces folded).symm)
  · rintro ⟨parameters, images⟩
    apply (bagSum_balance profile op left right values).mpr
    intro a
    have counts : ∀ i, List.count a (flatten profile (values i)) =
        dot (fun j => generators.get j i)
          (fun j => List.count a (flatten profile (parameters j))) := by
      intro i
      have same := (flatten_congr profile (images i)).count_eq a
      simpa only [count_bagSum] using same
    have generated := balanced_images left right (fun j => generators.get j)
      (fun j => supportGenerators_sound left right rowLabels colLabels rowCounts colCounts _
        (List.get_mem _ j)) (fun j => List.count a (flatten profile (parameters j)))
    simpa only [counts] using generated

theorem bagSum_congr {s n} (op : sig.ACUOp s) (coeff : Vector n)
    (values other : Fin n → Tree sig s)
    (same : ∀ i, coeff i ≠ 0 → Structural.Indexed.Eq sig (values i) (other i)) :
    Structural.Indexed.Eq sig (bagSum op coeff values) (bagSum op coeff other) := by
  induction n with
  | zero => exact .refl _
  | succ n ih =>
    apply Structural.Indexed.Eq.congr (sig.add op)
    apply Eqs.cons
    · by_cases zero : coeff 0 = 0
      · simp only [zero, bagCopies]
        exact .refl _
      · exact repeat_congr op _ (same 0 zero)
    · exact .cons (ih (fun i => coeff i.succ) (fun i => values i.succ)
        (fun i => other i.succ) (fun i => same i.succ)) .nil

def sharingImages {s n} (op : sig.ACUOp s) (left right : Vector n)
    (generators : List (Vector n)) (parameters : Fin generators.length → Tree sig s)
    (passthrough : Fin n → Tree sig s) : Fin n → Tree sig s := fun i =>
  if left i = 0 ∧ right i = 0 then passthrough i
  else bagSum op (fun j => generators.get j i) parameters

/-- FINITE-SHARING EXACTNESS in registered tree equality, with EVERY input image.

  sum_i left_i * X_i =B sum_i right_i * X_i
  ==================================================== FiniteSharing
  EXISTS shared Z_s and independent inactive P_i,
    FOR ALL i, X_i =B (P_i if inactive; sum_s degree_i(s) * Z_s otherwise)

Zero-sided grids and the empty equation are included. No user semantic bridge,
linearity assumption, fixed arity/coefficients, or trusted generator table occurs.
This is a general proof rule, not yet certificate-search/replay implementation.
-/
theorem bags_generated (profile : Profile sig) {s n rows cols}
    (op : sig.ACUOp s) (left right : Vector n)
    (rowLabels : Fin rows → Fin n) (colLabels : Fin cols → Fin n)
    (rowCounts : ∀ i, labelCount rowLabels i = left i)
    (colCounts : ∀ i, labelCount colLabels i = right i)
    (disjoint : Disjoint left right) (values : Fin n → Tree sig s) :
    Structural.Indexed.Eq sig (bagSum op left values) (bagSum op right values) ↔
      ∃ parameters : Fin (supportGenerators rowLabels colLabels).length → Tree sig s,
        ∃ passthrough : Fin n → Tree sig s,
          ∀ i, Structural.Indexed.Eq sig (values i)
            (sharingImages op left right (supportGenerators rowLabels colLabels) parameters passthrough i) := by
  classical
  let activeValues := fun i => if left i = 0 ∧ right i = 0 then zero sig op else values i
  have leftSame := bagSum_congr op left values activeValues (fun i nonzero => by
    simp only [activeValues, nonzero, false_and, if_false]
    exact .refl _)
  have rightSame := bagSum_congr op right values activeValues (fun i nonzero => by
    simp only [activeValues, nonzero, and_false, if_false]
    exact .refl _)
  constructor
  · intro equation
    have equation := leftSame.symm.trans (equation.trans rightSame)
    have active : ∀ i, left i = 0 → right i = 0 →
        Structural.Indexed.Eq sig (activeValues i) (zero sig op) := by
      intro i hl hr
      simp only [activeValues, hl, hr, and_self, if_true]
      exact .refl _
    obtain ⟨parameters, images⟩ := (bags_generated_active profile op left right rowLabels
      colLabels rowCounts colCounts disjoint activeValues active).mp equation
    refine ⟨parameters, values, fun i => ?_⟩
    by_cases inactive : left i = 0 ∧ right i = 0
    · simp only [sharingImages, if_pos inactive]
      exact .refl _
    · simpa only [sharingImages, activeValues, if_neg inactive] using images i
  · rintro ⟨parameters, passthrough, images⟩
    let generatedValues := fun i => bagSum op
      (fun j => (supportGenerators rowLabels colLabels).get j i) parameters
    have leftSame := bagSum_congr op left values generatedValues (fun i nonzero => by
      have inactive : ¬ (left i = 0 ∧ right i = 0) := fun h => nonzero h.1
      simpa only [sharingImages, if_neg inactive] using images i)
    have rightSame := bagSum_congr op right values generatedValues (fun i nonzero => by
      have inactive : ¬ (left i = 0 ∧ right i = 0) := fun h => nonzero h.2
      simpa only [sharingImages, if_neg inactive] using images i)
    have balanced : Structural.Indexed.Eq sig (bagSum op left generatedValues)
        (bagSum op right generatedValues) := by
      apply (bagSum_balance profile op left right generatedValues).mpr
      intro a
      simp only [generatedValues, count_bagSum]
      exact balanced_images left right _ (fun j =>
        supportGenerators_sound left right rowLabels colLabels rowCounts colCounts _
          (List.get_mem _ j)) _
    exact leftSame.trans (balanced.trans rightSame.symm)

/- Computational regressions, NOT evidence for the general completeness theorem:
   2X = 3Y gives X = 3Z, Y = 2Z, including Z = empty.
   2X = A+Y retains every balanced support, including redundant presentations.
   A one-sided or empty occurrence grid has no nonempty support.
   No external solver is invoked while elaborating this file. -/
#guard ((supportGenerators (fun _ : Fin 2 => (0 : Fin 2))
  (fun _ : Fin 3 => (1 : Fin 2))).map
    (fun v => (List.finRange 2).map v)) == [[3, 2]]
#guard ((supportGenerators (fun _ : Fin 2 => (0 : Fin 3))
  (fun c : Fin 2 => (if c = 0 then 1 else 2 : Fin 3))).map
    (fun v => (List.finRange 3).map v)) ==
      [[1, 2, 0], [1, 1, 1], [1, 1, 1], [1, 0, 2], [2, 2, 2]]
#guard (booleanMatrices 2 3).length == 64
#guard (supportGenerators (fun _ : Fin 1 => (0 : Fin 1))
  (fun c : Fin 0 => c.elim0)).length == 0
#guard (supportGenerators (fun r : Fin 0 => r.elim0)
  (fun c : Fin 0 => c.elim0) (n := 0)).length == 0

end FiniteSharing

/-! ## Exhaustive singleton requirements (CERTIFICATION.md §4.4)

Input: a coefficient sum of arbitrary bag terms, after finite sharing.
ZERO: every positive-coefficient term must be empty; coefficient zero is ignored.
ATOM-CHOOSE: exactly one coefficient-ONE term supplies the target singleton;
every other positive-coefficient term is empty. Enumerate ALL such indices.
This includes explicit singleton terms: their surviving equation with the target
is decomposed by the existing free-head rule, yielding a payload equation modulo B.
Repeated variables belong in the coefficients, not an assumption of linearity.

The rules are exhaustive because mass is a natural-number invariant: a singleton
has mass one, and c copies contribute c times the term's mass. They terminate
locally: finitely many indices, and the search can mark that requirement processed.
Replay may retain the original equation as a hypothesis; that is not a search loop.
These are general semantic metatheorems, not an automatic whole-system solver.
-/
namespace AtomProcessing

theorem mass_copies (profile : Profile sig) {s} (op : sig.ACUOp s)
    (k : Nat) (a : Tree sig s) : mass profile (bagCopies op k a) = k * mass profile a := by
  induction k with
  | zero => simp only [bagCopies, mass_zero, Nat.zero_mul]
  | succ k ih => simp only [bagCopies, mass_add, ih, Nat.succ_mul, Nat.add_comm]

theorem copies_zero (profile : Profile sig) {s} (op : sig.ACUOp s)
    (k : Nat) (a : Tree sig s) :
    Structural.Indexed.Eq sig (bagCopies op k a) (zero sig op) ↔
      (k ≠ 0 → Structural.Indexed.Eq sig a (zero sig op)) := by
  constructor
  · intro same positive
    have count := mass_congr profile same
    rw [mass_copies, mass_zero] at count
    have empty : mass profile a = 0 := (Nat.mul_eq_zero.mp count).resolve_left positive
    exact zero_of_mass profile a op empty
  · intro empty
    by_cases hk : k = 0
    · subst k; exact .refl _
    · have count := mass_congr profile (empty hk)
      rw [mass_zero] at count
      apply zero_of_mass profile _ op
      rw [mass_copies, count, Nat.mul_zero]

theorem copies_atom (profile : Profile sig) {s} (op : sig.ACUOp s)
    (k : Nat) (a target : Tree sig s) (atom : mass profile target = 1) :
    Structural.Indexed.Eq sig (bagCopies op k a) target ↔
      k = 1 ∧ Structural.Indexed.Eq sig a target := by
  have one : Structural.Indexed.Eq sig (bagCopies op 1 a) a :=
    .trans (.comm op a (zero sig op)) (.unit op a)
  constructor
  · intro same
    have count := mass_congr profile same
    rw [mass_copies, atom] at count
    have hk : k = 1 := Nat.eq_one_of_mul_eq_one_right count
    exact ⟨hk, one.symm.trans (hk ▸ same)⟩
  · rintro ⟨rfl, same⟩; exact one.trans same

theorem sum_zero (profile : Profile sig) {s n} (op : sig.ACUOp s)
    (coeff : FiniteSharing.Vector n) (values : Fin n → Tree sig s) :
    Structural.Indexed.Eq sig (FiniteSharing.bagSum op coeff values) (zero sig op) ↔
      ∀ i, coeff i ≠ 0 → Structural.Indexed.Eq sig (values i) (zero sig op) := by
  induction n with
  | zero => exact ⟨fun _ i => Fin.elim0 i, fun _ => .refl _⟩
  | succ n ih =>
    constructor
    · intro same
      have count := mass_congr profile same
      rw [FiniteSharing.bagSum, mass_add, mass_zero] at count
      have hl : mass profile (bagCopies op (coeff 0) (values 0)) = 0 := by omega
      have hr : mass profile (FiniteSharing.bagSum op (fun i => coeff i.succ)
          (fun i => values i.succ)) = 0 := by omega
      exact Fin.cases ((copies_zero profile op _ _).mp (zero_of_mass profile _ op hl))
        ((ih _ _).mp (zero_of_mass profile _ op hr))
    · intro empty
      exact .trans (.congr (sig.add op)
        (.cons ((copies_zero profile op _ _).mpr (empty 0))
          (.cons ((ih _ _).mpr (fun i => empty i.succ)) .nil))) (.unit op _)

theorem sum_atom (profile : Profile sig) {s n} (op : sig.ACUOp s)
    (coeff : FiniteSharing.Vector n) (values : Fin n → Tree sig s)
    (target : Tree sig s) (atom : mass profile target = 1) :
    Structural.Indexed.Eq sig (FiniteSharing.bagSum op coeff values) target ↔
      ∃ j, coeff j = 1 ∧ Structural.Indexed.Eq sig (values j) target ∧
        ∀ i, i ≠ j → coeff i ≠ 0 → Structural.Indexed.Eq sig (values i) (zero sig op) := by
  induction n with
  | zero =>
    constructor
    · intro same
      have count := mass_congr profile same
      simp only [FiniteSharing.bagSum, mass_zero, atom] at count
      exact False.elim (Nat.noConfusion count)
    · rintro ⟨j, _⟩; exact Fin.elim0 j
  | succ n ih =>
    have casesRule := split_atom profile op (bagCopies op (coeff 0) (values 0))
      (FiniteSharing.bagSum op (fun i => coeff i.succ) (fun i => values i.succ)) target atom
    constructor
    · intro same
      rcases casesRule.mp same with ⟨hl, hr⟩ | ⟨hl, hr⟩
      · obtain ⟨j, degree, chosen, others⟩ := (ih _ _).mp hr
        refine ⟨j.succ, degree, chosen, ?_⟩
        exact Fin.cases (fun _ => (copies_zero profile op _ _).mp hl)
          (fun i different => others i (fun equal => different (congrArg Fin.succ equal)))
      · obtain ⟨degree, chosen⟩ := (copies_atom profile op _ _ _ atom).mp hl
        refine ⟨0, degree, chosen, ?_⟩
        exact Fin.cases (fun different => False.elim (different rfl))
          (fun i _ => (sum_zero profile op _ _).mp hr i)
    · rintro ⟨j, degree, chosen, others⟩
      refine Fin.cases (motive := fun j => coeff j = 1 → Structural.Indexed.Eq sig (values j) target →
        (∀ i, i ≠ j → coeff i ≠ 0 → Structural.Indexed.Eq sig (values i) (zero sig op)) →
        Structural.Indexed.Eq sig (FiniteSharing.bagSum op coeff values) target) ?_ ?_ j degree chosen others
      · intro degree chosen others
        exact casesRule.mpr (.inr ⟨(copies_atom profile op _ _ _ atom).mpr ⟨degree, chosen⟩,
          (sum_zero profile op _ _).mpr (fun i => others i.succ (Fin.succ_ne_zero i))⟩)
      · intro j degree chosen others
        exact casesRule.mpr (.inl ⟨(copies_zero profile op _ _).mpr
          (others 0 (Ne.symm (Fin.succ_ne_zero j))),
          (ih _ _).mpr ⟨j, degree, chosen, fun i different =>
            others i.succ (fun equal => different (Fin.succ_inj.mp equal))⟩⟩)

end AtomProcessing

end DirectCertification
