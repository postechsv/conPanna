/-! Native pattern and transition semantics, independent of constructor encoding. -/
namespace Expresso

universe u

/-! ## Patterns and rules
`α` is the type of states. Its equality is ordinary `=`: sorts with structural
axioms (e.g. ACU bags) are quotient types, so `=` already means equality modulo
those axioms.

Three levels: a patch body has no variables; a patch binds them once, over one
type `A` (several variables go in a tuple); a pattern is a finite disjunction of
patches, a list: `[]` is `⊥` and `++` is `∨`. Rule bodies, rules and systems follow
the same shape. Order and duplicates do not matter to the meaning (`holds`, `step`). -/

variable {α : Type u}

/-- A patch body `⟨state | cond⟩`. -/
structure PatchBody (α : Type u) where
  state : α
  cond : Prop := True

/-- A patch `∃ a : A, body a`. -/
inductive Patch (α : Type u) : Type (u + 1) where
  | bind {A : Type u} (body : A → PatchBody α) : Patch α

/-- A pattern: the disjunction of its patches. -/
abbrev Pattern (α : Type u) := List (Patch α)

def PatchBody.holds (p : PatchBody α) (actual : α) : Prop :=
  p.state = actual ∧ p.cond

def Patch.Vars : Patch α → Type u
  | .bind (A := A) _ => A

def Patch.holds : Patch α → α → Prop
  | .bind body, state => ∃ a, (body a).holds state

def Pattern.holds (P : Pattern α) (state : α) : Prop :=
  ∃ p ∈ P, p.holds state

@[simp] theorem Pattern.holds_nil (s : α) : Pattern.holds [] s ↔ False := by
  simp [Pattern.holds]

@[simp] theorem Pattern.holds_cons (p : Patch α) (P : Pattern α) (s : α) :
    Pattern.holds (p :: P) s ↔ p.holds s ∨ P.holds s := by
  simp [Pattern.holds]

@[simp] theorem Pattern.holds_append (P Q : Pattern α) (s : α) :
    Pattern.holds (P ++ Q) s ↔ P.holds s ∨ Q.holds s := by
  simp [Pattern.holds, or_and_right, exists_or]

/-- A rule body `lhs => rhs if cond`. -/
structure RuleBody (α : Type u) where
  lhs : α
  rhs : α
  cond : Prop := True

/-- A rule `∀ a : A, body a`. -/
inductive Rule (α : Type u) : Type (u + 1) where
  | bind {A : Type u} (body : A → RuleBody α) : Rule α

/-- A system: a choice of its rules. -/
abbrev System (α : Type u) := List (Rule α)

def RuleBody.step (r : RuleBody α) (before after : α) : Prop :=
  r.lhs = before ∧ r.rhs = after ∧ r.cond

def Rule.Vars : Rule α → Type u
  | .bind (A := A) _ => A

def Rule.step : Rule α → α → α → Prop
  | .bind body, before, after => ∃ a, (body a).step before after

def System.step (R : System α) (before after : α) : Prop :=
  ∃ r ∈ R, r.step before after

@[simp] theorem System.step_nil (a b : α) : System.step [] a b ↔ False := by
  simp [System.step]

@[simp] theorem System.step_cons (r : Rule α) (R : System α) (a b : α) :
    System.step (r :: R) a b ↔ r.step a b ∨ R.step a b := by
  simp [System.step]

@[simp] theorem System.step_append (R₁ R₂ : System α) (a b : α) :
    System.step (R₁ ++ R₂) a b ↔ R₁.step a b ∨ R₂.step a b := by
  simp [System.step, or_and_right, exists_or]

/-! ## Semantic judgments and universal/existential decomposition
These describe ONE-STEP transitions. Choice is nondeterminism, not sequencing.
None of these definitions computes unifiers or post-images.
-/

-- A ⊑ B
def subsumes (A B : Pattern α) : Prop :=
  ∀ v, A.holds v → B.holds v

-- A ⊓ B ≠ ⊥
def overlaps (A B : Pattern α) : Prop :=
  ∃ v, A.holds v ∧ B.holds v

-- No Junk : B ⊑ R(A)
def isUnderPost (R : System α) (A B : Pattern α) : Prop :=
  ∀ b, B.holds b → ∃ a, A.holds a ∧ R.step a b

-- No Miss : R(A) ⊑ B
def isOverPost (R : System α) (A B : Pattern α) : Prop :=
  ∀ a b, A.holds a → R.step a b → B.holds b

-- R(A) ⊓ B ≠ ⊥ renaming? redifine using overlaps?
def overlapsPost (R : System α) (A B : Pattern α) : Prop :=
  ∃ a b, A.holds a ∧ R.step a b ∧ B.holds b

-- No Junk & No Miss : R(A) = B
def isPost (R : System α) (A B : Pattern α) : Prop :=
  isOverPost R A B ∧ isUnderPost R A B




/-! ## Patterns and systems compose -/

-- R(⊥) = ⊥
theorem isPost_bott (R : System α) : isPost R [] [] :=
  ⟨fun _ _ h => by simp at h, fun _ h => by simp at h⟩

-- ⊥(S) = ⊥
theorem isPost_empty (S : Pattern α) : isPost [] S [] :=
  ⟨fun _ _ _ h => by simp at h, fun _ h => by simp at h⟩

-- R(S₁) = P₁, R(S₂) = P₂ ⇒ R(S₁ ⊔ S₂) = P₁ ⊔ P₂
theorem isPost_disj {R : System α} {S₁ S₂ P₁ P₂ : Pattern α}
    (h₁ : isPost R S₁ P₁) (h₂ : isPost R S₂ P₂) : isPost R (S₁ ++ S₂) (P₁ ++ P₂) := by
  refine ⟨fun before after hs hstep => ?_, fun after hp => ?_⟩
  · rw [Pattern.holds_append] at hs ⊢
    exact hs.imp (h₁.1 before after · hstep) (h₂.1 before after · hstep)
  · rcases (Pattern.holds_append _ _ _).1 hp with hp | hp
    · obtain ⟨b, hs, hstep⟩ := h₁.2 after hp
      exact ⟨b, (Pattern.holds_append _ _ _).2 (.inl hs), hstep⟩
    · obtain ⟨b, hs, hstep⟩ := h₂.2 after hp
      exact ⟨b, (Pattern.holds_append _ _ _).2 (.inr hs), hstep⟩

-- R₁(S) = P₁, R₂(S) = P₂ ⇒ (R₁ ⊔ R₂)(S) = P₁ ⊔ P₂
theorem isPost_choice {R₁ R₂ : System α} {S P₁ P₂ : Pattern α}
    (h₁ : isPost R₁ S P₁) (h₂ : isPost R₂ S P₂) : isPost (R₁ ++ R₂) S (P₁ ++ P₂) := by
  refine ⟨fun before after hs hstep => ?_, fun after hp => ?_⟩
  · rw [Pattern.holds_append]
    rw [System.step_append] at hstep
    exact hstep.imp (h₁.1 before after hs) (h₂.1 before after hs)
  · rcases (Pattern.holds_append _ _ _).1 hp with hp | hp
    · obtain ⟨b, hs, hstep⟩ := h₁.2 after hp
      exact ⟨b, hs, (System.step_append _ _ _ _).2 (.inl hstep)⟩
    · obtain ⟨b, hs, hstep⟩ := h₂.2 after hp
      exact ⟨b, hs, (System.step_append _ _ _ _).2 (.inr hstep)⟩


-- R(A) ⊑ B ∧ C ⊑ B → R(A) ⊑ C
theorem over_of_subsumes
    {R : System α} {A B C : Pattern α}
    (hover : isOverPost R A C) (hsub : subsumes C B) :
    isOverPost R A B :=
  fun before after hsource hstep => hsub after (hover before after hsource hstep)

-- B ⊑ R(A) ∧ B ⊓ C ≠ ⊥ → R(A) ⊓ C ≠ ⊥
theorem overlapsPost_of_isUnderPost_overlaps
    {R : System α} {A B C : Pattern α}
    (hunder : isUnderPost R A B) (hoverlap : overlaps B C) :
    overlapsPost R A C :=
  match hoverlap with
  | ⟨after, hpost, htarget⟩ =>
    match hunder after hpost with
    | ⟨before, hsource, hstep⟩ => ⟨before, after, hsource, hstep, htarget⟩

/-! ## Multistep and invariance
`a =>* b`: zero or more steps. One closure for any step relation; a system's and a rule's
multisteps are its instances. -/

/-- `Steps step a b`: zero or more `step`s from `a` to `b` (reflexive-transitive closure). -/
inductive Steps (step : α → α → Prop) : α → α → Prop
  | refl (a : α) : Steps step a a
  | tail {a b c : α} : Steps step a b → step b c → Steps step a c

/-- `R.steps a b`: `a =>* b` under system `R`. -/
abbrev System.steps (R : System α) : α → α → Prop := Steps R.step

/-- `r.steps a b`: `a =>* b` under rule `r` alone. -/
abbrev Rule.steps (r : Rule α) : α → α → Prop := Steps r.step

-- I ⊑ A ∧ R(A) ⊑ A → every state reachable from I is in A
theorem invariant {R : System α} {I A : Pattern α}
    (hinit : subsumes I A) (hind : isOverPost R A A)
    {x y : α} (hx : I.holds x) (hxy : R.steps x y) : A.holds y := by
  induction hxy with
  | refl => exact hinit x hx
  | tail _ hstep ih => exact hind _ _ ih hstep

-- I ⊑ A ∧ R(A) ⊑ A ∧ A ⊑ P → every state reachable from I is in P
theorem invariant_safe {R : System α} {I A P : Pattern α}
    (hinit : subsumes I A) (hind : isOverPost R A A) (hsafe : subsumes A P)
    {x y : α} (hx : I.holds x) (hxy : R.steps x y) : P.holds y :=
  hsafe y (invariant hinit hind hx hxy)

-- R₁(S) ⊑ P ∧ R₂(S) ⊑ P → (R₁ ∪ R₂)(S) ⊑ P
theorem isOverPost_choice {R₁ R₂ : System α} {S P : Pattern α}
    (h₁ : isOverPost R₁ S P) (h₂ : isOverPost R₂ S P) : isOverPost (R₁ ++ R₂) S P :=
  fun a b ha hab => ((System.step_append _ _ _ _).1 hab).elim (h₁ a b ha) (h₂ a b ha)

end Expresso
