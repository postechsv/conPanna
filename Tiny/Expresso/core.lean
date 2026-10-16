/-! Native pattern and transition semantics, independent of constructor encoding. -/
namespace Expresso

universe u

/-! ## Patterns and rules
`α` is the type of states. Its equality is ordinary `=`: sorts with structural
axioms (e.g. ACU bags) are quotient types, so `=` already means equality modulo
those axioms.

Three levels: a patch body has no variables; a patch binds them once, over one
type `A` (several variables go in a tuple); a pattern is a finite disjunction of
patches. Rule bodies, rules and systems follow the same shape. -/

variable {α : Type u}

/-- A patch body `⟨state | cond⟩`. -/
structure PatchBody (α : Type u) where
  state : α
  cond : Prop := True

/-- A patch `∃ a : A, body a`. -/
inductive Patch (α : Type u) : Type (u + 1) where
  | bind {A : Type u} (body : A → PatchBody α) : Patch α

inductive Pattern (α : Type u) : Type (u + 1) where
  | bott : Pattern α
  | patch (p : Patch α) : Pattern α
  | disj (left right : Pattern α) : Pattern α

def PatchBody.holds (p : PatchBody α) (actual : α) : Prop :=
  p.state = actual ∧ p.cond

def Patch.Vars : Patch α → Type u
  | .bind (A := A) _ => A

def Patch.holds : Patch α → α → Prop
  | .bind body, state => ∃ a, (body a).holds state

def Pattern.holds : Pattern α → α → Prop
  | .bott, _ => False
  | .patch p, state => p.holds state
  | .disj left right, state => left.holds state ∨ right.holds state

/-- A rule body `lhs => rhs if cond`. -/
structure RuleBody (α : Type u) where
  lhs : α
  rhs : α
  cond : Prop := True

/-- A rule `∀ a : A, body a`. -/
inductive Rule (α : Type u) : Type (u + 1) where
  | bind {A : Type u} (body : A → RuleBody α) : Rule α

inductive System (α : Type u) : Type (u + 1) where
  | empty : System α
  | rule (r : Rule α) : System α
  | choice (left right : System α) : System α

def RuleBody.step (r : RuleBody α) (before after : α) : Prop :=
  r.lhs = before ∧ r.rhs = after ∧ r.cond

def Rule.Vars : Rule α → Type u
  | .bind (A := A) _ => A

def Rule.step : Rule α → α → α → Prop
  | .bind body, before, after => ∃ a, (body a).step before after

def System.step : System α → α → α → Prop
  | .empty, _, _ => False
  | .rule r, before, after => r.step before after
  | .choice left right, before, after =>
      left.step before after ∨ right.step before after

/-! ## Semantic judgments and universal/existential decomposition
These describe ONE-STEP transitions. Choice is nondeterminism, not sequencing.
None of these definitions computes unifiers or post-images.
-/

-- R(A) ⊓ B ≠ ⊥ renaming? redifine using overlaps?
def hasStep (R : System α) (A B : Pattern α) : Prop :=
  ∃ a b, A.holds a ∧ R.step a b ∧ B.holds b

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

-- No Junk & No Miss : R(A) = B
def isPost (R : System α) (A B : Pattern α) : Prop :=
  isOverPost R A B ∧ isUnderPost R A B


-- R(A) ⊑ B ∧ C ⊑ B → R(A) ⊑ C
theorem over_of_subsumes
    {R : System α} {A B C : Pattern α}
    (hover : isOverPost R A C) (hsub : subsumes C B) :
    isOverPost R A B :=
  fun before after hsource hstep => hsub after (hover before after hsource hstep)

-- B ⊑ R(A) ∧ B ⊓ C ≠ ⊥ → R(A) ⊓ C ≠ ⊥
theorem hasStep_of_isUnderPost_overlaps
    {R : System α} {A B C : Pattern α}
    (hunder : isUnderPost R A B) (hoverlap : overlaps B C) :
    hasStep R A C :=
  match hoverlap with
  | ⟨after, hpost, htarget⟩ =>
    match hunder after hpost with
    | ⟨before, hsource, hstep⟩ => ⟨before, after, hsource, hstep, htarget⟩

end Expresso
