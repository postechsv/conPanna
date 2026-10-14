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

def Subsumes (source target : Pattern α) : Prop :=
  ∀ state, source.holds state → target.holds state

def Overlaps (left right : Pattern α) : Prop :=
  ∃ state, left.holds state ∧ right.holds state

def postImage (rule : System α) (source : Pattern α) (after : α) : Prop :=
  ∃ before, source.holds before ∧ rule.step before after

def MapsInto (rule : System α) (source target : Pattern α) : Prop :=
  ∀ before after, source.holds before → rule.step before after →
    target.holds after

/-- No missing states: the candidate contains every actual successor.
This is the SAME universal mapping judgment, not a second semantics. -/
abbrev Over (rule : System α) (source post : Pattern α) : Prop := MapsInto rule source post

/-- No junk states: every candidate state is an actual successor. -/
def Under (rule : System α) (source post : Pattern α) : Prop :=
  ∀ after, post.holds after → postImage rule source after

def Exact (rule : System α) (source post : Pattern α) : Prop :=
  Over rule source post ∧ Under rule source post

def Reaches (rule : System α) (source target : Pattern α) : Prop :=
  ∃ before after, source.holds before ∧ rule.step before after ∧
    target.holds after

theorem mapsInto_of_over_subsumes
    {rule : System α} {source post target : Pattern α}
    (over : Over rule source post) (subsumes : Subsumes post target) :
    MapsInto rule source target :=
  fun before after hsource hstep => subsumes after (over before after hsource hstep)

theorem reaches_of_under_overlaps
    {rule : System α} {source post target : Pattern α}
    (under : Under rule source post) (overlap : Overlaps post target) :
    Reaches rule source target :=
  match overlap with
  | ⟨after, hpost, htarget⟩ =>
    match under after hpost with
    | ⟨before, hsource, hstep⟩ => ⟨before, after, hsource, hstep, htarget⟩

end Expresso
