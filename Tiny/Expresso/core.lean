/-! Native pattern and transition semantics, independent of constructor encoding. -/
namespace Expresso

universe u

/-! ## Patterns and rules
`α` is the type of states. Its equality is ordinary `=`: sorts with structural
axioms (e.g. ACU bags) are quotient types, so `=` already means equality modulo
those axioms. -/

variable {α : Type u}

-- TODO: maybe separate out atomic pattern as a different type
inductive Patt (α : Type u) : Type (u + 1) where
  | bott : Patt α
  | atom (state : α) (cond : Prop := True) : Patt α
  | disj (left right : Patt α) : Patt α
  | bind {A : Type u} (body : A → Patt α) : Patt α

def Patt.holds : Patt α → α → Prop
  | .bott, _ => False
  | .atom state cond, actual => state = actual ∧ cond
  | .disj left right, state => left.holds state ∨ right.holds state
  | .bind body, state => ∃ a, (body a).holds state

-- make sense only for atomic patterns
def Patt.getTerm : Patt α → Option α
  | .atom state _ => some state
  | _ => none

inductive System (α : Type u) : Type (u + 1) where
  | empty : System α
  | rule (lhs rhs : α) (requires : Prop := True) : System α
  | choice (left right : System α) : System α
  | bind {A : Type u} (body : A → System α) : System α

def System.step : System α → α → α → Prop
  | .empty, _, _ => False
  | .rule lhs rhs cond, before, after =>
      lhs = before ∧ rhs = after ∧ cond
  | .choice left right, before, after =>
      left.step before after ∨ right.step before after
  | .bind body, before, after => ∃ a, (body a).step before after

/-! ## Semantic judgments and universal/existential decomposition
These describe ONE-STEP transitions. Choice is nondeterminism, not sequencing.
None of these definitions computes unifiers or post-images.
-/

def Subsumes (source target : Patt α) : Prop :=
  ∀ state, source.holds state → target.holds state

def Overlaps (left right : Patt α) : Prop :=
  ∃ state, left.holds state ∧ right.holds state

def postImage (rule : System α) (source : Patt α) (after : α) : Prop :=
  ∃ before, source.holds before ∧ rule.step before after

def MapsInto (rule : System α) (source target : Patt α) : Prop :=
  ∀ before after, source.holds before → rule.step before after →
    target.holds after

/-- No missing states: the candidate contains every actual successor.
This is the SAME universal mapping judgment, not a second semantics. -/
abbrev Over (rule : System α) (source post : Patt α) : Prop := MapsInto rule source post

/-- No junk states: every candidate state is an actual successor. -/
def Under (rule : System α) (source post : Patt α) : Prop :=
  ∀ after, post.holds after → postImage rule source after

def Exact (rule : System α) (source post : Patt α) : Prop :=
  Over rule source post ∧ Under rule source post

def Reaches (rule : System α) (source target : Patt α) : Prop :=
  ∃ before after, source.holds before ∧ rule.step before after ∧
    target.holds after

theorem mapsInto_of_over_subsumes
    {rule : System α} {source post target : Patt α}
    (over : Over rule source post) (subsumes : Subsumes post target) :
    MapsInto rule source target :=
  fun before after hsource hstep => subsumes after (over before after hsource hstep)

theorem reaches_of_under_overlaps
    {rule : System α} {source post target : Patt α}
    (under : Under rule source post) (overlap : Overlaps post target) :
    Reaches rule source target :=
  match overlap with
  | ⟨after, hpost, htarget⟩ =>
    match under after hpost with
    | ⟨before, hsource, hstep⟩ => ⟨before, after, hsource, hstep, htarget⟩

end Expresso
