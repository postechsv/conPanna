/-! Native pattern and transition semantics, independent of constructor encoding. -/
namespace Expresso

universe u

/-! ## Equality Parameterized Patterns and Rules -/

-- α is the type of states, B is a user defined equality relation.
variable {α : Type u} {B : α → α → Prop}

inductive Patt (α : Type u) : Type (u + 1) where
  | bott : Patt α
  | atom (state : α) (cond : Prop := True) : Patt α
  | disj (left right : Patt α) : Patt α
  | bind {A : Type u} (body : A → Patt α) : Patt α

-- Patt.holds B means "holds modulo B", e.g., Patt.holds Eq
def Patt.holds (B : α → α → Prop) : Patt α → α → Prop
  | .bott, _ => False
  | .atom state cond, actual => B state actual ∧ cond
  | .disj left right, state => left.holds B state ∨ right.holds B state
  | .bind body, state => ∃ a, (body a).holds B state

inductive System (α : Type u) : Type (u + 1) where
  | empty : System α
  | rule (lhs rhs : α) (requires : Prop := True) : System α
  | choice (left right : System α) : System α
  | bind {A : Type u} (body : A → System α) : System α

def System.step (B : α → α → Prop) : System α → α → α → Prop
  | .empty, _, _ => False
  | .rule lhs rhs cond, before, after =>
      B lhs before ∧ B rhs after ∧ cond
  | .choice left right, before, after =>
      left.step B before after ∨ right.step B before after
  | .bind body, before, after => ∃ a, (body a).step B before after

/-! ## Semantic judgments and universal/existential decomposition
These describe ONE-STEP transitions. Choice is nondeterminism, not sequencing.
None of these definitions computes unifiers or post-images.
-/

def Subsumes (B : α → α → Prop) (source target : Patt α) : Prop :=
  ∀ state, source.holds B state → target.holds B state

def Overlaps (B : α → α → Prop) (left right : Patt α) : Prop :=
  ∃ state, left.holds B state ∧ right.holds B state

def postImage (B : α → α → Prop)
    (rule : System α) (source : Patt α) (after : α) : Prop :=
  ∃ before, source.holds B before ∧ rule.step B before after

def MapsInto (B : α → α → Prop)
    (rule : System α) (source target : Patt α) : Prop :=
  ∀ before after, source.holds B before → rule.step B before after →
    target.holds B after

/-- No missing states: the candidate contains every actual successor.
This is the SAME universal mapping judgment, not a second semantics. -/
abbrev Over (B : α → α → Prop)
    (rule : System α) (source post : Patt α) : Prop := MapsInto B rule source post

/-- No junk states: every candidate state is an actual successor. -/
def Under (B : α → α → Prop)
    (rule : System α) (source post : Patt α) : Prop :=
  ∀ after, post.holds B after → postImage B rule source after

def Exact (B : α → α → Prop)
    (rule : System α) (source post : Patt α) : Prop :=
  Over B rule source post ∧ Under B rule source post

def Reaches (B : α → α → Prop)
    (rule : System α) (source target : Patt α) : Prop :=
  ∃ before after, source.holds B before ∧ rule.step B before after ∧
    target.holds B after

theorem mapsInto_of_over_subsumes
    {rule : System α} {source post target : Patt α}
    (over : Over B rule source post) (subsumes : Subsumes B post target) :
    MapsInto B rule source target :=
  fun before after hsource hstep => subsumes after (over before after hsource hstep)

theorem reaches_of_under_overlaps
    {rule : System α} {source post target : Patt α}
    (under : Under B rule source post) (overlap : Overlaps B post target) :
    Reaches B rule source target :=
  match overlap with
  | ⟨after, hpost, htarget⟩ =>
    match under after hpost with
    | ⟨before, hsource, hstep⟩ => ⟨before, after, hsource, hstep, htarget⟩

end Expresso
