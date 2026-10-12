/-! Native pattern and transition semantics, independent of constructor encoding. -/
namespace Expresso

universe u v w x y

/-! ## Pattern and rule representations
B is the chosen equality on the state type: ordinary Eq or a supplied structural relation.
There is only ONE interpretation interface for each kind of representation.
Conditions remain predicates on the original assignments, not on quotient values.
-/

variable {α : Type u} {B : α → α → Prop}



structure RuleBody (α : Type u) where
  lhs : α
  rhs : α
  requires : Prop := True

/-- Shared data for heterogeneous pattern disjunction and rule choice. -/
structure Choice (P : Type v) (Q : Type w) where
  left : P
  right : Q

structure Atom (α : Type u) where
  term : α
  requires : Prop := True

inductive EmptyPattern where
  | empty

class Pattern (B : α → α → Prop) (P : Type v) where
  holds : P → α → Prop

instance : Pattern B α := ⟨fun term state => B term state⟩
instance : Pattern B (Atom α) := ⟨fun atom state => B atom.term state ∧ atom.requires⟩
instance {A : Type v} {P : Type w} [Pattern B P] : Pattern B (A → P) :=
  ⟨fun pattern state => ∃ a, Pattern.holds B (pattern a) state⟩
instance {P : Type v} {Q : Type w} [Pattern B P] [Pattern B Q] :
    Pattern B (Choice P Q) :=
  ⟨fun choice state => Pattern.holds B choice.left state ∨ Pattern.holds B choice.right state⟩
instance : Pattern B EmptyPattern := ⟨fun _ _ => False⟩

class Rules (B : α → α → Prop) (R : Type v) where
  step : R → α → α → Prop

instance : Rules B (RuleBody α) :=
  ⟨fun rule before after => B rule.lhs before ∧ B rule.rhs after ∧ rule.requires⟩
instance {A : Type v} {R : Type w} [Rules B R] : Rules B (A → R) :=
  ⟨fun rule before after => ∃ a, Rules.step B (rule a) before after⟩
instance {R : Type v} {S : Type w} [Rules B R] [Rules B S] : Rules B (Choice R S) :=
  ⟨fun choice before after => Rules.step B choice.left before after ∨
    Rules.step B choice.right before after⟩

/-! ## Semantic judgments and universal/existential decomposition
These describe ONE-STEP transitions. Choice is nondeterminism, not sequencing.
None of these definitions computes unifiers or post-images.
-/

variable {P : Type v} {Q : Type w} {Post : Type x} {R : Type y}

def Subsumes (B : α → α → Prop) [Pattern B P] [Pattern B Q]
    (source : P) (target : Q) : Prop :=
  ∀ state, Pattern.holds B source state → Pattern.holds B target state

def Overlaps (B : α → α → Prop) [Pattern B P] [Pattern B Q]
    (left : P) (right : Q) : Prop :=
  ∃ state, Pattern.holds B left state ∧ Pattern.holds B right state

def postImage (B : α → α → Prop) [Pattern B P] [Rules B R]
    (rule : R) (source : P) (after : α) : Prop :=
  ∃ before, Pattern.holds B source before ∧ Rules.step B rule before after

def MapsInto (B : α → α → Prop) [Pattern B P] [Pattern B Q] [Rules B R]
    (rule : R) (source : P) (target : Q) : Prop :=
  ∀ before after, Pattern.holds B source before → Rules.step B rule before after →
    Pattern.holds B target after

/-- No missing states: the candidate contains every actual successor.
This is the SAME universal mapping judgment, not a second semantics. -/
abbrev Over (B : α → α → Prop) [Pattern B P] [Pattern B Post] [Rules B R]
    (rule : R) (source : P) (post : Post) : Prop := MapsInto B rule source post

/-- No junk states: every candidate state is an actual successor. -/
def Under (B : α → α → Prop) [Pattern B P] [Pattern B Post] [Rules B R]
    (rule : R) (source : P) (post : Post) : Prop :=
  ∀ after, Pattern.holds B post after → postImage B rule source after

def Exact (B : α → α → Prop) [Pattern B P] [Pattern B Post] [Rules B R]
    (rule : R) (source : P) (post : Post) : Prop :=
  Over B rule source post ∧ Under B rule source post

def Reaches (B : α → α → Prop) [Pattern B P] [Pattern B Q] [Rules B R]
    (rule : R) (source : P) (target : Q) : Prop :=
  ∃ before after, Pattern.holds B source before ∧ Rules.step B rule before after ∧
    Pattern.holds B target after

theorem mapsInto_of_over_subsumes [Pattern B P] [Pattern B Post] [Pattern B Q] [Rules B R]
    {rule : R} {source : P} {post : Post} {target : Q}
    (over : Over B rule source post) (subsumes : Subsumes B post target) :
    MapsInto B rule source target :=
  fun before after hsource hstep => subsumes after (over before after hsource hstep)

theorem reaches_of_under_overlaps [Pattern B P] [Pattern B Post] [Pattern B Q] [Rules B R]
    {rule : R} {source : P} {post : Post} {target : Q}
    (under : Under B rule source post) (overlap : Overlaps B post target) :
    Reaches B rule source target :=
  match overlap with
  | ⟨after, hpost, htarget⟩ =>
    match under after hpost with
    | ⟨before, hsource, hstep⟩ => ⟨before, after, hsource, hstep, htarget⟩

end Expresso
