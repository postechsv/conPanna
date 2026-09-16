import Expresso.Expresso
import conPanna.Structural

/-!
Theory-indexed pattern and rewrite semantics. Raw model terms remain ordinary
Lean values; only semantic matching is interpreted through `Structural.EqMod`.
-/
namespace framework

universe u v w x y

namespace Patterns

class APattMod (theory : Structural.Theory.{u})
    (α : outParam (Type u)) [State α] (P : Type v) where
  semantics : P → α → Prop

instance {theory : Structural.Theory.{u}} {α : Type u} [State α] :
    APattMod theory α α where
  semantics pattern state := Structural.EqMod theory pattern state

instance {theory : Structural.Theory.{u}} {α : Type u} [State α] :
    APattMod theory α (APattBody α) where
  semantics pattern state :=
    Structural.EqMod theory pattern.term state ∧ pattern.requires

instance {theory : Structural.Theory.{u}} {α : Type u} {A : Type v}
    {P : Type w} [State α] [APattMod theory α P] :
    APattMod theory α (A → P) where
  semantics pattern state :=
    ∃ argument, APattMod.semantics theory (pattern argument) state

class PatternMod (theory : Structural.Theory.{u})
    (α : outParam (Type u)) [State α] (P : Type v) where
  semantics : P → α → Prop

instance {theory : Structural.Theory.{u}} {α : Type u} {P : Type v}
    [State α] [APattMod theory α P] : PatternMod theory α P where
  semantics := APattMod.semantics theory

instance {theory : Structural.Theory.{u}} {α : Type u}
    {P : Type v} {Q : Type w} [State α]
    [PatternMod theory α P] [PatternMod theory α Q] :
    PatternMod theory α (Disjunction P Q) where
  semantics patterns state :=
    PatternMod.semantics theory patterns.left state ∨
    PatternMod.semantics theory patterns.right state

instance {theory : Structural.Theory.{u}} {α : Type u} [State α] :
    APattMod theory α (EmptyPattern α) where
  semantics _ _ := False

def SubsumesMod (theory : Structural.Theory.{u})
    {α : Type u} {P : Type v} {Q : Type w}
    [State α] [PatternMod theory α P] [PatternMod theory α Q]
    (source : P) (target : Q) : Prop :=
  ∀ state, PatternMod.semantics theory source state →
    PatternMod.semantics theory target state

notation:50 source " ⊑[" theory "] " target =>
  SubsumesMod theory source target

end Patterns


namespace Rules

open Patterns

class AtRuleMod (theory : Structural.Theory.{u})
    (α : outParam (Type u)) [State α] (R : Type v) where
  semantics : R → α → α → Prop

instance {theory : Structural.Theory.{u}} {α : Type u} [State α] :
    AtRuleMod theory α (RuleBody α) where
  semantics rule before after :=
    Structural.EqMod theory rule.lhs before ∧
    Structural.EqMod theory rule.rhs after ∧ rule.requires

instance {theory : Structural.Theory.{u}} {α : Type u}
    {A : Type v} {R : Type w} [State α] [AtRuleMod theory α R] :
    AtRuleMod theory α (A → R) where
  semantics rule before after :=
    ∃ argument, AtRuleMod.semantics theory (rule argument) before after

def postImageMod (theory : Structural.Theory.{u})
    {α : Type u} {P : Type v} {R : Type w}
    [State α] [PatternMod theory α P] [AtRuleMod theory α R]
    (rule : R) (source : P) (after : α) : Prop :=
  ∃ before,
    PatternMod.semantics theory source before ∧
    AtRuleMod.semantics theory rule before after

def NarrowsToMod (theory : Structural.Theory.{u})
    {α : Type u} {P : Type v} {Post : Type w} {R : Type x}
    [State α] [PatternMod theory α P] [PatternMod theory α Post]
    [AtRuleMod theory α R]
    (rule : R) (source : P) (post : Post) : Prop :=
  ∀ after,
    PatternMod.semantics theory post after ↔
      postImageMod theory rule source after

notation:40 rule " ⊢[" theory "] " source " ↝ " post =>
  NarrowsToMod theory rule source post

/-- A computed post overapproximates every semantic one-step result. -/
def CoversPostMod (theory : Structural.Theory.{u})
    {α : Type u} {P : Type v} {Post : Type w} {R : Type x}
    [State α] [PatternMod theory α P] [PatternMod theory α Post]
    [AtRuleMod theory α R]
    (rule : R) (source : P) (post : Post) : Prop :=
  ∀ after, postImageMod theory rule source after →
    PatternMod.semantics theory post after

notation:40 rule " ⊢[" theory "] " source " ↝≤ " post =>
  CoversPostMod theory rule source post

def mapsIntoMod (theory : Structural.Theory.{u})
    {α : Type u} {P : Type v} {Q : Type w} {R : Type x}
    [State α] [PatternMod theory α P] [PatternMod theory α Q]
    [AtRuleMod theory α R]
    (rule : R) (source : P) (target : Q) : Prop :=
  ∀ before after,
    PatternMod.semantics theory source before →
    AtRuleMod.semantics theory rule before after →
    PatternMod.semantics theory target after

notation:40 rule " ⊢[" theory "] " source " ↪ " target =>
  mapsIntoMod theory rule source target

theorem mapsInto_of_narrowsTo_of_subsumes_mod
    {theory : Structural.Theory.{u}}
    {α : Type u} {P : Type v} {Post : Type w} {Q : Type x}
    {R : Type y} [State α] [PatternMod theory α P]
    [PatternMod theory α Post] [PatternMod theory α Q]
    [AtRuleMod theory α R]
    {rule : R} {source : P} {post : Post} {target : Q}
    (hnarrow : NarrowsToMod theory rule source post)
    (hsubsumes : SubsumesMod theory post target) :
    mapsIntoMod theory rule source target := by
  intro before after hsource hrule
  apply hsubsumes after
  exact (hnarrow after).2 ⟨before, hsource, hrule⟩

theorem mapsInto_of_cover_of_subsumes_mod
    {theory : Structural.Theory.{u}}
    {α : Type u} {P : Type v} {Post : Type w} {Q : Type x}
    {R : Type y} [State α] [PatternMod theory α P]
    [PatternMod theory α Post] [PatternMod theory α Q]
    [AtRuleMod theory α R]
    {rule : R} {source : P} {post : Post} {target : Q}
    (hcover : CoversPostMod theory rule source post)
    (hsubsumes : SubsumesMod theory post target) :
    mapsIntoMod theory rule source target := by
  intro before after hsource hrule
  apply hsubsumes after
  exact hcover after ⟨before, hsource, hrule⟩

theorem mapsInto_via_narrowing_mod
    {theory : Structural.Theory.{u}}
    {α : Type u} {P : Type v} {Q : Type w} {R : Type x}
    [state : State α] [sourcePattern : PatternMod theory α P]
    [targetPattern : PatternMod theory α Q]
    [ruleSemantics : AtRuleMod theory α R]
    {rule : R} {source : P} {target : Q}
    (decomposition :
      ∃ (Post : Type y) (postPattern : PatternMod theory α Post)
          (post : Post),
        @CoversPostMod theory α P Post R state sourcePattern postPattern
            ruleSemantics rule source post ∧
        @SubsumesMod theory α Post Q state postPattern targetPattern
            post target) :
    mapsIntoMod theory rule source target := by
  rcases decomposition with
    ⟨Post, postPattern, post, narrowing, subsumption⟩
  exact @mapsInto_of_cover_of_subsumes_mod theory α P Post Q R
    state sourcePattern postPattern targetPattern ruleSemantics
    rule source post target narrowing subsumption

end Rules

export Patterns (APattMod PatternMod SubsumesMod)
export Rules (AtRuleMod postImageMod NarrowsToMod CoversPostMod mapsIntoMod
  mapsInto_of_narrowsTo_of_subsumes_mod mapsInto_of_cover_of_subsumes_mod
  mapsInto_via_narrowing_mod)

end framework
