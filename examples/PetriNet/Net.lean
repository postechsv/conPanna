import conPanna.BaseTheory.ACU
import conPanna.core

/-!
Place/transition Petri nets, generically (Meseguer, "Conditional rewriting logic as a
unified model of concurrency", §5.3.1). A marking is a multiset of places, the ACU sort
`ACU P`; a transition consumes the tokens `pre` and produces `post`, as the rewrite rule
`pre ⊗ R ⇒ post ⊗ R`, where `R` is the rest of the marking.

A concrete net declares its places (an inductive type), its transitions (named rules built
with `transition`), and its system (the list of its transitions). Its invariants are proved
per net, by narrowing its system.
-/

namespace PetriNet

open Expresso

/-- A marking: a multiset of places, `∅`, `{p}` and `M + M'`, equal modulo ACU. -/
abbrev Marking (P : Type) := ACU P

/-- The transition consuming `pre` and producing `post`: `pre ⊗ R ⇒ post ⊗ R`. -/
abbrev transition {P : Type} (pre post : Marking P) : Rule (Marking P) :=
  .bind fun (R : Marking P) => { lhs := pre + R, rhs := post + R }

end PetriNet
