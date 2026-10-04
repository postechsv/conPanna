import conPanna.conPanna

/-!
Model-only Bakery variant: ordinary datatypes, with ACU registration attached to
the fragment. No safety proofs, certificates, encoding, or manual law witnesses.
`deriving ACU` identifies roles by constructor TYPE, not spelling.

The root command expands to structural assoc/comm/id declarations and the same
automatically proved indexed registration as `certify_structural`. This first
version supports one ACU fragment and first-order, nonparameterized sorts.
-/

namespace BakeryACU

inductive Mode where
  | idle
  | wait : Nat → Mode
  | crit : Nat → Mode
  deriving Repr

inductive ProcSet where
  | empty
  | singleton : Mode → ProcSet
  | union : ProcSet → ProcSet → ProcSet
  deriving Repr, ACU

structure Conf where
  next : Nat
  serving : Nat
  procs : ProcSet
  deriving Repr

instance : framework.State Conf := ⟨⟩

structural BakeryTheory for Conf

end BakeryACU
