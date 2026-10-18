import conPanna.Unification.Certification.Tactics

/-!
Bakery transition: rule ENTER's left side against a three-process state. The
claim (model, problem) is written by the user;
producer/tools/compile.py appends the answers and the proof from `enter.deriv`.
-/

/- certify
{
  "namespace": "Demo.Enter",
  "context": "Γ₀",
  "vars": [
    "K?",
    "P?",
    "N?",
    "M?",
    "Q?"
  ],
  "ops": {
    "<_,_,_>": "Conf.mk",
    "s": "({0} + 1)",
    "wait": "Mode.wait",
    "idle": "Mode.idle",
    "crit": "Mode.crit"
  }
}
-/

open Unification Certification

namespace Demo.Enter

/-! ## Claim -/

inductive Mode where
  | idle
  | wait (ticket : Nat)
  | crit (ticket : Nat)

abbrev ProcSet := ACU Mode

structure Conf where
  next : Nat
  serving : Nat
  procs : ProcSet

abbrev Γ₀ := Nat × ProcSet × Nat × Nat × ProcSet

-- < K?+1, K?, {wait K?} + P? >  =?  < N?+1, N?, {wait N?} + {idle} + {wait M?} + Q? >
def problem : Problem Conf Γ₀ :=
  .bind fun (K?, P?, N?, M?, Q?) =>
    (⟨K? + 1, K?, {Mode.wait K?} + P?⟩, ⟨N? + 1, N?, {Mode.wait N?} + {Mode.idle} + {Mode.wait M?} + Q?⟩)
