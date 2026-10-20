import examples.OTR.agreement.pf
import conPanna.Unification.Tactics.maudeCertifyComp

/-!
OneThirdRule: the obligations of `otr_inv`, printed by `#obligations` and pasted verbatim.
Completeness is certified by Maude (`maude_certify_comp`); soundness by instantiating each
unifier and checking the two sides equal modulo ACU.
-/

namespace OTRA

open Expresso Unification Narrowing

-- the statements below are `#obligations`' output, pasted verbatim
set_option linter.style.longLine false

theorem otr_inv.obligation_1 :
    Unification.complete (Narrowing.mayFire voteT invP)
      [Unification.Unifier.bind fun (x : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × Log) =>
          ((x.2.2.2.2.2.1, x.1, ∅, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, ∅, x.2.2.2.2.2.2), x.2.2.2.2.2.1, {x.1},
            {Item.node
                { id := x.1, round := x.2.1, step := Step.init, value := true, dec := Dec.undecided, vt := x.2.2.1,
                  vf := x.2.2.2.1, va := x.2.2.2.2.1 }},
            x.2.2.2.2.2.2),
        Unification.Unifier.bind fun (x : ℕ × Items × ℕ × ℕ × ℕ × ℕ × ℕ × Log) =>
          ((x.2.2.2.2.2.2.1, x.1, ∅, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.1, x.2.2.2.2.2.2.2),
            x.2.2.2.2.2.2.1, {x.1},
            x.2.1 +
              {Item.node
                  { id := x.1, round := x.2.2.1, step := Step.init, value := true, dec := Dec.undecided,
                    vt := x.2.2.2.1, vf := x.2.2.2.2.1, va := x.2.2.2.2.2.1 }},
            x.2.2.2.2.2.2.2),
        Unification.Unifier.bind fun (x : ℕ × OidSet × ℕ × ℕ × ℕ × ℕ × ℕ × Log) =>
          ((x.2.2.2.2.2.2.1, x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, ∅, x.2.2.2.2.2.2.2),
            x.2.2.2.2.2.2.1, {x.1} + x.2.1,
            {Item.node
                { id := x.1, round := x.2.2.1, step := Step.init, value := true, dec := Dec.undecided, vt := x.2.2.2.1,
                  vf := x.2.2.2.2.1, va := x.2.2.2.2.2.1 }},
            x.2.2.2.2.2.2.2),
        Unification.Unifier.bind fun (x : ℕ × OidSet × Items × ℕ × ℕ × ℕ × ℕ × ℕ × Log) =>
          ((x.2.2.2.2.2.2.2.1, x.1, x.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.1,
              x.2.2.2.2.2.2.2.2),
            x.2.2.2.2.2.2.2.1, {x.1} + x.2.1,
            x.2.2.1 +
              {Item.node
                  { id := x.1, round := x.2.2.2.1, step := Step.init, value := true, dec := Dec.undecided,
                    vt := x.2.2.2.2.1, vf := x.2.2.2.2.2.1, va := x.2.2.2.2.2.2.1 }},
            x.2.2.2.2.2.2.2.2)] := by
  maude_certify_comp

theorem otr_inv.obligation_2 :
    Unification.sound (Narrowing.mayFire voteT invP)
      [Unification.Unifier.bind fun (x : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × Log) =>
          ((x.2.2.2.2.2.1, x.1, ∅, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, ∅, x.2.2.2.2.2.2), x.2.2.2.2.2.1, {x.1},
            {Item.node
                { id := x.1, round := x.2.1, step := Step.init, value := true, dec := Dec.undecided, vt := x.2.2.1,
                  vf := x.2.2.2.1, va := x.2.2.2.2.1 }},
            x.2.2.2.2.2.2),
        Unification.Unifier.bind fun (x : ℕ × Items × ℕ × ℕ × ℕ × ℕ × ℕ × Log) =>
          ((x.2.2.2.2.2.2.1, x.1, ∅, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.1, x.2.2.2.2.2.2.2),
            x.2.2.2.2.2.2.1, {x.1},
            x.2.1 +
              {Item.node
                  { id := x.1, round := x.2.2.1, step := Step.init, value := true, dec := Dec.undecided,
                    vt := x.2.2.2.1, vf := x.2.2.2.2.1, va := x.2.2.2.2.2.1 }},
            x.2.2.2.2.2.2.2),
        Unification.Unifier.bind fun (x : ℕ × OidSet × ℕ × ℕ × ℕ × ℕ × ℕ × Log) =>
          ((x.2.2.2.2.2.2.1, x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, ∅, x.2.2.2.2.2.2.2),
            x.2.2.2.2.2.2.1, {x.1} + x.2.1,
            {Item.node
                { id := x.1, round := x.2.2.1, step := Step.init, value := true, dec := Dec.undecided, vt := x.2.2.2.1,
                  vf := x.2.2.2.2.1, va := x.2.2.2.2.2.1 }},
            x.2.2.2.2.2.2.2),
        Unification.Unifier.bind fun (x : ℕ × OidSet × Items × ℕ × ℕ × ℕ × ℕ × ℕ × Log) =>
          ((x.2.2.2.2.2.2.2.1, x.1, x.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.1,
              x.2.2.2.2.2.2.2.2),
            x.2.2.2.2.2.2.2.1, {x.1} + x.2.1,
            x.2.2.1 +
              {Item.node
                  { id := x.1, round := x.2.2.2.1, step := Step.init, value := true, dec := Dec.undecided,
                    vt := x.2.2.2.2.1, vf := x.2.2.2.2.2.1, va := x.2.2.2.2.2.2.1 }},
            x.2.2.2.2.2.2.2.2)] := by
  simp only [sound, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  repeat' apply And.intro
  all_goals
    rintro γ ⟨x, rfl⟩
    simp only [unifiedBy, mayFire, voteT, invP]
    try ac_rfl

theorem otr_inv.obligation_3 :
    Unification.complete (Narrowing.mayFire voteF invP)
      [Unification.Unifier.bind fun (x : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × Log) =>
          ((x.2.2.2.2.2.1, x.1, ∅, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, ∅, x.2.2.2.2.2.2), x.2.2.2.2.2.1, {x.1},
            {Item.node
                { id := x.1, round := x.2.1, step := Step.init, value := false, dec := Dec.undecided, vt := x.2.2.1,
                  vf := x.2.2.2.1, va := x.2.2.2.2.1 }},
            x.2.2.2.2.2.2),
        Unification.Unifier.bind fun (x : ℕ × Items × ℕ × ℕ × ℕ × ℕ × ℕ × Log) =>
          ((x.2.2.2.2.2.2.1, x.1, ∅, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.1, x.2.2.2.2.2.2.2),
            x.2.2.2.2.2.2.1, {x.1},
            x.2.1 +
              {Item.node
                  { id := x.1, round := x.2.2.1, step := Step.init, value := false, dec := Dec.undecided,
                    vt := x.2.2.2.1, vf := x.2.2.2.2.1, va := x.2.2.2.2.2.1 }},
            x.2.2.2.2.2.2.2),
        Unification.Unifier.bind fun (x : ℕ × OidSet × ℕ × ℕ × ℕ × ℕ × ℕ × Log) =>
          ((x.2.2.2.2.2.2.1, x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, ∅, x.2.2.2.2.2.2.2),
            x.2.2.2.2.2.2.1, {x.1} + x.2.1,
            {Item.node
                { id := x.1, round := x.2.2.1, step := Step.init, value := false, dec := Dec.undecided, vt := x.2.2.2.1,
                  vf := x.2.2.2.2.1, va := x.2.2.2.2.2.1 }},
            x.2.2.2.2.2.2.2),
        Unification.Unifier.bind fun (x : ℕ × OidSet × Items × ℕ × ℕ × ℕ × ℕ × ℕ × Log) =>
          ((x.2.2.2.2.2.2.2.1, x.1, x.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.1,
              x.2.2.2.2.2.2.2.2),
            x.2.2.2.2.2.2.2.1, {x.1} + x.2.1,
            x.2.2.1 +
              {Item.node
                  { id := x.1, round := x.2.2.2.1, step := Step.init, value := false, dec := Dec.undecided,
                    vt := x.2.2.2.2.1, vf := x.2.2.2.2.2.1, va := x.2.2.2.2.2.2.1 }},
            x.2.2.2.2.2.2.2.2)] := by
  maude_certify_comp

theorem otr_inv.obligation_4 :
    Unification.sound (Narrowing.mayFire voteF invP)
      [Unification.Unifier.bind fun (x : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × Log) =>
          ((x.2.2.2.2.2.1, x.1, ∅, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, ∅, x.2.2.2.2.2.2), x.2.2.2.2.2.1, {x.1},
            {Item.node
                { id := x.1, round := x.2.1, step := Step.init, value := false, dec := Dec.undecided, vt := x.2.2.1,
                  vf := x.2.2.2.1, va := x.2.2.2.2.1 }},
            x.2.2.2.2.2.2),
        Unification.Unifier.bind fun (x : ℕ × Items × ℕ × ℕ × ℕ × ℕ × ℕ × Log) =>
          ((x.2.2.2.2.2.2.1, x.1, ∅, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.1, x.2.2.2.2.2.2.2),
            x.2.2.2.2.2.2.1, {x.1},
            x.2.1 +
              {Item.node
                  { id := x.1, round := x.2.2.1, step := Step.init, value := false, dec := Dec.undecided,
                    vt := x.2.2.2.1, vf := x.2.2.2.2.1, va := x.2.2.2.2.2.1 }},
            x.2.2.2.2.2.2.2),
        Unification.Unifier.bind fun (x : ℕ × OidSet × ℕ × ℕ × ℕ × ℕ × ℕ × Log) =>
          ((x.2.2.2.2.2.2.1, x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, ∅, x.2.2.2.2.2.2.2),
            x.2.2.2.2.2.2.1, {x.1} + x.2.1,
            {Item.node
                { id := x.1, round := x.2.2.1, step := Step.init, value := false, dec := Dec.undecided, vt := x.2.2.2.1,
                  vf := x.2.2.2.2.1, va := x.2.2.2.2.2.1 }},
            x.2.2.2.2.2.2.2),
        Unification.Unifier.bind fun (x : ℕ × OidSet × Items × ℕ × ℕ × ℕ × ℕ × ℕ × Log) =>
          ((x.2.2.2.2.2.2.2.1, x.1, x.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.1,
              x.2.2.2.2.2.2.2.2),
            x.2.2.2.2.2.2.2.1, {x.1} + x.2.1,
            x.2.2.1 +
              {Item.node
                  { id := x.1, round := x.2.2.2.1, step := Step.init, value := false, dec := Dec.undecided,
                    vt := x.2.2.2.2.1, vf := x.2.2.2.2.2.1, va := x.2.2.2.2.2.2.1 }},
            x.2.2.2.2.2.2.2.2)] := by
  simp only [sound, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  repeat' apply And.intro
  all_goals
    rintro γ ⟨x, rfl⟩
    simp only [unifiedBy, mayFire, voteF, invP]
    try ac_rfl

theorem otr_inv.obligation_5 :
    Unification.complete (Narrowing.mayFire recvT invP)
      [Unification.Unifier.bind fun (x : ℕ × OidSet × Log × ℕ × Bool × Dec × ℕ × ℕ × ℕ × ℕ × ℕ) =>
          ((x.2.2.2.2.2.2.2.2.2.2, x.2.1, x.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1, ∅, ∅, x.2.2.1),
            x.2.2.2.2.2.2.2.2.2.2, x.2.1,
            {Item.node
                  { id := x.1, round := x.2.2.2.1, step := Step.wait, value := x.2.2.2.2.1, dec := x.2.2.2.2.2.1,
                    vt := x.2.2.2.2.2.2.1, vf := x.2.2.2.2.2.2.2.1, va := x.2.2.2.2.2.2.2.2.1 }} +
              {Item.msg true x.2.2.2.1 x.2.2.2.2.2.2.2.2.2.1 {x.1}},
            x.2.2.1),
        Unification.Unifier.bind fun (x : ℕ × ℕ × OidSet × Log × ℕ × Bool × Dec × ℕ × ℕ × ℕ × ℕ × OidSet) =>
          ((x.2.1, x.2.2.1, x.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2, ∅, x.2.2.2.1),
            x.2.1, x.2.2.1,
            {Item.node
                  { id := x.1, round := x.2.2.2.2.1, step := Step.wait, value := x.2.2.2.2.2.1, dec := x.2.2.2.2.2.2.1,
                    vt := x.2.2.2.2.2.2.2.1, vf := x.2.2.2.2.2.2.2.2.1, va := x.2.2.2.2.2.2.2.2.2.1 }} +
              {Item.msg true x.2.2.2.2.1 x.2.2.2.2.2.2.2.2.2.2.1 ({x.1} + x.2.2.2.2.2.2.2.2.2.2.2)},
            x.2.2.2.1),
        Unification.Unifier.bind fun (x : Items × ℕ × OidSet × Log × ℕ × ℕ × Bool × Dec × ℕ × ℕ × ℕ × ℕ) =>
          ((x.2.1, x.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2, ∅, x.1, x.2.2.2.1),
            x.2.1, x.2.2.1,
            x.1 +
                {Item.node
                    { id := x.2.2.2.2.1, round := x.2.2.2.2.2.1, step := Step.wait, value := x.2.2.2.2.2.2.1,
                      dec := x.2.2.2.2.2.2.2.1, vt := x.2.2.2.2.2.2.2.2.1, vf := x.2.2.2.2.2.2.2.2.2.1,
                      va := x.2.2.2.2.2.2.2.2.2.2.1 }} +
              {Item.msg true x.2.2.2.2.2.1 x.2.2.2.2.2.2.2.2.2.2.2 {x.2.2.2.2.1}},
            x.2.2.2.1),
        Unification.Unifier.bind fun (x : Items × OidSet × ℕ × OidSet × Log × ℕ × ℕ × Bool × Dec × ℕ × ℕ × ℕ × ℕ) =>
          ((x.2.2.1, x.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2,
              x.2.1, x.1, x.2.2.2.2.1),
            x.2.2.1, x.2.2.2.1,
            x.1 +
                {Item.node
                    { id := x.2.2.2.2.2.1, round := x.2.2.2.2.2.2.1, step := Step.wait, value := x.2.2.2.2.2.2.2.1,
                      dec := x.2.2.2.2.2.2.2.2.1, vt := x.2.2.2.2.2.2.2.2.2.1, vf := x.2.2.2.2.2.2.2.2.2.2.1,
                      va := x.2.2.2.2.2.2.2.2.2.2.2.1 }} +
              {Item.msg true x.2.2.2.2.2.2.1 x.2.2.2.2.2.2.2.2.2.2.2.2 ({x.2.2.2.2.2.1} + x.2.1)},
            x.2.2.2.2.1)] := by
  maude_certify_comp

theorem otr_inv.obligation_6 :
    Unification.sound (Narrowing.mayFire recvT invP)
      [Unification.Unifier.bind fun (x : ℕ × OidSet × Log × ℕ × Bool × Dec × ℕ × ℕ × ℕ × ℕ × ℕ) =>
          ((x.2.2.2.2.2.2.2.2.2.2, x.2.1, x.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1, ∅, ∅, x.2.2.1),
            x.2.2.2.2.2.2.2.2.2.2, x.2.1,
            {Item.node
                  { id := x.1, round := x.2.2.2.1, step := Step.wait, value := x.2.2.2.2.1, dec := x.2.2.2.2.2.1,
                    vt := x.2.2.2.2.2.2.1, vf := x.2.2.2.2.2.2.2.1, va := x.2.2.2.2.2.2.2.2.1 }} +
              {Item.msg true x.2.2.2.1 x.2.2.2.2.2.2.2.2.2.1 {x.1}},
            x.2.2.1),
        Unification.Unifier.bind fun (x : ℕ × ℕ × OidSet × Log × ℕ × Bool × Dec × ℕ × ℕ × ℕ × ℕ × OidSet) =>
          ((x.2.1, x.2.2.1, x.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2, ∅, x.2.2.2.1),
            x.2.1, x.2.2.1,
            {Item.node
                  { id := x.1, round := x.2.2.2.2.1, step := Step.wait, value := x.2.2.2.2.2.1, dec := x.2.2.2.2.2.2.1,
                    vt := x.2.2.2.2.2.2.2.1, vf := x.2.2.2.2.2.2.2.2.1, va := x.2.2.2.2.2.2.2.2.2.1 }} +
              {Item.msg true x.2.2.2.2.1 x.2.2.2.2.2.2.2.2.2.2.1 ({x.1} + x.2.2.2.2.2.2.2.2.2.2.2)},
            x.2.2.2.1),
        Unification.Unifier.bind fun (x : Items × ℕ × OidSet × Log × ℕ × ℕ × Bool × Dec × ℕ × ℕ × ℕ × ℕ) =>
          ((x.2.1, x.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2, ∅, x.1, x.2.2.2.1),
            x.2.1, x.2.2.1,
            x.1 +
                {Item.node
                    { id := x.2.2.2.2.1, round := x.2.2.2.2.2.1, step := Step.wait, value := x.2.2.2.2.2.2.1,
                      dec := x.2.2.2.2.2.2.2.1, vt := x.2.2.2.2.2.2.2.2.1, vf := x.2.2.2.2.2.2.2.2.2.1,
                      va := x.2.2.2.2.2.2.2.2.2.2.1 }} +
              {Item.msg true x.2.2.2.2.2.1 x.2.2.2.2.2.2.2.2.2.2.2 {x.2.2.2.2.1}},
            x.2.2.2.1),
        Unification.Unifier.bind fun (x : Items × OidSet × ℕ × OidSet × Log × ℕ × ℕ × Bool × Dec × ℕ × ℕ × ℕ × ℕ) =>
          ((x.2.2.1, x.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2,
              x.2.1, x.1, x.2.2.2.2.1),
            x.2.2.1, x.2.2.2.1,
            x.1 +
                {Item.node
                    { id := x.2.2.2.2.2.1, round := x.2.2.2.2.2.2.1, step := Step.wait, value := x.2.2.2.2.2.2.2.1,
                      dec := x.2.2.2.2.2.2.2.2.1, vt := x.2.2.2.2.2.2.2.2.2.1, vf := x.2.2.2.2.2.2.2.2.2.2.1,
                      va := x.2.2.2.2.2.2.2.2.2.2.2.1 }} +
              {Item.msg true x.2.2.2.2.2.2.1 x.2.2.2.2.2.2.2.2.2.2.2.2 ({x.2.2.2.2.2.1} + x.2.1)},
            x.2.2.2.2.1)] := by
  simp only [sound, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  repeat' apply And.intro
  all_goals
    rintro γ ⟨x, rfl⟩
    simp only [unifiedBy, mayFire, recvT, invP]
    try ac_rfl

theorem otr_inv.obligation_7 :
    Unification.complete (Narrowing.mayFire recvF invP)
      [Unification.Unifier.bind fun (x : ℕ × OidSet × Log × ℕ × Bool × Dec × ℕ × ℕ × ℕ × ℕ × ℕ) =>
          ((x.2.2.2.2.2.2.2.2.2.2, x.2.1, x.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1, ∅, ∅, x.2.2.1),
            x.2.2.2.2.2.2.2.2.2.2, x.2.1,
            {Item.node
                  { id := x.1, round := x.2.2.2.1, step := Step.wait, value := x.2.2.2.2.1, dec := x.2.2.2.2.2.1,
                    vt := x.2.2.2.2.2.2.1, vf := x.2.2.2.2.2.2.2.1, va := x.2.2.2.2.2.2.2.2.1 }} +
              {Item.msg false x.2.2.2.1 x.2.2.2.2.2.2.2.2.2.1 {x.1}},
            x.2.2.1),
        Unification.Unifier.bind fun (x : ℕ × ℕ × OidSet × Log × ℕ × Bool × Dec × ℕ × ℕ × ℕ × ℕ × OidSet) =>
          ((x.2.1, x.2.2.1, x.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2, ∅, x.2.2.2.1),
            x.2.1, x.2.2.1,
            {Item.node
                  { id := x.1, round := x.2.2.2.2.1, step := Step.wait, value := x.2.2.2.2.2.1, dec := x.2.2.2.2.2.2.1,
                    vt := x.2.2.2.2.2.2.2.1, vf := x.2.2.2.2.2.2.2.2.1, va := x.2.2.2.2.2.2.2.2.2.1 }} +
              {Item.msg false x.2.2.2.2.1 x.2.2.2.2.2.2.2.2.2.2.1 ({x.1} + x.2.2.2.2.2.2.2.2.2.2.2)},
            x.2.2.2.1),
        Unification.Unifier.bind fun (x : Items × ℕ × OidSet × Log × ℕ × ℕ × Bool × Dec × ℕ × ℕ × ℕ × ℕ) =>
          ((x.2.1, x.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2, ∅, x.1, x.2.2.2.1),
            x.2.1, x.2.2.1,
            x.1 +
                {Item.node
                    { id := x.2.2.2.2.1, round := x.2.2.2.2.2.1, step := Step.wait, value := x.2.2.2.2.2.2.1,
                      dec := x.2.2.2.2.2.2.2.1, vt := x.2.2.2.2.2.2.2.2.1, vf := x.2.2.2.2.2.2.2.2.2.1,
                      va := x.2.2.2.2.2.2.2.2.2.2.1 }} +
              {Item.msg false x.2.2.2.2.2.1 x.2.2.2.2.2.2.2.2.2.2.2 {x.2.2.2.2.1}},
            x.2.2.2.1),
        Unification.Unifier.bind fun (x : Items × OidSet × ℕ × OidSet × Log × ℕ × ℕ × Bool × Dec × ℕ × ℕ × ℕ × ℕ) =>
          ((x.2.2.1, x.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2,
              x.2.1, x.1, x.2.2.2.2.1),
            x.2.2.1, x.2.2.2.1,
            x.1 +
                {Item.node
                    { id := x.2.2.2.2.2.1, round := x.2.2.2.2.2.2.1, step := Step.wait, value := x.2.2.2.2.2.2.2.1,
                      dec := x.2.2.2.2.2.2.2.2.1, vt := x.2.2.2.2.2.2.2.2.2.1, vf := x.2.2.2.2.2.2.2.2.2.2.1,
                      va := x.2.2.2.2.2.2.2.2.2.2.2.1 }} +
              {Item.msg false x.2.2.2.2.2.2.1 x.2.2.2.2.2.2.2.2.2.2.2.2 ({x.2.2.2.2.2.1} + x.2.1)},
            x.2.2.2.2.1)] := by
  maude_certify_comp

theorem otr_inv.obligation_8 :
    Unification.sound (Narrowing.mayFire recvF invP)
      [Unification.Unifier.bind fun (x : ℕ × OidSet × Log × ℕ × Bool × Dec × ℕ × ℕ × ℕ × ℕ × ℕ) =>
          ((x.2.2.2.2.2.2.2.2.2.2, x.2.1, x.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1, ∅, ∅, x.2.2.1),
            x.2.2.2.2.2.2.2.2.2.2, x.2.1,
            {Item.node
                  { id := x.1, round := x.2.2.2.1, step := Step.wait, value := x.2.2.2.2.1, dec := x.2.2.2.2.2.1,
                    vt := x.2.2.2.2.2.2.1, vf := x.2.2.2.2.2.2.2.1, va := x.2.2.2.2.2.2.2.2.1 }} +
              {Item.msg false x.2.2.2.1 x.2.2.2.2.2.2.2.2.2.1 {x.1}},
            x.2.2.1),
        Unification.Unifier.bind fun (x : ℕ × ℕ × OidSet × Log × ℕ × Bool × Dec × ℕ × ℕ × ℕ × ℕ × OidSet) =>
          ((x.2.1, x.2.2.1, x.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2, ∅, x.2.2.2.1),
            x.2.1, x.2.2.1,
            {Item.node
                  { id := x.1, round := x.2.2.2.2.1, step := Step.wait, value := x.2.2.2.2.2.1, dec := x.2.2.2.2.2.2.1,
                    vt := x.2.2.2.2.2.2.2.1, vf := x.2.2.2.2.2.2.2.2.1, va := x.2.2.2.2.2.2.2.2.2.1 }} +
              {Item.msg false x.2.2.2.2.1 x.2.2.2.2.2.2.2.2.2.2.1 ({x.1} + x.2.2.2.2.2.2.2.2.2.2.2)},
            x.2.2.2.1),
        Unification.Unifier.bind fun (x : Items × ℕ × OidSet × Log × ℕ × ℕ × Bool × Dec × ℕ × ℕ × ℕ × ℕ) =>
          ((x.2.1, x.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2, ∅, x.1, x.2.2.2.1),
            x.2.1, x.2.2.1,
            x.1 +
                {Item.node
                    { id := x.2.2.2.2.1, round := x.2.2.2.2.2.1, step := Step.wait, value := x.2.2.2.2.2.2.1,
                      dec := x.2.2.2.2.2.2.2.1, vt := x.2.2.2.2.2.2.2.2.1, vf := x.2.2.2.2.2.2.2.2.2.1,
                      va := x.2.2.2.2.2.2.2.2.2.2.1 }} +
              {Item.msg false x.2.2.2.2.2.1 x.2.2.2.2.2.2.2.2.2.2.2 {x.2.2.2.2.1}},
            x.2.2.2.1),
        Unification.Unifier.bind fun (x : Items × OidSet × ℕ × OidSet × Log × ℕ × ℕ × Bool × Dec × ℕ × ℕ × ℕ × ℕ) =>
          ((x.2.2.1, x.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.2.2.2,
              x.2.1, x.1, x.2.2.2.2.1),
            x.2.2.1, x.2.2.2.1,
            x.1 +
                {Item.node
                    { id := x.2.2.2.2.2.1, round := x.2.2.2.2.2.2.1, step := Step.wait, value := x.2.2.2.2.2.2.2.1,
                      dec := x.2.2.2.2.2.2.2.2.1, vt := x.2.2.2.2.2.2.2.2.2.1, vf := x.2.2.2.2.2.2.2.2.2.2.1,
                      va := x.2.2.2.2.2.2.2.2.2.2.2.1 }} +
              {Item.msg false x.2.2.2.2.2.2.1 x.2.2.2.2.2.2.2.2.2.2.2.2 ({x.2.2.2.2.2.1} + x.2.1)},
            x.2.2.2.2.1)] := by
  simp only [sound, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  repeat' apply And.intro
  all_goals
    rintro γ ⟨x, rfl⟩
    simp only [unifiedBy, mayFire, recvF, invP]
    try ac_rfl

theorem otr_inv.obligation_9 :
    Unification.complete (Narrowing.mayFire decideT invP)
      [Unification.Unifier.bind fun (x : ℕ × ℕ × Bool × ℕ × ℕ × ℕ × ℕ × OidSet × Log) =>
          ((x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, ∅,
              x.2.2.2.2.2.2.2.2),
            x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1,
            {Item.node
                { id := x.1, round := x.2.1, step := Step.wait, value := x.2.2.1, dec := Dec.undecided, vt := x.2.2.2.1,
                  vf := x.2.2.2.2.1, va := x.2.2.2.2.2.1 }},
            x.2.2.2.2.2.2.2.2),
        Unification.Unifier.bind fun (x : Items × Log × ℕ × ℕ × Bool × ℕ × ℕ × ℕ × ℕ × OidSet) =>
          ((x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.2.1, x.1, x.2.1),
            x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2,
            x.1 +
              {Item.node
                  { id := x.2.2.1, round := x.2.2.2.1, step := Step.wait, value := x.2.2.2.2.1, dec := Dec.undecided,
                    vt := x.2.2.2.2.2.1, vf := x.2.2.2.2.2.2.1, va := x.2.2.2.2.2.2.2.1 }},
            x.2.1)] := by
  maude_certify_comp

theorem otr_inv.obligation_10 :
    Unification.sound (Narrowing.mayFire decideT invP)
      [Unification.Unifier.bind fun (x : ℕ × ℕ × Bool × ℕ × ℕ × ℕ × ℕ × OidSet × Log) =>
          ((x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, ∅,
              x.2.2.2.2.2.2.2.2),
            x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1,
            {Item.node
                { id := x.1, round := x.2.1, step := Step.wait, value := x.2.2.1, dec := Dec.undecided, vt := x.2.2.2.1,
                  vf := x.2.2.2.2.1, va := x.2.2.2.2.2.1 }},
            x.2.2.2.2.2.2.2.2),
        Unification.Unifier.bind fun (x : Items × Log × ℕ × ℕ × Bool × ℕ × ℕ × ℕ × ℕ × OidSet) =>
          ((x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.2.1, x.1, x.2.1),
            x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2,
            x.1 +
              {Item.node
                  { id := x.2.2.1, round := x.2.2.2.1, step := Step.wait, value := x.2.2.2.2.1, dec := Dec.undecided,
                    vt := x.2.2.2.2.2.1, vf := x.2.2.2.2.2.2.1, va := x.2.2.2.2.2.2.2.1 }},
            x.2.1)] := by
  simp only [sound, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  repeat' apply And.intro
  all_goals
    rintro γ ⟨x, rfl⟩
    simp only [unifiedBy, mayFire, decideT, invP]
    try ac_rfl

theorem otr_inv.obligation_11 :
    Unification.complete (Narrowing.mayFire decideF invP)
      [Unification.Unifier.bind fun (x : ℕ × ℕ × Bool × ℕ × ℕ × ℕ × ℕ × OidSet × Log) =>
          ((x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, ∅,
              x.2.2.2.2.2.2.2.2),
            x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1,
            {Item.node
                { id := x.1, round := x.2.1, step := Step.wait, value := x.2.2.1, dec := Dec.undecided, vt := x.2.2.2.1,
                  vf := x.2.2.2.2.1, va := x.2.2.2.2.2.1 }},
            x.2.2.2.2.2.2.2.2),
        Unification.Unifier.bind fun (x : Items × Log × ℕ × ℕ × Bool × ℕ × ℕ × ℕ × ℕ × OidSet) =>
          ((x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.2.1, x.1, x.2.1),
            x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2,
            x.1 +
              {Item.node
                  { id := x.2.2.1, round := x.2.2.2.1, step := Step.wait, value := x.2.2.2.2.1, dec := Dec.undecided,
                    vt := x.2.2.2.2.2.1, vf := x.2.2.2.2.2.2.1, va := x.2.2.2.2.2.2.2.1 }},
            x.2.1)] := by
  maude_certify_comp

theorem otr_inv.obligation_12 :
    Unification.sound (Narrowing.mayFire decideF invP)
      [Unification.Unifier.bind fun (x : ℕ × ℕ × Bool × ℕ × ℕ × ℕ × ℕ × OidSet × Log) =>
          ((x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, ∅,
              x.2.2.2.2.2.2.2.2),
            x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1,
            {Item.node
                { id := x.1, round := x.2.1, step := Step.wait, value := x.2.2.1, dec := Dec.undecided, vt := x.2.2.2.1,
                  vf := x.2.2.2.2.1, va := x.2.2.2.2.2.1 }},
            x.2.2.2.2.2.2.2.2),
        Unification.Unifier.bind fun (x : Items × Log × ℕ × ℕ × Bool × ℕ × ℕ × ℕ × ℕ × OidSet) =>
          ((x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.2.1, x.1, x.2.1),
            x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2,
            x.1 +
              {Item.node
                  { id := x.2.2.1, round := x.2.2.2.1, step := Step.wait, value := x.2.2.2.2.1, dec := Dec.undecided,
                    vt := x.2.2.2.2.2.1, vf := x.2.2.2.2.2.2.1, va := x.2.2.2.2.2.2.2.1 }},
            x.2.1)] := by
  simp only [sound, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  repeat' apply And.intro
  all_goals
    rintro γ ⟨x, rfl⟩
    simp only [unifiedBy, mayFire, decideF, invP]
    try ac_rfl

theorem otr_inv.obligation_13 :
    Unification.complete (Narrowing.mayFire updateT invP)
      [Unification.Unifier.bind fun (x : ℕ × ℕ × Bool × ℕ × ℕ × ℕ × ℕ × OidSet × Log) =>
          ((x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, ∅,
              x.2.2.2.2.2.2.2.2),
            x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1,
            {Item.node
                { id := x.1, round := x.2.1, step := Step.wait, value := x.2.2.1, dec := Dec.undecided, vt := x.2.2.2.1,
                  vf := x.2.2.2.2.1, va := x.2.2.2.2.2.1 }},
            x.2.2.2.2.2.2.2.2),
        Unification.Unifier.bind fun (x : Items × Log × ℕ × ℕ × Bool × ℕ × ℕ × ℕ × ℕ × OidSet) =>
          ((x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.2.1, x.1, x.2.1),
            x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2,
            x.1 +
              {Item.node
                  { id := x.2.2.1, round := x.2.2.2.1, step := Step.wait, value := x.2.2.2.2.1, dec := Dec.undecided,
                    vt := x.2.2.2.2.2.1, vf := x.2.2.2.2.2.2.1, va := x.2.2.2.2.2.2.2.1 }},
            x.2.1)] := by
  maude_certify_comp

theorem otr_inv.obligation_14 :
    Unification.sound (Narrowing.mayFire updateT invP)
      [Unification.Unifier.bind fun (x : ℕ × ℕ × Bool × ℕ × ℕ × ℕ × ℕ × OidSet × Log) =>
          ((x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, ∅,
              x.2.2.2.2.2.2.2.2),
            x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1,
            {Item.node
                { id := x.1, round := x.2.1, step := Step.wait, value := x.2.2.1, dec := Dec.undecided, vt := x.2.2.2.1,
                  vf := x.2.2.2.2.1, va := x.2.2.2.2.2.1 }},
            x.2.2.2.2.2.2.2.2),
        Unification.Unifier.bind fun (x : Items × Log × ℕ × ℕ × Bool × ℕ × ℕ × ℕ × ℕ × OidSet) =>
          ((x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.2.1, x.1, x.2.1),
            x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2,
            x.1 +
              {Item.node
                  { id := x.2.2.1, round := x.2.2.2.1, step := Step.wait, value := x.2.2.2.2.1, dec := Dec.undecided,
                    vt := x.2.2.2.2.2.1, vf := x.2.2.2.2.2.2.1, va := x.2.2.2.2.2.2.2.1 }},
            x.2.1)] := by
  simp only [sound, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  repeat' apply And.intro
  all_goals
    rintro γ ⟨x, rfl⟩
    simp only [unifiedBy, mayFire, updateT, invP]
    try ac_rfl

theorem otr_inv.obligation_15 :
    Unification.complete (Narrowing.mayFire updateF invP)
      [Unification.Unifier.bind fun (x : ℕ × ℕ × Bool × ℕ × ℕ × ℕ × ℕ × OidSet × Log) =>
          ((x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, ∅,
              x.2.2.2.2.2.2.2.2),
            x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1,
            {Item.node
                { id := x.1, round := x.2.1, step := Step.wait, value := x.2.2.1, dec := Dec.undecided, vt := x.2.2.2.1,
                  vf := x.2.2.2.2.1, va := x.2.2.2.2.2.1 }},
            x.2.2.2.2.2.2.2.2),
        Unification.Unifier.bind fun (x : Items × Log × ℕ × ℕ × Bool × ℕ × ℕ × ℕ × ℕ × OidSet) =>
          ((x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.2.1, x.1, x.2.1),
            x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2,
            x.1 +
              {Item.node
                  { id := x.2.2.1, round := x.2.2.2.1, step := Step.wait, value := x.2.2.2.2.1, dec := Dec.undecided,
                    vt := x.2.2.2.2.2.1, vf := x.2.2.2.2.2.2.1, va := x.2.2.2.2.2.2.2.1 }},
            x.2.1)] := by
  maude_certify_comp

theorem otr_inv.obligation_16 :
    Unification.sound (Narrowing.mayFire updateF invP)
      [Unification.Unifier.bind fun (x : ℕ × ℕ × Bool × ℕ × ℕ × ℕ × ℕ × OidSet × Log) =>
          ((x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1, x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, ∅,
              x.2.2.2.2.2.2.2.2),
            x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1,
            {Item.node
                { id := x.1, round := x.2.1, step := Step.wait, value := x.2.2.1, dec := Dec.undecided, vt := x.2.2.2.1,
                  vf := x.2.2.2.2.1, va := x.2.2.2.2.2.1 }},
            x.2.2.2.2.2.2.2.2),
        Unification.Unifier.bind fun (x : Items × Log × ℕ × ℕ × Bool × ℕ × ℕ × ℕ × ℕ × OidSet) =>
          ((x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
              x.2.2.2.2.2.2.2.1, x.1, x.2.1),
            x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2,
            x.1 +
              {Item.node
                  { id := x.2.2.1, round := x.2.2.2.1, step := Step.wait, value := x.2.2.2.2.1, dec := Dec.undecided,
                    vt := x.2.2.2.2.2.1, vf := x.2.2.2.2.2.2.1, va := x.2.2.2.2.2.2.2.1 }},
            x.2.1)] := by
  simp only [sound, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  repeat' apply And.intro
  all_goals
    rintro γ ⟨x, rfl⟩
    simp only [unifiedBy, mayFire, updateF, invP]
    try ac_rfl

theorem otr_inv.obligation_17 :
    Unification.complete (Narrowing.mayFire loss invP)
      [Unification.Unifier.bind fun (x : Bool × ℕ × ℕ × OidSet × ℕ × OidSet × Log) =>
          ((x.2.2.2.2.1, x.2.2.2.2.2.1, x.1, x.2.1, x.2.2.1, x.2.2.2.1, ∅, x.2.2.2.2.2.2), x.2.2.2.2.1, x.2.2.2.2.2.1,
            {Item.msg x.1 x.2.1 x.2.2.1 x.2.2.2.1}, x.2.2.2.2.2.2),
        Unification.Unifier.bind fun (x : Items × Bool × ℕ × ℕ × OidSet × ℕ × OidSet × Log) =>
          ((x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.1, x.2.2.2.2.2.2.2),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.1 + {Item.msg x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1},
            x.2.2.2.2.2.2.2)] := by
  maude_certify_comp

theorem otr_inv.obligation_18 :
    Unification.sound (Narrowing.mayFire loss invP)
      [Unification.Unifier.bind fun (x : Bool × ℕ × ℕ × OidSet × ℕ × OidSet × Log) =>
          ((x.2.2.2.2.1, x.2.2.2.2.2.1, x.1, x.2.1, x.2.2.1, x.2.2.2.1, ∅, x.2.2.2.2.2.2), x.2.2.2.2.1, x.2.2.2.2.2.1,
            {Item.msg x.1 x.2.1 x.2.2.1 x.2.2.2.1}, x.2.2.2.2.2.2),
        Unification.Unifier.bind fun (x : Items × Bool × ℕ × ℕ × OidSet × ℕ × OidSet × Log) =>
          ((x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.1, x.2.2.2.2.2.2.2),
            x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.1 + {Item.msg x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1},
            x.2.2.2.2.2.2.2)] := by
  simp only [sound, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true]
  repeat' apply And.intro
  all_goals
    rintro γ ⟨x, rfl⟩
    simp only [unifiedBy, mayFire, loss, invP]
    try ac_rfl

end OTRA
