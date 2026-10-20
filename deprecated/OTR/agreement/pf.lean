import examples.OTR.agreement.model

/-!
# OneThirdRule: the whole system preserves the agreement invariant

`narrow` computes the post of `inv` under all nine rules, as in Bakery. Each post patch
then lands, by `maude_match`, in the *image* of its rule (its right-hand side, from a
left-hand side in `Inv`; `model.lean`), and the images lie in `inv` because each rule
preserves `Inv` (`preserves_otr`). What remains per patch is to see that its condition is
the image's, up to the ACU normal form Maude returns (`image_cond`).
-/

namespace OTRA

open Expresso Unification Narrowing Subsumption

theorem inv_congr {a a' : Nat} {b b' : OidSet} {c c' : Items} {d d' : Log} (h : Inv a b c d)
    (ha : a = a') (hb : b = b') (hc : c = c') (hd : d = d') : Inv a' b' c' d' := by
  subst ha hb hc hd; exact h

/-- An equation between ACU terms; the right side may have holes left by `maude_match`,
filled by unification once the sides agree up to units (or one swap). -/
macro "acu_eq" : tactic => `(tactic| first
  | with_reducible rfl
  | (simp only [ACU.plus_unit, ACU.unit_plus]; done)
  | ((try simp only [ACU.plus_unit, ACU.unit_plus]); ac_rfl)
  | ((try simp only [ACU.plus_unit, ACU.unit_plus]); with_reducible rfl)
  | (rw [ACU.plus_comm]; try with_reducible rfl; done))

set_option hygiene false in
/-- The condition of a rule image from the condition `hc` of a post patch: the same
`Inv`, up to ACU, and the same rule condition. -/
macro "image_cond" : tactic => `(tactic| first
  | exact ⟨inv_congr hc (by acu_eq) (by acu_eq) (by acu_eq) (by acu_eq), trivial⟩
  | exact ⟨inv_congr hc.1 (by acu_eq) (by acu_eq) (by acu_eq) (by acu_eq), hc.2⟩)

/-- The images of `inv` under the rules. -/
def images : Pattern Conf := otr.map image

theorem images_sub : subsumes (inv ++ images) inv :=
  subsumes_of_cover fun a ha => by
    rcases List.mem_append.1 ha with ha | ha
    · exact subsumes_one ⟨a, ha, fun _ h => h⟩
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 ha
    exact image_sub (preserves_otr r hr)

theorem subsumes_trans {A B C : Pattern Conf} (h₁ : subsumes A B) (h₂ : subsumes B C) :
    subsumes A C :=
  fun s hs => h₂ s (h₁ s hs)

theorem otr_inv : isOverPost otr inv inv := by
  narrow otr from inv as post hpost
  refine over_of_subsumes hpost.1 (subsumes_trans (subsumes_of_cover fun a ha => ?_) images_sub)
  rw [← post_eq] at ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  repeat' rcases ha with rfl | ha
  all_goals apply subsumes_one
  -- each post patch lies in the image of its rule, in the order of `otr`: four patches for
  -- each `vote` and `recv` rule (the rest of the configuration and of the receivers, empty
  -- or not), two for each other rule
  iterate 4 (· maude_match image voteT; image_cond)
  iterate 4 (· maude_match image voteF; image_cond)
  iterate 4 (· maude_match image recvT; image_cond)
  iterate 4 (· maude_match image recvF; image_cond)
  iterate 2 (· maude_match image decideT; image_cond)
  iterate 2 (· maude_match image decideF; image_cond)
  iterate 2 (· maude_match image updateT; image_cond)
  iterate 2 (· maude_match image updateF; image_cond)
  -- `loss` forgets the message, so its image is not determined by the state: land in `inv`
  -- itself, as dropping messages keeps the invariant
  iterate 2 (· maude_match invP; exact inv_drop hc (by simp) (by simp [nodesOf]))

end OTRA
