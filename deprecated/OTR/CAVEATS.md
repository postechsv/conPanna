# OneThirdRule: caveats

Known weak points of the OTR proofs: what is a workaround or a heuristic, and what is
not yet general.

## `agreement/` (agreement for any number of nodes)

- **Ghost log in the model.** `Conf` has an extra field `log`, where `vote` records
  `⟨o, r, v⟩`. No rule reads it, but this is still a change to Kang & Bae's model:
  agreement is proved for the model with the log.
- **`narrow` normalizes the post.** It simplifies the post states and conditions with the
  full simp set and Maude's normal form, so units disappear and summands are reordered.
  The rule lemmas (`inv_*`) therefore cannot be applied by plain unification. Each case
  goes through a rule image (`maude_match image r`) and closes an ACU equation between
  the post patch's condition and the image's (`image_cond`, `acu_eq`).
- **`acu_eq` is local and partly heuristic.** It is defined in `pf.lean`. It tries:
  reducible `rfl`; unit removal; `ac_rfl`; and, for equations with holes, unification
  after unit removal or after *one* swap (`rw [ACU.plus_comm]`). The swap is enough for
  the shapes here (one node literal and one variable), but it is not a general
  ACU matcher. The AC-permutation `simp` alternative was dropped: it took 9–29 s per
  call on the nested `recv` sums.
- **`maude_match` holes (library change).** Target variables that the post state does
  not determine (update resets the counters and value) are left as holes `?w x` for the
  condition proof to fill. An unfilled hole leaves the proof incomplete, so nothing new
  is trusted. Only `update` needs this here.
- **`loss` does not use an image.** It forgets the message, so the image's message
  variables are not determined, even with holes (they would occur only inside `Inv`, up
  to ACU). Its two patches land in `invP` directly, using `inv_drop` (dropping messages
  keeps `Inv`).
- **Patch order is hard-coded.** `pf.lean` names each patch's rule by position (4, 4,
  4, 4, 2, 2, 2, 2, 2), so it relies on `narrow` returning patches in the order of `otr`.
  Trying every image with `first` also works but took about 2.5 min (one Maude call per
  attempt) and needed a raised heartbeat limit.
- **Matching against `invP` is trivial.** `invP`'s state is just its variables, so for
  it the identity substitution would do (`subsumes_invP`-style); `maude_match invP` is
  used only for uniformity.
- **The mathematics is in the lemmas, not the automation.** The nine preservation
  lemmas (`InvM.vote/recv/decide/update/drop`, about 250 lines) and `InvM.lock`/
  `InvM.agreement` are proved by hand with `count_simp`, `split_ifs` and `omega`.
  Narrowing and matching supply the case split and the bookkeeping.
- **Initial states are specified by hand.** `inv_init` assumes every node starts in
  round 0 with nothing counted, there are no messages, the log is empty, ids are
  distinct, and 2N < 3·TH. No pattern for initial states is narrowed.
- **The model cache is global.** The Maude tools read `producer/.cache/ctor.maude`.
  `narrow` and `maude_match` rewrite it from the current model on each call, but running
  two models' files at the same time can still race.

## `draft/OTR.lean` (invariants 1 and 3)

- Invariant 3's 26 cases are each closed by `aesop`, a generic search tactic, and share
  a raised heartbeat limit (`maxHeartbeats 1000000`). A thinner, specific closer would
  be preferable.
- Neither invariant matters for agreement, except id uniqueness. They were
  stress tests (two bag sorts, a relational condition).
- Soundness obligations close with `ac_rfl` alone. Bakery's AC simp list was not
  needed; this is a hint for the future `maude_certify_sound`, not a guarantee.

## Library fixes made for OTR

- Each ACU sort gets its own operator names when a model has more than one
  (`_+Items_`, `emptyItems`, …); a single ACU sort keeps `__`/`none`. Needed because the
  producer identifies bags by their union operator.
- `show.maude` prints a nested sum inside a sum as a bag, not as a single element.
- `maude_match`'s state-equation closer tries reducible `rfl` first and full `rfl` last.
