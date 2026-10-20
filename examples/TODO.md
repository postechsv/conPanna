# Example TODOs

Candidates for the next case studies, judged by the conPanna criterion: the proof's
patterns should carry the essence in constructor terms (distinguished objects linked by
shared ids), leaving only uniform facts to the conditions.

## Method: bad patterns, by disjointness

State the safety property as bad patterns (states that must never occur), and prove a
forward inductive invariant disjoint from them (`¬ overlaps inv bad`, with `invariant`).
A backward variant (closing the bad patterns under pre-image, Cubicle-style) was tried
on German and dropped: 166 pre-image patches for the two coherence patterns alone.

## Candidates

1. **German's cache-coherence protocol** (in progress: `German/draft/German.lean`, forward). The parameterized-
   verification benchmark: a directory with sharer and invalidate id sets, N caches with
   three channels each. Coherence (single writer / multiple readers) as bad pairs of
   caches. Recognised; constructor-rich; property is in the mutex family.
2. **Dijkstra's on-the-fly garbage collector** (tricolour marking). Heap objects
   `⟨id, colour, refs⟩` with nested reference sets; the bad pattern
   `{obj ⟨I, black, {J} + R⟩} + {obj ⟨J, white, S⟩}` links a pointer to its target by a
   shared id. Orthogonal property (heap safety). Scope: the tricolour invariant and
   "sweep frees only white objects when no grey remains"; full safety needs reachability.
3. **Lock server with grant/release messages** (Ivy) or **dining philosophers with fork
   objects**: small, constructor-rich illustrations; both exclusion properties.

## German: status and what it asks of the framework

- Forward invariant, one patch per directory situation (free; owner exclusive / grant in
  flight / being invalidated / acknowledged), owner linked to the sharer set `{I}`.
  Checked outside the framework by explicit-state enumeration: inductive for 2 caches;
  every state reachable with 3 caches satisfies it.
- Narrowing rule by rule: 102 post patches; 96 route to their patch by `maude_match`.
- Open: the condition proofs (`sorry`), `init_inv`, and `inv_bad`.
- Framework improvements it points to:
  - *Solving conditions in narrowing*: 6 patches do not route because a condition fixes
    a constructor value (a cache state known to be `invalid`, `IV = ∅`) that the target
    states literally. A post-narrowing step that instantiates such variables would route
    them by matching.
  - *Certified disjointness* `¬ overlaps A B`: unify the two patterns (certified as for
    narrowing) and refute each unifier's conditions. Needed for `inv_bad`, and would let
    Bakery's mutex be stated against a bad pattern too.

