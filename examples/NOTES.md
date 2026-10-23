# Case studies: notes

## What a good case study shows

conPanna splits a proof into a constructor part (narrowing, matching, simplification:
automated and certified) and a constraint part (conditions: theorem proving). Real
theorem-proving work is good news: it means the proof is beyond a purely automatic tool.
The problem is a strong bias either way (e.g. 1% or 99% theorem proving).

## Balance of the examples so far

| Example | Automated (narrowing, routing, simp) | Theorem proving | Balance |
|---|---|---|---|
| OTR agreement (deprecated) | rule enumeration only | almost everything (counting lemmas) | ~99% theorem proving: too biased |
| 2PC | 82 → 32 cases, routing, 30/32 conditions by simp | 2 short cases, plus the invariant design | heavily automated: close to "too easy" |
| Bakery (+abort) | case generation and routing | most condition proofs (~100 lines) | leans manual, but small |
| German (draft) | 102 cases generated and certified; 96/102 routed; 46 conditions by simp | ~50 conditions with real per-cache reasoning (sharer-set equivalence, invalidation facts), 6 substitutions, initial states, disjointness | about half and half |

German shows the intended split: automation handles the structure (which rule touches
the owner versus another cache, which directory situation a post lands in); theorem
proving handles the protocol's content (why the sharer set stays exactly the caches with
copies, why invalidations cannot interleave with grants). Neither does the other's part.

Caveats:
- The split is not final: better simp lemmas may move part of the ~50 conditions to
  automation, and solving conditions in narrowing would absorb the 6 substitutions.
  Measure the final balance on the finished proof.
- Report it per example in the paper: cases generated and discharged automatically versus
  lines of hand-written proof. That makes "neither 1% nor 99%" a checkable claim, and
  shows why 2PC (mostly automatic) and German (balanced) complement each other.

## What the ACU infrastructure saves

The "automated" column hides most of the ACU work. Without it, the user would write:

| Where ACU shows up | With conPanna | Without it |
|---|---|---|
| Equality modulo ACU | `ACU` is a quotient type: `=` is equality modulo associativity, commutativity and unit; rewriting and congruence work as usual | bags as lists or terms with a separate `≈`: setoid rewriting, `.trans`/`.symm`/congruence lemmas for every constructor holding a bag (`Conf`, `Dir`, `Item`, ...) |
| Case analysis per rule | narrowing enumerates the ACU unifiers (82 in 2PC, 102 post patches in German); certificates prove none is missing | by hand: where can the rule's object sit in the bag, which distinguished object does it alias, plus a proof that the split is exhaustive |
| Routing a post into the invariant | `maude_match` finds the substitution; the state equation is closed by AC normalization | per patch: the substitution, and the permuted sums proved equal with explicit `add_comm`/`add_assoc` chains, inside nested objects |
| Sets inside objects (`shr = {I} + SH`, receiver sets) | the same machinery, a second ACU sort | the same manual work again, per sort |

In German, "96/102 routed" alone stands for about a hundred manual permutation and
substitution proofs, and the 102 cases for a hand-made exhaustive aliasing analysis.

Residual ACU friction (for the limitations): the bridge to the multiset view
(`toMultiset`) with summary functions defined through it; sets as multisets plus `Nodup`
(no idempotent theory); ad-hoc ACU closers in the deprecated OTR proof (`acu_eq`).

So the theorem-proving share counts only what remains with ACU support. The fair
comparison is against a baseline without it, where the hand-written part is far larger:
build a plain-Lean baseline for one example to put numbers on it.

Plan for the paper: Bakery (+abort) as the running example; German as the scalability
case study, once finished; 2PC as a paragraph, or the fallback if German is not finished.

# TODOs

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
  The free situation is stated with summaries (`SH = shrIds CF`, `invIds CF` disjoint
  from `IV`, invalidations only while serving an exclusive request) and a parameter-free
  per-cache predicate, so the rest of the bag needs no transfer when the directory moves.
- Checked outside the framework by explicit-state enumeration (a Python script, as a
  hint): inductive for 2 caches; every state reachable with 3 caches satisfies it. The
  first version was true but not inductive; the check found the two missing facts.
- Narrowing rule by rule: 102 post patches; 96 route to their patch by `maude_match`;
  78 conditions close by one generic closer (`cond_close`).
- Done: all 15 rules (the remaining conditions by explicit multiset bookkeeping; the 6
  patches whose values only their conditions fix by a case split and an explicit match),
  `init_inv`, and the chain to `german_coherent`. `German/draft/coherence.lean` links the
  certified obligations; its theorem depends on `sorryAx` only through:
  - `inv_bad` (disjointness from the bad patterns), and
  - the soundness obligations (left `sorry`).
- Certification (completeness obligations, `German/draft/obligation.lean`; soundness left
  `sorry`): 78 cells. Fixed on the way (general producer/replay bugs): ill-sorted variable
  elimination; bag variables now eliminated by a term without them (no SOLVE); elimination
  printed with bag braces; SOLVE answers (`theta`) evaluated in later steps (`acu_rest`,
  `acu_free`, `copies_zero`/`copies_one`). Performance fixes found by profiling one large
  certificate (18 min → 2.5 min): `acu_distinct` fell back to `simp_all [eq_comm]` when a
  disequation was recorded the other way round (912 s in one call; now it flips the goal
  and drops the bag equations it never needs); COVER picks its answer by rewriting.
  All 75 completeness certificates check. Two structural costs remained, both fixed in the
  compiler: each step's state composed the previous steps' functions, so a late step
  unfolded the whole stack (now a `checkpoint` restates the state in direct form before
  every step); and COVER named the context variables against the whole answer list (now
  it selects its answer first). Each fix alone gave ~3×, both together ~19× on the largest
  certificate (12m49s → 40s); the file went from ~24 min to ~4.5 min, and 71 of 75
  certificates fit the default heartbeat budget (4 need 5×).
- Performance: the draft checks in about 1.5 minutes (rules elaborate in parallel); each
  rule needs a raised heartbeat limit for routing. Each `maude_match` attempt starts a
  fresh Python and Maude process (no caching); batching or a persistent process would cut
  wall-clock time.
- Framework improvements it points to:
  - *Solving conditions in narrowing*: instantiate variables a condition fixes, so the 6
    patches route by matching.
  - *Certified disjointness* `¬ overlaps A B`: unify the two patterns (certified as for
    narrowing) and refute each unifier's conditions. Needed for `inv_bad`, and would let
    Bakery's mutex be stated against a bad pattern too.
