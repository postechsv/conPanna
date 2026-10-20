# Deprecated examples

Kept for reference only; not part of the build (`lakefile.toml` builds `examples/`).

- `OTR/`: OneThirdRule. `draft/OTR.lean` (two invariants) and `agreement/` (agreement for
  any number of nodes). Dropped as a case study: its agreement invariant is global counting,
  where narrowing only enumerates the rules (see `OTR/CAVEATS.md`). `agreement/pf.lean`
  relied on `maude_match` leaving undetermined target variables as holes, a feature since
  reverted, so it no longer compiles as is.
