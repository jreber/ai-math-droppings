# Propositio

A standalone, mathlib-organized Lean 4 library extracted from
[ai-math](https://github.com/jreber/ai-math)'s `lean4/` proof tree. `ai-math` is a fast-moving
multi-agent research repo (KB-driven proof queue, session churn); this repo is the curated,
discoverable, reusable destination for results once they're stable — organized by mathematical
domain rather than by proof session, following mathlib's own directory convention.

## Status: migration in progress

This is an early, partial extraction (2026-07-22) — most of `ai-math/lean4/`'s ~588 files have
not moved yet. See `docs/migration-status.md` (once it exists) for the running list.

**Why some files are duplicated rather than moved:** `ai-math`'s Lean tree is a single densely
connected component — a handful of hub files (`Tactics`, `TerrasDensity`, ...) are imported by
dozens of otherwise-unrelated files. A file only gets *deleted* from `ai-math` once every one of
its consumers has also migrated here; until then it's copied to both places so neither repo's
build breaks. Check a file's own header comment / the migration log for its current status.

## Directory convention

Mirrors mathlib: one file per module, path = dotted import path, organized by area under
`Propositio/<Area>/...` (e.g. `Propositio/Collatz/CycleElementBound.lean` is
`import Propositio.Collatz.CycleElementBound`). Internal `namespace` declarations are left as
they were in `ai-math` (unqualified, e.g. `namespace CollatzCycleElementBound`) — only the file
location / import path changed, not the Lean names, so theorem names are stable across the move.

Top-level areas (populated incrementally):
- `Propositio/Collatz/` — Collatz/3n+1 results
- `Propositio/Beal/` — Beal conjecture results
- `Propositio/NumberTheory/` — Chebyshev bounds, Diophantine/irrationality-measure machinery,
  Zsygmondy, etc. (not yet populated)
- `Propositio/Combinatorics/` — Friendship theorem, Sunflower lemma, Sylvester-Gallai, Lonely
  Runner (not yet populated)
- `Propositio/Tactics.lean` — shared tactic infrastructure

## Building

```
lake exe cache get   # fetches mathlib's prebuilt oleans
lake build
```

If you're on the same machine as an `ai-math` checkout with `lean4/.lake/packages` already
built, you can symlink instead of re-downloading: `ln -s /path/to/ai-math/lean4/.lake/packages .lake/packages`.
