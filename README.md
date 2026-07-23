# Propositio

A standalone, mathlib-organized Lean 4 library extracted from
[ai-math](https://github.com/jreber/ai-math)'s `lean4/` proof tree. `ai-math` is a fast-moving
multi-agent research repo (KB-driven proof queue, session churn); this repo is the curated,
discoverable, reusable destination for the results themselves — organized by mathematical
domain rather than by proof session, following mathlib's own directory convention.

## Status: content-complete, verified

All 584 real theorem files from `ai-math/lean4/` (scratch/sanity-check files excluded) are here.
**552 build clean** (`lake build Propositio`, exit 0). The other 32 are present as source but
deliberately excluded from the aggregator — 2 genuinely broken on fresh compile (stale even in
`ai-math`'s own cache, not a migration artifact), 18 an abandoned construction already marked
OPEN in their own docstrings, 11 a giant generated case-split family never attempted anywhere
(the largest is 7.3MB / 2823 near-identical theorems), 1 an audit entry-point script. Full
breakdown in `docs/migration-status.md`.

`ai-math/lean4/` itself is untouched — deletion there is a deliberate follow-up decision, not
done as part of this extraction (see `docs/migration-status.md` for why).

## Directory convention

Mirrors mathlib: one file per module, path = dotted import path, organized by mathematical area
under `Propositio/<Area>/...`. Everything specific to a *problem* (Collatz, Beal, Zsygmondy,
Erdős–Straus) nests inside the field it belongs to rather than sitting as a sibling of one —
same principle mathlib itself uses. Internal `namespace` declarations are left exactly as they
were in `ai-math` (e.g. `namespace CollatzCycleElementBound` even though the file now lives at
`Propositio/NumberTheory/Collatz/CycleElementBound.lean`) — only the file location / import path
changed, not the Lean names, so theorem names are stable across the move.

- `Propositio/NumberTheory/Collatz/` — Collatz/3n+1 (232 files)
- `Propositio/NumberTheory/Beal/` — Beal conjecture (132 files)
- `Propositio/NumberTheory/Diophantine/` — two-log irrationality-measure machinery (72 files)
- `Propositio/NumberTheory/Analytic/` — Chebyshev/Mertens/prime-counting (43 files)
- `Propositio/NumberTheory/Zsygmondy/` (32 files), `.../ErdosStraus/` (18 files)
- `Propositio/Combinatorics/` — Friendship theorem, Sunflower lemma, Sylvester-Gallai, Lonely
  Runner, Mantel (36 files)
- `Propositio/Geometry/Monsky/` — Monsky's theorem (17 files)
- `Propositio/Tactics.lean` — shared tactic infrastructure
- `Propositio/Verify.lean` — axiom-audit entry point (not imported by the aggregator)

## Building

```
lake exe cache get   # fetches mathlib's prebuilt oleans
lake build Propositio
```

If you're on the same machine as an `ai-math` checkout with `lean4/.lake/packages` already
built, symlink instead of re-downloading: `ln -s /path/to/ai-math/lean4/.lake/packages .lake/packages`.

**Resource note for a from-scratch build**: this Lake version has no `-j`/`--jobs` flag, and a
handful of files are heavy enough (deep `interval_cases`, large case-split families) that
building everything at once with unbounded default concurrency can exhaust memory on a
constrained machine. See `docs/migration-status.md` for the batching pattern that worked.

## Explorer

`docs/explorer/index.html` — a self-contained visual map of the whole library (domain overview
→ per-domain dependency graph → docstring/axiom drilldown). Open it directly, no server needed.
Regenerate with `python3 scripts/export_graph.py` after a build (optionally preceded by
`scripts/audit_axioms.py` for full per-declaration axiom data). See `docs/explorer/README.md`.
