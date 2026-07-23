# Migration status

Source: `ai-math/lean4/` (588 `.lean` files as of 2026-07-22). Migrated using
`ai-math/scripts/migrate_to_propositio.py` (flat-name → domain-path import rewriter; internal
`namespace` declarations are never touched, only file location and `import` lines).

## Pass 1 — 2026-07-22 (proof of concept)

Domain: the Collatz "cycle bounds" closure (`CollatzCycleElementBound` + its full transitive
import closure). 9 files, all built clean (`lake build Propositio`, exit 0) with the expected
`[propext, Classical.choice, Quot.sound]` axiom set on the headline theorems.

| ai-math module | new path | status in ai-math |
|---|---|---|
| `Tactics` | `Propositio/Tactics.lean` | **kept** — hub, 4+ outside dependents |
| `TerrasDensity` | `Propositio/Collatz/Basic.lean` | **kept** — hub, ~40 outside dependents |
| `TerrasDensity.Tactics` | `Propositio/Collatz/Basic/Tactics.lean` | kept (companion of the above) |
| `CollatzCascadeCycles` | `Propositio/Collatz/CascadeCycles.lean` | **kept** — hub (Capstone, Uniform, ShortCycleExclusion, SteinerNumerator, ThreeCycleExclusion, `Verify.lean`) |
| `CollatzH5` | `Propositio/Collatz/H5.lean` | **kept** — hub (Capstone, Uniform, ThreeCycleExclusion, `Verify.lean`) |
| `LyapunovCascade` | `Propositio/Collatz/LyapunovCascade.lean` | **kept** — hub (Uniform, DescentDensity, ThreeCycleExclusion, ValuationDensity, Lyapunov, `Verify.lean`) |
| `CollatzCycleTelescope` | `Propositio/Collatz/CycleTelescope.lean` | **kept** — hub (LengthBound, Uniform, Fourteen/FifteenCycle, SteinerClosedForm/Numerator, `Verify.lean`) |
| `CollatzCycleDecide` | `Propositio/Collatz/CycleDecide.lean` | **kept** — hub (CycleEnum, Uniform, `Verify.lean`) |
| `CollatzCycleElementBound` | `Propositio/Collatz/CycleElementBound.lean` | **kept** — hub (Fourteen/Fifteen/SixteenCycle, SteinerNumerator, `Verify.lean`) |

**Zero files deleted from ai-math this pass** — every file in the chosen 9-file domain turned
out to have at least one consumer still living outside it in `ai-math/lean4/`. This repo's
dependency graph is one dense connected component under a few hub files
(`TerrasDensity`/`Tactics` especially); an incremental "migrate one domain, delete it" strategy
will mostly produce *copies*, not *moves*, until enough of the graph has migrated that a hub's
last outside consumer is gone too. Track deletion eligibility by re-running the reverse-dependency
check (see script header) before removing anything from `ai-math`.

## Pass 2 — 2026-07-22/23 (complete)

All remaining 575 files copied over (taxonomy as sketched below, now realized). Final verified
state, `lake build Propositio` exit 0, 552/584 files in the aggregator:

**32 files deliberately excluded from `Propositio.lean`** (present as source under `Propositio/`,
just not imported by the aggregator, so `lake build Propositio` stays green):
- `Verify.lean` — ai-math's axiom-audit entry-point script; not library content, has no outside
  importers once migrated, meant to be run directly rather than imported.
- 2 genuinely broken on fresh compile against current mathlib/sibling content (NOT a migration
  artifact — same content, same errors, if rebuilt fresh in ai-math today): `SteinerNumerator`
  (references identifiers no longer present in `CycleElementBound`, i.e. stale relative to a
  sibling file that moved on without it) and `Beal/MinimalityNormArg` (multiple real tactic
  failures — deprecated/renamed mathlib lemmas, a `linarith` that no longer closes). ai-math's
  own build cache was hiding both — neither had ever actually been rebuilt there recently either.
- 18 files are the abandoned Rhin-construction scaffold for μ(log₂3) (`Log23MeasureRhin`,
  `PadeCasoratian`, `OrderThreeSubCasoratian`, `OSalikhov{Hsmall,DenStructure,Ratio}`,
  `WeightedDiagonalLog43{MeasureReduced,DetIdentity,MeasureFinal}`,
  `DiagonalIntegralLog2{Delannoy,CoeffBound,Measure,IntegralRec}`) — explicitly marked OPEN/
  superseded in their own docstrings once the project found the different, elementary Baker-free
  route instead (see `OSalikhovUnconditional.lean`). Genuinely incomplete, not a bug.
- 11 files are the giant generated `ResidueDescent` case-split family (128 through 1048576;
  the largest, `ResidueDescent1048576.lean`, is 7.3MB / 2823 near-identical theorems) —
  deliberately never attempted. Building even the much smaller `65536*` siblings (~240KB each)
  OOM'd this machine (23GB RAM) when Lake's unbounded default concurrency piled several on at
  once; the `1048576`/`262144` members are larger still. ai-math's own build cache had never
  built any of these 11 either — they may never have been verified end-to-end anywhere.

**Resource lesson for future sessions**: this Lake version (bundled with Lean v4.29.1) has no
`-j`/`--jobs` flag and CPU-affinity (`taskset`) does not reduce how many files it schedules
concurrently — only real serialization (calling `lake build` with a small explicit target list,
one at a time or in small batches, with a memory watcher) is reliable for a corpus with files
this heavy. See `scripts/audit_axioms.py` and the batch pattern used to build the 120-file heavy
cycle-exclusion family for a reusable template.

**Still zero files deleted from `ai-math`.** The whole tree is one connected component via a
handful of hub files (confirmed in pass 1) — a clean incremental "move this, delete that" isn't
possible; it would have to be an all-or-nothing removal of `ai-math/lean4/` in one shot, and that
also requires updating `CLAUDE.md`'s protocol (gate scripts, `Verify.lean`, the autonomous
research loop's definition-of-done) plus 743 KB `docs/kb/frontier/*.json` `"file"` pointers that
currently reference `lean4/...` paths. Deliberately left as a follow-up decision for a session
where a human can review it, not executed unsupervised.
