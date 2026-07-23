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

## Not yet started

~579 remaining files. Rough taxonomy sketch for when they migrate (subject to revision as more
of the graph is mapped):
- `Propositio/Collatz/` — the other ~150 `CollatzX` files (density/residue-descent family is
  large: `CollatzResidueDescentNNNN` × ~15 files alone)
- `Propositio/Beal/` — `BealX` files
- `Propositio/NumberTheory/Diophantine/` — the two-log irrationality-measure machinery
  (`OSalikhov*`, `WeightedDiagonalLog43*`, `LinIndepMeasure3D*`, `IrrMeasureCombination`,
  `Pade*`, `OrderThreeRecurrence`, `DiagonalIntegralLog2*`)
- `Propositio/NumberTheory/Chebyshev/` — `Chebyshev*` prime-counting files
- `Propositio/Combinatorics/` — `FriendshipTheorem`, `ErdosRado` (Sunflower), `SylvesterGallai`
- `Propositio/NumberTheory/LonelyRunner/`, `.../Zsygmondy/`, `.../FermatLastTheorem/`
- `Verify.lean` (the axiom-audit sentinel) is itself a hub-of-hubs and should migrate last, once
  everything it imports has moved.
