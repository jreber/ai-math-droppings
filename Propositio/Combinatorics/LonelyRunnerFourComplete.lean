/-
# The Lonely Runner Conjecture, `k = 4`: COMPLETE and UNCONDITIONAL

This capstone assembles the full, honest, unconditional proof of the `k = 4` case of the
Lonely Runner Conjecture (three pairwise-distinct nonzero integer relative speeds, target
bound `1/4`, `nid` the genuine nearest-integer distance).

The proof is the composition of the reduction tower built across the corpus, now that its
last open link — the unit band lemma `ReducedBandPairUnit` — has been proved unconditionally
in `LonelyRunnerReducedUnit`:

* `LonelyRunnerReducedUnit.reducedBandPairUnit_proof`  — the crux (explicit construction);
* `LonelyRunnerBandPairRemaining.caseA_of_unit`        — crux ⟹ `FourThreeResidualCaseA`;
* `LonelyRunnerFourThreeResidualCaseB.fourThreeResidual_of_caseA` — Case A + Case B ⟹ `FourThreeResidual`;
* `LonelyRunnerCoprimeKernel.coprimeKernel_of_residual` — residual ⟹ full `CoprimeKernel`;
* `LonelyRunnerFourResidual.lonely_runner_four_reduce`  — kernel ⟹ every distinct triple.

The final theorem `lonely_runner_four` is unconditional. No `sorry`, no `axiom`, no
`native_decide`.
-/
import Mathlib.Data.Real.Basic
import Propositio.Combinatorics.LonelyRunnerSmallK
import Propositio.Combinatorics.LonelyRunnerFourResidual
import Propositio.Combinatorics.LonelyRunnerCoprimeKernel
import Propositio.Combinatorics.LonelyRunnerFourThreeResidualCaseB
import Propositio.Combinatorics.LonelyRunnerBandPairRemaining
import Propositio.Combinatorics.LonelyRunnerReducedUnit

namespace LonelyRunnerFourComplete

open LonelyRunnerSmallK LonelyRunnerFourResidual LonelyRunnerCoprimeKernel
  LonelyRunnerFourThreeResidualCaseB LonelyRunnerBandPairRemaining LonelyRunnerReducedUnit

/-- **The pairwise-coprime kernel, proved unconditionally.** -/
theorem coprimeKernel_final : CoprimeKernel :=
  coprimeKernel_of_residual
    (fourThreeResidual_of_caseA fourThreeResidualCaseA_final)

/-- **The Lonely Runner Conjecture, `k = 4` — COMPLETE.**

For any three pairwise-distinct nonzero integer speeds `v1, v2, v3`, there is a time `t` at
which all three runners are at nearest-integer distance `≥ 1/4` from the origin simultaneously
(equivalently, the fourth runner — fixed at the origin by the standard reduction — is lonely).
Unconditional. -/
theorem lonely_runner_four (v1 v2 v3 : ℤ) (h1 : v1 ≠ 0) (h2 : v2 ≠ 0) (h3 : v3 ≠ 0)
    (h12 : v1 ≠ v2) (h13 : v1 ≠ v3) (h23 : v2 ≠ v3) :
    ∃ t : ℝ, (1 : ℝ) / 4 ≤ nid ((v1 : ℝ) * t) ∧ (1 : ℝ) / 4 ≤ nid ((v2 : ℝ) * t) ∧
      (1 : ℝ) / 4 ≤ nid ((v3 : ℝ) * t) :=
  lonely_runner_four_reduce v1 v2 v3 h1 h2 h3 h12 h13 h23 coprimeKernel_final

end LonelyRunnerFourComplete
