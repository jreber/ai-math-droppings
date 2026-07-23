/-
# Lonely Runner `k = 4`: the residual now reduces to the *unit* band lemma alone

This capstone wires together the three pieces that sharpen the last open link of the honest
`k = 4` Lonely Runner Conjecture:

* `LonelyRunnerFourThreeResidualCaseAComplete.caseA_of_bandPair` : `BandPair → FourThreeResidualCaseA`.
* `LonelyRunnerBandPairReduction.bandPair_of_reduced` : `ReducedBandPair → BandPair`
  (the `p⁻¹`-substitution collapsing the two multipliers to one).
* `LonelyRunnerReducedNonUnit.reducedBandPair_nonunit` : the *non-unit* case of
  `ReducedBandPair` (an explicit construction — the regime where naive pigeonhole fails).

Consequently the whole residual reduces to the strictly smaller **unit** case
`ReducedBandPairUnit`: for `D ≥ 6`, `D ∤ r`, and `r` *coprime* to `D`, some `k` puts both
`k` and `r·k` in the middle band mod `D`. Equivalently: *the interval `[D/4, 3D/4]` and its
image under a unit `k ↦ r·k mod D` always intersect.* Everything here is axiom-clean; the
only thing that remains open is `ReducedBandPairUnit` (the genuine crux of `k = 4` Lonely
Runner — where the pigeonhole bound `2·|band| − D` can be negative, e.g. `D ≡ 1 (mod 4)`).
-/
import Propositio.Combinatorics.LonelyRunnerFourThreeResidualCaseAComplete
import Propositio.Combinatorics.LonelyRunnerBandPairReduction
import Propositio.Combinatorics.LonelyRunnerReducedNonUnit

namespace LonelyRunnerBandPairRemaining

open LonelyRunnerFourThreeResidualCaseAComplete LonelyRunnerBandPairReduction
  LonelyRunnerReducedNonUnit LonelyRunnerFourThreeResidualCaseB

/-- **The remaining crux: the unit case of the band lemma.** For every modulus `D ≥ 6` and
every `r` coprime to `D` (so `r ≢ 0`), the middle band `[D/4, 3D/4]` mod `D` meets its
preimage under the unit `k ↦ r·k`. This is all that stands between the current corpus and a
complete, unconditional proof of the honest `k = 4` Lonely Runner Conjecture. -/
def ReducedBandPairUnit : Prop :=
  ∀ (D : ℕ) (r : ℤ), 6 ≤ D → ¬ ((D : ℤ) ∣ r) → IsCoprime r (D : ℤ) →
    ∃ k : ℤ, inBand k D ∧ inBand (r * k) D

/-- The full single-multiplier `ReducedBandPair` follows from just its unit case: the
non-unit case is already discharged by `reducedBandPair_nonunit`. -/
theorem reducedBandPair_of_unit (h : ReducedBandPairUnit) : ReducedBandPair := by
  intro D r hD hnd
  by_cases hc : IsCoprime r (D : ℤ)
  · exact h D r hD hnd hc
  · exact reducedBandPair_nonunit D r hD hnd hc

/-- **Capstone reduction.** `FourThreeResidualCaseA` — the sole remaining residual of the
honest `k = 4` Lonely Runner Conjecture — follows from the single unit-case band lemma
`ReducedBandPairUnit`, unconditionally and axiom-cleanly. -/
theorem caseA_of_unit (h : ReducedBandPairUnit) : FourThreeResidualCaseA :=
  caseA_of_bandPair (bandPair_of_reduced (reducedBandPair_of_unit h))

end LonelyRunnerBandPairRemaining
