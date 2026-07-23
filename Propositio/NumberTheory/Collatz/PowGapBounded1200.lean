import Propositio.NumberTheory.Collatz.DescentDichotomy
import Propositio.NumberTheory.Collatz.PowGapReduce
import Propositio.NumberTheory.Collatz.PowGapSmall

/-!
# `PowGap` for `a ≤ 1200` — the finite mid-range for `μ(log₂3) ≲ 112`

The honest oSALIKHOV measure (`OSalikhovConsolidated.osalikhov_logb23_measure_c30`) has exponent
`μ ≈ 51.8` but an astronomically small constant `C = 1/(2BQ²(2A)^s) ≈ 6.6·10⁻¹¹⁶`.  Feeding it to the
`PowGap` reduction requires NORMALIZING the constant: for `a ≥ 100`, `1/a^M ≤ C/a^μ` once
`a^{M−μ} ≥ 1/C`, and `M − μ ≥ 58` suffices (`100^58 = 10¹¹⁶ ≥ 1/C`).  So the usable exponent after
normalization is `M ≈ 110`, and the corresponding mid-range threshold is `a₀ = 1200`
(`112·log₂(1200) ≈ 1146 < 1200`).

This file extends the bounded `native_decide` to `a ≤ 1200` (sub-threshold `k < 2a ≤ 2400`,
`1201 × 2401` cases, ≤ 722-digit powers, ~66 s / ~3.6 GB).  Combined with the slack `a¹¹² ≤ 2ᵃ`
(`a ≥ 1200`) and any `LinFormGapLog23Mu μ` (`μ ≤ 112`), it closes the Collatz `PowGap` via
`CollatzPowGapMu.powGap_of_linFormGapMu` with `a₀ = 1200`.
-/

namespace CollatzPowGapBounded1200

open CollatzDescentDichotomy CollatzPowGapReduce

/-- **PowGap for `a ≤ 1200`, `k ≤ 2400`** via `native_decide`. -/
theorem powGap_bounded_1200 :
    ∀ a : Fin 1201, ∀ k : Fin 2401,
      3 ^ (a : Nat) < 2 ^ (k : Nat) →
      2 ^ (a : Nat) * (2 ^ (k : Nat) - 3 ^ (a : Nat) + 1) > 3 ^ (a : Nat) := by
  native_decide

/-- **PowGap holds for all `a ≤ 1200` (any `k`).** -/
theorem powGap_of_le_1200 (a k : Nat) (ha : a ≤ 1200) (h3k : 3 ^ a < 2 ^ k) :
    2 ^ a * (2 ^ k - 3 ^ a + 1) > 3 ^ a := by
  by_cases hk : 2 * a ≤ k
  · exact powGap_of_two_a_le a k hk h3k
  · push_neg at hk
    exact powGap_bounded_1200 ⟨a, by omega⟩ ⟨k, by omega⟩ h3k

end CollatzPowGapBounded1200
