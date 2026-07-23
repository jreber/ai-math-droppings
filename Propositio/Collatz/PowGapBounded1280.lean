import Propositio.Collatz.DescentDichotomy
import Propositio.Collatz.PowGapReduce
import Propositio.Collatz.PowGapSmall

/-!
# `PowGap` for `a ≤ 1280` — the finite mid-range for `μ(log₂3) ≲ 120`

The honest oSALIKHOV measure (`OSalikhovConsolidated.osalikhov_logb23_measure_c30`) has exponent
`μ ≈ 51.8` but an astronomically small constant `C = 1/(2BQ²(2A)^s) ≈ 6.6·10⁻¹¹⁶`.  Feeding it to the
`PowGap` reduction requires NORMALIZING the constant: for `a ≥ 100`, `1/a^M ≤ C/a^μ` once
`a^{M−μ} ≥ 1/C`, and `M − μ ≥ 58` suffices (`100^58 = 10¹¹⁶ ≥ 1/C`).  So the usable exponent after
normalization is `M ≈ 110`, and the corresponding mid-range threshold is `a₀ = 1280`
(`112·log₂(1280) ≈ 1146 < 1280`).

This file extends the bounded `native_decide` to `a ≤ 1280` (sub-threshold `k < 2a ≤ 2560`,
`1281 × 2561` cases, ≤ 771-digit powers, ~90 s / ~3.6 GB).  Combined with the slack `a¹²⁰ ≤ 2ᵃ`
(`a ≥ 1280`) and any `LinFormGapLog23Mu μ` (`μ ≤ 120`), it closes the Collatz `PowGap` via
`CollatzPowGapMu.powGap_of_linFormGapMu` with `a₀ = 1280`.
-/

namespace CollatzPowGapBounded1280

open CollatzDescentDichotomy CollatzPowGapReduce

/-- **PowGap for `a ≤ 1280`, `k ≤ 2560`** via `native_decide`. -/
theorem powGap_bounded_1280 :
    ∀ a : Fin 1281, ∀ k : Fin 2561,
      3 ^ (a : Nat) < 2 ^ (k : Nat) →
      2 ^ (a : Nat) * (2 ^ (k : Nat) - 3 ^ (a : Nat) + 1) > 3 ^ (a : Nat) := by
  native_decide

/-- **PowGap holds for all `a ≤ 1280` (any `k`).** -/
theorem powGap_of_le_1280 (a k : Nat) (ha : a ≤ 1280) (h3k : 3 ^ a < 2 ^ k) :
    2 ^ a * (2 ^ k - 3 ^ a + 1) > 3 ^ a := by
  by_cases hk : 2 * a ≤ k
  · exact powGap_of_two_a_le a k hk h3k
  · push_neg at hk
    exact powGap_bounded_1280 ⟨a, by omega⟩ ⟨k, by omega⟩ h3k

end CollatzPowGapBounded1280
