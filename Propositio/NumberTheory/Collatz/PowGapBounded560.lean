import Propositio.NumberTheory.Collatz.DescentDichotomy
import Propositio.NumberTheory.Collatz.PowGapReduce
import Propositio.NumberTheory.Collatz.PowGapSmall

/-!
# `PowGap` for `a ≤ 560` — the finite mid-range for `μ(log₂3) ≲ 60`

The honest oSALIKHOV denominator bound is `Den n ≤ D·30ⁿ` (`OSalikhovDenBound.DenIntN_bound_30`;
the earlier `21ⁿ`/`22ⁿ` rates are FALSE — see `OSalikhovDenStructure`). With `C = 30` the cleared
form has `ρ = 30·(27/1000) = 81/100` and height `Q = 30·1500 = 45000`, giving the effective exponent
`1 + log(45000)/log(100/81) ≈ 1 + 50.8 = 51.8`. So the downstream `PowGap` reduction needs the
mid-range threshold `a₀` where `a⁶⁰ ≤ 2ᵃ` (`a₀ = 560`, since `60·log₂(560) ≈ 547.8 < 560`), which is
comfortably above the true `μ ≈ 52` — leaving margin for the crude-height variant (`μ ≈ 57`).

This file extends the bounded `native_decide` from `a ≤ 170` (`CollatzPowGapBounded170`) to
`a ≤ 560` (sub-threshold `k < 2a ≤ 1120`). Construction-independent: combined with the slack
`a⁶⁰ ≤ 2ᵃ` (`a ≥ 560`) and any `LinFormGapLog23Mu μ` (`μ ≤ 60`), it closes the Collatz `PowGap`
via `CollatzPowGapMu.powGap_of_linFormGapMu` with the explicit threshold `a₀ = 560`.

The `native_decide` cost: `561 × 1121` cases with ≤ 337-digit powers, ~12 s / ~3.6 GB.
-/

namespace CollatzPowGapBounded560

open CollatzDescentDichotomy CollatzPowGapReduce

/-- **PowGap for `a ≤ 560`, `k ≤ 1120`** via `native_decide`.
Sub-threshold for `a ≤ 560` lives in `k < 2a ≤ 1120`. -/
theorem powGap_bounded_560 :
    ∀ a : Fin 561, ∀ k : Fin 1121,
      3 ^ (a : Nat) < 2 ^ (k : Nat) →
      2 ^ (a : Nat) * (2 ^ (k : Nat) - 3 ^ (a : Nat) + 1) > 3 ^ (a : Nat) := by
  native_decide

/-- **PowGap holds for all `a ≤ 560` (any `k`).**  Mirrors `CollatzPowGapBounded170.powGap_of_le_170`:
`k ≥ 2a` is elementary (`powGap_of_two_a_le`); `k < 2a ≤ 1120` is the bounded `native_decide`. -/
theorem powGap_of_le_560 (a k : Nat) (ha : a ≤ 560) (h3k : 3 ^ a < 2 ^ k) :
    2 ^ a * (2 ^ k - 3 ^ a + 1) > 3 ^ a := by
  by_cases hk : 2 * a ≤ k
  · exact powGap_of_two_a_le a k hk h3k
  · push_neg at hk
    exact powGap_bounded_560 ⟨a, by omega⟩ ⟨k, by omega⟩ h3k

end CollatzPowGapBounded560
