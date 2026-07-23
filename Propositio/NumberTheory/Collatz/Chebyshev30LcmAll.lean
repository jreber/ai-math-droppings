import Propositio.NumberTheory.Collatz.Chebyshev30LcmCensus
import Propositio.NumberTheory.Collatz.Chebyshev30LcmPinSharp

/-!
# The Chebyshev-30 lcm pin, complete: `hlcm` for all `n ≥ 1`

Combines the finite census `1 ≤ n < 8500` (`census_1_to_8499`, one `native_decide` over a
verified incremental lcm sweep) with the sharp analytic threshold `n ≥ 8500`
(`lcm_two_n_le_target_sharp`) to give the prize denominator input

  `hlcm : ∀ n ≥ 1, 30·lcm(1..2n) ≤ 6·10ⁿ`

unconditionally.  This is the second of the two non-transcendence inputs of
`OSalikhovDenDvd.DenIntN_bound_30_of_inputs` (the first being the `p`-adic divisibility `hdvd`).
The bound is FALSE at `n = 0` (`30 > 6`), which is why the input is stated for `n ≥ 1`; the
`n = 0` case of the prize Den bound is covered separately by `DenIntN_bound_30_fin41`.
-/

namespace CollatzChebyshev30

open LcmGrowthBound

/-- **The complete lcm pin.**  `30·lcm(1..2n) ≤ 6·10ⁿ` for every `n ≥ 1`. -/
theorem lcm_two_n_le_target_all (n : ℕ) (hn : 1 ≤ n) :
    30 * lcmUpto (2 * n) ≤ 6 * 10 ^ n := by
  by_cases h : n < 8500
  · exact census_1_to_8499 n hn h
  · exact lcm_two_n_le_target_sharp n (by omega)

#print axioms lcm_two_n_le_target_all

end CollatzChebyshev30
