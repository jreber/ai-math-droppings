import Propositio.NumberTheory.Diophantine.OSalikhovDenBound
import Propositio.NumberTheory.Diophantine.OSalikhovDenDvd
import Propositio.Collatz.Chebyshev30LcmAll

/-!
# The prize denominator bound, reduced to the single input `hdvd`

`OSalikhovDenDvd.DenIntN_bound_30_of_inputs` reduced the lone prize sorry
`DenIntN n ≤ 6·30ⁿ` to two non-transcendence inputs `hdvd` (a `p`-adic divisibility) and
`hlcm` (an effective-Chebyshev `lcm` bound).  The `hlcm` input is now **discharged
unconditionally** by `CollatzChebyshev30.lcm_two_n_le_target_all` (the analytic sharp pin for
`n ≥ 8500` plus the verified incremental census for `1 ≤ n < 8500`).

This file consumes that, leaving the prize Den bound dependent on **only** the arithmetic
divisibility `hdvd`.  Note `hlcm` is FALSE at `n = 0`; the `n < 41` window (including `n = 0`)
is dispatched by the existing `DenIntN_bound_30_fin41` `native_decide`, and `hdvd`/`hlcm` are
used only for `n ≥ 41 ≥ 1`.
-/

namespace OSalikhovDenDvd

open OSalikhovIntCoord LcmGrowthBound CollatzChebyshev30

/-- **The prize Den bound, reduced to the single input `hdvd`.**  With `hlcm` now an
unconditional theorem (`lcm_two_n_le_target_all`), the lone prize sorry follows from just the
arithmetic divisibility `DenIntN m ∣ 3ᵐ·30·lcm(1..2m)`. -/
theorem DenIntN_bound_30_of_hdvd
    (hdvd : ∀ m, DenIntN m ∣ 3 ^ m * 30 * lcmUpto (2 * m))
    (n : ℕ) : DenIntN n ≤ 6 * 30 ^ n := by
  by_cases hn : n < 41
  · exact OSalikhovDenBound.DenIntN_bound_30_fin41 ⟨n, hn⟩
  · have hn1 : 1 ≤ n := by omega
    have hlpos : 0 < lcmUpto (2 * n) := Nat.pos_of_ne_zero (lcmUpto_ne_zero _)
    have hpos : 0 < 3 ^ n * 30 * lcmUpto (2 * n) := by positivity
    calc DenIntN n
        ≤ 3 ^ n * 30 * lcmUpto (2 * n) := Nat.le_of_dvd hpos (hdvd n)
      _ = 3 ^ n * (30 * lcmUpto (2 * n)) := by ring
      _ ≤ 3 ^ n * (6 * 10 ^ n) := mul_le_mul_left' (lcm_two_n_le_target_all n hn1) (3 ^ n)
      _ = 6 * 30 ^ n := by rw [show (30 : ℕ) = 3 * 10 by norm_num, mul_pow]; ring

/-- The ℝ-valued interface form, reduced to the single input `hdvd`. -/
theorem DenR_bound_30_of_hdvd
    (hdvd : ∀ m, DenIntN m ∣ 3 ^ m * 30 * lcmUpto (2 * m))
    (n : ℕ) : (DenIntN n : ℝ) ≤ (6 : ℝ) * (30 : ℝ) ^ n := by
  have h := DenIntN_bound_30_of_hdvd hdvd n
  have : (DenIntN n : ℝ) ≤ ((6 * 30 ^ n : ℕ) : ℝ) := by exact_mod_cast h
  calc (DenIntN n : ℝ) ≤ ((6 * 30 ^ n : ℕ) : ℝ) := this
    _ = 6 * 30 ^ n := by push_cast; ring

#print axioms DenIntN_bound_30_of_hdvd

end OSalikhovDenDvd
