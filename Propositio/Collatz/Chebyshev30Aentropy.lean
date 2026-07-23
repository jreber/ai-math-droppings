import Propositio.Collatz.Chebyshev30MSize
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Chebyshev-30: a clean rational upper bound on the entropy constant `Aentropy`

The period-30 entropy constant
`Aentropy = ½log2 + ⅓log3 + ⅕log5 − (1/30)log30 ≈ 0.92129`
(defined in `CollatzChebyshev30MSize`) is bounded above by the clean rational `37/40 = 0.925`.

This certifies the Chebyshev-30 route reaches `C = 30`: it gives both
`6·(Aentropy + 1/30)/5 < 1.151` and `Aentropy < (5/12)·log10 − 1/30`.

The proof rewrites `Aentropy` into the basis `{log2, log(3/2), log(5/4)}` (all with positive
coefficients), then bounds each generator from above:
* `log 2 < 0.6931471808`  (`Real.log_two_lt_d9`),
* `log (3/2) < 0.4055`  (Taylor series of `log(1 − 1/3)`, 12 terms),
* `log (5/4) < 0.2232`  (Taylor series of `log(1 − 1/5)`, 8 terms).
Combining: `11/10·0.6931471808 + 3/10·0.4055 + 1/6·0.2232 ≈ 0.92131 < 0.925`.
-/

namespace CollatzChebyshev30

open Real

/-- **Basis identity.**  `Aentropy = 11/10·log2 + 3/10·log(3/2) + 1/6·log(5/4)`.
The three coefficients are positive, so upper bounds on the generators combine directly. -/
theorem Aentropy_eq :
    Aentropy = 11/10 * Real.log 2 + 3/10 * Real.log (3/2) + 1/6 * Real.log (5/4) := by
  have h32 : Real.log (3/2) = Real.log 3 - Real.log 2 :=
    Real.log_div (by norm_num) (by norm_num)
  have h54 : Real.log (5/4) = Real.log 5 - Real.log 4 :=
    Real.log_div (by norm_num) (by norm_num)
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  have h30 : Real.log 30 = Real.log 2 + Real.log 3 + Real.log 5 := by
    rw [show (30 : ℝ) = 2 * 3 * 5 by norm_num,
        Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num)]
  unfold Aentropy
  rw [h32, h54, h4, h30]; ring

/-- **Upper bound on `log(3/2)`** via 12 terms of the Taylor series of `log(1 − 1/3)`. -/
theorem log_three_halves_lt : Real.log (3/2) < 0.4055 := by
  have t : |((1:ℝ)/3)| = 1/3 := by rw [abs_of_pos]; norm_num
  have z := Real.abs_log_sub_add_sum_range_le (show |((1:ℝ)/3)| < 1 by rw [t]; norm_num) 12
  rw [t, abs_le] at z
  obtain ⟨z1, _⟩ := z
  have hsum : (∑ i ∈ Finset.range 12, ((1:ℝ)/3)^(i+1)/((i:ℝ)+1))
      + (1/3:ℝ)^(12+1)/(1-(1:ℝ)/3) < 0.4055 := by
    norm_num [Finset.sum_range_succ]
  have hlog : Real.log ((3:ℝ)/2) = - Real.log (1 - 1/3) := by
    rw [show (3:ℝ)/2 = (1 - 1/3)⁻¹ by norm_num, Real.log_inv]
  rw [hlog]; linarith [z1, hsum]

/-- **Upper bound on `log(5/4)`** via 8 terms of the Taylor series of `log(1 − 1/5)`. -/
theorem log_five_quarters_lt : Real.log (5/4) < 0.2232 := by
  have t : |((1:ℝ)/5)| = 1/5 := by rw [abs_of_pos]; norm_num
  have z := Real.abs_log_sub_add_sum_range_le (show |((1:ℝ)/5)| < 1 by rw [t]; norm_num) 8
  rw [t, abs_le] at z
  obtain ⟨z1, _⟩ := z
  have hsum : (∑ i ∈ Finset.range 8, ((1:ℝ)/5)^(i+1)/((i:ℝ)+1))
      + (1/5:ℝ)^(8+1)/(1-(1:ℝ)/5) < 0.2232 := by
    norm_num [Finset.sum_range_succ]
  have hlog : Real.log ((5:ℝ)/4) = - Real.log (1 - 1/5) := by
    rw [show (5:ℝ)/4 = (1 - 1/5)⁻¹ by norm_num, Real.log_inv]
  rw [hlog]; linarith [z1, hsum]

/-- **Main result.**  `Aentropy < 37/40 = 0.925`.  (True value `≈ 0.92129`.) -/
theorem Aentropy_lt : Aentropy < 37/40 := by
  have hl2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have h32 := log_three_halves_lt
  have h54 := log_five_quarters_lt
  rw [Aentropy_eq]
  nlinarith [hl2, h32, h54]

/-- **The `theta_tight` slope is `< 23/20 = 1.15`** (hence `< 1.151`, with room to spare):
`6·(Aentropy + 1/30)/5 < 23/20`.  Since `Aentropy < 37/40` and `37/40 + 1/30 = 23/24`,
`6·(23/24)/5 = 23/20`.  This is the numeric certificate that the Chebyshev-30 route reaches the
`C = 30` den bound (`θ(x) ≤ 1.15·x + C` ⟹ `lcm(1..2n) ≤ 10ⁿ/5`), not merely `C < 37`. -/
theorem theta_tight_slope_lt : 6 * (Aentropy + 1 / 30) / 5 < 23 / 20 := by
  have := Aentropy_lt; linarith

end CollatzChebyshev30
