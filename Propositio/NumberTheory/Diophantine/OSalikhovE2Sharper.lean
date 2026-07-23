import Propositio.NumberTheory.Diophantine.OSalikhovDecomp

/-!
# Sharper geometric decay of `E2`:  `|E2 n| ≤ 5·(27/1000)ⁿ`

`OSalikhovDecomp.E2_abs_le_sharp` gives `|E2 n| ≤ 5·(1/32)ⁿ`.  The integrand base
`base(x) = x²(x²−9)(x²−25)/(x²−225)²` has max `|base| ≈ 0.02687 < 27/1000` on `[0,5]` (attained at
`x ≈ 4.347`), so the rate sharpens to `27/1000 = 0.027 < 1/32 = 0.03125`.  This matters for the
prize's quantitative `μ ≤ 22`: with the sharp Apéry lcm bound `Den ≤ D·21ⁿ`, the cleared form decays
at `ρ = 21·(27/1000) ≈ 0.567`, giving `μ = 1 + logQ/log(1/ρ) ≈ 19 ≤ 22` (vs `ρ = 21/32 ≈ 0.656`,
`μ ≈ 25.6` from the `1/32` bound).

The bound is tight (0.5 % margin), so the core polynomial inequality
`|x²(x²−9)(x²−25)| ≤ (27/1000)(225−x²)²` on `[0,5]` needs `nlinarith` hints concentrated near the
maximiser `x² ≈ 18.9`. -/

namespace OSalikhovTwoLog

open MeasureTheory intervalIntegral Set

/-- **Sharper pointwise integrand bound on `[0,5]`**: `|fOsal n x| ≤ (27/1000)ⁿ`. -/
theorem fOsal_abs_le_five_sharper (n : ℕ) {x : ℝ} (h0 : 0 ≤ x) (h5 : x ≤ 5) :
    |fOsal n x| ≤ (27 / 1000) ^ n := by
  have hxx : (0 : ℝ) ≤ x ^ 2 := sq_nonneg x
  have h25 : (0 : ℝ) ≤ 25 - x ^ 2 := by nlinarith
  have hden : (1 : ℝ) ≤ 225 - x ^ 2 := by nlinarith
  have hdenpos : (0 : ℝ) < 225 - x ^ 2 := by linarith
  set Pf : ℝ := x ^ 2 * (x ^ 2 - 9) * (x ^ 2 - 25) with hPf
  have hnum : x ^ (2 * n) * (x ^ 2 - 9) ^ n * (x ^ 2 - 25) ^ n = Pf ^ n := by
    rw [pow_mul, ← mul_pow, ← mul_pow, hPf]
  have hden_eq : (x ^ 2 - 225) ^ (2 * n + 1) = -((225 - x ^ 2) ^ (2 * n + 1)) := by
    rw [show x ^ 2 - 225 = -(225 - x ^ 2) by ring]; exact Odd.neg_pow ⟨n, by ring⟩ _
  have habs : |fOsal n x| = |Pf| ^ n / (225 - x ^ 2) ^ (2 * n + 1) := by
    unfold fOsal
    rw [hnum, hden_eq, div_neg, abs_neg, abs_div, abs_pow, abs_pow, abs_of_pos hdenpos]
  rw [habs, div_le_iff₀ (by positivity)]
  have hb : |Pf| ≤ 27 / 1000 * (225 - x ^ 2) ^ 2 := by
    rw [abs_le, hPf]
    refine ⟨?_, ?_⟩
    · nlinarith [mul_nonneg hxx h25, sq_nonneg (x ^ 2 - 19), sq_nonneg (x ^ 2 - 16),
        mul_nonneg hxx (sq_nonneg (x ^ 2 - 19)), mul_nonneg h25 (sq_nonneg (x ^ 2 - 19)),
        mul_nonneg (mul_nonneg hxx h25) h25, mul_nonneg (mul_nonneg hxx h25) hxx,
        mul_nonneg hxx (sq_nonneg (x ^ 2 - 9)), sq_nonneg (x ^ 2 - 9)]
    · nlinarith [mul_nonneg hxx h25, sq_nonneg (x ^ 2 - 19), sq_nonneg (x ^ 2 - 16),
        mul_nonneg hxx (sq_nonneg (x ^ 2 - 19)), mul_nonneg h25 (sq_nonneg (x ^ 2 - 19)),
        mul_nonneg (mul_nonneg hxx h25) h25, mul_nonneg hxx h25,
        mul_nonneg hxx (sq_nonneg (x ^ 2 - 9)), sq_nonneg (x ^ 2 - 9)]
  calc |Pf| ^ n ≤ (27 / 1000 * (225 - x ^ 2) ^ 2) ^ n := pow_le_pow_left₀ (abs_nonneg _) hb n
    _ = (27 / 1000 : ℝ) ^ n * (225 - x ^ 2) ^ (2 * n) := by rw [mul_pow, ← pow_mul]
    _ ≤ (27 / 1000 : ℝ) ^ n * (225 - x ^ 2) ^ (2 * n + 1) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact pow_le_pow_right₀ hden (by omega)

/-- **Sharper geometric decay of `E2`**: `|E2 n| ≤ 5·(27/1000)ⁿ`. -/
theorem E2_abs_le_sharper (n : ℕ) : |E2 n| ≤ 5 * (27 / 1000) ^ n := by
  have hbnd : ∀ x ∈ Set.uIoc (0 : ℝ) 5, ‖fOsal n x‖ ≤ (27 / 1000) ^ n := by
    intro x hx
    rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 5)] at hx
    rw [Real.norm_eq_abs]
    exact fOsal_abs_le_five_sharper n (le_of_lt hx.1) hx.2
  have := intervalIntegral.norm_integral_le_of_norm_le_const hbnd
  rw [Real.norm_eq_abs] at this
  calc |E2 n| = |∫ x in (0:ℝ)..5, fOsal n x| := by rw [E2]
    _ ≤ (27 / 1000) ^ n * |(5 : ℝ) - 0| := this
    _ = 5 * (27 / 1000) ^ n := by rw [show |(5:ℝ) - 0| = 5 by norm_num]; ring

end OSalikhovTwoLog
