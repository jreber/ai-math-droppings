import Propositio.NumberTheory.Diophantine.WeightedDiagonalLog43
import Propositio.NumberTheory.Diophantine.DiagonalIntegralLog2Hsmall
import Mathlib.Tactic

/-!
# The `hsmall` decay `lcm(1..n)·Jₙ → 0` for the weighted-diagonal `log(4/3)` construction

`Jₙ ≤ ρⁿ·log(4/3)` (`J_le`, `ρ = 7−4√3`) and `lcm(1..n)·ρⁿ → 0` (since `4ρ = 28−16√3 < 1`, using
the generic `DiagonalIntegralLog2.geom_lcm_tendsto_zero_gen`), so by squeezing against `J_pos`,
`lcm(1..n)·Jₙ → 0`.  This is the `hsmall` analytic input for the unconditional effective
irrationality measure of `log(4/3)` (the last analytic ingredient; the remaining bricks are the
integer linear form — `α₁(n) ∈ ℤ` via the Legendre binomial sum, and `den(Pₙ) | lcm(1..n)`).
-/

namespace WeightedDiagonalLog43

open Filter LcmGrowthBound

/-- `4·(7−4√3) < 1` (`16√3 > 27`). -/
theorem four_rho_lt_one : 4 * (7 - 4 * Real.sqrt 3) < 1 := by
  nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num), Real.sqrt_nonneg 3]

/-- `0 < 7 − 4√3` (`√3 < 7/4`). -/
theorem rho_pos : (0:ℝ) < 7 - 4 * Real.sqrt 3 := by
  nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num), Real.sqrt_nonneg 3]

/-- **The `hsmall` decay.** `lcm(1..n)·Jₙ → 0`. -/
theorem D_mul_J_tendsto_zero :
    Tendsto (fun n => (lcmUpto n : ℝ) * J n) atTop (nhds 0) := by
  have hgeom := DiagonalIntegralLog2.geom_lcm_tendsto_zero_gen (7 - 4 * Real.sqrt 3) rho_pos
    four_rho_lt_one
  have hupper : Tendsto
      (fun n => (lcmUpto n : ℝ) * (7 - 4 * Real.sqrt 3) ^ n * Real.log (4 / 3)) atTop (nhds 0) := by
    have := hgeom.mul_const (Real.log (4 / 3))
    simpa [mul_assoc] using this
  refine squeeze_zero (fun n => ?_) (fun n => ?_) hupper
  · exact mul_nonneg (by positivity) (le_of_lt (J_pos n))
  · have hlcm : (0:ℝ) ≤ (lcmUpto n : ℝ) := by positivity
    calc (lcmUpto n : ℝ) * J n
        ≤ (lcmUpto n : ℝ) * ((7 - 4 * Real.sqrt 3) ^ n * Real.log (4 / 3)) :=
          mul_le_mul_of_nonneg_left (J_le n) hlcm
      _ = (lcmUpto n : ℝ) * (7 - 4 * Real.sqrt 3) ^ n * Real.log (4 / 3) := by ring

end WeightedDiagonalLog43
