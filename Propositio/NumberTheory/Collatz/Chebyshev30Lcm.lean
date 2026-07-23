import Propositio.NumberTheory.Diophantine.LcmGrowthBound
import Propositio.NumberTheory.Collatz.Chebyshev30ThetaTight

/-!
# Chebyshev-30 lcm bound: `log(lcm(1..n)) ≤ 1.1455·n + θ(57600) + 2√n·log n`

Combining the explicit tight Chebyshev bound `theta_tight` (θ(x) ≤ (6(A+1/30)/5)·x + θ(57600),
constant ≈ 1.1455 < 1.151) with the existing corpus bridge `LcmGrowthBound.log_lcmUpto_eq_psi`
(`log(lcmUpto n) = ψ(n)`) and the mathlib ψ−θ gap `abs_psi_sub_theta_le_sqrt_mul_log`
(`|ψ−θ| ≤ 2√n·log n`).

This is the Chebyshev-30 replacement for `LcmGrowthBound.log_lcmUpto_le_sharp` (which uses mathlib's
`psi_le`, leading constant `log 4 = 1.386`): the leading constant here is `≈ 1.1455`, the genuine
period-30 Chebyshev rate.  At `n ↦ 2n` it gives `log lcm(1..2n) ≤ 2.291·n + subexp`, below the
`n·log 10 − log 5 ≈ 2.303·n` the prize's `hlcm` (`30·lcm(1..2n) ≤ 6·10ⁿ`) needs — whereas the
`log 4` bound gives `2.773·n`, too weak.  The remaining gap to `hlcm` is a numeric pin
(needs `log 3`, `log 5` upper bounds) plus a sub-exponential threshold absorption and small-`n`
`native_decide`.
-/

namespace CollatzChebyshev30

open Chebyshev Real LcmGrowthBound

/-- **Chebyshev-30 lcm bound.** `log(lcm(1..n)) ≤ (6(A+1/30)/5)·n + θ(57600) + 2√n·log n`,
leading constant `≈ 1.1455` — the period-30 Chebyshev rate, beating `log 4 ≈ 1.386`. -/
theorem log_lcmUpto_le_cheb30 (n : ℕ) :
    Real.log (lcmUpto n)
      ≤ (6 * (Aentropy + 1 / 30) / 5) * n + θ 57600 + 2 * Real.sqrt n * Real.log n := by
  rw [log_lcmUpto_eq_psi]
  rcases Nat.lt_or_ge n 1 with hn | hn
  · -- n = 0: ψ 0 = 0, RHS ≥ θ 57600 ≥ 0
    interval_cases n
    simp only [Nat.cast_zero, Chebyshev.psi, Nat.floor_zero, Finset.Ioc_self,
      Finset.sum_empty, Real.sqrt_zero, mul_zero, add_zero, Real.log_zero]
    have : (0 : ℝ) ≤ θ 57600 := Chebyshev.theta_nonneg _
    nlinarith [Aentropy_nonneg, this]
  · have hx : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hgap : ψ (n : ℝ) - θ (n : ℝ) ≤ 2 * Real.sqrt n * Real.log n :=
      le_trans (le_abs_self _) (abs_psi_sub_theta_le_sqrt_mul_log hx)
    have htheta := theta_tight (n : ℝ) (by positivity)
    linarith [hgap, htheta]

end CollatzChebyshev30
