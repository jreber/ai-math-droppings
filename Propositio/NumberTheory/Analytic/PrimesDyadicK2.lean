import Propositio.NumberTheory.Analytic.ChebyshevThetaLowerTight
import Propositio.NumberTheory.Analytic.ChebyshevPrimeCountingUpperTight
import Propositio.NumberTheory.Analytic.ChebyshevPrimeCountingLower
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The dyadic (K = 2) quantitative Bertrand gap, closed

`docs/kb/failed/2026-06-29__conj-2026-06-28-prime-dyadic-interval-count.json` records that the
`K = 2` dyadic Bertrand bound `π(2x) - π(x) ≥ c·x/log x` could **not** be closed by subtracting
this project's *original* two-sided Chebyshev `π`-bounds: the `θ`-lower constant
`log 2/128 ≈ 0.0054` was ~700× too small relative to the `θ`-upper constant `4 log 2 + 1 ≈ 3.77`
(needed `2·c_lo > c_hi`).

This file closes it by plugging in two tightened inputs built for this purpose:

* `ChebyshevThetaLowerTight.theta_ge_065` : `θ(x) ≥ 0.65·x` for large `x` (vs. the old `0.0054`),
  obtained by *not* discarding the asymptotic slope `log 2 ≈ 0.693` of the classical
  central-binomial argument.
* `ChebyshevPrimeCountingUpperTight.chebyshev_primeCounting_le_tight` : `π(x) ≤ 1.22·x/log x`
  (vs. the old `3.77·x/log x`), obtained by splitting `θ` at `y = x/(log x)²` instead of `√x`,
  which removes the factor-of-`≈2` loss of the `√x`-split method, combined with this project's
  *tight* `θ`-upper bound (`CollatzChebyshev30.theta_tight`, slope `1.15`).

With these, `2 · 0.65 = 1.3 > 1.22`, and the identical "subtract the bounds" mechanism from
`PrimesDyadicInterval` closes `K = 2` with a comfortable margin (using additionally
`log(2x) ≤ 1.01 · log x` for `x` large, a *fixed*-`K` fact — unlike the general-`K` case,
`log 2` does not grow with `x`).

## Main result

* `PrimesDyadicK2.primes_dyadic_interval_lower` :
  `∃ c > 0, ∃ x₀, ∀ x ≥ x₀, c·x/log x ≤ π(⌊2x⌋) - π(⌊x⌋)`.
-/

open Chebyshev Real

namespace PrimesDyadicK2

/-- **The dyadic (`K = 2`) quantitative Bertrand bound.**  There is an explicit positive
constant `c = 1/20` and a threshold `x₀` such that for all `x ≥ x₀` the interval `(x, 2x]`
contains at least `c·x/log x` primes. -/
theorem primes_dyadic_interval_lower :
    ∃ c : ℝ, 0 < c ∧ ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
      c * x / Real.log x ≤ (Nat.primeCounting ⌊2 * x⌋₊ : ℝ) - (Nat.primeCounting ⌊x⌋₊ : ℝ) := by
  obtain ⟨xθ, hθ⟩ := ChebyshevThetaLowerTight.theta_ge_065
  obtain ⟨xπ, hπ⟩ := ChebyshevPrimeCountingUpperTight.chebyshev_primeCounting_le_tight
  refine ⟨1 / 20, by norm_num, max (max (2 * xθ) xπ) (Real.exp 70 + 1), ?_⟩
  intro x hx
  have hx2θ : 2 * xθ ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hxπ : xπ ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hxe : Real.exp 70 + 1 ≤ x := le_trans (le_max_right _ _) hx
  have hxpos : 0 < x := by
    have := Real.exp_pos 70
    linarith
  have hlogx_ge70 : (70 : ℝ) ≤ Real.log x := by
    have hle : Real.exp 70 ≤ x := by linarith
    have := Real.log_le_log (Real.exp_pos 70) hle
    rwa [Real.log_exp] at this
  have hlogxpos : 0 < Real.log x := by linarith
  -- θ-lower bound at 2x
  have h2xθ : xθ ≤ 2 * x := by linarith
  have hθ2x : (13 / 20 : ℝ) * (2 * x) ≤ Chebyshev.theta (2 * x) := hθ (2 * x) h2xθ
  -- θ ↔ π bridge at 2x
  have h2xpos : (0 : ℝ) < 2 * x := by linarith
  have hbridge2x := ChebyshevPrimeCountingLower.theta_le_primeCounting_mul_log h2xpos
  -- log(2x) ≤ (101/100) log x
  have hlog2 : Real.log 2 < (0.6931471808 : ℝ) := Real.log_two_lt_d9
  have hlog2x : Real.log (2 * x) = Real.log 2 + Real.log x := Real.log_mul (by norm_num) hxpos.ne'
  have hlog2xle : Real.log (2 * x) ≤ (101 / 100 : ℝ) * Real.log x := by
    rw [hlog2x]; nlinarith [hlog2, hlogx_ge70]
  have hlog2xpos : 0 < Real.log (2 * x) := by rw [hlog2x]; nlinarith [Real.log_pos (by norm_num : (1:ℝ) < 2), hlogxpos]
  -- assemble the π(2x) lower bound: π(⌊2x⌋) ≥ (13/10) x / log(2x) ≥ (13/10) x / ((101/100) log x)
  set A : ℝ := (Nat.primeCounting ⌊2 * x⌋₊ : ℝ) with hA_def
  set B : ℝ := (Nat.primeCounting ⌊x⌋₊ : ℝ) with hB_def
  have hAnn : 0 ≤ A := Nat.cast_nonneg _
  have hA1 : (13 / 20 : ℝ) * (2 * x) ≤ A * Real.log (2 * x) := le_trans hθ2x hbridge2x
  have hA2 : A * Real.log (2 * x) ≤ A * ((101 / 100 : ℝ) * Real.log x) :=
    mul_le_mul_of_nonneg_left hlog2xle hAnn
  have hA3 : (13 / 20 : ℝ) * (2 * x) ≤ A * ((101 / 100 : ℝ) * Real.log x) := le_trans hA1 hA2
  -- π(x) upper bound
  have hBup : B ≤ (61 / 50 : ℝ) * x / Real.log x := hπ x hxπ
  have hB : B * Real.log x ≤ (61 / 50 : ℝ) * x := (le_div_iff₀ hlogxpos).mp hBup
  -- clear denominators in the goal and combine
  rw [div_le_iff₀ hlogxpos]
  -- goal : (1/20) * x * log x ≤ (A - B) * log x  -- no, goal is (1/20)*x ≤ (A-B)*log x after clearing
  nlinarith [hA3, hB, hlogxpos]

end PrimesDyadicK2
