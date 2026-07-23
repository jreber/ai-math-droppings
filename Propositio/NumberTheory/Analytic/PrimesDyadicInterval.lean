import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Propositio.NumberTheory.Analytic.ChebyshevPrimeCountingLower
import Propositio.NumberTheory.Analytic.ChebyshevPrimeCountingUpper

/-!
# Primes in a wide dilation interval: a quantitative interval lower bound

We derive, from the project's two-sided Chebyshev estimates for the prime-counting
function `π`, a quantitative lower bound on the number of primes in a *dilation
interval* `(x, K·x]`:

`π(K·x) − π(x) ≥ c · x / log x`  for all large `x`,

with explicit positive `c` and a fixed dilation factor `K > 1`.

## Why a *wide* interval, not a *dyadic* one

The requested target was the dyadic count `π(2x) − π(x) ≥ c·x/log x`.  Combining the
project's lower estimate `π(2x) ≥ c_lo·(2x)/log(2x)` with the upper estimate
`π(x) ≤ c_hi·x/log x` gives a leading coefficient `2·c_lo − c_hi`.  The *recorded*
project constants are

* `c_lo = (Real.log 2)/128 ≈ 0.0054`
  (`ChebyshevPrimeCountingLower.chebyshev_primeCounting_ge`, the θ-lower constant
  `c_psi/2 = (log 2/64)/2`), and
* `c_hi = 2·Real.log 4 + 1 = 4·Real.log 2 + 1 ≈ 3.77`
  (`ChebyshevPrimeCountingUpper.chebyshev_primeCounting_le`).

So `2·c_lo − c_hi ≈ 0.011 − 3.77 < 0`: with these (admissible but very loose)
constants the **dyadic margin does NOT close** — the subtract-the-bounds mechanism
yields a *negative* leading coefficient and hence no positive `c` at `K = 2`.
Sharpening it would require reproving Chebyshev with tighter constants, which is out
of scope here.

What *does* close honestly is a wider interval.  Doubling `x` multiplies the lower
bound by `≈ 2`; dilating by `K` multiplies it by `≈ K`.  Choosing `K` large enough
that `c_lo·K/2 > c_hi` (concretely `K = 4·c_hi/c_lo + 2`) makes the margin positive.
We use `log(K·x) ≤ 2·log x` for `x ≥ K` (since `log K ≤ log x`), so
`π(K·x) ≥ c_lo·K·x/log(K·x) ≥ (c_lo·K/2)·x/log x`, and the difference with the upper
bound `π(x) ≤ c_hi·x/log x` has leading coefficient `c_lo·K/2 − c_hi = c_hi + c_lo > 0`.

## Main result

* `PrimesDyadicInterval.primes_dilation_interval_lower` :
  `∃ K > 1, ∃ c > 0, ∃ x₀, ∀ x ≥ x₀, c·x/log x ≤ π(⌊K·x⌋) − π(⌊x⌋)`.
-/

open Real

namespace PrimesDyadicInterval

/-- **Quantitative primes in a dilation interval.**  There is a fixed dilation factor
`K > 1`, an explicit positive constant `c`, and a threshold `x₀` such that for all
`x ≥ x₀` the dilation interval `(x, K·x]` contains at least `c·x/log x` primes:

`c·x / log x ≤ π(⌊K·x⌋) − π(⌊x⌋)`.

This is derived purely from the project's two-sided Chebyshev bounds
`ChebyshevPrimeCountingLower.chebyshev_primeCounting_ge` and
`ChebyshevPrimeCountingUpper.chebyshev_primeCounting_le`.  See the file header for why
the recorded constants force a *wide* interval rather than the dyadic `K = 2`. -/
theorem primes_dilation_interval_lower :
    ∃ K : ℝ, 1 < K ∧ ∃ c : ℝ, 0 < c ∧ ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
      c * x / Real.log x ≤
        (Nat.primeCounting ⌊K * x⌋₊ : ℝ) - (Nat.primeCounting ⌊x⌋₊ : ℝ) := by
  obtain ⟨c_lo, hc_lo_pos, xL, hL⟩ := ChebyshevPrimeCountingLower.chebyshev_primeCounting_ge
  obtain ⟨c_hi, hc_hi_pos, xU, hU⟩ := ChebyshevPrimeCountingUpper.chebyshev_primeCounting_le
  set K : ℝ := 4 * c_hi / c_lo + 2 with hK_def
  set c : ℝ := c_hi + c_lo with hc_def
  -- `K > 2 > 1`
  have hKpos : 0 < K := by rw [hK_def]; positivity
  have hK1 : 1 < K := by
    rw [hK_def]
    have : 0 < 4 * c_hi / c_lo := by positivity
    linarith
  have hK1le : (1 : ℝ) ≤ K := le_of_lt hK1
  -- `c > 0`
  have hcpos : 0 < c := by rw [hc_def]; linarith
  -- `c_lo · K = 4·c_hi + 2·c_lo`
  have hcK : c_lo * K = 4 * c_hi + 2 * c_lo := by
    rw [hK_def]; field_simp
  refine ⟨K, hK1, c, hcpos, max (max xL xU) (max K 2), ?_⟩
  intro x hx
  -- unpack the threshold
  have hxL : xL ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hxU : xU ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hxK : K ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hx2 : (2 : ℝ) ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  have hxpos : 0 < x := by linarith
  have hxnn : (0 : ℝ) ≤ x := le_of_lt hxpos
  -- `K·x ≥ x ≥ xL`, so the lower bound applies at `K·x`.
  have hx_le_Kx : x ≤ K * x := le_mul_of_one_le_left hxnn hK1le
  have hKxL : xL ≤ K * x := le_trans hxL hx_le_Kx
  -- logs
  have hLpos : 0 < Real.log x := Real.log_pos (by linarith)
  have hKxne : K * x ≠ 0 := by positivity
  have hKne : K ≠ 0 := ne_of_gt hKpos
  have hxne : x ≠ 0 := ne_of_gt hxpos
  have hlogKx : Real.log (K * x) = Real.log K + Real.log x := Real.log_mul hKne hxne
  have hlogK_nonneg : 0 ≤ Real.log K := Real.log_nonneg hK1le
  have hlogK_le : Real.log K ≤ Real.log x := Real.log_le_log hKpos hxK
  -- `0 < log(K·x) ≤ 2·log x`
  have hLkpos : 0 < Real.log (K * x) := by rw [hlogKx]; linarith
  have hLk2L : Real.log (K * x) ≤ 2 * Real.log x := by rw [hlogKx]; linarith
  -- abbreviations for the two prime counts
  set A : ℝ := (Nat.primeCounting ⌊K * x⌋₊ : ℝ) with hA_def
  set B : ℝ := (Nat.primeCounting ⌊x⌋₊ : ℝ) with hB_def
  have hAnn : 0 ≤ A := Nat.cast_nonneg _
  -- lower bound at `K·x`, cleared of denominator
  have hLapp : c_lo * (K * x) / Real.log (K * x) ≤ A := hL (K * x) hKxL
  have hA : c_lo * (K * x) ≤ A * Real.log (K * x) := (div_le_iff₀ hLkpos).mp hLapp
  -- upper bound at `x`, cleared of denominator
  have hUapp : B ≤ c_hi * x / Real.log x := hU x hxU
  have hB : B * Real.log x ≤ c_hi * x := (le_div_iff₀ hLpos).mp hUapp
  -- `A · log(K·x) ≤ A · (2 log x) = 2 (A log x)`
  have hmul : A * Real.log (K * x) ≤ A * (2 * Real.log x) :=
    mul_le_mul_of_nonneg_left hLk2L hAnn
  have hAL2 : c_lo * (K * x) ≤ 2 * (A * Real.log x) := by nlinarith [hA, hmul]
  -- `c_lo · (K·x) = (4·c_hi + 2·c_lo)·x`
  have hcKx : c_lo * (K * x) = (4 * c_hi + 2 * c_lo) * x := by
    rw [← mul_assoc, hcK]
  -- assemble, after clearing the goal's denominator
  rw [div_le_iff₀ hLpos]
  -- goal: `c * x ≤ (A - B) * log x`
  rw [hc_def]
  nlinarith [hAL2, hB, hcKx]

end PrimesDyadicInterval
