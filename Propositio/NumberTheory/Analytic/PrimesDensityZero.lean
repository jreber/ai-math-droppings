import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Propositio.NumberTheory.Analytic.ChebyshevPrimeCountingUpper

/-!
# The primes have natural density zero: `π(⌊x⌋)/x → 0`

This file records the clean analytic corollary of Chebyshev's upper bound
(`ChebyshevPrimeCountingUpper.chebyshev_primeCounting_le`): the prime-counting function `π`
grows slower than `x`, so the **natural density** of the primes is `0`,

`π(⌊x⌋) / x → 0`  as  `x → ∞`.

Note this is a genuinely different statement from mathlib's
`schnirelmannDensity (setOf Nat.Prime) = 0`, which concerns the *Schnirelmann* density.

## Proof

From Chebyshev's bound there is `C > 0` and `x₀` with `π(⌊x⌋) ≤ C·x / log x` for `x ≥ x₀`.
Dividing by `x > 0`, for large `x` we have `0 ≤ π(⌊x⌋)/x ≤ C / log x`, and `C / log x → 0`
because `log x → ∞`.  A squeeze finishes it.
-/

open Filter Topology

namespace PrimesDensityZero

/-- **The primes have natural density zero.**  `π(⌊x⌋)/x → 0` as `x → ∞`. -/
theorem primeCounting_div_atTop_tendsto_zero :
    Filter.Tendsto (fun x : ℝ => (Nat.primeCounting ⌊x⌋₊ : ℝ) / x) Filter.atTop (nhds 0) := by
  obtain ⟨C, _hC, x₀, hbound⟩ := ChebyshevPrimeCountingUpper.chebyshev_primeCounting_le
  -- The dominating function `C / log x → 0`, since `log x → ∞`.
  have htop : Tendsto (fun x : ℝ => C / Real.log x) atTop (nhds 0) :=
    Real.tendsto_log_atTop.const_div_atTop C
  -- Squeeze `π(⌊x⌋)/x` between `0` and `C / log x`, both of which tend to `0`.
  refine squeeze_zero' ?_ ?_ htop
  · -- Eventually `0 ≤ π(⌊x⌋)/x`: the numerator is a cast (≥ 0) and `x > 0`.
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact div_nonneg (Nat.cast_nonneg _) hx.le
  · -- Eventually `π(⌊x⌋)/x ≤ C / log x`: divide Chebyshev's bound by `x > 0`.
    filter_upwards [eventually_ge_atTop x₀, eventually_gt_atTop (1 : ℝ)] with x hx0 hx1
    have hxpos : 0 < x := by linarith
    have hlog : 0 < Real.log x := Real.log_pos hx1
    have hb := hbound x hx0
    -- `π ≤ C·x / log x  ⇒  π · log x ≤ C · x`.
    rw [le_div_iff₀ hlog] at hb
    -- `π/x ≤ C/log x  ⇔  π · log x ≤ C · x`.
    rw [div_le_div_iff₀ hxpos hlog]
    linarith [hb]

end PrimesDensityZero
