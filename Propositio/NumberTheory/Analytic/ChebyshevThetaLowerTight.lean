import Propositio.NumberTheory.Analytic.ChebyshevThetaLower
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# A tighter Chebyshev `θ`-lower bound

`ChebyshevThetaLower.chebyshev_theta_ge` packages a single constant `c = (log 2)/128 ≈ 0.0054`
valid uniformly from a fixed formula (halving twice: once to get a `ψ`-bound uniform down to
`x = 2`, once more to absorb the `ψ ↔ θ` gap).  That double-halving is what makes the constant
so small.

The raw elementary bound `ChebyshevThetaLower.psi_ge_real`,
`(x - 2)·log 2 - log x ≤ ψ x`, already has asymptotic slope `log 2 ≈ 0.693147`, and the `ψ ↔ θ`
gap `|ψ x - θ x| ≤ 2·√x·log x` is `o(x)`.  This file re-derives a `θ`-lower bound *without*
discarding that asymptotic slope: for the concrete target `c = 0.65 < log 2` there is an
explicit threshold `x₀` with `c·x ≤ θ x` for all `x ≥ x₀`.

This directly unblocks the recorded gap in `conj-2026-06-28-prime-dyadic-interval-count`
(`docs/kb/failed/2026-06-29__...json`): the recorded `θ`-lower constant `log 2/128 ≈ 0.0054`
was far too small to beat half of any reasonable `θ`-upper constant.  `0.65` clears it easily.

## Main result

* `ChebyshevThetaLowerTight.theta_ge_065` : `∃ x₀, ∀ x ≥ x₀, 0.65·x ≤ θ x`.
-/

open Chebyshev Real

namespace ChebyshevThetaLowerTight

/-- **Tight `θ`-lower bound at `c = 0.65`.**  Threshold `x₀ = 800⁴`. -/
theorem theta_ge_065 :
    ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → (13 / 20 : ℝ) * x ≤ θ x := by
  refine ⟨(800 : ℝ) ^ 4, ?_⟩
  intro x hx
  have hx0eq : (800 : ℝ) ^ 4 = 409600000000 := by norm_num
  have hxbig : (409600000000 : ℝ) ≤ x := hx0eq ▸ hx
  have hxpos : 0 < x := by linarith
  have hx2 : (2 : ℝ) ≤ x := by linarith
  have hx1 : (1 : ℝ) ≤ x := by linarith
  -- ψ lower bound
  have hpsi := ChebyshevThetaLower.psi_ge_real x hx2
  -- ψ ↔ θ gap
  have habs := Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log hx1
  have hgap : ψ x - 2 * Real.sqrt x * Real.log x ≤ θ x := by
    have h := (abs_le.mp habs).2; linarith
  -- s = x^{1/4}
  set s := Real.sqrt (Real.sqrt x) with hs_def
  have hs_nn : 0 ≤ s := Real.sqrt_nonneg _
  have hss : s * s = Real.sqrt x := Real.mul_self_sqrt (Real.sqrt_nonneg x)
  have hxx : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hxpos.le
  have hs4 : s ^ 4 = x := by
    have heq : s ^ 4 = (s * s) * (s * s) := by ring
    rw [heq, hss, hxx]
  -- s ≥ 800
  have hval800 : Real.sqrt (Real.sqrt (((800 : ℝ)) ^ 4)) = 800 := by
    rw [show ((800 : ℝ) ^ 4) = (800 ^ 2) ^ 2 by ring, Real.sqrt_sq (by norm_num),
        Real.sqrt_sq (by norm_num)]
  have hs_ge : (800 : ℝ) ≤ s := by
    rw [hs_def, ← hval800]
    exact Real.sqrt_le_sqrt (Real.sqrt_le_sqrt hx)
  -- log x ≤ 4 s
  have hlogx4 : Real.log x ≤ 4 * s := by
    have hsx_pos : 0 < Real.sqrt x := Real.sqrt_pos.mpr hxpos
    have hlogsqrt : Real.log (Real.sqrt x) ≤ 2 * Real.sqrt (Real.sqrt x) :=
      ChebyshevThetaLower.log_le_two_sqrt hsx_pos
    have heq2 : Real.log (Real.sqrt x) = Real.log x / 2 := Real.log_sqrt hxpos.le
    rw [heq2] at hlogsqrt; rw [← hs_def] at hlogsqrt; linarith
  -- error term: 2 √x log x ≤ 8 s³
  have herr : 2 * Real.sqrt x * Real.log x ≤ 8 * s ^ 3 := by
    rw [← hss]
    calc 2 * (s * s) * Real.log x ≤ 2 * (s * s) * (4 * s) :=
          mul_le_mul_of_nonneg_left hlogx4 (by positivity)
      _ = 8 * s ^ 3 := by ring
  -- numeric bounds on log 2
  have hlog2_gt : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hlog2_lt : Real.log 2 < (0.6931471808 : ℝ) := Real.log_two_lt_d9
  -- piece A: 8 s³ ≤ (43/2000) s⁴  (needs s ≥ 16/(43/1000) ≈ 372, holds since s ≥ 800)
  have hpieceA : 8 * s ^ 3 ≤ (43 / 2000 : ℝ) * s ^ 4 := by
    have hs3nn : (0:ℝ) ≤ s ^ 3 := by positivity
    nlinarith [hs_ge, hs3nn]
  -- piece B: 2 log 2 + 4 s ≤ (43/2000) s⁴  (trivial at s ≥ 800)
  have hpieceB : 2 * Real.log 2 + 4 * s ≤ (43 / 2000 : ℝ) * s ^ 4 := by
    nlinarith [hs_ge, hlog2_lt]
  -- chain: θ x ≥ (x-2) log 2 - log x - 8 s³ ≥ (x-2) log 2 - 4s - 8s³
  have h1 : (x - 2) * Real.log 2 - Real.log x - 8 * s ^ 3 ≤ θ x := by
    linarith [hpsi, herr, hgap]
  have h4 : (x - 2) * Real.log 2 - 4 * s - 8 * s ^ 3 ≤ θ x := by
    linarith [h1, hlogx4]
  have hring : (x - 2) * Real.log 2 = x * Real.log 2 - 2 * Real.log 2 := by ring
  have h5 : x * Real.log 2 - (43 / 1000 : ℝ) * s ^ 4 ≤ θ x := by
    linarith [h4, hring, hpieceA, hpieceB]
  rw [hs4] at h5
  -- final: x·(log 2 - 43/1000) ≥ x·0.65
  have hcoef : (0 : ℝ) ≤ Real.log 2 - 43 / 1000 - 13 / 20 := by linarith [hlog2_gt]
  have hprod : (0 : ℝ) ≤ (Real.log 2 - 43 / 1000 - 13 / 20) * x := mul_nonneg hcoef hxpos.le
  nlinarith [h5, hprod]

end ChebyshevThetaLowerTight
