import Mathlib.Analysis.Asymptotics.Theta
import Mathlib.NumberTheory.PrimeCounting
import Propositio.NumberTheory.Analytic.ChebyshevPrimeCountingLower
import Propositio.NumberTheory.Analytic.ChebyshevPrimeCountingUpper

/-!
# Chebyshev's theorem in asymptotic form: `π(x) = Θ(x / log x)`

Combining the two-sided Chebyshev estimates for the prime-counting function `π`,

* `ChebyshevPrimeCountingLower.chebyshev_primeCounting_ge` : `c·x/log x ≤ π(⌊x⌋)` (large `x`),
* `ChebyshevPrimeCountingUpper.chebyshev_primeCounting_le` : `π(⌊x⌋) ≤ C·x/log x` (large `x`),

we obtain the order-of-magnitude statement (Chebyshev's theorem):

`π(⌊x⌋) =Θ[atTop] x / log x`.

mathlib lacks the full Prime Number Theorem, so this asymptotic capstone is a genuine gap.

## Main result

* `ChebyshevPrimeCountingTheta.chebyshev_primeCounting_isTheta` :
  `Asymptotics.IsTheta Filter.atTop (fun x => (π ⌊x⌋ : ℝ)) (fun x => x / log x)`.
-/

open Asymptotics Filter

namespace ChebyshevPrimeCountingTheta

/-- `π(⌊x⌋) = O(x / log x)` as `x → ∞` (Chebyshev's upper estimate, asymptotic form). -/
theorem primeCounting_isBigO :
    (fun x : ℝ => (Nat.primeCounting ⌊x⌋₊ : ℝ)) =O[atTop] (fun x : ℝ => x / Real.log x) := by
  obtain ⟨C, hCpos, x₀, hC⟩ := ChebyshevPrimeCountingUpper.chebyshev_primeCounting_le
  rw [Asymptotics.isBigO_iff]
  refine ⟨C, ?_⟩
  filter_upwards [eventually_ge_atTop (max x₀ 2)] with x hx
  have hx0 : x₀ ≤ x := le_trans (le_max_left _ _) hx
  have hx2 : 2 ≤ x := le_trans (le_max_right _ _) hx
  have hxpos : 0 < x := by linarith
  have hlogpos : 0 < Real.log x := Real.log_pos (by linarith)
  have hgpos : 0 ≤ x / Real.log x := le_of_lt (div_pos hxpos hlogpos)
  have hbound : (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤ C * (x / Real.log x) := by
    have := hC x hx0
    rwa [mul_div_assoc] at this
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg hgpos]
  exact hbound

/-- `x / log x = O(π(⌊x⌋))` as `x → ∞` (Chebyshev's lower estimate, asymptotic form). -/
theorem isBigO_primeCounting :
    (fun x : ℝ => x / Real.log x) =O[atTop] (fun x : ℝ => (Nat.primeCounting ⌊x⌋₊ : ℝ)) := by
  obtain ⟨c, hcpos, x₀, hc⟩ := ChebyshevPrimeCountingLower.chebyshev_primeCounting_ge
  rw [Asymptotics.isBigO_iff]
  refine ⟨1 / c, ?_⟩
  filter_upwards [eventually_ge_atTop (max x₀ 2)] with x hx
  have hx0 : x₀ ≤ x := le_trans (le_max_left _ _) hx
  have hx2 : 2 ≤ x := le_trans (le_max_right _ _) hx
  have hxpos : 0 < x := by linarith
  have hlogpos : 0 < Real.log x := Real.log_pos (by linarith)
  have hgpos : 0 ≤ x / Real.log x := le_of_lt (div_pos hxpos hlogpos)
  -- `c · (x/log x) ≤ π(⌊x⌋)`, hence `x/log x ≤ (1/c) · π(⌊x⌋)`.
  have hlow : c * (x / Real.log x) ≤ (Nat.primeCounting ⌊x⌋₊ : ℝ) := by
    have := hc x hx0
    rwa [mul_div_assoc] at this
  have hbound : x / Real.log x ≤ (1 / c) * (Nat.primeCounting ⌊x⌋₊ : ℝ) := by
    rw [one_div_mul_eq_div, le_div_iff₀ hcpos]
    nlinarith [hlow]
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg hgpos, abs_of_nonneg (Nat.cast_nonneg _)]
  exact hbound

/-- **Chebyshev's theorem (asymptotic form).**
The prime-counting function has the order of magnitude `x / log x`:
`π(⌊x⌋) =Θ[atTop] x / log x`. -/
theorem chebyshev_primeCounting_isTheta :
    Asymptotics.IsTheta Filter.atTop
      (fun x : ℝ => (Nat.primeCounting ⌊x⌋₊ : ℝ))
      (fun x : ℝ => x / Real.log x) :=
  ⟨primeCounting_isBigO, isBigO_primeCounting⟩

end ChebyshevPrimeCountingTheta
