import Propositio.NumberTheory.Analytic.ChebyshevThetaLower
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.Asymptotics.Theta

/-!
# Chebyshev's functions have linear order: `θ(x) = Θ(x)` and `ψ(x) = Θ(x)`

The two Chebyshev functions `θ` and `ψ` grow linearly.  Combining

* the mathlib *upper* bounds
  `Chebyshev.theta_le_log4_mul_x : θ x ≤ log 4 · x` and
  `Chebyshev.psi_le_const_mul_self : ψ x ≤ (log 4 + 4) · x`, with
* the *lower* bounds proved in `ChebyshevThetaLower`
  (`chebyshev_theta_ge`, `chebyshev_psi_ge`),

we obtain Chebyshev's estimate in order-of-magnitude form:

`θ(x) =Θ[atTop] x`  and  `ψ(x) =Θ[atTop] x`.

## Main results

* `ChebyshevPsiThetaTheta.chebyshev_theta_isTheta` : `θ =Θ[atTop] id`.
* `ChebyshevPsiThetaTheta.chebyshev_psi_isTheta`  : `ψ =Θ[atTop] id`.
-/

open Asymptotics Filter

namespace ChebyshevPsiThetaTheta

/-- `θ(x) = O(x)` as `x → ∞` (Chebyshev's upper estimate for `θ`). -/
theorem theta_isBigO :
    (fun x : ℝ => Chebyshev.theta x) =O[atTop] (fun x : ℝ => x) := by
  rw [Asymptotics.isBigO_iff]
  refine ⟨Real.log 4, ?_⟩
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (Chebyshev.theta_nonneg x), abs_of_nonneg hx]
  exact Chebyshev.theta_le_log4_mul_x hx

/-- `x = O(θ(x))` as `x → ∞` (Chebyshev's lower estimate for `θ`). -/
theorem isBigO_theta :
    (fun x : ℝ => x) =O[atTop] (fun x : ℝ => Chebyshev.theta x) := by
  obtain ⟨c, hcpos, x₀, hc⟩ := ChebyshevThetaLower.chebyshev_theta_ge
  rw [Asymptotics.isBigO_iff]
  refine ⟨1 / c, ?_⟩
  filter_upwards [eventually_ge_atTop (max x₀ 0)] with x hx
  have hx0 : x₀ ≤ x := le_trans (le_max_left _ _) hx
  have hxnn : 0 ≤ x := le_trans (le_max_right _ _) hx
  have hlow : c * x ≤ Chebyshev.theta x := hc x hx0
  have hbound : x ≤ (1 / c) * Chebyshev.theta x := by
    rw [one_div_mul_eq_div, le_div_iff₀ hcpos]
    nlinarith [hlow]
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg hxnn, abs_of_nonneg (Chebyshev.theta_nonneg x)]
  exact hbound

/-- **Chebyshev's estimate for `θ` (order-of-magnitude form).**
The first Chebyshev function has linear order: `θ(x) =Θ[atTop] x`. -/
theorem chebyshev_theta_isTheta :
    Asymptotics.IsTheta Filter.atTop (fun x : ℝ => Chebyshev.theta x) (fun x : ℝ => x) :=
  ⟨theta_isBigO, isBigO_theta⟩

/-- `ψ(x) = O(x)` as `x → ∞` (Chebyshev's upper estimate for `ψ`). -/
theorem psi_isBigO :
    (fun x : ℝ => Chebyshev.psi x) =O[atTop] (fun x : ℝ => x) := by
  rw [Asymptotics.isBigO_iff]
  refine ⟨Real.log 4 + 4, ?_⟩
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (Chebyshev.psi_nonneg x), abs_of_nonneg hx]
  exact Chebyshev.psi_le_const_mul_self hx

/-- `x = O(ψ(x))` as `x → ∞` (Chebyshev's lower estimate for `ψ`). -/
theorem isBigO_psi :
    (fun x : ℝ => x) =O[atTop] (fun x : ℝ => Chebyshev.psi x) := by
  obtain ⟨c, hcpos, hc⟩ := ChebyshevThetaLower.chebyshev_psi_ge
  rw [Asymptotics.isBigO_iff]
  refine ⟨1 / c, ?_⟩
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
  have hxnn : 0 ≤ x := by linarith
  have hlow : c * x ≤ Chebyshev.psi x := hc x hx
  have hbound : x ≤ (1 / c) * Chebyshev.psi x := by
    rw [one_div_mul_eq_div, le_div_iff₀ hcpos]
    nlinarith [hlow]
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg hxnn, abs_of_nonneg (Chebyshev.psi_nonneg x)]
  exact hbound

/-- **Chebyshev's estimate for `ψ` (order-of-magnitude form).**
The second Chebyshev function has linear order: `ψ(x) =Θ[atTop] x`. -/
theorem chebyshev_psi_isTheta :
    Asymptotics.IsTheta Filter.atTop (fun x : ℝ => Chebyshev.psi x) (fun x : ℝ => x) :=
  ⟨psi_isBigO, isBigO_psi⟩

end ChebyshevPsiThetaTheta
