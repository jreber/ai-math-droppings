import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Tactic

/-!
# The real Euler product for ζ(2)

`mathlib` provides the Euler product for the *complex* Riemann ζ function
(`riemannZeta_eulerProduct_hasProd`) and the real series value `hasSum_zeta_two`
(`∑ 1/n² = π²/6`), but not the *real* product statement.  This file proves

`∏_p (1 - p⁻²)⁻¹ = π²/6`

directly in `ℝ`, by applying the general completely-multiplicative Euler product
`EulerProduct.eulerProduct_completely_multiplicative_hasProd` to the real,
completely-multiplicative function `n ↦ n^(-2 : ℤ)`.
-/

open EulerProduct

namespace RealEulerProductZetaTwo

/-- The real, completely-multiplicative function `n ↦ n^(-2 : ℤ)` packaged as a
`MonoidWithZeroHom`, so that it can feed the general Euler product. -/
noncomputable def zetaTwoHom : ℕ →*₀ ℝ where
  toFun n := (n : ℝ) ^ (-2 : ℤ)
  map_zero' := by rw [Nat.cast_zero, zero_zpow (-2 : ℤ) (by norm_num)]
  map_one' := by simp
  map_mul' m n := by push_cast; rw [mul_zpow]

@[simp] lemma zetaTwoHom_apply (n : ℕ) : zetaTwoHom n = (n : ℝ) ^ (-2 : ℤ) := rfl

/-- Pointwise: `n^(-2 : ℤ) = 1 / n²`. -/
lemma zetaTwoHom_eq_one_div (n : ℕ) : zetaTwoHom n = 1 / (n : ℝ) ^ 2 := by
  rw [zetaTwoHom_apply, zpow_neg, one_div]
  norm_cast

/-- The norm of the summand is `1 / n²`, hence summable (this is `∑ 1/n²`). -/
lemma summable_norm_zetaTwoHom : Summable (fun n : ℕ => ‖zetaTwoHom n‖) := by
  refine hasSum_zeta_two.summable.congr (fun n => ?_)
  rw [zetaTwoHom_eq_one_div, Real.norm_eq_abs, abs_of_nonneg (by positivity)]

/-- The series of the summand is `π²/6`. -/
lemma tsum_zetaTwoHom : ∑' n : ℕ, zetaTwoHom n = Real.pi ^ 2 / 6 := by
  rw [tsum_congr zetaTwoHom_eq_one_div]
  exact hasSum_zeta_two.tsum_eq

end RealEulerProductZetaTwo

open RealEulerProductZetaTwo

/-- **The real Euler product for ζ(2).**
`∏_p (1 - p^(-2))⁻¹ = π²/6`, stated in terms of `HasProd`. -/
theorem real_euler_product_zeta_two :
    HasProd (fun p : Nat.Primes => (1 - ((p : ℝ)) ^ (-2 : ℤ))⁻¹) (Real.pi ^ 2 / 6) := by
  have key := eulerProduct_completely_multiplicative_hasProd summable_norm_zetaTwoHom
  rw [tsum_zetaTwoHom] at key
  convert key using 2 with p

/-- **The real Euler product for ζ(2)**, `tprod` form. -/
theorem real_euler_product_zeta_two_tprod :
    ∏' p : Nat.Primes, (1 - ((p : ℝ)) ^ (-2 : ℤ))⁻¹ = Real.pi ^ 2 / 6 :=
  real_euler_product_zeta_two.tprod_eq
