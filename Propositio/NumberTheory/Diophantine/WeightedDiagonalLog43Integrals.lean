import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

namespace WeightedDiagonalLog43Integrals
open intervalIntegral

/-- `∫₀¹ (1+x)⁻¹ dx = log 2`.  Shift by `1` to `∫₁² x⁻¹ = log 2`. -/
theorem integral_one_add_inv : (∫ x in (0:ℝ)..1, (1 + x)⁻¹) = Real.log 2 := by
  have hshift : (∫ x in (0:ℝ)..1, (1 + x)⁻¹) = ∫ x in (0:ℝ)..1, (x + 1)⁻¹ := by
    simp_rw [add_comm]
  rw [hshift, intervalIntegral.integral_comp_add_right (fun x => x⁻¹) 1,
    integral_inv_of_pos (by norm_num) (by norm_num)]
  norm_num

/-- `∫₀¹ (2+x)⁻¹ dx = log(3/2)`.  Shift by `2` to `∫₂³ x⁻¹ = log 3 − log 2`. -/
theorem integral_two_add_inv : (∫ x in (0:ℝ)..1, (2 + x)⁻¹) = Real.log (3/2) := by
  have hshift : (∫ x in (0:ℝ)..1, (2 + x)⁻¹) = ∫ x in (0:ℝ)..1, (x + 2)⁻¹ := by
    simp_rw [add_comm]
  rw [hshift, intervalIntegral.integral_comp_add_right (fun x => x⁻¹) 2,
    integral_inv_of_pos (by norm_num) (by norm_num)]
  norm_num

/-- for `i ≥ 1`: `∫₀¹ ((1+x)^(i+1))⁻¹ dx = (1 − (2^i)⁻¹)/i`. -/
theorem integral_one_add_pow_inv (i : ℕ) (hi : 1 ≤ i) :
    (∫ x in (0:ℝ)..1, ((1 + x)^(i+1))⁻¹) = (1 - ((2:ℝ)^i)⁻¹)/(i:ℝ) := by
  have hi0 : (i : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  -- rewrite the integrand as a zpow of `(1 + x)`
  have hint : (∫ x in (0:ℝ)..1, ((1 + x)^(i+1))⁻¹)
      = ∫ x in (0:ℝ)..1, ((1 + x))^(-(i+1 : ℤ)) := by
    refine intervalIntegral.integral_congr ?_
    intro x hx
    simp only []
    rw [show (-(i+1 : ℤ)) = -((i+1 : ℕ) : ℤ) by push_cast; ring,
      zpow_neg, zpow_natCast]
  rw [hint]
  -- shift by 1
  have hshift : (∫ x in (0:ℝ)..1, ((1 + x))^(-(i+1 : ℤ)))
      = ∫ x in (0:ℝ)..1, ((x + 1))^(-(i+1 : ℤ)) := by
    simp_rw [add_comm]
  rw [hshift, intervalIntegral.integral_comp_add_right (fun x => x ^ (-(i+1 : ℤ))) 1]
  -- now ∫₁² t^(-(i+1))
  rw [integral_zpow (Or.inr ⟨(by omega : -(i+1 : ℤ) ≠ -1), by
    norm_num [Set.mem_uIcc]⟩)]
  have hexp : -(i+1 : ℤ) + 1 = -(i : ℤ) := by ring
  rw [hexp]
  norm_num
  -- (2^(-i) - 1^(-i))/(-i) = (1 - (2^i)⁻¹)/i
  field_simp
  ring

/-- for `i ≥ 1`: `∫₀¹ ((2+x)^(i+1))⁻¹ dx = ((2^i)⁻¹ − (3^i)⁻¹)/i`. -/
theorem integral_two_add_pow_inv (i : ℕ) (hi : 1 ≤ i) :
    (∫ x in (0:ℝ)..1, ((2 + x)^(i+1))⁻¹) = (((2:ℝ)^i)⁻¹ - ((3:ℝ)^i)⁻¹)/(i:ℝ) := by
  have hi0 : (i : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hint : (∫ x in (0:ℝ)..1, ((2 + x)^(i+1))⁻¹)
      = ∫ x in (0:ℝ)..1, ((2 + x))^(-(i+1 : ℤ)) := by
    refine intervalIntegral.integral_congr ?_
    intro x hx
    simp only []
    rw [show (-(i+1 : ℤ)) = -((i+1 : ℕ) : ℤ) by push_cast; ring,
      zpow_neg, zpow_natCast]
  rw [hint]
  have hshift : (∫ x in (0:ℝ)..1, ((2 + x))^(-(i+1 : ℤ)))
      = ∫ x in (0:ℝ)..1, ((x + 2))^(-(i+1 : ℤ)) := by
    simp_rw [add_comm]
  rw [hshift, intervalIntegral.integral_comp_add_right (fun x => x ^ (-(i+1 : ℤ))) 2]
  rw [integral_zpow (Or.inr ⟨(by omega : -(i+1 : ℤ) ≠ -1), by
    norm_num [Set.mem_uIcc]⟩)]
  have hexp : -(i+1 : ℤ) + 1 = -(i : ℤ) := by ring
  rw [hexp]
  norm_num
  field_simp
  ring

end WeightedDiagonalLog43Integrals
