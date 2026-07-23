import Propositio.NumberTheory.Diophantine.LcmGrowthBound
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Analysis.Asymptotics.Lemmas

/-!
# Diagonal integral × lcm(1..n) · (3 − 2√2)ⁿ tends to 0

This file proves `lcm(1..n) · (3 − 2√2)ⁿ → 0` as `n → ∞`.

**Key bound:** `log(lcm(1..n)) = ψ(n) ≤ (log 4)·n + 2·√n·log n` (Chebyshev),
while `(3−2√2)ⁿ = exp(n·log(3−2√2))`, and `log(4·(3−2√2)) < 0` since `4·(3−2√2) < 1`.
So `log(lcm(1..n)·(3−2√2)ⁿ) ≤ L·n + 2·√n·log n → −∞` where `L = log(4·(3−2√2)) < 0`.
-/

open Filter Real Asymptotics LcmGrowthBound

namespace DiagonalIntegralLog2

/-! ## Arithmetic constants -/

private lemma sqrt2_sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)

private lemma sqrt2_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)

-- The base: c = 3 - 2√2
private lemma hc_pos : (0 : ℝ) < 3 - 2 * Real.sqrt 2 := by
  nlinarith [sqrt2_sq, sqrt2_pos]

private lemma hc_ne : (3 : ℝ) - 2 * Real.sqrt 2 ≠ 0 := ne_of_gt hc_pos

private lemma h4c_lt_one : 4 * (3 - 2 * Real.sqrt 2 : ℝ) < 1 := by
  nlinarith [sqrt2_sq, sqrt2_pos]

private lemma h4c_pos : (0 : ℝ) < 4 * (3 - 2 * Real.sqrt 2) := by
  nlinarith [hc_pos]

/-! ## Key negativity: log(4c) < 0 -/

-- L = log(4·(3-2√2)) < 0
private lemma hL_neg : Real.log (4 * (3 - 2 * Real.sqrt 2)) < 0 :=
  Real.log_neg h4c_pos h4c_lt_one

private lemma L_eq_sum :
    Real.log (4 * (3 - 2 * Real.sqrt 2)) = Real.log 4 + Real.log (3 - 2 * Real.sqrt 2) :=
  Real.log_mul (by norm_num : (4:ℝ) ≠ 0) hc_ne

/-! ## Auxiliary function h n = L·n + 2·√n·log n -/

private noncomputable def h (n : ℕ) : ℝ :=
  Real.log (4 * (3 - 2 * Real.sqrt 2)) * n + 2 * Real.sqrt n * Real.log n

/-! ## Step 1: h n → atBot via the eventual bound h n ≤ (L/2)·n -/

private lemma log_le_const_mul_sqrt : ∀ᶠ n : ℕ in atTop,
    Real.log n ≤ (-(Real.log (4 * (3 - 2 * Real.sqrt 2))) / 4) * Real.sqrt n := by
  set L := Real.log (4 * (3 - 2 * Real.sqrt 2))
  have hr : (0 : ℝ) < 1/2 := by norm_num
  have hε : 0 < -L / 4 := by linarith [hL_neg]
  -- log =o[atTop] (· ^ (1/2)) over ℕ
  have hiso : (fun n : ℕ => Real.log n) =o[atTop] (fun n : ℕ => (n : ℝ) ^ ((1:ℝ)/2)) :=
    (isLittleO_log_rpow_atTop hr).natCast_atTop
  -- Extract the eventual ‖log n‖ ≤ (-L/4) * ‖n^(1/2)‖ bound
  have hbigO : ∀ᶠ n : ℕ in atTop, ‖Real.log n‖ ≤ (-L / 4) * ‖(n : ℝ) ^ ((1:ℝ)/2)‖ :=
    hiso.def hε
  filter_upwards [hbigO, eventually_ge_atTop 0] with n hle hn0
  have h_norm_rpow : ‖(n : ℝ) ^ ((1:ℝ)/2)‖ = Real.sqrt n := by
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)]
    rw [Real.sqrt_eq_rpow]
  calc Real.log n
      ≤ ‖Real.log n‖ := le_abs_self _
    _ ≤ -L / 4 * ‖(n : ℝ) ^ ((1:ℝ)/2)‖ := hle
    _ = -L / 4 * Real.sqrt n := by rw [h_norm_rpow]

private lemma h_le_half_L_mul_n : ∀ᶠ n : ℕ in atTop,
    h n ≤ (Real.log (4 * (3 - 2 * Real.sqrt 2)) / 2) * n := by
  set L := Real.log (4 * (3 - 2 * Real.sqrt 2)) with hL_def
  filter_upwards [log_le_const_mul_sqrt, eventually_ge_atTop 1] with n hlog hn1
  simp only [h]
  have hsqrt_nn : 0 ≤ Real.sqrt n := Real.sqrt_nonneg n
  have hlognn : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn1)
  have hsq : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt (by exact_mod_cast Nat.zero_le n)
  nlinarith [hlog, hsqrt_nn, hlognn, hL_neg]

private lemma h_tendsto_atBot : Tendsto h atTop atBot := by
  set L := Real.log (4 * (3 - 2 * Real.sqrt 2)) with hL_def
  have hL2 : L / 2 < 0 := by linarith [hL_neg]
  have upper : Tendsto (fun n : ℕ => (L / 2) * (n : ℝ)) atTop atBot := by
    rw [tendsto_const_mul_atBot_of_neg hL2]
    exact tendsto_natCast_atTop_atTop
  exact tendsto_atBot_mono' atTop h_le_half_L_mul_n upper

/-! ## Step 2: lcmUpto n · cⁿ ≤ exp(h n) eventually -/

private lemma lcm_mul_pow_le_exp_h :
    ∀ᶠ n : ℕ in atTop,
      (lcmUpto n : ℝ) * (3 - 2 * Real.sqrt 2) ^ n ≤ Real.exp (h n) := by
  set c := (3 : ℝ) - 2 * Real.sqrt 2 with hc_def
  filter_upwards [eventually_ge_atTop 1] with n hn1
  have hlcm_pos : (0 : ℝ) < lcmUpto n :=
    Nat.cast_pos.mpr (Nat.pos_of_ne_zero (lcmUpto_ne_zero n))
  have hcn_pos : 0 < c ^ n := pow_pos hc_pos n
  have hprod_pos : 0 < (lcmUpto n : ℝ) * c ^ n := mul_pos hlcm_pos hcn_pos
  -- Compute log of the product
  have hlog_prod : Real.log ((lcmUpto n : ℝ) * c ^ n) =
      Real.log (lcmUpto n) + n * Real.log c := by
    rw [Real.log_mul (ne_of_gt hlcm_pos) (ne_of_gt hcn_pos)]
    rw [Real.log_pow]
  -- Use Chebyshev bound: log(lcmUpto n) ≤ log 4 * n + 2 * √n * log n
  have hpsi_bound : Real.log (lcmUpto n) ≤ Real.log 4 * n + 2 * Real.sqrt n * Real.log n :=
    log_lcmUpto_le_sharp n hn1
  -- The log bound for the product
  have hlog_le : Real.log ((lcmUpto n : ℝ) * c ^ n) ≤ h n := by
    rw [hlog_prod]
    simp only [h]
    have heq : Real.log 4 * n + 2 * Real.sqrt n * Real.log n + n * Real.log c =
        Real.log (4 * (3 - 2 * Real.sqrt 2)) * n + 2 * Real.sqrt n * Real.log n := by
      rw [L_eq_sum]
      ring
    linarith
  exact (Real.log_le_iff_le_exp hprod_pos).mp hlog_le

/-! ## Step 3: Lower bound is 0 -/

private lemma prod_nonneg (n : ℕ) : (0 : ℝ) ≤ (lcmUpto n : ℝ) * (3 - 2 * Real.sqrt 2) ^ n :=
  mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hc_pos.le n)

/-! ## Main theorem -/

theorem geom_lcm_tendsto_zero :
    Tendsto (fun n : ℕ => (lcmUpto n : ℝ) * (3 - 2 * Real.sqrt 2) ^ n) atTop (nhds 0) := by
  -- exp(h n) → 0
  have hexp : Tendsto (fun n : ℕ => Real.exp (h n)) atTop (nhds 0) :=
    Real.tendsto_exp_atBot.comp h_tendsto_atBot
  -- Squeeze: 0 ≤ lcmUpto(n)·cⁿ ≤ exp(h n), exp(h n) → 0
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hexp
    (Eventually.of_forall prod_nonneg)
    lcm_mul_pow_le_exp_h

end DiagonalIntegralLog2
