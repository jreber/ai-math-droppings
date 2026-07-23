import Propositio.Collatz.Chebyshev30LcmTight
import Propositio.Collatz.Chebyshev30Aentropy
import Propositio.NumberTheory.Diophantine.LcmGrowthBound
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.NumberTheory.Primorial

/-!
# Chebyshev-30 lcm pin, SHARP threshold via discrete slack-monotonicity

`CollatzChebyshev30LcmPin.lean` reduced the prize denominator target
`30·lcm(1..2n) ≤ 6·10ⁿ` to a finite census `n < 2·10⁷` by bounding every sub-exponential error
term crudely by a multiple of `√(2n)`.  That window is far too large for a census.

Here we shrink the window to a census-feasible `N0` by a *discrete telescoping* argument on the
analytic slack `D(n) = (n·log10 − log5) − [ (6A/5)(2n) + F(2n) + θ(30) + G(2n) ]`, where `F`, `G`
are the `o(n)` error terms of `log_lcmUpto_le_cheb30_tight`.  We show `D(n+1) − D(n) ≥ 0` for all
`n ≥ N0` (`slack_step`) — each error increment is `O(log(2n)/n)` and is dominated by the linear
budget `log10 − 12A/5 > 0.082` — together with the base case `D(N0) ≥ 0` (`slack_base`).
Telescoping then gives `D(n) ≥ 0` for all `n ≥ N0`, i.e. the real-log target, which we recover as
the Nat inequality exactly as in `CollatzChebyshev30LcmPin.lean`.
-/

namespace CollatzChebyshev30

open Chebyshev Real LcmGrowthBound

/-- **`θ(30) < 23`.**  `θ 30 = log(primorial 30) = log 6469693230 < 23` since
`6469693230 < 2.7²³ ≤ (exp 1)²³ = exp 23`. -/
theorem theta30_lt : theta 30 < 23 := by
  have heq : theta 30 = Real.log (primorial 30) := by
    rw [theta_eq_log_primorial]
    norm_num
  have hprim : primorial 30 = 6469693230 := by decide
  rw [heq, hprim]
  have hexp : (6469693230 : ℝ) < Real.exp 23 := by
    have h1 : (2.7 : ℝ) ≤ Real.exp 1 := le_of_lt (lt_trans (by norm_num) Real.exp_one_gt_d9)
    have h2 : Real.exp 23 = (Real.exp 1) ^ 23 := by
      rw [← Real.exp_nat_mul]; norm_num
    rw [h2]
    calc (6469693230 : ℝ) < (2.7 : ℝ) ^ 23 := by norm_num
      _ ≤ (Real.exp 1) ^ 23 := by gcongr
  rw [show (23 : ℝ) = Real.log (Real.exp 23) from (Real.log_exp 23).symm]
  exact Real.log_lt_log (by norm_num) hexp

#print axioms theta30_lt

/-! ## Generic analytic helpers -/

/-- If `x ≤ c^k` then `x^(1/k) ≤ c` (numeric `k`-th-root upper bound). -/
theorem rpow_inv_le {x c : ℝ} {k : ℕ} (hk : 0 < k) (hx : 0 ≤ x) (hc : 0 ≤ c)
    (h : x ≤ c ^ k) : x ^ ((1:ℝ)/k) ≤ c := by
  have hknn : (k:ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have hxk : (x ^ ((1:ℝ)/k)) ^ k = x := by
    rw [← Real.rpow_natCast (x ^ ((1:ℝ)/k)) k, ← Real.rpow_mul hx,
        one_div, inv_mul_cancel₀ hknn, Real.rpow_one]
  by_contra hcon
  push_neg at hcon
  have : c ^ k < (x ^ ((1:ℝ)/k)) ^ k := pow_lt_pow_left₀ hcon hc hk.ne'
  rw [hxk] at this; linarith

/-- **Concave-Bernoulli increment** (step of `2`).  For `x > 0` and `0 ≤ p ≤ 1`,
`(x+2)^p − x^p ≤ 2p·x^p / x`. -/
theorem bern_incr {x : ℝ} (hx : 0 < x) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (x + 2) ^ p - x ^ p ≤ 2 * p * x ^ p / x := by
  have hx0 : (0:ℝ) ≤ x := hx.le
  have hfac : x + 2 = x * (1 + 2 / x) := by field_simp
  have h1 : (x + 2) ^ p = x ^ p * (1 + 2 / x) ^ p := by
    rw [hfac, Real.mul_rpow hx0 (by positivity)]
  have hs : (-1:ℝ) ≤ 2 / x := by
    have h0 : (0:ℝ) ≤ 2 / x := by positivity
    linarith
  have hb : (1 + 2 / x) ^ p ≤ 1 + p * (2 / x) :=
    rpow_one_add_le_one_add_mul_self hs hp0 hp1
  have hnn : (0:ℝ) ≤ x ^ p := Real.rpow_nonneg hx0 _
  have hstep : (x + 2) ^ p ≤ x ^ p * (1 + p * (2 / x)) := by
    rw [h1]; exact mul_le_mul_of_nonneg_left hb hnn
  have hexp : x ^ p * (1 + p * (2 / x)) - x ^ p = 2 * p * x ^ p / x := by
    field_simp; ring
  linarith [hstep, hexp]

/-- **The ratio `(c·N)^β / N` is decreasing in `N`** for `0 ≤ β ≤ 1`. -/
theorem rpow_div_decr {c N N0 : ℝ} (hc : 0 ≤ c) (hN0 : 0 < N0) (hN : N0 ≤ N)
    {β : ℝ} (_hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) :
    (c * N) ^ β / N ≤ (c * N0) ^ β / N0 := by
  have hNpos : (0:ℝ) < N := lt_of_lt_of_le hN0 hN
  have e1 : (c * N) ^ β / N = c ^ β * N ^ (β - 1) := by
    rw [Real.mul_rpow hc hNpos.le, Real.rpow_sub hNpos, Real.rpow_one, mul_div_assoc]
  have e0 : (c * N0) ^ β / N0 = c ^ β * N0 ^ (β - 1) := by
    rw [Real.mul_rpow hc hN0.le, Real.rpow_sub hN0, Real.rpow_one, mul_div_assoc]
  rw [e1, e0]
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hc β)
  exact Real.rpow_le_rpow_of_nonpos hN0 hN (by linarith)

/-- **Log increment** (step of `2`).  `log(x+2) − log x ≤ 2/x` for `x > 0`. -/
theorem log_incr {x : ℝ} (hx : 0 < x) :
    Real.log (x + 2) - Real.log x ≤ 2 / x := by
  rw [← Real.log_div (by linarith) (by linarith)]
  have hratio : (x + 2) / x = 1 + 2 / x := by field_simp
  rw [hratio]
  have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 1 + 2 / x by positivity)
  linarith

/-- `log x ≤ 5·x^(1/5)` for `x ≥ 0`. -/
theorem log_le_5rpow {x : ℝ} (hx : 0 ≤ x) : Real.log x ≤ 5 * x ^ ((1:ℝ)/5) := by
  have h := Real.log_le_rpow_div hx (show (0:ℝ) < 1/5 by norm_num)
  have heq : x ^ ((1:ℝ)/5) / (1/5) = 5 * x ^ ((1:ℝ)/5) := by ring
  rw [heq] at h; exact h

/-! ## Numeric constants at the pin point `N0 = 8500` (`2N0 = 17000`, `4N0 = 34000`) -/

theorem r2N0_3 : (17000:ℝ) ^ ((1:ℝ)/3) ≤ 25.72 :=
  rpow_inv_le (by norm_num) (by norm_num) (by norm_num) (by norm_num)
theorem r2N0_4 : (17000:ℝ) ^ ((1:ℝ)/4) ≤ 11.42 :=
  rpow_inv_le (by norm_num) (by norm_num) (by norm_num) (by norm_num)
theorem r2N0_5 : (17000:ℝ) ^ ((1:ℝ)/5) ≤ 7.02 :=
  rpow_inv_le (by norm_num) (by norm_num) (by norm_num) (by norm_num)
theorem r4N0_5 : (34000:ℝ) ^ ((1:ℝ)/5) ≤ 8.07 :=
  rpow_inv_le (by norm_num) (by norm_num) (by norm_num) (by norm_num)
theorem r2N0_sqrt : Real.sqrt 17000 ≤ 130.4 := by
  rw [show (130.4:ℝ) = Real.sqrt (130.4 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
  exact Real.sqrt_le_sqrt (by norm_num)

/-- **Lower bound on `log(5/4)`** (mirror of `log_five_quarters_lt`, 8 Taylor terms). -/
theorem log_five_quarters_gt : (0.2231 : ℝ) < Real.log (5/4) := by
  have t : |((1:ℝ)/5)| = 1/5 := by rw [abs_of_pos]; norm_num
  have z := Real.abs_log_sub_add_sum_range_le (show |((1:ℝ)/5)| < 1 by rw [t]; norm_num) 8
  rw [t, abs_le] at z
  obtain ⟨_, z2⟩ := z
  have hsum : (0.2231 : ℝ) < (∑ i ∈ Finset.range 8, ((1:ℝ)/5)^(i+1)/((i:ℝ)+1))
      - (1/5:ℝ)^(8+1)/(1-(1:ℝ)/5) := by
    norm_num [Finset.sum_range_succ]
  have hlog : Real.log ((5:ℝ)/4) = - Real.log (1 - 1/5) := by
    rw [show (5:ℝ)/4 = (1 - 1/5)⁻¹ by norm_num, Real.log_inv]
  rw [hlog]; linarith [z2, hsum]

/-- `log 17000 ≤ 10` (since `17000 ≤ 2.7¹⁰ ≤ (exp 1)¹⁰ = exp 10`). -/
theorem log17000_lt : Real.log 17000 ≤ 10 := by
  have hexp : (17000:ℝ) ≤ Real.exp 10 := by
    have h1 : (2.7:ℝ) ≤ Real.exp 1 := le_of_lt (lt_trans (by norm_num) Real.exp_one_gt_d9)
    have h2 : Real.exp 10 = (Real.exp 1) ^ 10 := by rw [← Real.exp_nat_mul]; norm_num
    rw [h2]
    calc (17000:ℝ) ≤ (2.7:ℝ) ^ 10 := by norm_num
      _ ≤ (Real.exp 1) ^ 10 := by gcongr
  calc Real.log 17000 ≤ Real.log (Real.exp 10) := Real.log_le_log (by norm_num) hexp
    _ = 10 := Real.log_exp 10

/-- `(34000)^(2/5) ≤ 65.13`. -/
theorem r34_25 : (34000:ℝ) ^ ((2:ℝ)/5) ≤ 65.13 := by
  have e : (34000:ℝ) ^ ((2:ℝ)/5) = ((34000:ℝ) ^ ((1:ℝ)/5)) ^ 2 := by
    rw [← Real.rpow_natCast ((34000:ℝ) ^ ((1:ℝ)/5)) 2, ← Real.rpow_mul (by norm_num)]; norm_num
  rw [e]
  nlinarith [r4N0_5, Real.rpow_nonneg (show (0:ℝ) ≤ 34000 by norm_num) ((1:ℝ)/5)]

/-! ### `(c·x)^β / x` numeric bounds for `x ≥ 17000` -/

theorem div_decr_half {x : ℝ} (hx : 17000 ≤ x) : x ^ ((1:ℝ)/2) / x ≤ 130.4/17000 := by
  have hd := rpow_div_decr (c:=1) (by norm_num) (show (0:ℝ) < 17000 by norm_num) hx
              (β:=(1:ℝ)/2) (by norm_num) (by norm_num)
  rw [one_mul, one_mul] at hd
  have h17 : (17000:ℝ) ^ ((1:ℝ)/2) ≤ 130.4 := by rw [← Real.sqrt_eq_rpow]; exact r2N0_sqrt
  calc x ^ ((1:ℝ)/2) / x ≤ (17000:ℝ) ^ ((1:ℝ)/2) / 17000 := hd
    _ ≤ 130.4/17000 := by gcongr

theorem div_decr_3 {x : ℝ} (hx : 17000 ≤ x) : x ^ ((1:ℝ)/3) / x ≤ 25.72/17000 := by
  have hd := rpow_div_decr (c:=1) (by norm_num) (show (0:ℝ) < 17000 by norm_num) hx
              (β:=(1:ℝ)/3) (by norm_num) (by norm_num)
  rw [one_mul, one_mul] at hd
  calc x ^ ((1:ℝ)/3) / x ≤ (17000:ℝ) ^ ((1:ℝ)/3) / 17000 := hd
    _ ≤ 25.72/17000 := by gcongr; exact r2N0_3

theorem div_decr_4 {x : ℝ} (hx : 17000 ≤ x) : x ^ ((1:ℝ)/4) / x ≤ 11.42/17000 := by
  have hd := rpow_div_decr (c:=1) (by norm_num) (show (0:ℝ) < 17000 by norm_num) hx
              (β:=(1:ℝ)/4) (by norm_num) (by norm_num)
  rw [one_mul, one_mul] at hd
  calc x ^ ((1:ℝ)/4) / x ≤ (17000:ℝ) ^ ((1:ℝ)/4) / 17000 := hd
    _ ≤ 11.42/17000 := by gcongr; exact r2N0_4

theorem div_decr_5 {x : ℝ} (hx : 17000 ≤ x) : x ^ ((1:ℝ)/5) / x ≤ 7.02/17000 := by
  have hd := rpow_div_decr (c:=1) (by norm_num) (show (0:ℝ) < 17000 by norm_num) hx
              (β:=(1:ℝ)/5) (by norm_num) (by norm_num)
  rw [one_mul, one_mul] at hd
  calc x ^ ((1:ℝ)/5) / x ≤ (17000:ℝ) ^ ((1:ℝ)/5) / 17000 := hd
    _ ≤ 7.02/17000 := by gcongr; exact r2N0_5

theorem div_decr_2x5 {x : ℝ} (hx : 17000 ≤ x) : (2*x) ^ ((1:ℝ)/5) / x ≤ 8.07/17000 := by
  have hd := rpow_div_decr (c:=2) (by norm_num) (show (0:ℝ) < 17000 by norm_num) hx
              (β:=(1:ℝ)/5) (by norm_num) (by norm_num)
  have e : (2:ℝ) * 17000 = 34000 := by norm_num
  rw [e] at hd
  calc (2*x) ^ ((1:ℝ)/5) / x ≤ (34000:ℝ) ^ ((1:ℝ)/5) / 17000 := hd
    _ ≤ 8.07/17000 := by gcongr; exact r4N0_5

theorem div_decr_2x25 {x : ℝ} (hx : 17000 ≤ x) : (2*x) ^ ((2:ℝ)/5) / x ≤ 65.13/17000 := by
  have hd := rpow_div_decr (c:=2) (by norm_num) (show (0:ℝ) < 17000 by norm_num) hx
              (β:=(2:ℝ)/5) (by norm_num) (by norm_num)
  have e : (2:ℝ) * 17000 = 34000 := by norm_num
  rw [e] at hd
  calc (2*x) ^ ((2:ℝ)/5) / x ≤ (34000:ℝ) ^ ((2:ℝ)/5) / 17000 := hd
    _ ≤ 65.13/17000 := by gcongr; exact r34_25

/-! ## The tight-bound RHS as a single-argument function, and the telescoping slack -/

/-- The RHS of `log_lcmUpto_le_cheb30_tight` as a function of the argument `x` (`= 2n`). -/
noncomputable def RHSf (x : ℝ) : ℝ :=
  (6 * Aentropy / 5) * x
  + (Real.log x / Real.log 6 + 1) * (4 * Real.log x + 4)
  + theta 30
  + Real.log 4 * (Real.sqrt x + x ^ ((1:ℝ)/3) + x ^ ((1:ℝ)/4)
      + (Real.log x / Real.log 2) * x ^ ((1:ℝ)/5))

/-- `log(lcm(1..2n)) ≤ RHSf (2n)` for `n ≥ 1`. -/
theorem log_le_RHSb (n : ℕ) (hn : 1 ≤ n) :
    Real.log (lcmUpto (2 * n)) ≤ RHSf (2 * (n : ℝ)) := by
  have h := log_lcmUpto_le_cheb30_tight (2 * n) (by omega)
  unfold RHSf
  push_cast at h ⊢
  convert h using 3

-- **Telescoping step.**  `RHSf (x+2) ≤ RHSf x + log 10` for `x ≥ 17000`.  The error increments
-- `ΔF, ΔG` are `O(log(x)/x)`, dominated by the linear budget `log10 − 12·Aentropy/5`.
set_option maxHeartbeats 1200000 in
theorem slack_step_real (x : ℝ) (hx : 17000 ≤ x) :
    RHSf (x + 2) ≤ RHSf x + Real.log 10 := by
  have hxpos : (0:ℝ) < x := by linarith
  have hx2 : (0:ℝ) < x + 2 := by linarith
  have hx1 : (1:ℝ) ≤ x := by linarith
  have hx21 : (1:ℝ) ≤ x + 2 := by linarith
  -- log numeric bounds
  have hlog2L : (0.693:ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlog2pos : (0:ℝ) < Real.log 2 := by linarith
  have hlog4eq : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  have hlog4u : Real.log 4 ≤ 1.387 := by rw [hlog4eq]; linarith [Real.log_two_lt_d9]
  have hlog4nn : (0:ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hlog6L : (1.386:ℝ) ≤ Real.log 6 := by
    have h23 : Real.log 2 ≤ Real.log 3 := Real.log_le_log (by norm_num) (by norm_num)
    have e6 : Real.log 6 = Real.log 2 + Real.log 3 := by
      rw [show (6:ℝ) = 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    rw [e6]; linarith
  have hlog6pos : (0:ℝ) < Real.log 6 := by linarith
  have hlog6U : Real.log 6 ≤ 1.792 := by
    have e6 : Real.log 6 = 2 * Real.log 2 + Real.log (3/2) := by
      rw [show (6:ℝ) = 2 ^ 2 * (3/2) by norm_num,
          Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
      push_cast; ring
    rw [e6]; linarith [Real.log_two_lt_d9, log_three_halves_lt]
  have hlog10L : (2.3025:ℝ) ≤ Real.log 10 := by
    have e : Real.log 10 = 3 * Real.log 2 + Real.log (5/4) := by
      rw [show (10:ℝ) = 2 ^ 3 * (5/4) by norm_num,
          Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
      push_cast; ring
    rw [e]; linarith [Real.log_two_gt_d9, log_five_quarters_gt]
  -- log argument facts
  have haa_nn : (0:ℝ) ≤ Real.log (x + 2) - Real.log x :=
    by linarith [Real.log_le_log hxpos (show x ≤ x + 2 by linarith)]
  have haa : Real.log (x + 2) - Real.log x ≤ 2 / x := log_incr hxpos
  have ha_nn : (0:ℝ) ≤ Real.log x := Real.log_nonneg hx1
  have ha'_nn : (0:ℝ) ≤ Real.log (x + 2) := Real.log_nonneg hx21
  ----------------------------------------------------------------------------
  -- (A) F-term increment :  F(x+2) - F(x) ≤ 0.029
  ----------------------------------------------------------------------------
  have hFid : (Real.log (x+2) / Real.log 6 + 1) * (4 * Real.log (x+2) + 4)
        - (Real.log x / Real.log 6 + 1) * (4 * Real.log x + 4)
      = (4 / Real.log 6) * ((Real.log (x+2) - Real.log x)
          * (Real.log (x+2) + Real.log x + 1 + Real.log 6)) := by
    field_simp; ring
  -- bound  a'/x ≤ 5·8.07/17000
  have ha'_5 : Real.log (x + 2) ≤ 5 * (2 * x) ^ ((1:ℝ)/5) := by
    have h1 := log_le_5rpow hx2.le
    have h2 : (x + 2) ^ ((1:ℝ)/5) ≤ (2 * x) ^ ((1:ℝ)/5) :=
      Real.rpow_le_rpow hx2.le (by linarith) (by norm_num)
    linarith
  have hsum_le : Real.log (x+2) + Real.log x + 1 + Real.log 6
      ≤ 2 * Real.log (x+2) + 1 + Real.log 6 := by linarith [haa_nn]
  have hsum_nn : (0:ℝ) ≤ Real.log (x+2) + Real.log x + 1 + Real.log 6 := by linarith
  have hQR : (Real.log (x+2) - Real.log x) * (Real.log (x+2) + Real.log x + 1 + Real.log 6)
      ≤ (2 / x) * (2 * Real.log (x+2) + 1 + Real.log 6) :=
    mul_le_mul haa hsum_le hsum_nn (by positivity)
  have h4l6nn : (0:ℝ) ≤ 4 / Real.log 6 := by positivity
  have hstep1 : (4 / Real.log 6) * ((Real.log (x+2) - Real.log x)
        * (Real.log (x+2) + Real.log x + 1 + Real.log 6))
      ≤ (4 / Real.log 6) * ((2 / x) * (2 * Real.log (x+2) + 1 + Real.log 6)) :=
    mul_le_mul_of_nonneg_left hQR h4l6nn
  -- numeric bound on the RHS of hstep1
  have hub : 2 * Real.log (x+2) + 1 + Real.log 6 ≤ 10 * (2 * x) ^ ((1:ℝ)/5) + 2.792 := by
    linarith [ha'_5, hlog6U]
  have hK : (2 / x) * (2 * Real.log (x+2) + 1 + Real.log 6) ≤ 0.00983 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hxpos]
    have hp : (2 * x) ^ ((1:ℝ)/5) ≤ (8.07/17000) * x := by
      rw [← div_le_iff₀ hxpos]; exact div_decr_2x5 hx
    nlinarith [hub, hp, hx]
  have h4l6u : 4 / Real.log 6 ≤ 2.89 := by
    rw [div_le_iff₀ hlog6pos]; nlinarith [hlog6L]
  have hKnn : (0:ℝ) ≤ (2 / x) * (2 * Real.log (x+2) + 1 + Real.log 6) := by positivity
  have hFle : (Real.log (x+2) / Real.log 6 + 1) * (4 * Real.log (x+2) + 4)
      ≤ (Real.log x / Real.log 6 + 1) * (4 * Real.log x + 4) + 0.029 := by
    have hbig : (4 / Real.log 6) * ((Real.log (x+2) - Real.log x)
          * (Real.log (x+2) + Real.log x + 1 + Real.log 6)) ≤ 0.029 :=
      calc _ ≤ (4 / Real.log 6) * ((2 / x) * (2 * Real.log (x+2) + 1 + Real.log 6)) := hstep1
        _ ≤ 2.89 * 0.00983 := mul_le_mul h4l6u hK hKnn (by norm_num)
        _ ≤ 0.029 := by norm_num
    linarith [hFid.le, hFid.ge, hbig]
  ----------------------------------------------------------------------------
  -- (B) bracket increment :  G-bracket(x+2) - G-bracket(x) ≤ 0.0214
  ----------------------------------------------------------------------------
  -- B2 : sqrt term
  have hP2 : (x+2) ^ ((1:ℝ)/2) - x ^ ((1:ℝ)/2) ≤ 0.007671 := by
    have hb := bern_incr hxpos (p:=(1:ℝ)/2) (by norm_num) (by norm_num)
    have e : 2 * ((1:ℝ)/2) * x ^ ((1:ℝ)/2) / x = x ^ ((1:ℝ)/2) / x := by ring
    rw [e] at hb
    linarith [hb, div_decr_half hx]
  have hP3 : (x+2) ^ ((1:ℝ)/3) - x ^ ((1:ℝ)/3) ≤ 0.001009 := by
    have hb := bern_incr hxpos (p:=(1:ℝ)/3) (by norm_num) (by norm_num)
    have e : 2 * ((1:ℝ)/3) * x ^ ((1:ℝ)/3) / x = (2/3) * (x ^ ((1:ℝ)/3) / x) := by ring
    rw [e] at hb
    linarith [hb, div_decr_3 hx]
  have hP4 : (x+2) ^ ((1:ℝ)/4) - x ^ ((1:ℝ)/4) ≤ 0.000336 := by
    have hb := bern_incr hxpos (p:=(1:ℝ)/4) (by norm_num) (by norm_num)
    have e : 2 * ((1:ℝ)/4) * x ^ ((1:ℝ)/4) / x = (1/2) * (x ^ ((1:ℝ)/4) / x) := by ring
    rw [e] at hb
    linarith [hb, div_decr_4 hx]
  -- B5 : the (log/log2)·x^{1/5} term
  have hP5'P5 : (x+2) ^ ((1:ℝ)/5) - x ^ ((1:ℝ)/5) ≤ (2/5) * (x ^ ((1:ℝ)/5) / x) := by
    have hb := bern_incr hxpos (p:=(1:ℝ)/5) (by norm_num) (by norm_num)
    have e : 2 * ((1:ℝ)/5) * x ^ ((1:ℝ)/5) / x = (2/5) * (x ^ ((1:ℝ)/5) / x) := by ring
    rw [e] at hb; exact hb
  have hP5'P5nn : (0:ℝ) ≤ (x+2) ^ ((1:ℝ)/5) - x ^ ((1:ℝ)/5) := by
    have : x ^ ((1:ℝ)/5) ≤ (x+2) ^ ((1:ℝ)/5) :=
      Real.rpow_le_rpow hxpos.le (by linarith) (by norm_num)
    linarith
  have hx5nn : (0:ℝ) ≤ x ^ ((1:ℝ)/5) := Real.rpow_nonneg hxpos.le _
  have ha'5nn : (0:ℝ) ≤ 5 * (2 * x) ^ ((1:ℝ)/5) := by positivity
  -- a'·(P5'-P5) ≤ 2·(2x)^{2/5}/x ≤ 2·65.13/17000
  have hT1 : Real.log (x+2) * ((x+2) ^ ((1:ℝ)/5) - x ^ ((1:ℝ)/5)) ≤ 2 * (65.13/17000) := by
    have hstep : Real.log (x+2) * ((x+2) ^ ((1:ℝ)/5) - x ^ ((1:ℝ)/5))
        ≤ (5 * (2 * x) ^ ((1:ℝ)/5)) * ((2/5) * (x ^ ((1:ℝ)/5) / x)) :=
      mul_le_mul ha'_5 hP5'P5 hP5'P5nn ha'5nn
    have hx_le : x ^ ((1:ℝ)/5) ≤ (2 * x) ^ ((1:ℝ)/5) :=
      Real.rpow_le_rpow hxpos.le (by linarith) (by norm_num)
    have hprodeq : (2 * x) ^ ((1:ℝ)/5) * (2 * x) ^ ((1:ℝ)/5) = (2 * x) ^ ((2:ℝ)/5) := by
      rw [← Real.rpow_add (by linarith)]; norm_num
    have h2xnn : (0:ℝ) ≤ (2 * x) ^ ((1:ℝ)/5) := Real.rpow_nonneg (by linarith) _
    have hprod : (2 * x) ^ ((1:ℝ)/5) * x ^ ((1:ℝ)/5) ≤ (2 * x) ^ ((2:ℝ)/5) := by
      have := mul_le_mul_of_nonneg_left hx_le h2xnn
      linarith [this, hprodeq.le, hprodeq.ge]
    have hrw : (5 * (2 * x) ^ ((1:ℝ)/5)) * ((2/5) * (x ^ ((1:ℝ)/5) / x))
        = 2 * (((2 * x) ^ ((1:ℝ)/5) * x ^ ((1:ℝ)/5)) / x) := by field_simp
    have hdd := div_decr_2x25 hx
    have hfin : 2 * (((2 * x) ^ ((1:ℝ)/5) * x ^ ((1:ℝ)/5)) / x) ≤ 2 * (65.13/17000) := by
      have hmono : ((2 * x) ^ ((1:ℝ)/5) * x ^ ((1:ℝ)/5)) / x ≤ (2 * x) ^ ((2:ℝ)/5) / x :=
        div_le_div_of_nonneg_right hprod hxpos.le
      linarith [hmono, hdd]
    linarith [hstep, hrw.le, hrw.ge, hfin]
  -- P5·(a'-a) ≤ 2·7.02/17000
  have hT2 : x ^ ((1:ℝ)/5) * (Real.log (x+2) - Real.log x) ≤ 2 * (7.02/17000) := by
    have hstep : x ^ ((1:ℝ)/5) * (Real.log (x+2) - Real.log x)
        ≤ x ^ ((1:ℝ)/5) * (2 / x) :=
      mul_le_mul_of_nonneg_left haa hx5nn
    have hrw : x ^ ((1:ℝ)/5) * (2 / x) = 2 * (x ^ ((1:ℝ)/5) / x) := by ring
    have hdd := div_decr_5 hx
    linarith [hstep, hrw.le, hrw.ge, hdd]
  have hv : Real.log (x+2) * (x+2) ^ ((1:ℝ)/5) - Real.log x * x ^ ((1:ℝ)/5) ≤ 0.008489 := by
    have hid : Real.log (x+2) * (x+2) ^ ((1:ℝ)/5) - Real.log x * x ^ ((1:ℝ)/5)
        = Real.log (x+2) * ((x+2) ^ ((1:ℝ)/5) - x ^ ((1:ℝ)/5))
          + x ^ ((1:ℝ)/5) * (Real.log (x+2) - Real.log x) := by ring
    rw [hid]; linarith [hT1, hT2]
  have hfifth : (Real.log (x+2) / Real.log 2) * (x+2) ^ ((1:ℝ)/5)
      - (Real.log x / Real.log 2) * x ^ ((1:ℝ)/5) ≤ 0.01228 := by
    have heq : (Real.log (x+2) / Real.log 2) * (x+2) ^ ((1:ℝ)/5)
        - (Real.log x / Real.log 2) * x ^ ((1:ℝ)/5)
        = (Real.log (x+2) * (x+2) ^ ((1:ℝ)/5) - Real.log x * x ^ ((1:ℝ)/5)) / Real.log 2 := by
      field_simp
    rw [heq, div_le_iff₀ hlog2pos]
    nlinarith [hv, hlog2L]
  -- combine the four into the bracket increment, then multiply by log4
  have hbrle : Real.log 4 * ((x+2) ^ ((1:ℝ)/2) + (x+2) ^ ((1:ℝ)/3) + (x+2) ^ ((1:ℝ)/4)
        + (Real.log (x+2) / Real.log 2) * (x+2) ^ ((1:ℝ)/5))
      ≤ Real.log 4 * (x ^ ((1:ℝ)/2) + x ^ ((1:ℝ)/3) + x ^ ((1:ℝ)/4)
        + (Real.log x / Real.log 2) * x ^ ((1:ℝ)/5)) + 0.030 := by
    have hΔ : ((x+2) ^ ((1:ℝ)/2) + (x+2) ^ ((1:ℝ)/3) + (x+2) ^ ((1:ℝ)/4)
          + (Real.log (x+2) / Real.log 2) * (x+2) ^ ((1:ℝ)/5))
        - (x ^ ((1:ℝ)/2) + x ^ ((1:ℝ)/3) + x ^ ((1:ℝ)/4)
          + (Real.log x / Real.log 2) * x ^ ((1:ℝ)/5)) ≤ 0.0214 := by
      linarith [hP2, hP3, hP4, hfifth]
    have hmul := mul_le_mul_of_nonneg_left hΔ hlog4nn
    have hnum : Real.log 4 * (0.0214:ℝ) ≤ 0.030 := by nlinarith [hlog4u, hlog4nn]
    nlinarith [hmul, hnum]
  ----------------------------------------------------------------------------
  -- (C) assemble
  ----------------------------------------------------------------------------
  have hlead : (6 * Aentropy / 5) * (x + 2) = (6 * Aentropy / 5) * x + 12 * Aentropy / 5 := by
    ring
  have hA : 12 * Aentropy / 5 ≤ 2.22 := by linarith [Aentropy_lt]
  unfold RHSf
  simp only [Real.sqrt_eq_rpow]
  linarith [hlead, hFle, hbrle, hA, hlog10L]

/-- **Lower bound on `log(3/2)`** (mirror of `log_three_halves_lt`, 12 Taylor terms). -/
theorem log_three_halves_gt : (0.405 : ℝ) < Real.log (3/2) := by
  have t : |((1:ℝ)/3)| = 1/3 := by rw [abs_of_pos]; norm_num
  have z := Real.abs_log_sub_add_sum_range_le (show |((1:ℝ)/3)| < 1 by rw [t]; norm_num) 12
  rw [t, abs_le] at z
  obtain ⟨_, z2⟩ := z
  have hsum : (0.405 : ℝ) < (∑ i ∈ Finset.range 12, ((1:ℝ)/3)^(i+1)/((i:ℝ)+1))
      - (1/3:ℝ)^(12+1)/(1-(1:ℝ)/3) := by
    norm_num [Finset.sum_range_succ]
  have hlog : Real.log ((3:ℝ)/2) = - Real.log (1 - 1/3) := by
    rw [show (3:ℝ)/2 = (1 - 1/3)⁻¹ by norm_num, Real.log_inv]
  rw [hlog]; linarith [z2, hsum]

-- **Base case** of the telescope at `N0 = 8500` (`2N0 = 17000`).
set_option maxHeartbeats 800000 in
theorem slack_base : Real.log 30 + RHSf 17000 ≤ Real.log 6 + 8500 * Real.log 10 := by
  -- log numeric bounds
  have hlog2L : (0.693:ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlog2pos : (0:ℝ) < Real.log 2 := by linarith
  have hlog4eq : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  have hlog4u : Real.log 4 ≤ 1.387 := by rw [hlog4eq]; linarith [Real.log_two_lt_d9]
  have hlog4nn : (0:ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have e6 : Real.log 6 = 2 * Real.log 2 + Real.log (3/2) := by
    rw [show (6:ℝ) = 2 ^ 2 * (3/2) by norm_num,
        Real.log_mul (by norm_num) (by norm_num), Real.log_pow]; push_cast; ring
  have hlog6L : (1.79:ℝ) ≤ Real.log 6 := by rw [e6]; linarith [Real.log_two_gt_d9, log_three_halves_gt]
  have hlog6pos : (0:ℝ) < Real.log 6 := by linarith
  have hlog30U : Real.log 30 ≤ 3.41 := by
    have e : Real.log 30 = 4 * Real.log 2 + Real.log (3/2) + Real.log (5/4) := by
      rw [show (30:ℝ) = 2 ^ 4 * (3/2) * (5/4) by norm_num,
          Real.log_mul (by norm_num) (by norm_num),
          Real.log_mul (by norm_num) (by norm_num), Real.log_pow]; push_cast; ring
    rw [e]; linarith [Real.log_two_lt_d9, log_three_halves_lt, log_five_quarters_lt]
  have hlog10L : (2.3025:ℝ) ≤ Real.log 10 := by
    have e : Real.log 10 = 3 * Real.log 2 + Real.log (5/4) := by
      rw [show (10:ℝ) = 2 ^ 3 * (5/4) by norm_num,
          Real.log_mul (by norm_num) (by norm_num), Real.log_pow]; push_cast; ring
    rw [e]; linarith [Real.log_two_gt_d9, log_five_quarters_gt]
  have ha10 : Real.log 17000 ≤ 10 := log17000_lt
  have ha_nn : (0:ℝ) ≤ Real.log 17000 := Real.log_nonneg (by norm_num)
  -- leading
  have hlead : (6 * Aentropy / 5) * 17000 ≤ 18870 := by linarith [Aentropy_lt]
  -- F-term
  have hfac1 : Real.log 17000 / Real.log 6 ≤ 10/1.79 := by
    rw [div_le_iff₀ hlog6pos]; nlinarith [ha10, hlog6L]
  have hF : (Real.log 17000 / Real.log 6 + 1) * (4 * Real.log 17000 + 4) ≤ 290 := by
    have h1 : Real.log 17000 / Real.log 6 + 1 ≤ 10/1.79 + 1 := by linarith [hfac1]
    have h2 : 4 * Real.log 17000 + 4 ≤ 44 := by linarith [ha10]
    have h3 : (0:ℝ) ≤ 4 * Real.log 17000 + 4 := by linarith [ha_nn]
    have := mul_le_mul h1 h2 h3 (by norm_num)
    nlinarith [this]
  -- G-term
  have hf2 : Real.log 17000 / Real.log 2 ≤ 10/0.693 := by
    rw [div_le_iff₀ hlog2pos]; nlinarith [ha10, hlog2L]
  have hc5nn : (0:ℝ) ≤ (17000:ℝ) ^ ((1:ℝ)/5) := Real.rpow_nonneg (by norm_num) _
  have hf2nn : (0:ℝ) ≤ Real.log 17000 / Real.log 2 := by positivity
  have hfifthb : (Real.log 17000 / Real.log 2) * (17000:ℝ) ^ ((1:ℝ)/5) ≤ (10/0.693) * 7.02 :=
    mul_le_mul hf2 r2N0_5 hc5nn (by norm_num)
  have hSnn : (0:ℝ) ≤ Real.sqrt 17000 + (17000:ℝ) ^ ((1:ℝ)/3) + (17000:ℝ) ^ ((1:ℝ)/4)
      + (Real.log 17000 / Real.log 2) * (17000:ℝ) ^ ((1:ℝ)/5) := by
    have : (0:ℝ) ≤ (Real.log 17000 / Real.log 2) * (17000:ℝ) ^ ((1:ℝ)/5) := by positivity
    have h3 : (0:ℝ) ≤ (17000:ℝ) ^ ((1:ℝ)/3) := Real.rpow_nonneg (by norm_num) _
    have h4 : (0:ℝ) ≤ (17000:ℝ) ^ ((1:ℝ)/4) := Real.rpow_nonneg (by norm_num) _
    have h5 : (0:ℝ) ≤ Real.sqrt 17000 := Real.sqrt_nonneg _
    linarith
  have hS : Real.sqrt 17000 + (17000:ℝ) ^ ((1:ℝ)/3) + (17000:ℝ) ^ ((1:ℝ)/4)
        + (Real.log 17000 / Real.log 2) * (17000:ℝ) ^ ((1:ℝ)/5)
      ≤ 130.4 + 25.72 + 11.42 + (10/0.693) * 7.02 := by
    linarith [r2N0_sqrt, r2N0_3, r2N0_4, hfifthb]
  have hG : Real.log 4 * (Real.sqrt 17000 + (17000:ℝ) ^ ((1:ℝ)/3) + (17000:ℝ) ^ ((1:ℝ)/4)
        + (Real.log 17000 / Real.log 2) * (17000:ℝ) ^ ((1:ℝ)/5)) ≤ 373 := by
    have := mul_le_mul hlog4u hS hSnn (by norm_num : (0:ℝ) ≤ 1.387)
    nlinarith [this]
  have htheta : theta 30 ≤ 23 := le_of_lt theta30_lt
  unfold RHSf
  linarith [hlead, hF, hG, htheta, hlog30U, hlog6L, hlog10L]

/-- **Telescoped real target.**  `log 30 + RHSf (2n) ≤ log 6 + n·log 10` for all `n ≥ 8500`. -/
theorem real_target (n : ℕ) (hn : 8500 ≤ n) :
    Real.log 30 + RHSf (2 * (n : ℝ)) ≤ Real.log 6 + (n : ℝ) * Real.log 10 := by
  induction n, hn using Nat.le_induction with
  | base =>
      have e1 : (2:ℝ) * ((8500:ℕ) : ℝ) = 17000 := by norm_num
      have e2 : ((8500:ℕ) : ℝ) = 8500 := by norm_num
      rw [e1, e2]; exact slack_base
  | succ m hm ih =>
      have hmR : (8500:ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
      have hx : (17000:ℝ) ≤ 2 * (m : ℝ) := by linarith
      have hstep := slack_step_real (2 * (m : ℝ)) hx
      have harg : (2:ℝ) * ((m : ℝ) + 1) = 2 * (m : ℝ) + 2 := by ring
      push_cast
      rw [harg]
      linarith [hstep, ih]

/-- **Prize lcm pin, sharp threshold.**  For all `n ≥ 8500`, `30·lcm(1..2n) ≤ 6·10ⁿ`. -/
theorem lcm_two_n_le_target_sharp (n : ℕ) (hn : 8500 ≤ n) :
    30 * LcmGrowthBound.lcmUpto (2 * n) ≤ 6 * 10 ^ n := by
  have hnpos : 0 < n := by omega
  rw [← Nat.cast_le (α := ℝ)]
  push_cast
  have hlpos : (0:ℝ) < (lcmUpto (2 * n) : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (lcmUpto_ne_zero (2 * n))
  have hApos : (0:ℝ) < 30 * (lcmUpto (2 * n) : ℝ) := by positivity
  have hBpos : (0:ℝ) < 6 * (10:ℝ) ^ n := by positivity
  have key : Real.log (30 * (lcmUpto (2 * n) : ℝ)) ≤ Real.log (6 * (10:ℝ) ^ n) := by
    rw [Real.log_mul (by norm_num) (ne_of_gt hlpos),
        Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    have h1 := log_le_RHSb n (by omega)
    have h2 := real_target n hn
    linarith [h1, h2]
  calc (30:ℝ) * (lcmUpto (2 * n) : ℝ)
      = Real.exp (Real.log (30 * (lcmUpto (2 * n) : ℝ))) := (Real.exp_log hApos).symm
    _ ≤ Real.exp (Real.log (6 * (10:ℝ) ^ n)) := Real.exp_le_exp.mpr key
    _ = 6 * (10:ℝ) ^ n := Real.exp_log hBpos

#print axioms lcm_two_n_le_target_sharp

end CollatzChebyshev30
