import Propositio.Collatz.Chebyshev30LcmTight
import Propositio.Collatz.Chebyshev30Aentropy
import Propositio.NumberTheory.Diophantine.LcmGrowthBound
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Sqrt

/-!
# Chebyshev-30 lcm pin: reduce the prize's `hlcm` target to a finite window

The prize bound `30 · lcm(1..2n) ≤ 6 · 10ⁿ` is the denominator-side target.  Combining the
*tight* Chebyshev-30 lcm bound `log_lcmUpto_le_cheb30_tight` (leading slope `6A/5 < 1.11`, every
error term `o(n)` with a small additive constant) with the entropy certificate `Aentropy < 37/40`
shows the real-log form of this inequality holds for all sufficiently large `n`, and hence the Nat
inequality itself.

We land an explicit threshold `N0 = 20000000`.  This is far from optimal (the analytic crossover
is `n ≈ 6879`), but it is a clean, fully rigorous, axiom-clean reduction: every sub-`n` error term
is dominated by `√(2n)`, which we pin `≤ n/3000` once `n ≥ N0`, leaving the linear margin
`log10 − 12A/5 > 0.082` to absorb it.  The residual handoff window is `n < N0`.

Main result: `lcm_two_n_le_target (n) (hn : 20000000 ≤ n) : 30 · lcmUpto (2n) ≤ 6 · 10ⁿ`.
-/

namespace CollatzChebyshev30

open Chebyshev Real LcmGrowthBound

/-- **Lower bound on `log(5/4)`** via 8 terms of the Taylor series of `log(1 − 1/5)` (the mirror
of `log_five_quarters_lt`). -/
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

/-- **Prize lcm pin to a finite window.**  For all `n ≥ 20000000`,
`30 · lcm(1..2n) ≤ 6 · 10ⁿ`.  This is the denominator-side target of the prize, reduced to a
finite census `n < 20000000`. -/
theorem lcm_two_n_le_target (n : ℕ) (hn : 20000000 ≤ n) :
    30 * LcmGrowthBound.lcmUpto (2*n) ≤ 6 * 10^n := by
  have hnpos : 0 < n := by omega
  rw [← Nat.cast_le (α := ℝ)]
  push_cast
  -- goal: 30 * ↑(lcmUpto (2*n)) ≤ 6 * 10^n   (in ℝ)
  have hlpos : (0:ℝ) < (lcmUpto (2*n) : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (lcmUpto_ne_zero (2*n))
  have hApos : (0:ℝ) < 30 * (lcmUpto (2*n) : ℝ) := mul_pos (by norm_num) hlpos
  have hBpos : (0:ℝ) < 6 * (10:ℝ)^n :=
    mul_pos (by norm_num) (pow_pos (by norm_num) n)
  -- It suffices to compare logs.
  have key : Real.log (30 * (lcmUpto (2*n) : ℝ)) ≤ Real.log (6 * (10:ℝ)^n) := by
    rw [Real.log_mul (by norm_num) (ne_of_gt hlpos),
        Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    -- goal: log 30 + log ↑lcm ≤ log 6 + ↑n * log 10
    have htight := log_lcmUpto_le_cheb30_tight (2*n) (by omega)
    push_cast at htight
    set N := (n:ℝ) with hN_def
    set s := Real.sqrt (2 * N) with hs_def
    set q := (2 * N) ^ ((1:ℝ)/4) with hq_def
    -- basic facts
    have hNpos : (0:ℝ) < N := by rw [hN_def]; exact_mod_cast hnpos
    have hNbig : (20000000:ℝ) ≤ N := by rw [hN_def]; exact_mod_cast hn
    have hx0 : (0:ℝ) < 2 * N := by linarith
    have hx1 : (1:ℝ) ≤ 2 * N := by linarith
    -- root facts
    have hq1 : (1:ℝ) ≤ q := by
      rw [hq_def]
      calc (1:ℝ) = (2*N)^(0:ℝ) := by rw [Real.rpow_zero]
        _ ≤ (2*N)^((1:ℝ)/4) := Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
    have hq0 : (0:ℝ) ≤ q := le_trans zero_le_one hq1
    have hs0 : (0:ℝ) ≤ s := by rw [hs_def]; exact Real.sqrt_nonneg _
    have hexp_eq : (1:ℝ)/4 * ((2:ℕ):ℝ) = 1/(2:ℝ) := by push_cast; ring
    have hqs : q ^ 2 = s := by
      rw [hs_def, Real.sqrt_eq_rpow, hq_def, ← Real.rpow_natCast ((2*N)^((1:ℝ)/4)) 2,
          ← Real.rpow_mul hx0.le, hexp_eq]
    have hcube : (2*N)^((1:ℝ)/3) ≤ s := by
      rw [hs_def, Real.sqrt_eq_rpow]
      exact Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
    have hfifth : (2*N)^((1:ℝ)/5) ≤ q := by
      rw [hq_def]
      exact Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
    have hfourth : q ≤ s := by
      have h1 : q * 1 ≤ q * q := mul_le_mul_of_nonneg_left hq1 hq0
      have h2 : q * q = s := by rw [← hqs]; ring
      linarith [h1, h2]
    -- log(2N) ≤ 4 q
    have hlog2N : Real.log (2*N) ≤ 4 * q := by
      have hlq : Real.log q ≤ q - 1 := Real.log_le_sub_one_of_pos (by linarith [hq1])
      have heq : Real.log q = (1:ℝ)/4 * Real.log (2*N) := by
        rw [hq_def, Real.log_rpow hx0]
      rw [heq] at hlq
      linarith
    -- numerics
    have hlog4eq : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]; push_cast; ring
    have hlog4 : Real.log 4 ≤ 1.4 := by rw [hlog4eq]; linarith [Real.log_two_lt_d9]
    have hlog4nonneg : (0:ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    have hlog6ge1 : (1:ℝ) ≤ Real.log 6 := by
      have he : Real.exp 1 < 6 := lt_trans Real.exp_one_lt_d9 (by norm_num)
      have h2 := Real.log_lt_log (Real.exp_pos 1) he
      rw [Real.log_exp] at h2
      linarith
    have hlog6 : (0:ℝ) ≤ Real.log 6 := by linarith [hlog6ge1]
    have hlog2pos : (0:ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
    have hlog30 : Real.log 30 ≤ 3.41 := by
      have e : Real.log 30 = 4 * Real.log 2 + Real.log (3/2) + Real.log (5/4) := by
        rw [show (30:ℝ) = 2^4 * (3/2) * (5/4) by norm_num,
            Real.log_mul (by norm_num) (by norm_num),
            Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
        push_cast; ring
      rw [e]
      linarith [Real.log_two_lt_d9, log_three_halves_lt, log_five_quarters_lt]
    have hlog10 : (2.3025:ℝ) ≤ Real.log 10 := by
      have e : Real.log 10 = 3 * Real.log 2 + Real.log (5/4) := by
        rw [show (10:ℝ) = 2^3 * (5/4) by norm_num,
            Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
        push_cast; ring
      rw [e]
      linarith [Real.log_two_gt_d9, log_five_quarters_gt]
    -- leading-term bound: (6A/5)(2N) ≤ 2.22 N
    have hlead : 6 * Aentropy / 5 * (2 * N) ≤ 2.22 * N := by
      have h := mul_le_mul_of_nonneg_left (le_of_lt Aentropy_lt) hNpos.le
      linarith [h]
    have htheta30 : theta 30 ≤ 42 := by
      have h := theta_le_log4_mul_x (show (0:ℝ) ≤ 30 by norm_num)
      linarith [h, hlog4]
    -- F-term: (log(2N)/log6 + 1)(4 log(2N) + 4) ≤ 96 s + 4
    have hF : (Real.log (2*N)/Real.log 6 + 1) * (4 * Real.log (2*N) + 4) ≤ 96 * s + 4 := by
      have hL0 : (0:ℝ) ≤ Real.log (2*N) := Real.log_nonneg hx1
      have hdiv : Real.log (2*N) / Real.log 6 ≤ Real.log (2*N) := div_le_self hL0 hlog6ge1
      have hfac1 : Real.log (2*N)/Real.log 6 + 1 ≤ 4*q + 1 := by linarith [hdiv, hlog2N]
      have hfac2 : 4 * Real.log (2*N) + 4 ≤ 16*q + 4 := by linarith [hlog2N]
      have hmul : (Real.log (2*N)/Real.log 6 + 1) * (4 * Real.log (2*N) + 4)
          ≤ (4*q+1) * (16*q+4) :=
        mul_le_mul hfac1 hfac2 (by linarith [hL0]) (by linarith [hq0])
      have hexp : (4*q+1) * (16*q+4) ≤ 96 * s + 4 := by
        have hexpand : (4*q+1) * (16*q+4) = 64 * q^2 + 32*q + 4 := by ring
        rw [hexpand, hqs]
        linarith [hfourth]
      linarith [hmul, hexp]
    -- product term: (log(2N)/log2)·(2N)^{1/5} ≤ 6 s
    have hprod : Real.log (2*N)/Real.log 2 * (2*N)^((1:ℝ)/5) ≤ 6 * s := by
      have hdiv2 : Real.log (2*N) / Real.log 2 ≤ 1.5 * Real.log (2*N) := by
        rw [div_le_iff₀ hlog2pos]
        have h1le : (1:ℝ) ≤ 1.5 * Real.log 2 := by linarith [Real.log_two_gt_d9]
        have hm := mul_le_mul_of_nonneg_left h1le (Real.log_nonneg hx1)
        linarith [hm]
      have h5nn : (0:ℝ) ≤ (2*N)^((1:ℝ)/5) := Real.rpow_nonneg hx0.le _
      calc Real.log (2*N)/Real.log 2 * (2*N)^((1:ℝ)/5)
          ≤ (1.5 * Real.log (2*N)) * q :=
            mul_le_mul hdiv2 hfifth h5nn (by have := Real.log_nonneg hx1; linarith)
        _ ≤ 6 * s := by
            have h1 : Real.log (2*N) * q ≤ 4 * q * q :=
              mul_le_mul_of_nonneg_right hlog2N hq0
            have h2 : (4:ℝ) * q * q = 4 * s := by rw [← hqs]; ring
            linarith [h1, h2]
    -- G-term: log4·(s + (2N)^{1/3} + q + (log(2N)/log2)(2N)^{1/5}) ≤ 13 s
    have hG : Real.log 4 * (s + (2*N)^((1:ℝ)/3) + q
        + Real.log (2*N)/Real.log 2 * (2*N)^((1:ℝ)/5)) ≤ 13 * s := by
      have hsum9 : s + (2*N)^((1:ℝ)/3) + q
          + Real.log (2*N)/Real.log 2 * (2*N)^((1:ℝ)/5) ≤ 9 * s := by
        linarith [hcube, hfourth, hprod, hs0]
      have hsumnn : (0:ℝ) ≤ s + (2*N)^((1:ℝ)/3) + q
          + Real.log (2*N)/Real.log 2 * (2*N)^((1:ℝ)/5) := by
        have h1 : (0:ℝ) ≤ (2*N)^((1:ℝ)/3) := Real.rpow_nonneg hx0.le _
        have h2 : (0:ℝ) ≤ Real.log (2*N)/Real.log 2 * (2*N)^((1:ℝ)/5) :=
          mul_nonneg (div_nonneg (Real.log_nonneg hx1) (Real.log_nonneg (by norm_num)))
            (Real.rpow_nonneg hx0.le _)
        linarith [hs0, hq0, h1, h2]
      calc Real.log 4 * (s + (2*N)^((1:ℝ)/3) + q
              + Real.log (2*N)/Real.log 2 * (2*N)^((1:ℝ)/5))
          ≤ 1.4 * (s + (2*N)^((1:ℝ)/3) + q
              + Real.log (2*N)/Real.log 2 * (2*N)^((1:ℝ)/5)) :=
            mul_le_mul_of_nonneg_right hlog4 hsumnn
        _ ≤ 1.4 * (9 * s) := mul_le_mul_of_nonneg_left hsum9 (by norm_num)
        _ ≤ 13 * s := by linarith [hs0]
    -- finite-window pin: √(2N) ≤ N/3000
    have hs3000 : 3000 * s ≤ N := by
      have hss : s ^ 2 = 2 * N := by rw [hs_def]; exact Real.sq_sqrt hx0.le
      have hsq : (3000 * s)^2 ≤ N^2 := by
        have e1 : (3000*s)^2 = 9000000 * s^2 := by ring
        have e2 : (9000000:ℝ) * s^2 = 18000000 * N := by rw [hss]; ring
        have hbig : (18000000:ℝ) * N ≤ N^2 := by
          have h := mul_le_mul_of_nonneg_left
            (show (18000000:ℝ) ≤ N by linarith [hNbig]) hNpos.le
          rw [pow_two]; linarith [h]
        rw [e1, e2]; exact hbig
      exact le_of_sq_le_sq hsq hNpos.le
    have hrhs : 2.3025 * N ≤ N * Real.log 10 := by
      have h := mul_le_mul_of_nonneg_left hlog10 hNpos.le
      linarith [h]
    -- assemble
    have hcomb : Real.log (lcmUpto (2*n) : ℝ) ≤ 2.22 * N + (96*s+4) + 42 + 13*s :=
      le_trans htight (by linarith [hlead, hF, htheta30, hG])
    linarith [hcomb, hlog30, hlog6, hrhs, hs3000, hNbig]
  -- recover from logs
  calc (30:ℝ) * (lcmUpto (2*n) : ℝ)
      = Real.exp (Real.log (30 * (lcmUpto (2*n) : ℝ))) := (Real.exp_log hApos).symm
    _ ≤ Real.exp (Real.log (6 * (10:ℝ)^n)) := Real.exp_le_exp.mpr key
    _ = 6 * (10:ℝ)^n := Real.exp_log hBpos

#print axioms lcm_two_n_le_target

end CollatzChebyshev30
