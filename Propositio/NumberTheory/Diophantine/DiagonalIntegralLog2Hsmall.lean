import Propositio.NumberTheory.Diophantine.DiagonalIntegralLog2Tendsto
import Propositio.NumberTheory.Diophantine.DiagonalIntegralLog2Irrational
import Mathlib.Tactic
import Mathlib.Topology.Order.LiminfLimsup

/-!
# Explicit geometric majorant for `lcmUpto n · (3 − 2√2)ⁿ`  (the `hsmall` brick)

This file proves the two geometric-bound theorems that feed the `hsmall` input of
`irrationality_measure_le`:

* `exists_geom_bound`: there exist `A > 0`, `ρ ∈ (0, 1)` with
    `lcmUpto n · (3 − 2√2)ⁿ ≤ A · ρⁿ` for all `n`.

* `exists_hsmall_bound`: the same bound holds for `lcmUpto n · Iₙ`
    (using `D_mul_I_le_geom` and `Real.log 2 > 0`).

**Proof outline for `exists_geom_bound`.** Let `c = 3 − 2√2`.  We know `4c < 1`
(`h4c_lt_one`).  Pick any `ρ` with `4c < ρ < 1` (by density of `ℝ`).  Then
`β := c/ρ` satisfies `0 < β` and `4β < 1` (since `β < c/(4c) = 1/4`).  By the
generalised version of `geom_lcm_tendsto_zero` (with base `β`), the sequence
`(lcmUpto n) · βⁿ` tends to 0 and hence has a bounded range.  The bound `A` on that
range satisfies `(lcmUpto n) · cⁿ = ((lcmUpto n) · βⁿ) · ρⁿ ≤ A · ρⁿ`.
-/

namespace DiagonalIntegralLog2

open Filter Real LcmGrowthBound

/-! ## Arithmetic facts about `c = 3 − 2√2` -/

private lemma sqrt2_sq' : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
private lemma sqrt2_pos' : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
private lemma hc_pos' : (0 : ℝ) < 3 - 2 * Real.sqrt 2 := by nlinarith [sqrt2_sq', sqrt2_pos']
private lemma h4c_lt_one' : 4 * (3 - 2 * Real.sqrt 2 : ℝ) < 1 := by
  nlinarith [sqrt2_sq', sqrt2_pos']
private lemma h4c_pos' : (0 : ℝ) < 4 * (3 - 2 * Real.sqrt 2) := by nlinarith [hc_pos']

/-! ## Generalised geometric-lcm tendsto zero -/

/-- **Generalised form of `geom_lcm_tendsto_zero`.**  For *any* `β` with `0 < β` and `4β < 1`,
`lcmUpto n · βⁿ → 0`.  The proof is a verbatim generalisation of the concrete `c = 3 − 2√2`
argument in `DiagonalIntegralLog2Tendsto`. -/
lemma geom_lcm_tendsto_zero_gen (β : ℝ) (hβ0 : 0 < β) (hβ4 : 4 * β < 1) :
    Tendsto (fun n : ℕ => (lcmUpto n : ℝ) * β ^ n) atTop (nhds 0) := by
  -- log(4β) < 0
  have h4β_pos : (0 : ℝ) < 4 * β := by linarith
  have h4β_lt1 : (4 : ℝ) * β < 1 := hβ4
  have hβ_ne : β ≠ 0 := ne_of_gt hβ0
  have hL_neg : Real.log (4 * β) < 0 := Real.log_neg h4β_pos h4β_lt1
  have hL_ne : Real.log (4 * β) ≠ 0 := ne_of_lt hL_neg
  -- Build the auxiliary function h n = log(4β)·n + 2·√n·log n
  set L := Real.log (4 * β) with hL_def
  -- Step A: log n ≤ (-L/4)·√n eventually
  have hlog_le : ∀ᶠ n : ℕ in atTop, Real.log n ≤ (-L / 4) * Real.sqrt n := by
    have hr : (0 : ℝ) < 1 / 2 := by norm_num
    have hε : 0 < -L / 4 := by linarith [hL_neg]
    have hiso : (fun n : ℕ => Real.log n) =o[atTop] (fun n : ℕ => (n : ℝ) ^ ((1:ℝ)/2)) :=
      (isLittleO_log_rpow_atTop hr).natCast_atTop
    have hbigO : ∀ᶠ n : ℕ in atTop, ‖Real.log n‖ ≤ (-L / 4) * ‖(n : ℝ) ^ ((1:ℝ)/2)‖ :=
      hiso.def hε
    filter_upwards [hbigO, eventually_ge_atTop 0] with n hle _
    have h_norm_rpow : ‖(n : ℝ) ^ ((1:ℝ)/2)‖ = Real.sqrt n := by
      rw [Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _), Real.sqrt_eq_rpow]
    calc Real.log n ≤ ‖Real.log n‖ := le_abs_self _
      _ ≤ -L / 4 * ‖(n : ℝ) ^ ((1:ℝ)/2)‖ := hle
      _ = -L / 4 * Real.sqrt n := by rw [h_norm_rpow]
  -- Step B: h_gen n ≤ (L/2)·n eventually, where h_gen n = L·n + 2·√n·log n
  have h_le_half : ∀ᶠ n : ℕ in atTop,
      L * n + 2 * Real.sqrt n * Real.log n ≤ (L / 2) * n := by
    filter_upwards [hlog_le, eventually_ge_atTop 1] with n hlog hn1
    have hsqrt_nn : 0 ≤ Real.sqrt n := Real.sqrt_nonneg n
    have hlognn : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn1)
    have hsq : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt (by exact_mod_cast Nat.zero_le n)
    nlinarith [hlog, hsqrt_nn, hlognn, hL_neg]
  -- Step C: h_gen n → atBot
  have h_tendsto_atBot : Tendsto (fun n : ℕ => L * n + 2 * Real.sqrt n * Real.log n) atTop atBot := by
    have hL2 : L / 2 < 0 := by linarith [hL_neg]
    have upper : Tendsto (fun n : ℕ => (L / 2) * (n : ℝ)) atTop atBot := by
      rw [tendsto_const_mul_atBot_of_neg hL2]
      exact tendsto_natCast_atTop_atTop
    exact tendsto_atBot_mono' atTop h_le_half upper
  -- Step D: log bound on the product
  have L_eq : Real.log (4 * β) = Real.log 4 + Real.log β :=
    Real.log_mul (by norm_num) hβ_ne
  have lcm_mul_pow_le_exp : ∀ᶠ n : ℕ in atTop,
      (lcmUpto n : ℝ) * β ^ n ≤ Real.exp (L * n + 2 * Real.sqrt n * Real.log n) := by
    filter_upwards [eventually_ge_atTop 1] with n hn1
    have hlcm_pos : (0 : ℝ) < lcmUpto n :=
      Nat.cast_pos.mpr (Nat.pos_of_ne_zero (lcmUpto_ne_zero n))
    have hβn_pos : 0 < β ^ n := pow_pos hβ0 n
    have hprod_pos : 0 < (lcmUpto n : ℝ) * β ^ n := mul_pos hlcm_pos hβn_pos
    have hpsi_bound : Real.log (lcmUpto n) ≤ Real.log 4 * n + 2 * Real.sqrt n * Real.log n :=
      log_lcmUpto_le_sharp n hn1
    have hlog_prod : Real.log ((lcmUpto n : ℝ) * β ^ n) =
        Real.log (lcmUpto n) + n * Real.log β := by
      rw [Real.log_mul (ne_of_gt hlcm_pos) (ne_of_gt hβn_pos), Real.log_pow]
    have hlog_le : Real.log ((lcmUpto n : ℝ) * β ^ n) ≤
        L * n + 2 * Real.sqrt n * Real.log n := by
      rw [hlog_prod]
      have : L * n = Real.log 4 * n + Real.log β * n := by
        rw [hL_def, L_eq]; ring
      linarith [hpsi_bound]
    exact (Real.log_le_iff_le_exp hprod_pos).mp hlog_le
  -- Step E: squeeze between 0 and exp(h_gen n)
  have hexp : Tendsto (fun n : ℕ => Real.exp (L * n + 2 * Real.sqrt n * Real.log n)) atTop (nhds 0) :=
    Real.tendsto_exp_atBot.comp h_tendsto_atBot
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hexp
    (Eventually.of_forall (fun n => mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hβ0.le n)))
    lcm_mul_pow_le_exp

/-! ## The two main theorems -/

/-- There is an explicit geometric majorant `A·ρⁿ` (ρ<1) for `lcmUpto n · (3−2√2)ⁿ`. -/
theorem exists_geom_bound :
    ∃ A ρ : ℝ, 0 < A ∧ 0 < ρ ∧ ρ < 1 ∧
      ∀ n : ℕ, (lcmUpto n : ℝ) * (3 - 2 * Real.sqrt 2) ^ n ≤ A * ρ ^ n := by
  -- Let c = 3 − 2√2.  Pick ρ strictly between 4c and 1.
  set c := (3 : ℝ) - 2 * Real.sqrt 2
  obtain ⟨ρ, h4c_ρ, hρ1⟩ := exists_between h4c_lt_one'
  -- β := c/ρ satisfies 0 < β and 4β < 1
  have hρ_pos : 0 < ρ := by linarith [h4c_pos']
  have hβ_def : c / ρ > 0 := div_pos hc_pos' hρ_pos
  have h4β : 4 * (c / ρ) < 1 := by
    have hc_lt : 4 * c < ρ := h4c_ρ
    have : 4 * c / ρ < 1 := (div_lt_one hρ_pos).mpr hc_lt
    calc 4 * (c / ρ) = 4 * c / ρ := by ring
      _ < 1 := this
  -- The sequence (lcmUpto n)·(c/ρ)^n tends to 0
  have htend : Tendsto (fun n : ℕ => (lcmUpto n : ℝ) * (c / ρ) ^ n) atTop (nhds 0) :=
    geom_lcm_tendsto_zero_gen (c / ρ) hβ_def h4β
  -- Its range is bounded above: ∃ A, ∀ n, (lcmUpto n)·(c/ρ)^n ≤ A
  have hbdd : BddAbove (Set.range (fun n : ℕ => (lcmUpto n : ℝ) * (c / ρ) ^ n)) :=
    htend.bddAbove_range
  obtain ⟨A, hA⟩ := hbdd
  -- Make A ≥ 1 so that A > 0
  refine ⟨max A 1, ρ, ?_, hρ_pos, hρ1, ?_⟩
  · linarith [le_max_right A 1]
  intro n
  -- (lcmUpto n)·cⁿ = ((lcmUpto n)·(c/ρ)^n)·ρⁿ ≤ A·ρⁿ
  have hrn : (c / ρ) ^ n * ρ ^ n = c ^ n := by
    rw [← mul_pow, div_mul_cancel₀ c (ne_of_gt hρ_pos)]
  have hbound : (lcmUpto n : ℝ) * (c / ρ) ^ n ≤ A :=
    hA (Set.mem_range.mpr ⟨n, rfl⟩)
  have hrn_nn : 0 ≤ ρ ^ n := pow_nonneg hρ_pos.le n
  calc (lcmUpto n : ℝ) * c ^ n
      = (lcmUpto n : ℝ) * ((c / ρ) ^ n * ρ ^ n) := by
        rw [hrn]
    _ = ((lcmUpto n : ℝ) * (c / ρ) ^ n) * ρ ^ n := by ring
    _ ≤ A * ρ ^ n := by
        apply mul_le_mul_of_nonneg_right hbound hrn_nn
    _ ≤ max A 1 * ρ ^ n := by
        apply mul_le_mul_of_nonneg_right (le_max_left A 1) hrn_nn

/-- Consequence: the diagonal-integral form `Dₙ·Iₙ` has an explicit geometric majorant — the
`hsmall` shape (with `aₙ = Dₙ·cₙ`, `bₙ = −uₙ`, `θ = log 2`, since `|aₙ·log2 − bₙ| = Dₙ·Iₙ`). -/
theorem exists_hsmall_bound :
    ∃ A ρ : ℝ, 0 < A ∧ 0 < ρ ∧ ρ < 1 ∧
      ∀ n : ℕ, (lcmUpto n : ℝ) * I n ≤ A * ρ ^ n := by
  obtain ⟨A, ρ, hA, hρ, hρ1, hgeom⟩ := exists_geom_bound
  -- log 2 > 0
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  -- Use A' = A * log 2
  refine ⟨A * Real.log 2, ρ, mul_pos hA hlog2, hρ, hρ1, fun n => ?_⟩
  calc (lcmUpto n : ℝ) * I n
      ≤ (lcmUpto n : ℝ) * ((3 - 2 * Real.sqrt 2) ^ n * Real.log 2) := D_mul_I_le_geom n
    _ = ((lcmUpto n : ℝ) * (3 - 2 * Real.sqrt 2) ^ n) * Real.log 2 := by ring
    _ ≤ (A * ρ ^ n) * Real.log 2 := by
        apply mul_le_mul_of_nonneg_right (hgeom n) (le_of_lt hlog2)
    _ = A * Real.log 2 * ρ ^ n := by ring

end DiagonalIntegralLog2
