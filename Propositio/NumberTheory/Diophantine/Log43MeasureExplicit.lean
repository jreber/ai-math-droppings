import Propositio.NumberTheory.Diophantine.WeightedDiagonalLog43AResRec
import Propositio.NumberTheory.Diophantine.WeightedDiagonalLog43Measure
import Propositio.NumberTheory.Diophantine.WeightedDiagonalLog43Integrality
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

/-!
# An EXPLICIT NUMERIC irrationality-measure exponent for `log(4/3)`

The unconditional effective irrationality measure of `log(4/3)` proved in
`WeightedDiagonalLog43AResRec.log43_measure_unconditional` is stated with the *symbolic* exponent
`1 + Real.log Q / Real.log ρ⁻¹`, where the construction's concrete witnesses are
`ρ = 1/2` and `Q = 14·exp(log 4 + 4) = 56·e⁴`.

This file turns that symbolic exponent into a concrete numeral.  Numerically

```
s        = log Q / log 2 = (log 56 + 4)/log 2 ≈ 11.578
μ_true   = 1 + s         ≈ 12.578
```

so the smallest clean integer upper bound is `μ₀ = 13`.  The exponent bound is proved with explicit
rational/numeric log bounds:

* `Q = 56·e⁴ ≤ 4096 = 2¹²`  (since `e⁴ = (e)⁴ < 2.7182818286⁴ < 55`, using `Real.exp_one_lt_d9`),
* hence `log Q ≤ log(2¹²) = 12·log 2`, i.e. `s = log Q / log 2 ≤ 12`, i.e. `1 + s ≤ 13`.

Then, since `q ≥ 1`, `(q:ℝ)^(1+s) ≤ (q:ℝ)^13` (monotonicity of `rpow` in the exponent for base
`≥ 1`), so the construction's lower bound `C / q^(1+s)` dominates `C / q^13`, yielding the explicit
measure with exponent `13`.

The proof re-runs the analytic assembly (`IrrMeasureCombination.irrationality_measure_le_const`, the
de-existentialized twin of `irrationality_measure_le`) with the construction's concrete witnesses, so
the constant `C` is exposed and the exponent is a concrete numeral — both new content over the
existential `log43_measure_unconditional`.
-/

namespace WeightedDiagonalLog43

open Filter LcmGrowthBound

/-- **Explicit-exponent effective irrationality measure of `log(4/3)`.**
There exist `A > 0` and `C > 0` such that for all integers `p, q` with `q ≥ 1` and `1 ≤ 2·A·q`,
`C / q¹³ ≤ |log(4/3) − p/q|`.  The exponent `13` is an explicit numeral upper bound for the
construction's true exponent `1 + log Q / log ρ⁻¹ ≈ 12.578` (`ρ = 1/2`, `Q = 56·e⁴`). -/
theorem log43_irrationalityMeasure_le :
    ∃ A C : ℝ, 0 < A ∧ 0 < C ∧ ∀ (p q : ℤ), 1 ≤ q → (1 : ℝ) ≤ 2 * A * q →
      C / (q : ℝ) ^ (13 : ℝ) ≤ |Real.log (4 / 3) - (p : ℝ) / q| := by
  -- The two arithmetic inputs, now unconditional.
  have hint : ∀ n, ∃ m : ℤ, Jα n = (m : ℚ) := Jα_int
  have hden_q : ∀ n, ∃ m : ℤ, (lcmUpto n : ℚ) * JP n = (m : ℚ) := fun n => by
    rw [JP_eq_Pexpl aRes_recurrence_holds n]; exact lcmUpto_mul_Pexpl_int n
  -- Integer auxiliary sequences (as in `log43_measure_of_int_den`).
  set a : ℕ → ℤ := fun n => (lcmUpto n : ℤ) * (hint n).choose with ha
  set b : ℕ → ℤ := fun n => -(hden_q n).choose with hb
  have hαval : ∀ n, ((hint n).choose : ℝ) = (Jα n : ℝ) := fun n => by
    have h : (Jα n : ℝ) = ((hint n).choose : ℝ) := by exact_mod_cast (hint n).choose_spec
    linarith [h]
  have hαvalQ : ∀ n, ((hint n).choose : ℚ) = Jα n := fun n => ((hint n).choose_spec).symm
  have hPval : ∀ n, ((hden_q n).choose : ℝ) = (lcmUpto n : ℝ) * (JP n : ℝ) := fun n => by
    have h : (lcmUpto n : ℝ) * (JP n : ℝ) = ((hden_q n).choose : ℝ) := by
      exact_mod_cast (hden_q n).choose_spec
    linarith [h]
  have hDposZ : ∀ n, (0 : ℤ) < (lcmUpto n : ℤ) := fun n => by
    exact_mod_cast Nat.pos_of_ne_zero (lcmUpto_ne_zero n)
  -- The `hsmall` geometric majorant, with witness `A`.
  obtain ⟨A, hApos, hAbound⟩ := exists_hsmall_bound_J
  -- The denominator base `Q = 14·exp(log 4 + 4) = 56·e⁴`.
  set Q : ℝ := 14 * Real.exp (Real.log 4 + 4) with hQdef
  have hQ1 : 1 < Q := by
    rw [hQdef]
    have : (1 : ℝ) ≤ Real.exp (Real.log 4 + 4) := Real.one_le_exp (by positivity)
    nlinarith [this]
  -- The four hypotheses for `irrationality_measure_le_const`.
  have hsmall : ∀ n, |(a n : ℝ) * Real.log (4 / 3) - b n| ≤ A * (1 / 2) ^ n := by
    intro n
    have key : (a n : ℝ) * Real.log (4 / 3) - (b n : ℝ) = (lcmUpto n : ℝ) * J n := by
      simp only [ha, hb, Int.cast_neg, Int.cast_mul, Int.cast_natCast]
      rw [hαval n, hPval n, J_decomp n]; ring
    have hpos : 0 ≤ (a n : ℝ) * Real.log (4 / 3) - (b n : ℝ) := by
      rw [key]; exact mul_nonneg (by positivity) (le_of_lt (J_pos n))
    rw [abs_of_nonneg hpos, key]; exact hAbound n
  have hapos : ∀ n, 0 < a n := by
    intro n
    have hαpos : (0 : ℤ) < (hint n).choose := by
      have : (0 : ℚ) < ((hint n).choose : ℚ) := by rw [hαvalQ n]; exact_mod_cast Jα_pos n
      exact_mod_cast this
    exact mul_pos (hDposZ n) hαpos
  have hden : ∀ n, (a n : ℝ) ≤ 1 * Q ^ n := by
    intro n
    rw [one_mul]
    have hαle : (Jα n : ℝ) ≤ 14 ^ n := by exact_mod_cast Jα_le_pow n
    have hlcm : (lcmUpto n : ℝ) ≤ Real.exp ((Real.log 4 + 4) * n) := lcmUpto_le n
    have haval : (a n : ℝ) = (lcmUpto n : ℝ) * (Jα n : ℝ) := by
      simp only [ha, Int.cast_mul, Int.cast_natCast, hαval n]
    rw [haval]
    have hQpow : Q ^ n = Real.exp ((Real.log 4 + 4) * n) * 14 ^ n := by
      rw [hQdef, mul_pow, ← Real.exp_nat_mul, mul_comm (n : ℝ) (Real.log 4 + 4)]
      ring
    rw [hQpow]
    have h14nn : (0 : ℝ) ≤ (14 : ℝ) ^ n := by positivity
    have hlcmnn : (0 : ℝ) ≤ (lcmUpto n : ℝ) := by positivity
    calc (lcmUpto n : ℝ) * (Jα n : ℝ)
        ≤ (lcmUpto n : ℝ) * 14 ^ n := mul_le_mul_of_nonneg_left hαle hlcmnn
      _ ≤ Real.exp ((Real.log 4 + 4) * n) * 14 ^ n := mul_le_mul_of_nonneg_right hlcm h14nn
  have hdet : ∀ n, a n * b (n + 1) ≠ a (n + 1) * b n := by
    intro n hcontra
    apply casoratian_nonzero n
    have hreal : (a n : ℝ) * (b (n + 1) : ℝ) = (a (n + 1) : ℝ) * (b n : ℝ) := by
      exact_mod_cast hcontra
    have haR : ∀ m, (a m : ℝ) = (lcmUpto m : ℝ) * (Jα m : ℝ) := fun m => by
      simp only [ha, Int.cast_mul, Int.cast_natCast, hαval m]
    have hbR : ∀ m, (b m : ℝ) = -((lcmUpto m : ℝ) * (JP m : ℝ)) := fun m => by
      simp only [hb, Int.cast_neg, hPval m]
    rw [haR n, haR (n + 1), hbR n, hbR (n + 1)] at hreal
    have hDn : (lcmUpto n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (lcmUpto_ne_zero n)
    have hDn1 : (lcmUpto (n + 1) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (lcmUpto_ne_zero (n + 1))
    have hcas : (Jα n : ℝ) * (JP (n + 1) : ℝ) - (Jα (n + 1) : ℝ) * (JP n : ℝ) = 0 := by
      have hfac : (lcmUpto n : ℝ) * (lcmUpto (n + 1) : ℝ)
          * ((Jα n : ℝ) * (JP (n + 1) : ℝ) - (Jα (n + 1) : ℝ) * (JP n : ℝ)) = 0 := by
        nlinarith [hreal]
      rcases mul_eq_zero.mp hfac with h | h
      · exact absurd h (mul_ne_zero hDn hDn1)
      · exact h
    have hQzero : (Jα n * JP (n + 1) - Jα (n + 1) * JP n : ℚ) = 0 := by exact_mod_cast hcas
    linarith [hQzero]
  -- The de-existentialized measure, with the exposed constant and symbolic exponent.
  have hmeas := IrrMeasureCombination.irrationality_measure_le_const
    (Real.log (4 / 3)) a b A 1 (1 / 2) Q hApos (by norm_num) (by norm_num) (by norm_num) hQ1
    hsmall hapos hden hdet
  -- Name the symbolic exponent slope `s = log Q / log 2`.
  set s : ℝ := Real.log Q / Real.log ((1 / 2 : ℝ))⁻¹ with hsdef
  -- Bound `s ≤ 12`, hence `1 + s ≤ 13`.
  have hinv : ((1 / 2 : ℝ))⁻¹ = 2 := by norm_num
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hQpos : 0 < Q := by linarith
  have hQval : Q = 56 * Real.exp 4 := by
    rw [hQdef, Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 4)]; ring
  have hexp4 : Real.exp 4 ≤ 55 := by
    have h1 : Real.exp 4 = Real.exp 1 ^ 4 := by
      rw [Real.exp_one_pow]; norm_num
    rw [h1]
    have h2 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
    have h3 : (0 : ℝ) ≤ Real.exp 1 := (Real.exp_pos 1).le
    calc Real.exp 1 ^ 4 ≤ (2.7182818286 : ℝ) ^ 4 := pow_le_pow_left₀ h3 h2.le 4
      _ ≤ 55 := by norm_num
  have hQle : Q ≤ 4096 := by rw [hQval]; nlinarith [hexp4, Real.exp_pos 4]
  have hlogQ : Real.log Q ≤ 12 * Real.log 2 := by
    have h4096 : (4096 : ℝ) = 2 ^ 12 := by norm_num
    have hmono := (Real.log_le_log_iff hQpos (by norm_num)).mpr hQle
    rw [h4096, Real.log_pow] at hmono
    push_cast at hmono; linarith [hmono]
  have hs_le : s ≤ 12 := by
    rw [hsdef, hinv, div_le_iff₀ hlog2pos]
    linarith [hlogQ]
  -- Package: provide `A` and the exposed constant; drop the exponent from `1 + s` to `13`.
  refine ⟨A, 1 / (2 * 1 * Q ^ 2 * (2 * A) ^ s), hApos, by positivity, ?_⟩
  intro p q hq1 hAq
  have hbound := hmeas p q hq1 hAq
  have hq1R : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq1
  have hqRpos : (0 : ℝ) < (q : ℝ) := by linarith
  have hmono13 : (q : ℝ) ^ (1 + s) ≤ (q : ℝ) ^ (13 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hq1R (by linarith [hs_le])
  have hden_pos : (0 : ℝ) < (q : ℝ) ^ (1 + s) := Real.rpow_pos_of_pos hqRpos _
  have hC0 : (0 : ℝ) ≤ 1 / (2 * 1 * Q ^ 2 * (2 * A) ^ s) := by positivity
  have hdrop : 1 / (2 * 1 * Q ^ 2 * (2 * A) ^ s) / (q : ℝ) ^ (13 : ℝ)
      ≤ 1 / (2 * 1 * Q ^ 2 * (2 * A) ^ s) / (q : ℝ) ^ (1 + s) :=
    div_le_div_of_nonneg_left hC0 hden_pos hmono13
  exact le_trans hdrop hbound

end WeightedDiagonalLog43
