import Propositio.NumberTheory.Diophantine.WeightedDiagonalLog43
import Propositio.NumberTheory.Diophantine.WeightedDiagonalLog43Decomp
import Propositio.NumberTheory.Diophantine.WeightedDiagonalLog43Hsmall
import Propositio.NumberTheory.Diophantine.DiagonalIntegralLog2Hsmall
import Propositio.NumberTheory.Diophantine.IrrMeasureCombination
import Mathlib.Tactic

/-!
# Conditional effective irrationality measure of `log(4/3)`

Assembles the proved analytic ingredients of the weighted-diagonal construction into a CONDITIONAL
effective irrationality measure of `log(4/3)`, assuming the two arithmetic facts:
* `hint : ∀ n, ∃ m : ℤ, Jα n = m`  — the log-coefficient `α₁(n)` is an integer
  (`= Pₙ(7) = Σ C(n,k)C(n+k,k)3ᵏ`; the Legendre/Zeilberger brick), and
* `hden_q : ∀ n, ∃ m : ℤ, (lcmUpto n)·JP n = m` — `lcm(1..n)` clears `Pₙ`'s denominator (2,3-adic).

Everything else is proved here axiom-clean and reused from the construction: the decomposition
`J_decomp`, the size bound `Jα n ≤ 14ⁿ`, the `hsmall` geometric majorant (`J_le` + the generic
`geom_lcm_tendsto_zero_gen`), positivity (`Jα_pos`, `J_pos`), and the Casoratian (`casoratian_nonzero`).
Feeds `IrrMeasureCombination.irrationality_measure_le`.
-/

namespace WeightedDiagonalLog43

open Filter LcmGrowthBound

/-- Size bound `α₁(n) ≤ 14ⁿ` (since the dominant root is `7+4√3 < 14`), by induction off the
recurrence dropping the negative term and `7(2n+3)/(n+2) ≤ 14`. -/
theorem Jα_le_pow (n : ℕ) : Jα n ≤ 14 ^ n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => norm_num [Jα]
    | 1 => norm_num [Jα]
    | (m + 2) =>
      have ihm1 := ih (m + 1) (by omega)
      have hposm : 0 ≤ Jα m := le_of_lt (Jα_pos m)
      have hposm1 : 0 ≤ Jα (m + 1) := le_of_lt (Jα_pos (m + 1))
      have hrec := Jα_rec m
      have hm2 : (0 : ℚ) < (m : ℚ) + 2 := by positivity
      have h1 : ((m : ℚ) + 2) * Jα (m + 2) ≤ 7 * (2 * (m : ℚ) + 3) * Jα (m + 1) := by
        rw [hrec]; nlinarith [hposm]
      have h2 : 7 * (2 * (m : ℚ) + 3) * Jα (m + 1) ≤ ((m : ℚ) + 2) * (14 * Jα (m + 1)) := by
        nlinarith [hposm1]
      have h4 : Jα (m + 2) ≤ 14 * Jα (m + 1) := le_of_mul_le_mul_left (le_trans h1 h2) hm2
      calc Jα (m + 2) ≤ 14 * Jα (m + 1) := h4
        _ ≤ 14 * 14 ^ (m + 1) := by nlinarith [ihm1]
        _ = 14 ^ (m + 2) := by ring

/-- `0 < 2·(7−4√3)` and `4·(2·(7−4√3)) < 1` (so the generic geom lemma applies with `β = 2ρ`). -/
private theorem two_rho_pos : (0 : ℝ) < 2 * (7 - 4 * Real.sqrt 3) := by
  nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num), Real.sqrt_nonneg 3]
private theorem four_two_rho_lt_one : 4 * (2 * (7 - 4 * Real.sqrt 3)) < 1 := by
  nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num), Real.sqrt_nonneg 3]

/-- **The `hsmall` geometric majorant** `lcm(1..n)·Jₙ ≤ A·(1/2)ⁿ`.  From `J_le`
(`Jₙ ≤ ρⁿ·log(4/3)`, `ρ=7−4√3`) and `lcm(1..n)·(2ρ)ⁿ ≤ A₀` (bounded, since `4·2ρ<1`):
`lcm·Jₙ ≤ (lcm·(2ρ)ⁿ)·(1/2)ⁿ·log(4/3) ≤ A₀·log(4/3)·(1/2)ⁿ`. -/
theorem exists_hsmall_bound_J :
    ∃ A : ℝ, 0 < A ∧ ∀ n, (lcmUpto n : ℝ) * J n ≤ A * (1 / 2) ^ n := by
  have htend := DiagonalIntegralLog2.geom_lcm_tendsto_zero_gen (2 * (7 - 4 * Real.sqrt 3))
    two_rho_pos four_two_rho_lt_one
  obtain ⟨A0, hA0⟩ := htend.bddAbove_range
  have hlog43 : 0 < Real.log (4 / 3) := Real.log_pos (by norm_num)
  have hA0pos : (0 : ℝ) < A0 := by
    have : (lcmUpto 0 : ℝ) * (2 * (7 - 4 * Real.sqrt 3)) ^ 0 ≤ A0 := hA0 ⟨0, rfl⟩
    simp only [pow_zero, mul_one] at this
    have : (1 : ℝ) ≤ A0 := by simpa [lcmUpto] using this
    linarith
  refine ⟨A0 * Real.log (4 / 3), by positivity, fun n => ?_⟩
  have hlcmnn : (0 : ℝ) ≤ (lcmUpto n : ℝ) := by positivity
  have hbnd : (lcmUpto n : ℝ) * (2 * (7 - 4 * Real.sqrt 3)) ^ n ≤ A0 := hA0 ⟨n, rfl⟩
  -- ρⁿ = (2ρ)ⁿ·(1/2)ⁿ
  have hρsplit : (7 - 4 * Real.sqrt 3) ^ n
      = (2 * (7 - 4 * Real.sqrt 3)) ^ n * (1 / 2) ^ n := by
    rw [← mul_pow]; congr 1; ring
  calc (lcmUpto n : ℝ) * J n
      ≤ (lcmUpto n : ℝ) * ((7 - 4 * Real.sqrt 3) ^ n * Real.log (4 / 3)) :=
        mul_le_mul_of_nonneg_left (J_le n) hlcmnn
    _ = ((lcmUpto n : ℝ) * (2 * (7 - 4 * Real.sqrt 3)) ^ n) * (1 / 2) ^ n * Real.log (4 / 3) := by
        rw [hρsplit]; ring
    _ ≤ A0 * (1 / 2) ^ n * Real.log (4 / 3) := by
        have h12 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ n := by positivity
        have := mul_le_mul_of_nonneg_right hbnd h12
        nlinarith [this, hlog43, pow_nonneg (by norm_num : (0:ℝ) ≤ 1/2) n,
          mul_nonneg hlcmnn (pow_nonneg two_rho_pos.le n)]
    _ = A0 * Real.log (4 / 3) * (1 / 2) ^ n := by ring

/-- **Conditional effective irrationality measure of `log(4/3)`.**  Assuming `α₁(n) ∈ ℤ` (`hint`)
and `lcm(1..n)` clears `Pₙ`'s denominator (`hden_q`), `log(4/3)` has an effective irrationality
measure `C/q^(1+logQ/logρ⁻¹) ≤ |log(4/3) − p/q|`. -/
theorem log43_measure_of_int_den
    (hint : ∀ n, ∃ m : ℤ, Jα n = (m : ℚ))
    (hden_q : ∀ n, ∃ m : ℤ, (lcmUpto n : ℚ) * JP n = (m : ℚ)) :
    ∃ A ρ Q : ℝ, 0 < A ∧ 0 < ρ ∧ ρ < 1 ∧ 1 < Q ∧
      ∃ C > 0, ∀ (p q : ℤ), 1 ≤ q → (1 : ℝ) ≤ 2 * A * q →
        C / (q : ℝ) ^ (1 + Real.log Q / Real.log ρ⁻¹) ≤ |Real.log (4 / 3) - (p : ℝ) / q| := by
  -- integer sequences
  set a : ℕ → ℤ := fun n => (lcmUpto n : ℤ) * (hint n).choose with ha
  set b : ℕ → ℤ := fun n => -(hden_q n).choose with hb
  -- the integer value of α₁(n) and Pₙ-clearing
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
  -- hsmall majorant
  obtain ⟨A, hApos, hAbound⟩ := exists_hsmall_bound_J
  -- denominator base Q for hden
  set Q : ℝ := 14 * Real.exp (Real.log 4 + 4) with hQdef
  have hQ1 : 1 < Q := by
    rw [hQdef]
    have : (1 : ℝ) ≤ Real.exp (Real.log 4 + 4) := Real.one_le_exp (by positivity)
    nlinarith [this]
  refine ⟨A, 1 / 2, Q, hApos, by norm_num, by norm_num, hQ1, ?_⟩
  apply IrrMeasureCombination.irrationality_measure_le (Real.log (4 / 3)) a b A 1 (1 / 2) Q
    hApos (by norm_num) (by norm_num) (by norm_num) hQ1
  · -- hsmall : |a n·θ − b n| ≤ A·(1/2)ⁿ
    intro n
    have key : (a n : ℝ) * Real.log (4 / 3) - (b n : ℝ) = (lcmUpto n : ℝ) * J n := by
      simp only [ha, hb, Int.cast_neg, Int.cast_mul, Int.cast_natCast]
      rw [hαval n, hPval n, J_decomp n]; ring
    have hpos : 0 ≤ (a n : ℝ) * Real.log (4 / 3) - (b n : ℝ) := by
      rw [key]; exact mul_nonneg (by positivity) (le_of_lt (J_pos n))
    rw [abs_of_nonneg hpos, key]; exact hAbound n
  · -- hapos : 0 < a n
    intro n
    have hαpos : (0 : ℤ) < (hint n).choose := by
      have : (0 : ℚ) < ((hint n).choose : ℚ) := by rw [hαvalQ n]; exact_mod_cast Jα_pos n
      exact_mod_cast this
    exact mul_pos (hDposZ n) hαpos
  · -- hden : (a n : ℝ) ≤ 1 · Qⁿ
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
  · -- hdet : a n · b (n+1) ≠ a (n+1) · b n
    intro n hcontra
    apply casoratian_nonzero n
    -- from the ℤ contradiction, derive Jα n · JP(n+1) − Jα(n+1)·JP n = 0
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
    -- transfer to ℚ
    have : (Jα n * JP (n + 1) - Jα (n + 1) * JP n : ℚ) = 0 := by exact_mod_cast hcas
    linarith [this]

end WeightedDiagonalLog43
