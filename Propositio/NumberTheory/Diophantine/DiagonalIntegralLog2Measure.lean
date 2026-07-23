import Propositio.NumberTheory.Diophantine.DiagonalIntegralLog2IntForm
import Propositio.NumberTheory.Diophantine.DiagonalIntegralLog2CoeffBound
import Propositio.NumberTheory.Diophantine.DiagonalIntegralLog2Hsmall
import Propositio.NumberTheory.Diophantine.PadeCasoratian
import Propositio.NumberTheory.Diophantine.IrrMeasureCombination
import Mathlib.Tactic

/-!
# Conditional full effective measure of `log 2`

This file composes the proved/reduced ingredients into a CONDITIONAL effective irrationality
measure of `log 2`: assuming the Padé recurrence on the construction's denominator `cₙ` and
rational part `rₙ`, `log 2` has an effective measure via `IrrMeasureCombination.irrationality_measure_le`.

It isolates the rational-part sequence `r n` and the two connection identities
`I n = cₙ·log2 + r n` and `u n = Dₙ·r n`, which are the glue between the integer linear form and
the abstract `PadeCasoratian` non-vanishing.
-/

namespace DiagonalIntegralLog2

open Polynomial LcmGrowthBound

/-- The rational part `rₙ` of the diagonal integral (matching `I_eq_rat_add_log`). -/
noncomputable def r (n : ℕ) : ℝ :=
  ∑ k ∈ (Finset.range (2 * n + 1)).erase n,
    (((X - 1 : ℝ[X]) ^ n * (2 - X) ^ n).coeff k) * ((2 : ℝ) ^ ((k : ℤ) - n) - 1) / ((k : ℤ) - n)

/-- `Iₙ = cₙ·log2 + rₙ` with `cₙ = (intCoeff n n : ℝ)`. -/
theorem I_eq_c_log2_add_r (n : ℕ) :
    I n = (intCoeff n n : ℝ) * Real.log 2 + r n := by
  rw [I_eq_rat_add_log, r, intCoeff_cast]

/-- `Dₙ·rₙ ∈ ℤ` and equals the integer-linear-form witness `uₙ`: more precisely
`Dₙ·Iₙ = (Dₙ·cₙ)·log2 + Dₙ·rₙ`, so `Dₙ·rₙ` is the rational/integer part. -/
theorem D_mul_I_eq (n : ℕ) :
    (lcmUpto n : ℝ) * I n = ((lcmUpto n : ℤ) * intCoeff n n : ℝ) * Real.log 2
      + (lcmUpto n : ℝ) * r n := by
  rw [I_eq_c_log2_add_r]; push_cast; ring

/-- The integer-linear-form witness satisfies `uₙ = Dₙ·rₙ` (as reals). -/
theorem u_eq_D_mul_r (n : ℕ) :
    (((D_mul_I_int_form n).choose : ℤ) : ℝ) = (lcmUpto n : ℝ) * r n := by
  have hspec := (D_mul_I_int_form n).choose_spec
  have heq := D_mul_I_eq n
  linarith [hspec, heq]

/-! ### Concrete base values (for the recurrence base case and `W₀`) -/

theorem intCoeff_zero_zero : intCoeff 0 0 = 1 := by
  simp [intCoeff, Polynomial.coeff_one]

private theorem coeff_quad (k : ℕ) (v : ℤ) (hv : (-X ^ 2 + 3 * X - 2 : ℤ[X]).coeff k = v) :
    intCoeff 1 k = v := by
  have he : ((X - 1 : ℤ[X]) ^ 1 * (2 - X) ^ 1) = -X ^ 2 + 3 * X - 2 := by ring
  rw [intCoeff, he, hv]

theorem intCoeff_one_one : intCoeff 1 1 = 3 := coeff_quad 1 3 (by
  simp [Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_neg,
    Polynomial.coeff_X_pow, Polynomial.coeff_ofNat_mul, Polynomial.coeff_X_one])

theorem intCoeff_one_zero : intCoeff 1 0 = -2 := coeff_quad 0 (-2) (by
  simp [Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_neg,
    Polynomial.coeff_X_pow, Polynomial.coeff_ofNat_mul, Polynomial.coeff_X])

theorem intCoeff_one_two : intCoeff 1 2 = -1 := coeff_quad 2 (-1) (by
  simp [Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_neg,
    Polynomial.coeff_X_pow, Polynomial.coeff_ofNat_mul, Polynomial.coeff_X])

/-- The real coefficient of `(X−1)ⁿ(2−X)ⁿ` (matching `r`) is `(intCoeff n k : ℝ)`. -/
theorem rterm_cast (n k : ℕ) :
    (((X - 1 : ℝ[X]) ^ n * (2 - X) ^ n).coeff k) = (intCoeff n k : ℝ) := intCoeff_cast n k

theorem r_zero : r 0 = 0 := by simp [r]

theorem r_one : r 1 = -2 := by
  have hset : (Finset.range 3).erase 1 = {0, 2} := by decide
  simp only [r, show 2 * 1 + 1 = 3 from rfl, hset]
  rw [Finset.sum_insert (by decide), Finset.sum_singleton, rterm_cast, rterm_cast,
    intCoeff_one_zero, intCoeff_one_two]
  norm_num

/-- **Linear independence of `1, log 2` over `ℚ`** (from `log_two_irrational`): if
`P·log2 + s = 0` with `P ∈ ℤ`, `s ∈ ℚ`, then `P = 0` (and hence `s = 0`).  This is the key step
for reducing the conditional measure's two recurrence hypotheses (`cₙ`, `rₙ`) to the single
integral recurrence: substituting `Iₙ = cₙ·log2 + rₙ` splits a recurrence on `Iₙ` into a
`log2`-coefficient part (forcing the `cₙ` recurrence) and a rational part (the `rₙ` recurrence). -/
theorem log2_lin_indep (P : ℤ) (s : ℚ) (h : (P : ℝ) * Real.log 2 + (s : ℝ) = 0) : P = 0 := by
  by_contra hP
  have hPR : (P : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hP
  refine log_two_irrational ⟨-s / P, ?_⟩
  push_cast
  field_simp
  linarith [h]

/-! ### The conditional full effective measure -/

/-- The engine's coefficient sequence `aₙ = Dₙ·cₙ`. -/
noncomputable def aSeq (n : ℕ) : ℤ := (lcmUpto n : ℤ) * intCoeff n n
/-- The engine's `bₙ = −uₙ`. -/
noncomputable def bSeq (n : ℕ) : ℤ := -(D_mul_I_int_form n).choose

/-- **Conditional full effective irrationality measure of `log 2`.**  Assuming the Padé recurrence
on `cₙ = intCoeff n n` and on the rational part `rₙ`, `log 2` has an effective irrationality
measure: there are `A, ρ∈(0,1), Q>1` and `C>0` with `C/qᵘ ≤ |log2 − p/q|`, `u = 1+logQ/log ρ⁻¹`.
The recurrence is the single remaining unproved input (verified numerically; a creative-telescoping
target). -/
theorem log2_measure_of_recurrence
    (hrec_c : PadeCasoratian.Recurrence (fun n => (intCoeff n n : ℝ)))
    (hrec_r : PadeCasoratian.Recurrence r) :
    ∃ A ρ Q : ℝ, 0 < A ∧ 0 < ρ ∧ ρ < 1 ∧ 1 < Q ∧
      ∃ C > 0, ∀ (p q : ℤ), 1 ≤ q → (1 : ℝ) ≤ 2 * A * q →
        C / (q : ℝ) ^ (1 + Real.log Q / Real.log ρ⁻¹) ≤ |Real.log 2 - (p : ℝ) / q| := by
  obtain ⟨A, ρ, hA, hρ0, hρ1, hbound⟩ := exists_hsmall_bound
  -- cₙ > 0 from the recurrence
  have hcpos : ∀ n, (0 : ℝ) < (intCoeff n n : ℝ) :=
    PadeCasoratian.rec_pos (fun n => (intCoeff n n : ℝ)) hrec_c
      (by simp only [intCoeff_zero_zero]; norm_num)
      (by simp only [intCoeff_zero_zero, intCoeff_one_one]; norm_num)
  have hcposZ : ∀ n, 0 < intCoeff n n := fun n => by exact_mod_cast hcpos n
  have hDposZ : ∀ n, (0 : ℤ) < (lcmUpto n : ℤ) := fun n => by
    have := Nat.pos_of_ne_zero (lcmUpto_ne_zero n); exact_mod_cast this
  -- set Q and B for the denominator bound
  set Q : ℝ := 6 * Real.exp (Real.log 4 + 4) with hQdef
  have hQ1 : 1 < Q := by
    rw [hQdef]
    have : (1 : ℝ) ≤ Real.exp (Real.log 4 + 4) := Real.one_le_exp (by positivity)
    nlinarith [this]
  refine ⟨A, ρ, Q, hA, hρ0, hρ1, hQ1, ?_⟩
  apply IrrMeasureCombination.irrationality_measure_le (Real.log 2) aSeq bSeq A 1 ρ Q
    hA (by norm_num) hρ0 hρ1 hQ1
  · -- hsmall
    intro n
    have key : (aSeq n : ℝ) * Real.log 2 - (bSeq n : ℝ) = (lcmUpto n : ℝ) * I n := by
      have hs := (D_mul_I_int_form n).choose_spec
      simp only [aSeq, bSeq, Int.cast_neg, Int.cast_mul, Int.cast_natCast]
      push_cast at hs ⊢
      linarith [hs]
    have hpos : 0 ≤ (aSeq n : ℝ) * Real.log 2 - (bSeq n : ℝ) := by
      rw [key]; exact le_of_lt (D_mul_I_pos n)
    rw [abs_of_nonneg hpos, key]
    exact hbound n
  · -- hapos
    intro n
    exact mul_pos (hDposZ n) (hcposZ n)
  · -- hden
    intro n
    have hc6 : (intCoeff n n : ℝ) ≤ 6 ^ n := by
      have := abs_coeff_le_six_pow n n
      rw [← intCoeff] at this
      have h2 := (abs_le.mp (by exact_mod_cast this : |(intCoeff n n : ℝ)| ≤ (6:ℝ) ^ n)).2
      exact h2
    have hlcm : (lcmUpto n : ℝ) ≤ Real.exp ((Real.log 4 + 4) * n) := lcmUpto_le n
    have hane : (aSeq n : ℝ) = (lcmUpto n : ℝ) * (intCoeff n n : ℝ) := by
      simp only [aSeq, Int.cast_mul, Int.cast_natCast]
    rw [hane, one_mul]
    have hQpow : Q ^ n = Real.exp ((Real.log 4 + 4) * n) * 6 ^ n := by
      rw [hQdef, mul_pow, ← Real.exp_nat_mul]; ring_nf
    rw [hQpow]
    have h6nn : (0 : ℝ) ≤ (6 : ℝ) ^ n := by positivity
    have hlcmnn : (0 : ℝ) ≤ (lcmUpto n : ℝ) := by positivity
    calc (lcmUpto n : ℝ) * (intCoeff n n : ℝ)
        ≤ (lcmUpto n : ℝ) * 6 ^ n := mul_le_mul_of_nonneg_left hc6 hlcmnn
      _ ≤ Real.exp ((Real.log 4 + 4) * n) * 6 ^ n := mul_le_mul_of_nonneg_right hlcm h6nn
  · -- hdet
    intro n hcontra
    have hW : PadeCasoratian.W (fun n => (intCoeff n n : ℝ)) r n ≠ 0 := by
      apply PadeCasoratian.casoratian_ne_zero _ _ hrec_c hrec_r _ n
      show (intCoeff 0 0 : ℝ) * r (0 + 1) - (intCoeff 1 1 : ℝ) * r 0 ≠ 0
      rw [r_zero, show (0 : ℕ) + 1 = 1 from rfl, r_one, intCoeff_zero_zero, intCoeff_one_one]
      norm_num
    apply hW
    -- from the ℤ equality, derive W = 0
    have hreal : (aSeq n : ℝ) * (bSeq (n + 1) : ℝ) = (aSeq (n + 1) : ℝ) * (bSeq n : ℝ) := by
      exact_mod_cast hcontra
    have hb : ∀ m, (bSeq m : ℝ) = -((lcmUpto m : ℝ) * r m) := by
      intro m; simp only [bSeq, Int.cast_neg, u_eq_D_mul_r]
    have ha : ∀ m, (aSeq m : ℝ) = (lcmUpto m : ℝ) * (intCoeff m m : ℝ) := by
      intro m; simp only [aSeq, Int.cast_mul, Int.cast_natCast]
    rw [ha n, ha (n + 1), hb n, hb (n + 1)] at hreal
    have hDn : (lcmUpto n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (lcmUpto_ne_zero n)
    have hDn1 : (lcmUpto (n + 1) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (lcmUpto_ne_zero (n + 1))
    simp only [PadeCasoratian.W]
    have hfac : (lcmUpto n : ℝ) * (lcmUpto (n + 1) : ℝ)
        * ((intCoeff n n : ℝ) * r (n + 1) - (intCoeff (n + 1) (n + 1) : ℝ) * r n) = 0 := by
      nlinarith [hreal]
    rcases mul_eq_zero.mp hfac with h | h
    · exact absurd h (mul_ne_zero hDn hDn1)
    · exact h

end DiagonalIntegralLog2
