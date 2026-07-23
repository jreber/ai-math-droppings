import Propositio.NumberTheory.Diophantine.DiagonalIntegralLog2Measure
import Propositio.NumberTheory.Diophantine.DiagonalIntegralLog2Delannoy
import Mathlib.Tactic

/-!
# The integral recurrence — closing the fully unconditional effective measure of `log 2`

`Iₙ = ∫₀¹ xⁿ(1−x)ⁿ/(1+x)ⁿ⁺¹ dx = ∫₁² (t−1)ⁿ(2−t)ⁿ/tⁿ⁺¹ dt` satisfies the SAME Padé / central
Delannoy recurrence `(n+2)Iₙ₊₂ = 3(2n+3)Iₙ₊₁ − (n+1)Iₙ`, by the SAME Gosper certificate that
proved the `cₙ` recurrence: `Gₙ(t) = (t²−2)·((t−1)(2−t))ⁿ⁺¹/tⁿ⁺²`.  Two facts make it work:

* **Pointwise** `G'ₙ(t) = −(n+1)gₙ(t) + 3(2n+3)gₙ₊₁(t) − (n+2)gₙ₊₂(t)` where `gₘ(t)=(t−1)ᵐ(2−t)ᵐ/tᵐ⁺¹`
  (this is the `heart` identity divided by `tⁿ⁺³`); and
* **Boundary** `Gₙ(1) = Gₙ(2) = 0` because `(t−1)` vanishes at `1` and `(2−t)` at `2`.

FTC then gives `0 = Gₙ(2)−Gₙ(1) = ∫₁² G'ₙ = −(n+1)Iₙ + 3(2n+3)Iₙ₊₁ − (n+2)Iₙ₊₂`.

Since `rₙ = Iₙ − cₙ·log2` and the recurrence is linear, `rₙ` then satisfies it too (pure algebra,
the `cₙ` recurrence being already proved), discharging BOTH hypotheses of
`log2_measure_of_recurrence` and yielding the unconditional `log2_measure_unconditional`.
-/

namespace DiagonalIntegralLog2

open Polynomial MeasureTheory intervalIntegral Set

/-- The diagonal integrand in the substituted `t`-variable: `gₘ(t) = (t−1)ᵐ(2−t)ᵐ/tᵐ⁺¹`,
so `I m = ∫₁² gₘ`. -/
noncomputable def gInt (m : ℕ) (t : ℝ) : ℝ := (t - 1) ^ m * (2 - t) ^ m / t ^ (m + 1)

theorem I_eq_gInt (m : ℕ) : I m = ∫ t in (1:ℝ)..2, gInt m t := by
  simp only [gInt]; rw [I_eq_sub]

theorem gInt_continuousOn (m : ℕ) : ContinuousOn (gInt m) (uIcc 1 2) := by
  rw [uIcc_of_le (by norm_num : (1:ℝ) ≤ 2)]
  apply ContinuousOn.div
  · exact (((continuous_id.sub continuous_const).pow m).mul
      ((continuous_const.sub continuous_id).pow m)).continuousOn
  · exact (continuous_id.pow (m + 1)).continuousOn
  · intro t ht
    simp only [mem_Icc] at ht
    exact pow_ne_zero _ (ne_of_gt (by linarith [ht.1] : (0:ℝ) < t))

theorem gInt_intervalIntegrable (m : ℕ) : IntervalIntegrable (gInt m) volume 1 2 :=
  (gInt_continuousOn m).intervalIntegrable

/-- The Gosper certificate `Gₙ(t) = (t²−2)·((t−1)(2−t))ⁿ⁺¹/tⁿ⁺²`. -/
noncomputable def Gcert (n : ℕ) (t : ℝ) : ℝ :=
  (t ^ 2 - 2) * (t - 1) ^ (n + 1) * (2 - t) ^ (n + 1) / t ^ (n + 2)

/-- **Pointwise certificate derivative.** `G'ₙ(t) = −(n+1)gₙ + 3(2n+3)gₙ₊₁ − (n+2)gₙ₊₂` for `t>0`. -/
theorem hasDerivAt_Gcert (n : ℕ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (Gcert n)
      (-((n:ℝ) + 1) * gInt n t + 3 * (2 * (n:ℝ) + 3) * gInt (n + 1) t
        - ((n:ℝ) + 2) * gInt (n + 2) t) t := by
  have ht0 : t ≠ 0 := ne_of_gt ht
  have htn : t ^ (n + 2) ≠ 0 := pow_ne_zero _ ht0
  have ha : HasDerivAt (fun s : ℝ => s ^ 2 - 2) (2 * t) t := by
    simpa using (hasDerivAt_pow 2 t).sub_const 2
  have hb0 : HasDerivAt (fun s : ℝ => s - 1) 1 t := by
    simpa using (hasDerivAt_id t).sub_const 1
  have hb : HasDerivAt (fun s : ℝ => (s - 1) ^ (n + 1)) ((↑(n + 1)) * (t - 1) ^ n) t := by
    simpa using hb0.pow (n + 1)
  have hc0 : HasDerivAt (fun s : ℝ => 2 - s) (-1) t := by
    simpa using (hasDerivAt_const t (2:ℝ)).sub (hasDerivAt_id t)
  have hc : HasDerivAt (fun s : ℝ => (2 - s) ^ (n + 1)) ((↑(n + 1)) * (2 - t) ^ n * (-1)) t := by
    simpa using hc0.pow (n + 1)
  have hN := (ha.mul hb).mul hc
  have hD : HasDerivAt (fun s : ℝ => s ^ (n + 2)) ((↑(n + 2)) * t ^ (n + 1)) t := by
    simpa using hasDerivAt_pow (n + 2) t
  have hG := hN.div hD htn
  convert hG using 1
  simp only [gInt, Pi.mul_apply]
  push_cast
  field_simp
  ring

theorem Gcert_two (n : ℕ) : Gcert n 2 = 0 := by
  simp only [Gcert]
  rw [show (2:ℝ) - 2 = 0 by ring, zero_pow (Nat.succ_ne_zero n)]
  ring

theorem Gcert_one (n : ℕ) : Gcert n 1 = 0 := by
  simp only [Gcert]
  rw [show (1:ℝ) - 1 = 0 by ring, zero_pow (Nat.succ_ne_zero n)]
  ring

/-- **The integral recurrence.** `Iₙ` satisfies the Padé / central Delannoy recurrence. -/
theorem I_recurrence : PadeCasoratian.Recurrence (fun n => I n) := by
  intro n
  -- abbreviations
  have hA := (gInt_intervalIntegrable n).const_mul (-((n:ℝ) + 1))
  have hB := (gInt_intervalIntegrable (n + 1)).const_mul (3 * (2 * (n:ℝ) + 3))
  have hC := (gInt_intervalIntegrable (n + 2)).const_mul (((n:ℝ) + 2))
  -- FTC on the certificate
  have hderiv : ∀ x ∈ uIcc (1:ℝ) 2, HasDerivAt (Gcert n)
      (-((n:ℝ) + 1) * gInt n x + 3 * (2 * (n:ℝ) + 3) * gInt (n + 1) x
        - ((n:ℝ) + 2) * gInt (n + 2) x) x := by
    intro x hx
    rw [uIcc_of_le (by norm_num : (1:ℝ) ≤ 2)] at hx
    simp only [mem_Icc] at hx
    exact hasDerivAt_Gcert n (by linarith [hx.1] : (0:ℝ) < x)
  have hF'int : IntervalIntegrable
      (fun x => -((n:ℝ) + 1) * gInt n x + 3 * (2 * (n:ℝ) + 3) * gInt (n + 1) x
        - ((n:ℝ) + 2) * gInt (n + 2) x) volume 1 2 := (hA.add hB).sub hC
  have hFTC := integral_eq_sub_of_hasDerivAt hderiv hF'int
  rw [Gcert_two, Gcert_one, sub_zero] at hFTC
  -- split the integral and identify the three pieces with `I`
  rw [integral_sub (hA.add hB) hC, integral_add hA hB, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    ← I_eq_gInt, ← I_eq_gInt, ← I_eq_gInt] at hFTC
  -- hFTC : -(n+1)·Iₙ + 3(2n+3)·Iₙ₊₁ − (n+2)·Iₙ₊₂ = 0
  simp only []
  linarith [hFTC]

/-- **The rational-part recurrence** `rₙ`, from `I_recurrence` and the proved `cₙ` recurrence:
`rₙ = Iₙ − cₙ·log2`, and the recurrence is linear. -/
theorem r_recurrence : PadeCasoratian.Recurrence r := by
  intro n
  have hI : ((n:ℝ) + 2) * I (n + 2) = 3 * (2 * (n:ℝ) + 3) * I (n + 1) - ((n:ℝ) + 1) * I n :=
    I_recurrence n
  have hc : ((n:ℝ) + 2) * (intCoeff (n + 2) (n + 2) : ℝ)
      = 3 * (2 * (n:ℝ) + 3) * (intCoeff (n + 1) (n + 1) : ℝ) - ((n:ℝ) + 1) * (intCoeff n n : ℝ) :=
    intCoeff_diag_recurrence n
  have hr : ∀ m, r m = I m - (intCoeff m m : ℝ) * Real.log 2 := by
    intro m; have := I_eq_c_log2_add_r m; linarith [this]
  show ((n:ℝ) + 2) * r (n + 2) = 3 * (2 * (n:ℝ) + 3) * r (n + 1) - ((n:ℝ) + 1) * r n
  rw [hr, hr, hr]
  linear_combination hI - Real.log 2 * hc

/-- **Fully unconditional effective irrationality measure of `log 2`.**  Both recurrence
hypotheses of `log2_measure_of_recurrence` are now proved (`intCoeff_diag_recurrence`,
`r_recurrence`), so `log 2` has an effective irrationality measure with NO hypotheses. -/
theorem log2_measure_unconditional :
    ∃ A ρ Q : ℝ, 0 < A ∧ 0 < ρ ∧ ρ < 1 ∧ 1 < Q ∧
      ∃ C > 0, ∀ (p q : ℤ), 1 ≤ q → (1 : ℝ) ≤ 2 * A * q →
        C / (q : ℝ) ^ (1 + Real.log Q / Real.log ρ⁻¹) ≤ |Real.log 2 - (p : ℝ) / q| :=
  log2_measure_of_recurrence intCoeff_diag_recurrence r_recurrence

end DiagonalIntegralLog2
