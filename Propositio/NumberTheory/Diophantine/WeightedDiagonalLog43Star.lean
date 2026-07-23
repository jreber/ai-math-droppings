import Propositio.NumberTheory.Diophantine.WeightedDiagonalLog43PFI
import Propositio.NumberTheory.Diophantine.WeightedDiagonalLog43Decomp
import Propositio.NumberTheory.Diophantine.WeightedDiagonalLog43Integrals
import Propositio.NumberTheory.Diophantine.WeightedDiagonalLog43ResidueRec
import Mathlib.Tactic

/-!
# The partial-fraction integral identity (STAR): `Jₙ = Pexpl n + aRes(n,1)·log(4/3)`

Combining the cleared partial-fraction identity `PFI` (`WeightedDiagonalLog43PFI`) with term-by-term
integration over `[0,1]` (`WeightedDiagonalLog43Integrals`) gives the explicit single-log form

  `Jₙ = aRes(n,1)·log 2 + bRes(n,1)·log(3/2) + Pexpl n`   (`Jstar_raw`),

and `residue-sum-zero` collapses the two logs:

  `Jₙ = Pexpl n + aRes(n,1)·log(4/3)`   (`Jstar`).

Subtracting `J_decomp` and applying the integral recurrence forces `Pexpl` to satisfy the same
three-term recurrence as `JP` — closing `∀ n, JP n = Pexpl n` — **provided** the leading residue
`aRes(·,1)` satisfies that recurrence (`aRes_recurrence`).
-/

namespace WeightedDiagonalLog43

open Polynomial MeasureTheory intervalIntegral
open scoped BigOperators

/-- Real principal-part value at the pole `x = −1`: `Areal n x = aeval x (Apoly n)`. -/
noncomputable def Areal (n : ℕ) (x : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1), (aRes n (n + 1 - i) : ℝ) * (1 + x) ^ i

/-- Real principal-part value at the pole `x = −2`. -/
noncomputable def Breal (n : ℕ) (x : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1), (bRes n (n + 1 - i) : ℝ) * (2 + x) ^ i

theorem aeval_Apoly (n : ℕ) (x : ℝ) : Polynomial.aeval x (Apoly n) = Areal n x := by
  unfold Apoly Areal
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_mul, map_pow, map_add, map_one, Polynomial.aeval_X, Polynomial.aeval_C]
  simp

theorem aeval_Bpoly (n : ℕ) (x : ℝ) : Polynomial.aeval x (Bpoly n) = Breal n x := by
  unfold Bpoly Breal
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_mul, map_pow, map_add, map_ofNat, Polynomial.aeval_X, Polynomial.aeval_C]
  simp

/-- **PFI evaluated at a real point.** -/
theorem PFI_real (n : ℕ) (x : ℝ) :
    x ^ n * (1 - x) ^ n = Areal n x * (2 + x) ^ (n + 1) + (1 + x) ^ (n + 1) * Breal n x := by
  have h := congrArg (Polynomial.aeval x) (PFI n)
  simp only [map_mul, map_pow, map_sub, map_add, map_one, map_ofNat, Polynomial.aeval_X] at h
  rw [aeval_Apoly, aeval_Bpoly] at h
  exact h

/-- **Pointwise partial-fraction expansion of the integrand** on `0<1+x`, `0<2+x`. -/
theorem hJ_pointwise (n : ℕ) {x : ℝ} (hx1 : 0 < 1 + x) (hx2 : 0 < 2 + x) :
    hJ n x = Areal n x / (1 + x) ^ (n + 1) + Breal n x / (2 + x) ^ (n + 1) := by
  have hd1 : ((1 + x) ^ (n + 1)) ≠ 0 := pow_ne_zero _ (ne_of_gt hx1)
  have hd2 : ((2 + x) ^ (n + 1)) ≠ 0 := pow_ne_zero _ (ne_of_gt hx2)
  rw [hJ, PFI_real n x]
  field_simp

/-- The `A`-side integrand as an explicit sum of `((1+x)^k)⁻¹` terms (on `0<1+x`). -/
theorem Areal_div (n : ℕ) {x : ℝ} (hx1 : 0 < 1 + x) :
    Areal n x / (1 + x) ^ (n + 1)
      = ∑ i ∈ Finset.range (n + 1), (aRes n (n + 1 - i) : ℝ) * ((1 + x) ^ (n + 1 - i))⁻¹ := by
  unfold Areal
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  rw [mul_div_assoc]
  congr 1
  rw [div_eq_mul_inv,
    show (1 + x) ^ (n + 1) = (1 + x) ^ i * (1 + x) ^ (n + 1 - i) from by
      rw [← pow_add]; congr 1; omega,
    mul_inv, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero i (ne_of_gt hx1)), one_mul]

/-- The `B`-side integrand as an explicit sum (on `0<2+x`). -/
theorem Breal_div (n : ℕ) {x : ℝ} (hx2 : 0 < 2 + x) :
    Breal n x / (2 + x) ^ (n + 1)
      = ∑ i ∈ Finset.range (n + 1), (bRes n (n + 1 - i) : ℝ) * ((2 + x) ^ (n + 1 - i))⁻¹ := by
  unfold Breal
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  rw [mul_div_assoc]
  congr 1
  rw [div_eq_mul_inv,
    show (2 + x) ^ (n + 1) = (2 + x) ^ i * (2 + x) ^ (n + 1 - i) from by
      rw [← pow_add]; congr 1; omega,
    mul_inv, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero i (ne_of_gt hx2)), one_mul]

/-! ### The elementary integrals as a function of the pole order -/

/-- `IA k = ∫₀¹ ((1+x)^k)⁻¹ dx`. -/
noncomputable def IA (k : ℕ) : ℝ := ∫ x in (0:ℝ)..1, ((1 + x) ^ k)⁻¹

/-- `IB k = ∫₀¹ ((2+x)^k)⁻¹ dx`. -/
noncomputable def IB (k : ℕ) : ℝ := ∫ x in (0:ℝ)..1, ((2 + x) ^ k)⁻¹

theorem IA_one : IA 1 = Real.log 2 := by
  unfold IA; simp only [pow_one]; exact WeightedDiagonalLog43Integrals.integral_one_add_inv

theorem IB_one : IB 1 = Real.log (3 / 2) := by
  unfold IB; simp only [pow_one]; exact WeightedDiagonalLog43Integrals.integral_two_add_inv

theorem IA_succ_succ (i : ℕ) : IA (i + 2) = (1 - ((2 : ℝ) ^ (i + 1))⁻¹) / (i + 1) := by
  have h := WeightedDiagonalLog43Integrals.integral_one_add_pow_inv (i + 1) (by omega)
  unfold IA
  rw [show i + 2 = (i + 1) + 1 from rfl]
  rw [h]; push_cast; ring

theorem IB_succ_succ (i : ℕ) :
    IB (i + 2) = (((2 : ℝ) ^ (i + 1))⁻¹ - ((3 : ℝ) ^ (i + 1))⁻¹) / (i + 1) := by
  have h := WeightedDiagonalLog43Integrals.integral_two_add_pow_inv (i + 1) (by omega)
  unfold IB
  rw [show i + 2 = (i + 1) + 1 from rfl]
  rw [h]; push_cast; ring

/-- Each integrand term `c·((a+x)^k)⁻¹` is interval-integrable on `[0,1]` for `a > 0`. -/
theorem integrable_term (c a : ℝ) (ha : 0 < a) (k : ℕ) :
    IntervalIntegrable (fun x => c * ((a + x) ^ k)⁻¹) volume 0 1 := by
  apply ContinuousOn.intervalIntegrable
  apply ContinuousOn.mul continuousOn_const
  apply ContinuousOn.inv₀
  · exact (continuousOn_const.add continuousOn_id).pow k
  · intro x hx
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hx
    have : 0 < a + x := by simp only [Set.mem_Icc] at hx; linarith [hx.1]
    positivity

/-! ### The integral evaluated as a residue sum -/

/-- **`J` as a sum over pole orders.**  `Jₙ = ∑ aRes(n,n+1−i)·IA(n+1−i) + ∑ bRes(n,n+1−i)·IB(n+1−i)`. -/
theorem J_eq_residue_sum (n : ℕ) :
    J n = (∑ i ∈ Finset.range (n + 1), (aRes n (n + 1 - i) : ℝ) * IA (n + 1 - i))
        + ∑ i ∈ Finset.range (n + 1), (bRes n (n + 1 - i) : ℝ) * IB (n + 1 - i) := by
  have hcong : J n = ∫ x in (0:ℝ)..1,
      ((∑ i ∈ Finset.range (n + 1), (aRes n (n + 1 - i) : ℝ) * ((1 + x) ^ (n + 1 - i))⁻¹)
        + ∑ i ∈ Finset.range (n + 1), (bRes n (n + 1 - i) : ℝ) * ((2 + x) ^ (n + 1 - i))⁻¹) := by
    rw [J]
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hx
    simp only [Set.mem_Icc] at hx
    have hx1 : (0:ℝ) < 1 + x := by linarith [hx.1]
    have hx2 : (0:ℝ) < 2 + x := by linarith [hx.1]
    rw [hJ_pointwise n hx1 hx2, Areal_div n hx1, Breal_div n hx2]
  rw [hcong]
  -- split the integral of the sum
  have hintA : ∀ i ∈ Finset.range (n + 1),
      IntervalIntegrable (fun x => (aRes n (n + 1 - i) : ℝ) * ((1 + x) ^ (n + 1 - i))⁻¹) volume 0 1 :=
    fun i _ => integrable_term _ 1 (by norm_num) _
  have hintB : ∀ i ∈ Finset.range (n + 1),
      IntervalIntegrable (fun x => (bRes n (n + 1 - i) : ℝ) * ((2 + x) ^ (n + 1 - i))⁻¹) volume 0 1 :=
    fun i _ => integrable_term _ 2 (by norm_num) _
  have hcontA : ∀ a : ℝ, 0 < a → ∀ i,
      ContinuousOn (fun x => (aRes n (n + 1 - i) : ℝ) * ((a + x) ^ (n + 1 - i))⁻¹)
        (Set.uIcc (0:ℝ) 1) := by
    intro a ha i
    apply ContinuousOn.mul continuousOn_const
    apply ContinuousOn.inv₀ ((continuousOn_const.add continuousOn_id).pow _)
    intro x hx
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hx
    simp only [Set.mem_Icc] at hx
    have : (0:ℝ) < a + x := by linarith [hx.1]
    positivity
  have hF : IntervalIntegrable
      (fun x => ∑ i ∈ Finset.range (n + 1), (aRes n (n + 1 - i) : ℝ) * ((1 + x) ^ (n + 1 - i))⁻¹)
      volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    exact continuousOn_finset_sum _ (fun i _ => hcontA 1 (by norm_num) i)
  have hG : IntervalIntegrable
      (fun x => ∑ i ∈ Finset.range (n + 1), (bRes n (n + 1 - i) : ℝ) * ((2 + x) ^ (n + 1 - i))⁻¹)
      volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    refine continuousOn_finset_sum _ (fun i _ => ?_)
    apply ContinuousOn.mul continuousOn_const
    apply ContinuousOn.inv₀ ((continuousOn_const.add continuousOn_id).pow _)
    intro x hx
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hx
    simp only [Set.mem_Icc] at hx
    have : (0:ℝ) < 2 + x := by linarith [hx.1]
    positivity
  rw [intervalIntegral.integral_add hF hG,
      intervalIntegral.integral_finset_sum hintA,
      intervalIntegral.integral_finset_sum hintB]
  congr 1
  · apply Finset.sum_congr rfl; intro i _
    rw [intervalIntegral.integral_const_mul]; rfl
  · apply Finset.sum_congr rfl; intro i _
    rw [intervalIntegral.integral_const_mul]; rfl

/-! ### Reindexing the residue sum to the closed form `Pexpl` -/

theorem reflect_A (n : ℕ) :
    (∑ i ∈ Finset.range (n + 1), (aRes n (n + 1 - i) : ℝ) * IA (n + 1 - i))
      = ∑ i ∈ Finset.range (n + 1), (aRes n (i + 1) : ℝ) * IA (i + 1) := by
  rw [← Finset.sum_range_reflect (fun j => (aRes n (j + 1) : ℝ) * IA (j + 1)) (n + 1)]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  rw [show n + 1 - 1 - i = n - i from by omega, show n + 1 - i = (n - i) + 1 from by omega]

theorem reflect_B (n : ℕ) :
    (∑ i ∈ Finset.range (n + 1), (bRes n (n + 1 - i) : ℝ) * IB (n + 1 - i))
      = ∑ i ∈ Finset.range (n + 1), (bRes n (i + 1) : ℝ) * IB (i + 1) := by
  rw [← Finset.sum_range_reflect (fun j => (bRes n (j + 1) : ℝ) * IB (j + 1)) (n + 1)]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  rw [show n + 1 - 1 - i = n - i from by omega, show n + 1 - i = (n - i) + 1 from by omega]

/-- The real cast of `Pexpl` as the sum matching the integral remainder. -/
theorem Pexpl_real (n : ℕ) :
    (Pexpl n : ℝ)
      = ∑ i ∈ Finset.range n, ((aRes n (i + 2) : ℝ) * IA (i + 2) + (bRes n (i + 2) : ℝ) * IB (i + 2)) := by
  unfold Pexpl
  rw [show Finset.Icc 1 n = Finset.Ico 1 (n + 1) from by
        ext k; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega,
    Finset.sum_Ico_eq_sum_range, show n + 1 - 1 = n from by omega]
  push_cast
  apply Finset.sum_congr rfl
  intro i _
  rw [show 1 + i = i + 1 from by omega]
  unfold Pbracket
  rw [IA_succ_succ, IB_succ_succ]
  have hi1 : ((i : ℝ) + 1) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-- **The raw partial-fraction integral identity (two logs).** -/
theorem Jstar_raw (n : ℕ) :
    J n = (aRes n 1 : ℝ) * Real.log 2 + (bRes n 1 : ℝ) * Real.log (3 / 2) + (Pexpl n : ℝ) := by
  rw [J_eq_residue_sum, reflect_A, reflect_B,
    Finset.sum_range_succ' (fun i => (aRes n (i + 1) : ℝ) * IA (i + 1)) n,
    Finset.sum_range_succ' (fun i => (bRes n (i + 1) : ℝ) * IB (i + 1)) n,
    Pexpl_real, Finset.sum_add_distrib]
  simp only [Nat.zero_add, IA_one, IB_one]
  ring

/-- **The single-log partial-fraction integral identity (STAR).** -/
theorem Jstar (n : ℕ) : J n = (Pexpl n : ℝ) + (aRes n 1 : ℝ) * Real.log (4 / 3) := by
  have hsum := aRes_one_add_bRes_one n
  have hb : (bRes n 1 : ℝ) = -(aRes n 1 : ℝ) := by
    have : ((aRes n 1 + bRes n 1 : ℤ) : ℝ) = 0 := by exact_mod_cast hsum
    push_cast at this; linarith
  have hlog : Real.log 2 - Real.log (3 / 2) = Real.log (4 / 3) := by
    rw [← Real.log_div (by norm_num) (by norm_num)]; norm_num
  rw [Jstar_raw, hb]
  linear_combination (aRes n 1 : ℝ) * hlog

/-! ### Conditional closure: the leading-residue recurrence forces the `Pexpl` recurrence -/

/-- The hypothesis that the leading residue `aRes(·,1)` satisfies the `J`-recurrence
(`= Legendre P_n(7)`).  Stated over `ℝ`. -/
def aRes_recurrence : Prop :=
  ∀ n : ℕ, ((n : ℝ) + 2) * (aRes (n + 2) 1 : ℝ)
    = 7 * (2 * (n : ℝ) + 3) * (aRes (n + 1) 1 : ℝ) - ((n : ℝ) + 1) * (aRes n 1 : ℝ)

/-- **Conditional `Pexpl` recurrence.**  If `aRes(·,1)` satisfies the recurrence, so does `Pexpl`. -/
theorem Pexpl_rec (haRes : aRes_recurrence) (n : ℕ) :
    ((n : ℚ) + 2) * Pexpl (n + 2)
      = 7 * (2 * (n : ℚ) + 3) * Pexpl (n + 1) - ((n : ℚ) + 1) * Pexpl n := by
  have hr := J_recurrence n
  rw [Jstar n, Jstar (n + 1), Jstar (n + 2)] at hr
  have ha := haRes n
  have hReal : (((n : ℚ) + 2) * Pexpl (n + 2) : ℝ)
      = ((7 * (2 * (n : ℚ) + 3) * Pexpl (n + 1) - ((n : ℚ) + 1) * Pexpl n : ℚ) : ℝ) := by
    push_cast
    linear_combination hr - Real.log (4 / 3) * ha
  exact_mod_cast hReal

/-- **Conditional `JP = Pexpl`.** -/
theorem JP_eq_Pexpl (haRes : aRes_recurrence) : ∀ n, JP n = Pexpl n :=
  JP_eq_Pexpl_of_rec (fun n => Pexpl_rec haRes n)

/-- **Conditional unconditional measure.**  Modulo the leading-residue recurrence
`aRes_recurrence`, `log(4/3)` has an effective irrationality measure. -/
theorem log43_measure_of_aRes_recurrence (haRes : aRes_recurrence) :
    ∃ A ρ Q : ℝ, 0 < A ∧ 0 < ρ ∧ ρ < 1 ∧ 1 < Q ∧
      ∃ C > 0, ∀ (p q : ℤ), 1 ≤ q → (1 : ℝ) ≤ 2 * A * q →
        C / (q : ℝ) ^ (1 + Real.log Q / Real.log ρ⁻¹) ≤ |Real.log (4 / 3) - (p : ℝ) / q| :=
  log43_measure_of_Pexpl_eq (JP_eq_Pexpl haRes)

end WeightedDiagonalLog43

