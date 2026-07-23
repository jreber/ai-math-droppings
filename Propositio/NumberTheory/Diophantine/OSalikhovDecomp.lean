import Propositio.NumberTheory.Diophantine.OSalikhovTwoLog

/-!
# oSALIKHOV partial-fraction decomposition (`E1 = A1 + B·log(2/3)`, `E2 = A2 − B·log2`)

This file proves the integral evaluations underlying the construction's two real forms.  We start
with the **base case** `n = 0`, where `f₀(x) = 1/(x²−225)` and `A1(0)=A2(0)=0`, `B(0)=1/30`:
```
  E1 0 = ∫₀³ 1/(x²−225) = (1/30)·log(2/3)       E2 0 = ∫₀⁵ 1/(x²−225) = −(1/30)·log2
```
via the antiderivative `F₀(x) = (1/30)(log(15−x) − log(15+x))` (valid on `(−15,15)`, where both
`15∓x > 0`), `F₀'(x) = 1/(x²−225)`, and the fundamental theorem of calculus.  These match
`B(0) = 1/30` and the residue antisymmetry `d₁ = −B` confirmed numerically.
-/

namespace OSalikhovTwoLog

open MeasureTheory intervalIntegral Set

/-- Antiderivative of `f₀(x)=1/(x²−225)` on `(−15,15)`:
`F₀(x) = (1/30)(log(15−x) − log(15+x))`. -/
noncomputable def F0 (x : ℝ) : ℝ := (1 / 30) * (Real.log (15 - x) - Real.log (15 + x))

/-- `F₀' = f₀` on `(−15,15)`. -/
theorem hasDerivAt_F0 {x : ℝ} (hx : -15 < x) (hx' : x < 15) :
    HasDerivAt F0 (fOsal 0 x) x := by
  have h1 : (15 : ℝ) - x ≠ 0 := by linarith
  have h2 : (15 : ℝ) + x ≠ 0 := by linarith
  have h3 : x ^ 2 - 225 ≠ 0 := by nlinarith
  have d1 : HasDerivAt (fun y => Real.log (15 - y)) (-1 / (15 - x)) x := by
    have hi : HasDerivAt (fun y => (15 : ℝ) - y) (-1) x := by
      simpa using (hasDerivAt_id x).const_sub 15
    simpa using hi.log h1
  have d2 : HasDerivAt (fun y => Real.log (15 + y)) (1 / (15 + x)) x := by
    have hi : HasDerivAt (fun y => (15 : ℝ) + y) 1 x := by
      simpa using (hasDerivAt_id x).const_add 15
    simpa using hi.log h2
  have key : (1 / 30 : ℝ) * (-1 / (15 - x) - 1 / (15 + x)) = fOsal 0 x := by
    unfold fOsal
    rw [show 2 * 0 = 0 from rfl, show 2 * 0 + 1 = 1 from rfl, pow_zero, pow_zero, pow_zero, pow_one]
    field_simp
    ring
  rw [← key]
  exact (d1.sub d2).const_mul (1 / 30)

/-- **Base case `E1 0`**: `∫₀³ 1/(x²−225) = (1/30)·log(2/3)`. -/
theorem E1_zero : E1 0 = (1 / 30) * Real.log (2 / 3) := by
  unfold E1
  rw [integral_eq_sub_of_hasDerivAt (f := F0)
      (fun x hx => hasDerivAt_F0
        (by rw [uIcc_of_le (by norm_num)] at hx; simp only [mem_Icc] at hx; linarith [hx.1])
        (by rw [uIcc_of_le (by norm_num)] at hx; simp only [mem_Icc] at hx; linarith [hx.2]))
      (fOsal_intervalIntegrable_three 0)]
  unfold F0
  rw [show (15 : ℝ) - 3 = 12 by norm_num, show (15 : ℝ) + 3 = 18 by norm_num,
      show (15 : ℝ) - 0 = 15 by norm_num, show (15 : ℝ) + 0 = 15 by norm_num,
      sub_self (Real.log 15),
      show (2 : ℝ) / 3 = 12 / 18 by norm_num, Real.log_div (by norm_num) (by norm_num)]
  ring

/-- **Base case `E2 0`**: `∫₀⁵ 1/(x²−225) = −(1/30)·log2`. -/
theorem E2_zero : E2 0 = -(1 / 30) * Real.log 2 := by
  unfold E2
  rw [integral_eq_sub_of_hasDerivAt (f := F0)
      (fun x hx => hasDerivAt_F0
        (by rw [uIcc_of_le (by norm_num)] at hx; simp only [mem_Icc] at hx; linarith [hx.1])
        (by rw [uIcc_of_le (by norm_num)] at hx; simp only [mem_Icc] at hx; linarith [hx.2]))
      (fOsal_intervalIntegrable_five 0)]
  unfold F0
  have hlog : Real.log 10 - Real.log 20 = - Real.log 2 := by
    rw [← Real.log_div (by norm_num) (by norm_num), show (10 : ℝ) / 20 = 2⁻¹ by norm_num,
      Real.log_inv]
  rw [show (15 : ℝ) - 5 = 10 by norm_num, show (15 : ℝ) + 5 = 20 by norm_num,
      show (15 : ℝ) - 0 = 15 by norm_num, show (15 : ℝ) + 0 = 15 by norm_num,
      sub_self (Real.log 15), hlog]
  ring

/-! ## Base case `E1 1` (triple pole, FTC)

`f₁(x) = x²(x²−9)(x²−25)/(x²−225)³ = 1 + Σ_{j=1}^3 c_j/(x−15)^j + d_j/(x+15)^j` with (exact, from the
residue computation) `c₁=409/30=B(1)`, `c₂=116`, `c₃=360`, `d_j=(−1)·`mirror.  Antiderivative `F1`,
FTC over `[0,3]` ⟹ `E1 1 = 199/36 + (409/30)·log(2/3) = A1(1) + B(1)·log(2/3)`. -/

/-- Antiderivative of `f₁` on `(−15,15)`. -/
noncomputable def F1 (x : ℝ) : ℝ :=
  x - 180 * ((x - 15) ^ 2)⁻¹ - 116 * (x - 15)⁻¹ + (409 / 30) * Real.log (15 - x)
    + 180 * ((x + 15) ^ 2)⁻¹ - 116 * (x + 15)⁻¹ - (409 / 30) * Real.log (15 + x)

theorem hasDerivAt_F1 {x : ℝ} (hx : -15 < x) (hx' : x < 15) :
    HasDerivAt F1 (fOsal 1 x) x := by
  have h1 : (x - 15) ≠ 0 := by linarith
  have h2 : (x + 15) ≠ 0 := by linarith
  have hl1 : (15 - x) ≠ 0 := by linarith
  have hl2 : (15 + x) ≠ 0 := by linarith
  have hQ : x ^ 2 - 225 ≠ 0 := by nlinarith [hx, hx']
  have d_xm15 : HasDerivAt (fun x : ℝ => x - 15) 1 x := by simpa using (hasDerivAt_id x).sub_const 15
  have d_xp15 : HasDerivAt (fun x : ℝ => x + 15) 1 x := by simpa using (hasDerivAt_id x).add_const 15
  have d_sq1 : HasDerivAt (fun x : ℝ => (x - 15) ^ 2) (2 * (x - 15)) x := by
    simpa using d_xm15.pow 2
  have d_sq2 : HasDerivAt (fun x : ℝ => (x + 15) ^ 2) (2 * (x + 15)) x := by
    simpa using d_xp15.pow 2
  -- the seven terms
  have t0 : HasDerivAt (fun x : ℝ => x) 1 x := hasDerivAt_id x
  have t1 : HasDerivAt (fun x : ℝ => 180 * ((x - 15) ^ 2)⁻¹)
      (180 * (-(2 * (x - 15)) / ((x - 15) ^ 2) ^ 2)) x :=
    (d_sq1.inv (pow_ne_zero 2 h1)).const_mul 180
  have t2 : HasDerivAt (fun x : ℝ => 116 * (x - 15)⁻¹) (116 * (-1 / (x - 15) ^ 2)) x := by
    have := (d_xm15.inv h1).const_mul 116; simpa using this
  have t3 : HasDerivAt (fun x : ℝ => (409 / 30) * Real.log (15 - x))
      ((409 / 30) * (-1 / (15 - x))) x := by
    have hi : HasDerivAt (fun x : ℝ => (15 : ℝ) - x) (-1) x := by
      simpa using (hasDerivAt_id x).const_sub 15
    have := (hi.log hl1).const_mul (409 / 30); simpa using this
  have t4 : HasDerivAt (fun x : ℝ => 180 * ((x + 15) ^ 2)⁻¹)
      (180 * (-(2 * (x + 15)) / ((x + 15) ^ 2) ^ 2)) x :=
    (d_sq2.inv (pow_ne_zero 2 h2)).const_mul 180
  have t5 : HasDerivAt (fun x : ℝ => 116 * (x + 15)⁻¹) (116 * (-1 / (x + 15) ^ 2)) x := by
    have := (d_xp15.inv h2).const_mul 116; simpa using this
  have t6 : HasDerivAt (fun x : ℝ => (409 / 30) * Real.log (15 + x))
      ((409 / 30) * (1 / (15 + x))) x := by
    have hi : HasDerivAt (fun x : ℝ => (15 : ℝ) + x) 1 x := by
      simpa using (hasDerivAt_id x).const_add 15
    have := (hi.log hl2).const_mul (409 / 30); simpa using this
  have hsum := ((((((t0.sub t1).sub t2).add t3).add t4).sub t5).sub t6)
  convert hsum using 1
  unfold fOsal
  rw [show 2 * 1 = 2 from rfl, show 2 * 1 + 1 = 3 from rfl, pow_one]
  field_simp
  ring

/-- **Base case `E1 1`**: `∫₀³ f₁ = 199/36 + (409/30)·log(2/3)`. -/
theorem E1_one : E1 1 = 199 / 36 + (409 / 30) * Real.log (2 / 3) := by
  unfold E1
  rw [integral_eq_sub_of_hasDerivAt (f := F1)
      (fun x hx => hasDerivAt_F1
        (by rw [uIcc_of_le (by norm_num)] at hx; simp only [mem_Icc] at hx; linarith [hx.1])
        (by rw [uIcc_of_le (by norm_num)] at hx; simp only [mem_Icc] at hx; linarith [hx.2]))
      (fOsal_intervalIntegrable_three 1)]
  unfold F1
  rw [show (15 : ℝ) - 3 = 12 by norm_num, show (15 : ℝ) + 3 = 18 by norm_num,
      show (15 : ℝ) - 0 = 15 by norm_num, show (15 : ℝ) + 0 = 15 by norm_num,
      show (2 : ℝ) / 3 = 12 / 18 by norm_num, Real.log_div (by norm_num) (by norm_num)]
  ring

/-- **Base case `E2 1`** (reuses the same antiderivative `F1`): `∫₀⁵ f₁ = 189/20 − (409/30)·log2`. -/
theorem E2_one : E2 1 = 189 / 20 - (409 / 30) * Real.log 2 := by
  unfold E2
  rw [integral_eq_sub_of_hasDerivAt (f := F1)
      (fun x hx => hasDerivAt_F1
        (by rw [uIcc_of_le (by norm_num)] at hx; simp only [mem_Icc] at hx; linarith [hx.1])
        (by rw [uIcc_of_le (by norm_num)] at hx; simp only [mem_Icc] at hx; linarith [hx.2]))
      (fOsal_intervalIntegrable_five 1)]
  unfold F1
  rw [show (15 : ℝ) - 5 = 10 by norm_num, show (15 : ℝ) + 5 = 20 by norm_num,
      show (15 : ℝ) - 0 = 15 by norm_num, show (15 : ℝ) + 0 = 15 by norm_num,
      show (20 : ℝ) = 10 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  ring

/-! ## Integral decay bound (`|E1 n| ≤ 3·(1/100)ⁿ`)

The integrand factor `φ(x) = x²(9−x²)(25−x²)/(225−x²)²` satisfies `φ(x) ≤ 1/100` on `[0,3]`
(a degree-6 polynomial inequality; the sharp sup is `≈ 0.0086 < 1/100`, attained at `x ≈ 2.027`,
the smallest indicial root).  Since `|f_n(x)| = φ(x)ⁿ/(225−x²)` and `225−x² ≥ 1`, this gives
`|f_n(x)| ≤ (1/100)ⁿ` on `[0,3]`, hence `|E1 n| ≤ 3·(1/100)ⁿ` — the geometric decay of the integral
remainder (the `I_le`/`J_le` analogue; an input to the eventual `hsmall`). -/

/-- On `[0,3]`: `|f_n(x)| = [x²(9−x²)(25−x²)]ⁿ/(225−x²)^(2n+1) ≤ (1/100)ⁿ`. -/
theorem fOsal_abs_le_three (n : ℕ) {x : ℝ} (h0 : 0 ≤ x) (h3 : x ≤ 3) :
    |fOsal n x| ≤ (1 / 100) ^ n := by
  have hxx : (0 : ℝ) ≤ x ^ 2 := sq_nonneg x
  have h9 : (0 : ℝ) ≤ 9 - x ^ 2 := by nlinarith
  have h25 : (0 : ℝ) ≤ 25 - x ^ 2 := by nlinarith
  have hden : (1 : ℝ) ≤ 225 - x ^ 2 := by nlinarith
  have hdenpos : (0 : ℝ) < 225 - x ^ 2 := by linarith
  set base : ℝ := x ^ 2 * (9 - x ^ 2) * (25 - x ^ 2) with hbase
  have hbase0 : 0 ≤ base := by rw [hbase]; positivity
  -- |f_n| = baseⁿ/(225−x²)^(2n+1)
  have hnum : x ^ (2 * n) * (x ^ 2 - 9) ^ n * (x ^ 2 - 25) ^ n = base ^ n := by
    rw [pow_mul, ← mul_pow, ← mul_pow, hbase]; congr 1; ring
  have hden_eq : (x ^ 2 - 225) ^ (2 * n + 1) = -((225 - x ^ 2) ^ (2 * n + 1)) := by
    rw [show x ^ 2 - 225 = -(225 - x ^ 2) by ring]
    exact Odd.neg_pow ⟨n, by ring⟩ _
  have habs : |fOsal n x| = base ^ n / (225 - x ^ 2) ^ (2 * n + 1) := by
    unfold fOsal
    rw [hnum, hden_eq, div_neg, abs_neg, abs_of_nonneg
      (div_nonneg (pow_nonneg hbase0 n) (pow_nonneg hdenpos.le _))]
  rw [habs, div_le_iff₀ (by positivity)]
  -- goal: baseⁿ ≤ (1/100)ⁿ · (225−x²)^(2n+1)
  have hb : base ≤ 1 / 100 * (225 - x ^ 2) ^ 2 := by
    rw [hbase]; nlinarith [mul_nonneg hxx h9, mul_nonneg h9 h9, mul_nonneg hxx hxx,
      mul_nonneg (mul_nonneg hxx h9) h9, mul_nonneg (mul_nonneg hxx hxx) h9,
      mul_nonneg hxx (mul_nonneg h9 h9), sq_nonneg (x ^ 2 - 4), sq_nonneg (x ^ 2 - 5),
      mul_nonneg h9 h25, mul_nonneg hxx h25]
  calc base ^ n
      ≤ (1 / 100 * (225 - x ^ 2) ^ 2) ^ n := pow_le_pow_left₀ hbase0 hb n
    _ = (1 / 100 : ℝ) ^ n * (225 - x ^ 2) ^ (2 * n) := by rw [mul_pow, ← pow_mul]
    _ ≤ (1 / 100 : ℝ) ^ n * (225 - x ^ 2) ^ (2 * n + 1) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact pow_le_pow_right₀ hden (by omega)

/-- **Geometric decay of the integral remainder**: `|E1 n| ≤ 3·(1/100)ⁿ`. -/
theorem E1_abs_le (n : ℕ) : |E1 n| ≤ 3 * (1 / 100) ^ n := by
  have hbnd : ∀ x ∈ Set.uIoc (0 : ℝ) 3, ‖fOsal n x‖ ≤ (1 / 100) ^ n := by
    intro x hx
    rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 3)] at hx
    rw [Real.norm_eq_abs]
    exact fOsal_abs_le_three n (le_of_lt hx.1) hx.2
  have := intervalIntegral.norm_integral_le_of_norm_le_const hbnd
  rw [Real.norm_eq_abs] at this
  calc |E1 n| = |∫ x in (0:ℝ)..3, fOsal n x| := by rw [E1]
    _ ≤ (1 / 100) ^ n * |(3 : ℝ) - 0| := this
    _ = 3 * (1 / 100) ^ n := by rw [show |(3:ℝ) - 0| = 3 by norm_num]; ring

/-- On `[0,5]` (where `f_n` changes sign at `x=3`): `|f_n(x)| ≤ (1/4)ⁿ` via factorwise absolute
bounds `x² ≤ 25`, `|x²−9| ≤ 16`, `|x²−25| ≤ 25`, `225−x² ≥ 200`. -/
theorem fOsal_abs_le_five (n : ℕ) {x : ℝ} (h0 : 0 ≤ x) (h5 : x ≤ 5) :
    |fOsal n x| ≤ (1 / 4) ^ n := by
  have hx2 : x ^ 2 ≤ 25 := by nlinarith
  have hxx : (0 : ℝ) ≤ x ^ 2 := sq_nonneg x
  have hdenpos : (0 : ℝ) < 225 - x ^ 2 := by nlinarith
  have hnum : |x ^ (2 * n) * (x ^ 2 - 9) ^ n * (x ^ 2 - 25) ^ n| ≤ (10000 : ℝ) ^ n := by
    calc |x ^ (2 * n) * (x ^ 2 - 9) ^ n * (x ^ 2 - 25) ^ n|
        = x ^ (2 * n) * |x ^ 2 - 9| ^ n * |x ^ 2 - 25| ^ n := by
          rw [abs_mul, abs_mul, abs_pow, abs_pow, abs_pow, abs_of_nonneg h0]
      _ ≤ 25 ^ n * 16 ^ n * 25 ^ n := by
          gcongr
          · rw [pow_mul]; exact pow_le_pow_left₀ hxx hx2 n
          · rw [abs_le]; constructor <;> nlinarith
          · rw [abs_le]; constructor <;> nlinarith
      _ = (10000 : ℝ) ^ n := by rw [← mul_pow, ← mul_pow]; norm_num
  have hden : (40000 : ℝ) ^ n * 200 ≤ (225 - x ^ 2) ^ (2 * n + 1) := by
    calc (40000 : ℝ) ^ n * 200 ≤ ((225 - x ^ 2) ^ 2) ^ n * (225 - x ^ 2) := by
          gcongr
          · nlinarith
          · nlinarith
      _ = (225 - x ^ 2) ^ (2 * n + 1) := by rw [← pow_mul, ← pow_succ]
  rw [show fOsal n x = x ^ (2 * n) * (x ^ 2 - 9) ^ n * (x ^ 2 - 25) ^ n / (x ^ 2 - 225) ^ (2 * n + 1)
        from rfl, abs_div]
  rw [show |(x ^ 2 - 225) ^ (2 * n + 1)| = (225 - x ^ 2) ^ (2 * n + 1) by
        rw [abs_pow, abs_of_nonpos (by nlinarith), neg_sub]]
  rw [div_le_iff₀ (by positivity)]
  have hpow : (1 / 4 : ℝ) ^ n * 40000 ^ n = 10000 ^ n := by rw [← mul_pow]; norm_num
  calc |x ^ (2 * n) * (x ^ 2 - 9) ^ n * (x ^ 2 - 25) ^ n|
      ≤ (10000 : ℝ) ^ n := hnum
    _ = (1 / 4 : ℝ) ^ n * 40000 ^ n := hpow.symm
    _ ≤ (1 / 4 : ℝ) ^ n * (225 - x ^ 2) ^ (2 * n + 1) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        calc (40000 : ℝ) ^ n ≤ 40000 ^ n * 200 := by
              nlinarith [pow_pos (show (0:ℝ) < 40000 by norm_num) n]
          _ ≤ (225 - x ^ 2) ^ (2 * n + 1) := hden

/-- **Sharp** `[0,5]` bound `|f_n(x)| ≤ (1/32)ⁿ` via the actual integrand factor
`|φ(x)| = |x²(x²−9)(x²−25)|/(225−x²)² ≤ 1/32` (sup `≈0.026` at `x≈4.5`).  Sharper than the
factorwise `(1/4)ⁿ` — needed for `hsmall` (rate `1/32 < 0.0317` beats the lcm-clearing). -/
theorem fOsal_abs_le_five_sharp (n : ℕ) {x : ℝ} (h0 : 0 ≤ x) (h5 : x ≤ 5) :
    |fOsal n x| ≤ (1 / 32) ^ n := by
  have hxx : (0 : ℝ) ≤ x ^ 2 := sq_nonneg x
  have h25 : (0 : ℝ) ≤ 25 - x ^ 2 := by nlinarith
  have hden : (1 : ℝ) ≤ 225 - x ^ 2 := by nlinarith
  have hdenpos : (0 : ℝ) < 225 - x ^ 2 := by linarith
  set Pf : ℝ := x ^ 2 * (x ^ 2 - 9) * (x ^ 2 - 25) with hPf
  have hnum : x ^ (2 * n) * (x ^ 2 - 9) ^ n * (x ^ 2 - 25) ^ n = Pf ^ n := by
    rw [pow_mul, ← mul_pow, ← mul_pow, hPf]
  have hden_eq : (x ^ 2 - 225) ^ (2 * n + 1) = -((225 - x ^ 2) ^ (2 * n + 1)) := by
    rw [show x ^ 2 - 225 = -(225 - x ^ 2) by ring]; exact Odd.neg_pow ⟨n, by ring⟩ _
  have habs : |fOsal n x| = |Pf| ^ n / (225 - x ^ 2) ^ (2 * n + 1) := by
    unfold fOsal
    rw [hnum, hden_eq, div_neg, abs_neg, abs_div, abs_pow, abs_pow, abs_of_pos hdenpos]
  rw [habs, div_le_iff₀ (by positivity)]
  have hb : |Pf| ≤ 1 / 32 * (225 - x ^ 2) ^ 2 := by
    rw [abs_le, hPf]
    refine ⟨?_, ?_⟩
    · nlinarith [mul_nonneg hxx h25, sq_nonneg (x ^ 2 - 9), sq_nonneg (x ^ 2 - 16),
        mul_nonneg hxx (sq_nonneg (x ^ 2 - 16)), sq_nonneg (x ^ 2 - 20),
        mul_nonneg (mul_nonneg hxx h25) h25, mul_nonneg (mul_nonneg hxx h25) hxx,
        mul_nonneg hxx (sq_nonneg (x ^ 2 - 9))]
    · nlinarith [mul_nonneg hxx h25, sq_nonneg (x ^ 2 - 9), sq_nonneg (x ^ 2 - 16),
        mul_nonneg hxx (sq_nonneg (x ^ 2 - 16)), sq_nonneg (x ^ 2 - 20),
        mul_nonneg (mul_nonneg hxx h25) h25, mul_nonneg hxx h25]
  calc |Pf| ^ n ≤ (1 / 32 * (225 - x ^ 2) ^ 2) ^ n := pow_le_pow_left₀ (abs_nonneg _) hb n
    _ = (1 / 32 : ℝ) ^ n * (225 - x ^ 2) ^ (2 * n) := by rw [mul_pow, ← pow_mul]
    _ ≤ (1 / 32 : ℝ) ^ n * (225 - x ^ 2) ^ (2 * n + 1) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact pow_le_pow_right₀ hden (by omega)

/-- **Sharp geometric decay of `E2`**: `|E2 n| ≤ 5·(1/32)ⁿ`. -/
theorem E2_abs_le_sharp (n : ℕ) : |E2 n| ≤ 5 * (1 / 32) ^ n := by
  have hbnd : ∀ x ∈ Set.uIoc (0 : ℝ) 5, ‖fOsal n x‖ ≤ (1 / 32) ^ n := by
    intro x hx
    rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 5)] at hx
    rw [Real.norm_eq_abs]
    exact fOsal_abs_le_five_sharp n (le_of_lt hx.1) hx.2
  have := intervalIntegral.norm_integral_le_of_norm_le_const hbnd
  rw [Real.norm_eq_abs] at this
  calc |E2 n| = |∫ x in (0:ℝ)..5, fOsal n x| := by rw [E2]
    _ ≤ (1 / 32) ^ n * |(5 : ℝ) - 0| := this
    _ = 5 * (1 / 32) ^ n := by rw [show |(5:ℝ) - 0| = 5 by norm_num]; ring

/-- **Geometric decay of `E2`**: `|E2 n| ≤ 5·(1/4)ⁿ`. -/
theorem E2_abs_le (n : ℕ) : |E2 n| ≤ 5 * (1 / 4) ^ n := by
  have hbnd : ∀ x ∈ Set.uIoc (0 : ℝ) 5, ‖fOsal n x‖ ≤ (1 / 4) ^ n := by
    intro x hx
    rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 5)] at hx
    rw [Real.norm_eq_abs]
    exact fOsal_abs_le_five n (le_of_lt hx.1) hx.2
  have := intervalIntegral.norm_integral_le_of_norm_le_const hbnd
  rw [Real.norm_eq_abs] at this
  calc |E2 n| = |∫ x in (0:ℝ)..5, fOsal n x| := by rw [E2]
    _ ≤ (1 / 4) ^ n * |(5 : ℝ) - 0| := this
    _ = 5 * (1 / 4) ^ n := by rw [show |(5:ℝ) - 0| = 5 by norm_num]; ring

end OSalikhovTwoLog
