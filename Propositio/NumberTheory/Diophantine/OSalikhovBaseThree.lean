import Propositio.NumberTheory.Diophantine.OSalikhovDecomp

/-!
# Base case `E1 3`, `E2 3` (order-7 poles) — split for memory

`f₃(x) = x⁶(x²−9)³(x²−25)³ / (x²−225)⁷ = (x⁴+1473x²+1260993) + Σ_{j=1}^7 c_j/(x−15)^j + d_j/(x+15)^j`

where:
```
c_7 = 41990400000,  c_6 = 43390080000, c_5 = 20602512000
c_4 = 5945601600,   c_3 = 1161689880,  c_2 = 161897900
c_1 = 494871721/30 = Bseq(3)
```
and `dⱼ = (−1)^j · cⱼ` (by symmetry: f₃ is even).

Antiderivative `F3 = F3m + F3p` where:
- `F3m`: polynomial `x⁵/5+491x³+1260993x` + `(x−15)^{−k}` poles for k=1..6 + `(494871721/30)·log(15−x)`
- `F3p`: `(x+15)^{−k}` poles for k=1..6 + `(−494871721/30)·log(15+x)`

FTC gives:
- `E1 3 = F3(3) − F3(0) = 65011641937/9720 + (494871721/30)·log(2/3) = A1seq(3) + Bseq(3)·log(2/3)`
- `E2 3 = F3(5) − F3(0) = 2286792921/200 − (494871721/30)·log 2 = A2seq(3) − Bseq(3)·log 2`

Memory note: The partial-fraction identity `fOsal3_pf` (the ring step with degree-18 cleared numerator)
is isolated in its own declaration following the `OSalikhovBaseTwo` pattern.
-/

namespace OSalikhovTwoLog

open MeasureTheory intervalIntegral Set

/-- `(−15)`-pole half of the antiderivative of `f₃` (includes polynomial part). -/
noncomputable def F3m (x : ℝ) : ℝ :=
  x ^ 5 / 5 + 491 * x ^ 3 + 1260993 * x
  - 6998400000 * ((x - 15) ^ 6)⁻¹
  - 8678016000 * ((x - 15) ^ 5)⁻¹
  - 5150628000 * ((x - 15) ^ 4)⁻¹
  - 1981867200 * ((x - 15) ^ 3)⁻¹
  - 580844940 * ((x - 15) ^ 2)⁻¹
  - 161897900 * (x - 15)⁻¹
  + (494871721 / 30) * Real.log (15 - x)

/-- `(+15)`-pole half of the antiderivative of `f₃`. -/
noncomputable def F3p (x : ℝ) : ℝ :=
  6998400000 * ((x + 15) ^ 6)⁻¹
  - 8678016000 * ((x + 15) ^ 5)⁻¹
  + 5150628000 * ((x + 15) ^ 4)⁻¹
  - 1981867200 * ((x + 15) ^ 3)⁻¹
  + 580844940 * ((x + 15) ^ 2)⁻¹
  - 161897900 * (x + 15)⁻¹
  - (494871721 / 30) * Real.log (15 + x)

/-- Antiderivative of `f₃` on `(−15, 15)`. -/
noncomputable def F3 (x : ℝ) : ℝ := F3m x + F3p x

/-- Derivative of `F3m` (formula for the chain-rule output). -/
noncomputable def dF3m (x : ℝ) : ℝ :=
  x ^ 4 + 1473 * x ^ 2 + 1260993
  + 6998400000 * 6 * ((x - 15) ^ 7)⁻¹
  + 8678016000 * 5 * ((x - 15) ^ 6)⁻¹
  + 5150628000 * 4 * ((x - 15) ^ 5)⁻¹
  + 1981867200 * 3 * ((x - 15) ^ 4)⁻¹
  + 580844940 * 2 * ((x - 15) ^ 3)⁻¹
  + 161897900 * ((x - 15) ^ 2)⁻¹
  + (494871721 / 30) * (-1 / (15 - x))

/-- Derivative of `F3p`. -/
noncomputable def dF3p (x : ℝ) : ℝ :=
  - 6998400000 * 6 * ((x + 15) ^ 7)⁻¹
  + 8678016000 * 5 * ((x + 15) ^ 6)⁻¹
  - 5150628000 * 4 * ((x + 15) ^ 5)⁻¹
  + 1981867200 * 3 * ((x + 15) ^ 4)⁻¹
  - 580844940 * 2 * ((x + 15) ^ 3)⁻¹
  + 161897900 * ((x + 15) ^ 2)⁻¹
  - (494871721 / 30) * (1 / (15 + x))

/-- **Isolated partial-fraction identity** `fOsal 3 x = dF3m x + dF3p x`.
This is the heavy `field_simp; ring` step, isolated for memory. -/
theorem fOsal3_pf {x : ℝ} (h1 : x - 15 ≠ 0) (h2 : x + 15 ≠ 0) :
    fOsal 3 x = dF3m x + dF3p x := by
  unfold fOsal dF3m dF3p
  rw [show 2 * 3 = 6 from rfl, show 2 * 3 + 1 = 7 from rfl,
      show x ^ 2 - 225 = (x - 15) * (x + 15) by ring,
      show (15 : ℝ) - x = -(x - 15) by ring, show (15 : ℝ) + x = x + 15 by ring]
  field_simp
  ring

theorem hasDerivAt_F3m {x : ℝ} (hx : -15 < x) (hx' : x < 15) : HasDerivAt F3m (dF3m x) x := by
  have h1 : (x - 15) ≠ 0 := by linarith
  have hl1 : (15 - x) ≠ 0 := by linarith
  have dm : HasDerivAt (fun x : ℝ => x - 15) 1 x := by simpa using (hasDerivAt_id x).sub_const 15
  have dpow2 : HasDerivAt (fun x : ℝ => (x - 15) ^ 2) (2 * (x - 15)) x := by simpa using dm.pow 2
  have dpow3 : HasDerivAt (fun x : ℝ => (x - 15) ^ 3) (3 * (x - 15) ^ 2) x := by simpa using dm.pow 3
  have dpow4 : HasDerivAt (fun x : ℝ => (x - 15) ^ 4) (4 * (x - 15) ^ 3) x := by simpa using dm.pow 4
  have dpow5 : HasDerivAt (fun x : ℝ => (x - 15) ^ 5) (5 * (x - 15) ^ 4) x := by simpa using dm.pow 5
  have dpow6 : HasDerivAt (fun x : ℝ => (x - 15) ^ 6) (6 * (x - 15) ^ 5) x := by simpa using dm.pow 6
  have a0 : HasDerivAt (fun x : ℝ => x ^ 5 / 5) (x ^ 4) x := by
    simpa using ((hasDerivAt_id x).pow 5).div_const 5
  have a1 : HasDerivAt (fun x : ℝ => 491 * x ^ 3) (1473 * x ^ 2) x := by
    have h3 : HasDerivAt (fun x : ℝ => x ^ 3) (3 * x ^ 2) x := by simpa using hasDerivAt_pow 3 x
    have h491 := h3.const_mul (491 : ℝ)
    convert h491 using 1; ring
  have a2 : HasDerivAt (fun x : ℝ => 1260993 * x) (1260993 : ℝ) x := by
    have h := (hasDerivAt_id x).const_mul (1260993 : ℝ); simpa using h
  have b6 : HasDerivAt (fun x : ℝ => 6998400000 * ((x - 15) ^ 6)⁻¹)
      (6998400000 * (-(6 * (x - 15) ^ 5) / ((x - 15) ^ 6) ^ 2)) x :=
    (dpow6.inv (pow_ne_zero 6 h1)).const_mul 6998400000
  have b5 : HasDerivAt (fun x : ℝ => 8678016000 * ((x - 15) ^ 5)⁻¹)
      (8678016000 * (-(5 * (x - 15) ^ 4) / ((x - 15) ^ 5) ^ 2)) x :=
    (dpow5.inv (pow_ne_zero 5 h1)).const_mul 8678016000
  have b4 : HasDerivAt (fun x : ℝ => 5150628000 * ((x - 15) ^ 4)⁻¹)
      (5150628000 * (-(4 * (x - 15) ^ 3) / ((x - 15) ^ 4) ^ 2)) x :=
    (dpow4.inv (pow_ne_zero 4 h1)).const_mul 5150628000
  have b3 : HasDerivAt (fun x : ℝ => 1981867200 * ((x - 15) ^ 3)⁻¹)
      (1981867200 * (-(3 * (x - 15) ^ 2) / ((x - 15) ^ 3) ^ 2)) x :=
    (dpow3.inv (pow_ne_zero 3 h1)).const_mul 1981867200
  have b2 : HasDerivAt (fun x : ℝ => 580844940 * ((x - 15) ^ 2)⁻¹)
      (580844940 * (-(2 * (x - 15)) / ((x - 15) ^ 2) ^ 2)) x :=
    (dpow2.inv (pow_ne_zero 2 h1)).const_mul 580844940
  have b1 : HasDerivAt (fun x : ℝ => 161897900 * (x - 15)⁻¹)
      (161897900 * (-1 / (x - 15) ^ 2)) x := by
    have d := (dm.inv h1).const_mul 161897900; simpa using d
  have lm : HasDerivAt (fun x : ℝ => (494871721 / 30 : ℝ) * Real.log (15 - x))
      ((494871721 / 30 : ℝ) * (-1 / (15 - x))) x := by
    have hi : HasDerivAt (fun x : ℝ => (15 : ℝ) - x) (-1) x := by
      simpa using (hasDerivAt_id x).const_sub 15
    simpa using (hi.log hl1).const_mul (494871721 / 30 : ℝ)
  have hsum := ((((((((a0.add a1).add a2).sub b6).sub b5).sub b4).sub b3).sub b2).sub b1).add lm
  convert hsum using 1
  unfold dF3m
  field_simp
  ring

theorem hasDerivAt_F3p {x : ℝ} (hx : -15 < x) (hx' : x < 15) : HasDerivAt F3p (dF3p x) x := by
  have h2 : (x + 15) ≠ 0 := by linarith
  have hl2 : (15 + x) ≠ 0 := by linarith
  have dp : HasDerivAt (fun x : ℝ => x + 15) 1 x := by simpa using (hasDerivAt_id x).add_const 15
  have dpow2 : HasDerivAt (fun x : ℝ => (x + 15) ^ 2) (2 * (x + 15)) x := by simpa using dp.pow 2
  have dpow3 : HasDerivAt (fun x : ℝ => (x + 15) ^ 3) (3 * (x + 15) ^ 2) x := by simpa using dp.pow 3
  have dpow4 : HasDerivAt (fun x : ℝ => (x + 15) ^ 4) (4 * (x + 15) ^ 3) x := by simpa using dp.pow 4
  have dpow5 : HasDerivAt (fun x : ℝ => (x + 15) ^ 5) (5 * (x + 15) ^ 4) x := by simpa using dp.pow 5
  have dpow6 : HasDerivAt (fun x : ℝ => (x + 15) ^ 6) (6 * (x + 15) ^ 5) x := by simpa using dp.pow 6
  have b6 : HasDerivAt (fun x : ℝ => 6998400000 * ((x + 15) ^ 6)⁻¹)
      (6998400000 * (-(6 * (x + 15) ^ 5) / ((x + 15) ^ 6) ^ 2)) x :=
    (dpow6.inv (pow_ne_zero 6 h2)).const_mul 6998400000
  have b5 : HasDerivAt (fun x : ℝ => 8678016000 * ((x + 15) ^ 5)⁻¹)
      (8678016000 * (-(5 * (x + 15) ^ 4) / ((x + 15) ^ 5) ^ 2)) x :=
    (dpow5.inv (pow_ne_zero 5 h2)).const_mul 8678016000
  have b4 : HasDerivAt (fun x : ℝ => 5150628000 * ((x + 15) ^ 4)⁻¹)
      (5150628000 * (-(4 * (x + 15) ^ 3) / ((x + 15) ^ 4) ^ 2)) x :=
    (dpow4.inv (pow_ne_zero 4 h2)).const_mul 5150628000
  have b3 : HasDerivAt (fun x : ℝ => 1981867200 * ((x + 15) ^ 3)⁻¹)
      (1981867200 * (-(3 * (x + 15) ^ 2) / ((x + 15) ^ 3) ^ 2)) x :=
    (dpow3.inv (pow_ne_zero 3 h2)).const_mul 1981867200
  have b2 : HasDerivAt (fun x : ℝ => 580844940 * ((x + 15) ^ 2)⁻¹)
      (580844940 * (-(2 * (x + 15)) / ((x + 15) ^ 2) ^ 2)) x :=
    (dpow2.inv (pow_ne_zero 2 h2)).const_mul 580844940
  have b1 : HasDerivAt (fun x : ℝ => 161897900 * (x + 15)⁻¹)
      (161897900 * (-1 / (x + 15) ^ 2)) x := by
    have d := (dp.inv h2).const_mul 161897900; simpa using d
  have lp : HasDerivAt (fun x : ℝ => (494871721 / 30 : ℝ) * Real.log (15 + x))
      ((494871721 / 30 : ℝ) * (1 / (15 + x))) x := by
    have hi : HasDerivAt (fun x : ℝ => (15 : ℝ) + x) 1 x := by
      simpa using (hasDerivAt_id x).const_add 15
    simpa using (hi.log hl2).const_mul (494871721 / 30 : ℝ)
  have hsum := ((((((b6.sub b5).add b4).sub b3).add b2).sub b1).sub lp)
  convert hsum using 1
  unfold dF3p
  field_simp
  ring

theorem hasDerivAt_F3 {x : ℝ} (hx : -15 < x) (hx' : x < 15) : HasDerivAt F3 (fOsal 3 x) x := by
  have h1 : (x - 15) ≠ 0 := by linarith
  have h2 : (x + 15) ≠ 0 := by linarith
  rw [fOsal3_pf h1 h2]
  exact (hasDerivAt_F3m hx hx').add (hasDerivAt_F3p hx hx')

/-- **Base case `E1 3`**: `∫₀³ f₃ = 65011641937/9720 + (494871721/30)·log(2/3)`. -/
theorem E1_three : E1 3 = 65011641937 / 9720 + (494871721 / 30) * Real.log (2 / 3) := by
  unfold E1
  rw [integral_eq_sub_of_hasDerivAt (f := F3)
      (fun x hx => hasDerivAt_F3
        (by rw [uIcc_of_le (by norm_num)] at hx; simp only [mem_Icc] at hx; linarith [hx.1])
        (by rw [uIcc_of_le (by norm_num)] at hx; simp only [mem_Icc] at hx; linarith [hx.2]))
      (fOsal_intervalIntegrable_three 3)]
  unfold F3 F3m F3p
  rw [show (15 : ℝ) - 3 = 12 by norm_num, show (15 : ℝ) + 3 = 18 by norm_num,
      show (15 : ℝ) - 0 = 15 by norm_num, show (15 : ℝ) + 0 = 15 by norm_num,
      show (2 : ℝ) / 3 = 12 / 18 by norm_num, Real.log_div (by norm_num) (by norm_num)]
  ring

/-- **Base case `E2 3`** (reuses `F3`): `∫₀⁵ f₃ = 2286792921/200 − (494871721/30)·log2`. -/
theorem E2_three : E2 3 = 2286792921 / 200 - (494871721 / 30) * Real.log 2 := by
  unfold E2
  rw [integral_eq_sub_of_hasDerivAt (f := F3)
      (fun x hx => hasDerivAt_F3
        (by rw [uIcc_of_le (by norm_num)] at hx; simp only [mem_Icc] at hx; linarith [hx.1])
        (by rw [uIcc_of_le (by norm_num)] at hx; simp only [mem_Icc] at hx; linarith [hx.2]))
      (fOsal_intervalIntegrable_five 3)]
  unfold F3 F3m F3p
  rw [show (15 : ℝ) - 5 = 10 by norm_num, show (15 : ℝ) + 5 = 20 by norm_num,
      show (15 : ℝ) - 0 = 15 by norm_num, show (15 : ℝ) + 0 = 15 by norm_num,
      show (20 : ℝ) = 10 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  ring

end OSalikhovTwoLog
