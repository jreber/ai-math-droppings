import Propositio.NumberTheory.Diophantine.OSalikhovDecomp

/-!
# Base case `E1 2`, `E2 2` (order-5 poles) — split for memory

`f₂ = (x²+1057) + Σ_{j=1}^5 c_j/(x−15)^j + d_j/(x+15)^j`, `c₁=139867/10=B(2), c₂=132440, c₃=781680,
c₄=2635200, c₅=3888000`, `d_j=(−1)^j c_j`.

Memory split (Lean frees memory between declarations; a 7 GB box OOMs on the inline 12-term version):
* `fOsal2_pf` — the heavy `field_simp;ring` partial-fraction identity, isolated, with the denominator
  pre-factored `x²−225=(x−15)(x+15)` so the cleared identity is degree 12, not 30.
* `hasDerivAt_F2m`, `hasDerivAt_F2p` — the two `≈6`-term `HasDerivAt` halves (each F1-sized), isolated.
* `hasDerivAt_F2` — only a cheap `.add` + rewrite by `fOsal2_pf`.
Leaf file (nothing imports it). -/

namespace OSalikhovTwoLog

open MeasureTheory intervalIntegral Set

/-- `(−15)`-pole half of the antiderivative. -/
noncomputable def F2m (x : ℝ) : ℝ :=
  x ^ 3 / 3 + 1057 * x - 972000 * ((x - 15) ^ 4)⁻¹ - 878400 * ((x - 15) ^ 3)⁻¹
    - 390840 * ((x - 15) ^ 2)⁻¹ - 132440 * (x - 15)⁻¹ + (139867 / 10) * Real.log (15 - x)

/-- `(+15)`-pole half of the antiderivative. -/
noncomputable def F2p (x : ℝ) : ℝ :=
  972000 * ((x + 15) ^ 4)⁻¹ - 878400 * ((x + 15) ^ 3)⁻¹ + 390840 * ((x + 15) ^ 2)⁻¹
    - 132440 * (x + 15)⁻¹ - (139867 / 10) * Real.log (15 + x)

/-- Antiderivative of `f₂` on `(−15,15)`. -/
noncomputable def F2 (x : ℝ) : ℝ := F2m x + F2p x

/-- The two half-derivatives. -/
noncomputable def dF2m (x : ℝ) : ℝ :=
  3 * x ^ 2 / 3 + 1057 - (-3888000 * ((x - 15) ^ 5)⁻¹) - (-2635200 * ((x - 15) ^ 4)⁻¹)
    - (-781680 * ((x - 15) ^ 3)⁻¹) - (-132440 * ((x - 15) ^ 2)⁻¹) + (139867 / 10) * (-1 / (15 - x))
noncomputable def dF2p (x : ℝ) : ℝ :=
  (-3888000 * ((x + 15) ^ 5)⁻¹) - (-2635200 * ((x + 15) ^ 4)⁻¹) + (-781680 * ((x + 15) ^ 3)⁻¹)
    - (-132440 * ((x + 15) ^ 2)⁻¹) - (139867 / 10) * (1 / (15 + x))

/-- **Isolated partial-fraction identity** `f₂ = dF2m + dF2p` (the only heavy `field_simp;ring`). -/
theorem fOsal2_pf {x : ℝ} (h1 : x - 15 ≠ 0) (h2 : x + 15 ≠ 0) :
    fOsal 2 x = dF2m x + dF2p x := by
  unfold fOsal dF2m dF2p
  rw [show 2 * 2 = 4 from rfl, show 2 * 2 + 1 = 5 from rfl,
      show x ^ 2 - 225 = (x - 15) * (x + 15) by ring,
      show (15 : ℝ) - x = -(x - 15) by ring, show (15 : ℝ) + x = x + 15 by ring]
  field_simp
  ring

theorem hasDerivAt_F2m {x : ℝ} (hx : -15 < x) (hx' : x < 15) : HasDerivAt F2m (dF2m x) x := by
  have h1 : (x - 15) ≠ 0 := by linarith
  have hl1 : (15 - x) ≠ 0 := by linarith
  have dm : HasDerivAt (fun x : ℝ => x - 15) 1 x := by simpa using (hasDerivAt_id x).sub_const 15
  have dpow2 : HasDerivAt (fun x : ℝ => (x - 15) ^ 2) (2 * (x - 15)) x := by simpa using dm.pow 2
  have dpow3 : HasDerivAt (fun x : ℝ => (x - 15) ^ 3) (3 * (x - 15) ^ 2) x := by simpa using dm.pow 3
  have dpow4 : HasDerivAt (fun x : ℝ => (x - 15) ^ 4) (4 * (x - 15) ^ 3) x := by simpa using dm.pow 4
  have a0 : HasDerivAt (fun x : ℝ => x ^ 3 / 3) (3 * x ^ 2 / 3) x := by
    simpa using ((hasDerivAt_id x).pow 3).div_const 3
  have a1 : HasDerivAt (fun x : ℝ => 1057 * x) 1057 x := by simpa using (hasDerivAt_id x).const_mul 1057
  have b4 : HasDerivAt (fun x : ℝ => 972000 * ((x - 15) ^ 4)⁻¹) (-3888000 * ((x - 15) ^ 5)⁻¹) x := by
    have d := ((dpow4.inv (pow_ne_zero 4 h1)).const_mul 972000); convert d using 1 <;> field_simp <;> ring
  have b3 : HasDerivAt (fun x : ℝ => 878400 * ((x - 15) ^ 3)⁻¹) (-2635200 * ((x - 15) ^ 4)⁻¹) x := by
    have d := ((dpow3.inv (pow_ne_zero 3 h1)).const_mul 878400); convert d using 1 <;> field_simp <;> ring
  have b2 : HasDerivAt (fun x : ℝ => 390840 * ((x - 15) ^ 2)⁻¹) (-781680 * ((x - 15) ^ 3)⁻¹) x := by
    have d := ((dpow2.inv (pow_ne_zero 2 h1)).const_mul 390840); convert d using 1 <;> field_simp <;> ring
  have b1 : HasDerivAt (fun x : ℝ => 132440 * (x - 15)⁻¹) (-132440 * ((x - 15) ^ 2)⁻¹) x := by
    have d := ((dm.inv h1).const_mul 132440); convert d using 1 <;> field_simp <;> ring
  have lm : HasDerivAt (fun x : ℝ => (139867 / 10) * Real.log (15 - x))
      ((139867 / 10) * (-1 / (15 - x))) x := by
    have hi : HasDerivAt (fun x : ℝ => (15 : ℝ) - x) (-1) x := by
      simpa using (hasDerivAt_id x).const_sub 15
    simpa using (hi.log hl1).const_mul (139867 / 10)
  exact ((((((a0.add a1).sub b4).sub b3).sub b2).sub b1).add lm)

theorem hasDerivAt_F2p {x : ℝ} (hx : -15 < x) (hx' : x < 15) : HasDerivAt F2p (dF2p x) x := by
  have h2 : (x + 15) ≠ 0 := by linarith
  have hl2 : (15 + x) ≠ 0 := by linarith
  have dp : HasDerivAt (fun x : ℝ => x + 15) 1 x := by simpa using (hasDerivAt_id x).add_const 15
  have dpow2 : HasDerivAt (fun x : ℝ => (x + 15) ^ 2) (2 * (x + 15)) x := by simpa using dp.pow 2
  have dpow3 : HasDerivAt (fun x : ℝ => (x + 15) ^ 3) (3 * (x + 15) ^ 2) x := by simpa using dp.pow 3
  have dpow4 : HasDerivAt (fun x : ℝ => (x + 15) ^ 4) (4 * (x + 15) ^ 3) x := by simpa using dp.pow 4
  have b4 : HasDerivAt (fun x : ℝ => 972000 * ((x + 15) ^ 4)⁻¹) (-3888000 * ((x + 15) ^ 5)⁻¹) x := by
    have d := ((dpow4.inv (pow_ne_zero 4 h2)).const_mul 972000); convert d using 1 <;> field_simp <;> ring
  have b3 : HasDerivAt (fun x : ℝ => 878400 * ((x + 15) ^ 3)⁻¹) (-2635200 * ((x + 15) ^ 4)⁻¹) x := by
    have d := ((dpow3.inv (pow_ne_zero 3 h2)).const_mul 878400); convert d using 1 <;> field_simp <;> ring
  have b2 : HasDerivAt (fun x : ℝ => 390840 * ((x + 15) ^ 2)⁻¹) (-781680 * ((x + 15) ^ 3)⁻¹) x := by
    have d := ((dpow2.inv (pow_ne_zero 2 h2)).const_mul 390840); convert d using 1 <;> field_simp <;> ring
  have b1 : HasDerivAt (fun x : ℝ => 132440 * (x + 15)⁻¹) (-132440 * ((x + 15) ^ 2)⁻¹) x := by
    have d := ((dp.inv h2).const_mul 132440); convert d using 1 <;> field_simp <;> ring
  have lp : HasDerivAt (fun x : ℝ => (139867 / 10) * Real.log (15 + x))
      ((139867 / 10) * (1 / (15 + x))) x := by
    have hi : HasDerivAt (fun x : ℝ => (15 : ℝ) + x) 1 x := by
      simpa using (hasDerivAt_id x).const_add 15
    simpa using (hi.log hl2).const_mul (139867 / 10)
  exact ((((b4.sub b3).add b2).sub b1).sub lp)

theorem hasDerivAt_F2 {x : ℝ} (hx : -15 < x) (hx' : x < 15) : HasDerivAt F2 (fOsal 2 x) x := by
  have h1 : (x - 15) ≠ 0 := by linarith
  have h2 : (x + 15) ≠ 0 := by linarith
  rw [fOsal2_pf h1 h2]
  exact (hasDerivAt_F2m hx hx').add (hasDerivAt_F2p hx hx')

/-- **Base case `E1 2`**: `∫₀³ f₂ = 3674885/648 + (139867/10)·log(2/3)`. -/
theorem E1_two : E1 2 = 3674885 / 648 + (139867 / 10) * Real.log (2 / 3) := by
  unfold E1
  rw [integral_eq_sub_of_hasDerivAt (f := F2)
      (fun x hx => hasDerivAt_F2
        (by rw [uIcc_of_le (by norm_num)] at hx; simp only [mem_Icc] at hx; linarith [hx.1])
        (by rw [uIcc_of_le (by norm_num)] at hx; simp only [mem_Icc] at hx; linarith [hx.2]))
      (fOsal_intervalIntegrable_three 2)]
  unfold F2 F2m F2p
  rw [show (15 : ℝ) - 3 = 12 by norm_num, show (15 : ℝ) + 3 = 18 by norm_num,
      show (15 : ℝ) - 0 = 15 by norm_num, show (15 : ℝ) + 0 = 15 by norm_num,
      show (2 : ℝ) / 3 = 12 / 18 by norm_num, Real.log_div (by norm_num) (by norm_num)]
  ring

/-- **Base case `E2 2`** (reuses `F2`): `∫₀⁵ f₂ = 1163381/120 − (139867/10)·log2`. -/
theorem E2_two : E2 2 = 1163381 / 120 - (139867 / 10) * Real.log 2 := by
  unfold E2
  rw [integral_eq_sub_of_hasDerivAt (f := F2)
      (fun x hx => hasDerivAt_F2
        (by rw [uIcc_of_le (by norm_num)] at hx; simp only [mem_Icc] at hx; linarith [hx.1])
        (by rw [uIcc_of_le (by norm_num)] at hx; simp only [mem_Icc] at hx; linarith [hx.2]))
      (fOsal_intervalIntegrable_five 2)]
  unfold F2 F2m F2p
  rw [show (15 : ℝ) - 5 = 10 by norm_num, show (15 : ℝ) + 5 = 20 by norm_num,
      show (15 : ℝ) - 0 = 15 by norm_num, show (15 : ℝ) + 0 = 15 by norm_num,
      show (20 : ℝ) = 10 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  ring

end OSalikhovTwoLog
