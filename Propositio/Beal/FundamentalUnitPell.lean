import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.NumberTheory.Pell
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

/-!
# Fundamental unit of ℤ[φ] — the golden ratio φ = (1+√5)/2

This file proves that the golden ratio `φ = (1+√5)/2` is the fundamental unit of
`ℤ[φ] = 𝓞(ℚ(√5))`. We work in `ℝ` using `Real.goldenRatio` and `Real.goldenConj`.

## Main results (proved, axiom-clean unless noted)

1. `goldenRatio_gt_one`: φ > 1.
2. `goldenRatio_sq_eq`: φ² = φ + 1.
3. `phi_is_unit`: φ * (φ - 1) = 1.
4. `phi_inv_eq`: φ⁻¹ = φ - 1.
5. `norm_form_identity`: (a + b*φ) * (a + b*ψ) = a² + ab - b².
6. `sqrt5_gt_two`: √5 > 2.
7. `sqrt5_lt_three`: √5 < 3.
8. `two_phi_sub_one`: 2φ - 1 = √5.
9. `one_div_phi`: 1/φ = φ - 1.
10. `phi_plus_inv`: φ + 1/φ = √5.
11. `no_unit_in_one_phi`: No unit a+b*φ with N = ±1 lies in (1, φ).
12. `pell5_prop`: (9,4) satisfies x² - 5y² = 1.
13. `pell5_fundamental_solution`: (9,4) is fundamental.
14. `beal_fundamental_unit_sqrt5`: Every unit equals ±φⁿ.
-/

open Real goldenRatio

noncomputable section

namespace BealFundamentalUnitPell

/-! ## Tier 0: Re-export key GoldenRatio facts from mathlib -/

theorem goldenRatio_gt_one : (1 : ℝ) < goldenRatio := one_lt_goldenRatio
theorem phi_lt_two : goldenRatio < 2 := goldenRatio_lt_two
theorem goldenRatio_sq_eq : goldenRatio ^ 2 = goldenRatio + 1 := goldenRatio_sq
theorem golden_sum : goldenRatio + goldenConj = 1 := goldenRatio_add_goldenConj
theorem golden_prod : goldenRatio * goldenConj = -1 := goldenRatio_mul_goldenConj
theorem goldenConj_lt_zero : goldenConj < 0 := goldenConj_neg
theorem goldenConj_gt_neg_one : (-1 : ℝ) < goldenConj := neg_one_lt_goldenConj
theorem golden_diff : goldenRatio - goldenConj = Real.sqrt 5 := goldenRatio_sub_goldenConj

/-! ## Tier 1: φ is a unit — φ * (φ - 1) = 1 -/

theorem phi_is_unit : goldenRatio * (goldenRatio - 1) = 1 := by
  nlinarith [goldenRatio_sq, goldenRatio_pos]

theorem phi_inv_eq : goldenRatio⁻¹ = goldenRatio - 1 := by
  have h : goldenRatio * (goldenRatio - 1) = 1 := phi_is_unit
  have : goldenRatio * (goldenRatio - 1) = goldenRatio * goldenRatio⁻¹ := by
    rw [mul_inv_cancel₀ goldenRatio_ne_zero]
    linarith
  have := mul_left_cancel₀ goldenRatio_ne_zero this
  linarith

/-! ## Tier 1: Norm form identity -/

/-- (a + b*φ) * (a + b*ψ) = a² + ab - b² (the field norm N(a+bφ)). -/
theorem norm_form_identity (a b : ℤ) :
    ((a : ℝ) + b * goldenRatio) * ((a : ℝ) + b * goldenConj) =
      (a ^ 2 + a * b - b ^ 2 : ℤ) := by
  push_cast
  have hsum : goldenRatio + goldenConj = 1 := goldenRatio_add_goldenConj
  have hprod : goldenRatio * goldenConj = -1 := goldenRatio_mul_goldenConj
  -- (a + bφ)(a + bψ) = a² + ab(φ+ψ) + b²(φψ) = a² + ab·1 + b²·(-1) = a² + ab - b²
  linear_combination (a : ℝ) * b * hsum + (b : ℝ) ^ 2 * hprod

/-! ## Tier 2: √5 bounds and φ identities -/

theorem sqrt5_gt_two : (2 : ℝ) < Real.sqrt 5 := by
  have h4 : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [← h4]; exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)

theorem sqrt5_lt_three : Real.sqrt 5 < 3 := by
  rw [Real.sqrt_lt' (by norm_num)]; norm_num

theorem two_phi_sub_one : 2 * goldenRatio - 1 = Real.sqrt 5 := by
  have hphi_sq : goldenRatio ^ 2 = goldenRatio + 1 := goldenRatio_sq
  have h2phi_pos : (0 : ℝ) < 2 * goldenRatio - 1 := by linarith [one_lt_goldenRatio]
  have hdef : (2 * goldenRatio - 1) ^ 2 = 5 := by nlinarith [hphi_sq]
  have hsq5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hsq5_pos : (0 : ℝ) < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)
  nlinarith [sq_nonneg (2 * goldenRatio - 1 - Real.sqrt 5)]

theorem one_div_phi : (1 : ℝ) / goldenRatio = goldenRatio - 1 := by
  rw [div_eq_iff goldenRatio_ne_zero]; linarith [phi_is_unit]

theorem phi_plus_inv : goldenRatio + 1 / goldenRatio = Real.sqrt 5 := by
  rw [one_div_phi]; linarith [two_phi_sub_one]

/-! ## Tier 2: Key minimality lemma — no unit in (1, φ) -/

/-- **Fundamental minimality.** No element `a + b*φ` with norm ±1 lies in `(1, φ)`. -/
theorem no_unit_in_one_phi (a b : ℤ)
    (hN : a ^ 2 + a * b - b ^ 2 = 1 ∨ a ^ 2 + a * b - b ^ 2 = -1)
    (h1 : (1 : ℝ) < (a : ℝ) + b * goldenRatio)
    (h2 : (a : ℝ) + b * goldenRatio < goldenRatio) : False := by
  -- Abbreviations
  let u : ℝ := (a : ℝ) + b * goldenRatio
  let ub : ℝ := (a : ℝ) + b * goldenConj
  -- Key algebraic facts
  have hsum : goldenRatio + goldenConj = 1 := goldenRatio_add_goldenConj
  have hprod : goldenRatio * goldenConj = -1 := goldenRatio_mul_goldenConj
  -- Norm: u * ū = N(a+bφ) = a²+ab-b²
  have hNorm : u * ub = (a ^ 2 + a * b - b ^ 2 : ℤ) := by
    show ((a : ℝ) + b * goldenRatio) * ((a : ℝ) + b * goldenConj) = _
    push_cast
    linear_combination (a : ℝ) * b * hsum + (b : ℝ) ^ 2 * hprod
  -- b*√5 = u - ū (from φ - ψ = √5)
  have hbsqrt5 : (b : ℝ) * Real.sqrt 5 = u - ub := by
    show (b : ℝ) * Real.sqrt 5 = ((a : ℝ) + b * goldenRatio) - ((a : ℝ) + b * goldenConj)
    have hdiff : goldenRatio - goldenConj = Real.sqrt 5 := goldenRatio_sub_goldenConj
    linear_combination -(b : ℝ) * hdiff
  have hu_pos : (0 : ℝ) < u := by show (0 : ℝ) < (a : ℝ) + b * goldenRatio; linarith
  have hphi_pos : (0 : ℝ) < goldenRatio := goldenRatio_pos
  have hphi_inv : goldenRatio * (goldenRatio - 1) = 1 := phi_is_unit
  have hsq5_pos : (0 : ℝ) < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)
  rcases hN with hNpos | hNneg
  · -- ━━━ Case N = +1 ━━━
    -- u * ub = 1
    have hNorm1 : u * ub = 1 := by
      have := hNorm; simp only [hNpos] at this; push_cast at this; linarith
    -- ub = 1/u
    have hub_eq : ub = 1 / u := by
      have hu_ne : u ≠ 0 := ne_of_gt hu_pos
      field_simp [hu_ne]
      linarith [hNorm1]
    -- b*√5 = u - 1/u
    have hbsqrt5' : (b : ℝ) * Real.sqrt 5 = u - 1 / u := by
      rw [hbsqrt5]; show u - ub = u - 1 / u; rw [hub_eq]
    -- b*√5 > 0 (u > 1 implies u > 1/u)
    have hbsq5_pos : (0 : ℝ) < (b : ℝ) * Real.sqrt 5 := by
      rw [hbsqrt5']
      have : 1 / u < 1 := by rw [div_lt_one hu_pos]; linarith
      have : 1 / u < u := by linarith
      linarith
    -- 1/u > φ-1 (since u < φ and both positive)
    have h_inv_gt : goldenRatio - 1 < 1 / u := by
      rw [← one_div_phi]
      apply div_lt_div_of_pos_left _ _ h2
      · norm_num
      · linarith
    -- b*√5 = u - 1/u < φ - (φ-1) = 1
    have hbsq5_lt1 : (b : ℝ) * Real.sqrt 5 < 1 := by
      rw [hbsqrt5']; linarith
    -- b > 0: from b*√5 > 0
    have hb_pos_r : (0 : ℝ) < (b : ℝ) := by
      rcases (mul_pos_iff.mp hbsq5_pos) with ⟨hb, _⟩ | ⟨_, hsq5⟩
      · exact hb
      · exact absurd hsq5 (not_lt.mpr (le_of_lt hsq5_pos))
    -- b ≥ 1: b is a positive integer
    have hb_ge1 : (1 : ℝ) ≤ (b : ℝ) := by
      have : (0 : ℤ) < b := by exact_mod_cast hb_pos_r
      exact_mod_cast this
    -- b ≥ 1 and √5 > 2 means b*√5 ≥ √5 > 2 > 1 — contradicts b*√5 < 1
    nlinarith [sqrt5_gt_two]
  · -- ━━━ Case N = -1 ━━━
    -- u * ub = -1
    have hNorm_neg : u * ub = -1 := by
      have := hNorm; simp only [hNneg] at this; push_cast at this; linarith
    -- ub = -1/u
    have hub_eq : ub = -(1 / u) := by
      have hu_ne : u ≠ 0 := ne_of_gt hu_pos
      have : u * ub = -(1 : ℝ) := hNorm_neg
      have : ub = -(1 / u) := by
        field_simp [hu_ne] at this ⊢; linarith
      exact this
    -- b*√5 = u + 1/u
    have hbsqrt5' : (b : ℝ) * Real.sqrt 5 = u + 1 / u := by
      rw [hbsqrt5]; show u - ub = u + 1 / u; rw [hub_eq]; ring
    -- b*√5 > 2 by AM-GM (u > 1 strictly)
    have hbsq5_gt2 : (2 : ℝ) < (b : ℝ) * Real.sqrt 5 := by
      rw [hbsqrt5']
      have h_one_div_u : 1 / u > 0 := div_pos one_pos hu_pos
      have h_um1_sq : 0 < (u - 1) ^ 2 := by
        apply sq_pos_of_ne_zero; linarith
      have : u ^ 2 - 2 * u + 1 > 0 := by nlinarith [h_um1_sq]
      have : u + 1 / u - 2 = (u ^ 2 - 2 * u + 1) / u := by
        field_simp; ring
      linarith [div_pos (by linarith : u ^ 2 - 2 * u + 1 > 0) hu_pos,
                this.symm ▸ div_pos (by linarith) hu_pos]
    -- b ≥ 1 (from b*√5 > 2 > 0 and √5 > 0)
    have hb_ge1 : (1 : ℤ) ≤ b := by
      by_contra h
      have hb_le0 : b ≤ 0 := Int.not_lt.mp (by omega)
      have hb_le0_r : (b : ℝ) ≤ 0 := by exact_mod_cast hb_le0
      have : (b : ℝ) * Real.sqrt 5 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hb_le0_r
                                             (le_of_lt hsq5_pos)
      linarith
    have hb_ge1_r : (1 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb_ge1
    -- b*√5 < √5 (use u + 1/u < φ + 1/φ = √5)
    -- Key: (φ - u)(φu - 1) > 0, divide by φu to get φ + 1/φ > u + 1/u
    have hbsq5_lt_sqrt5 : (b : ℝ) * Real.sqrt 5 < Real.sqrt 5 := by
      rw [hbsqrt5', ← phi_plus_inv]
      -- u + 1/u < φ + 1/φ
      have hphiu_pos : goldenRatio * u > 0 := mul_pos hphi_pos hu_pos
      have hphiu_gt1 : goldenRatio * u > 1 := by nlinarith
      have hkey : (goldenRatio - u) * (goldenRatio * u - 1) > 0 :=
        mul_pos (by linarith) (by linarith)
      have heq : goldenRatio + 1 / goldenRatio - (u + 1 / u) =
          (goldenRatio - u) * (goldenRatio * u - 1) / (goldenRatio * u) := by
        field_simp; ring
      linarith [div_pos hkey hphiu_pos, heq.symm.le]
    -- b ≥ 1 and √5 > 0: b*√5 ≥ √5 — contradicts b*√5 < √5
    nlinarith

/-! ## Tier 2: Pell equation -/

theorem pell5_prop : (9 : ℤ) ^ 2 - 5 * 4 ^ 2 = 1 := by norm_num

/-! ## Tier 3: (9,4) is the fundamental Pell solution -/

theorem pell5_fundamental_solution :
    Pell.IsFundamental (Pell.Solution₁.mk 9 4 pell5_prop) := by
  refine ⟨by norm_num [Pell.Solution₁.x_mk], by norm_num [Pell.Solution₁.y_mk], ?_⟩
  intro b hb
  rw [Pell.Solution₁.x_mk]
  -- Goal: 9 ≤ b.x. Proof: no Pell solution exists with 1 < b.x < 9.
  by_contra h
  push_neg at h
  have hprop := b.prop  -- b.x ^ 2 - 5 * b.y ^ 2 = 1
  have hx_lb : 2 ≤ b.x := hb
  have hx_ub : b.x ≤ 8 := by omega
  -- Case split: b.x ∈ {2,...,8}
  interval_cases b.x
  · -- b.x = 2: 4 - 5y² = 1 ⟹ 5y² = 3, no integer solution (5 ∤ 3)
    have : 5 * b.y ^ 2 = 3 := by nlinarith
    omega
  · -- b.x = 3: 9 - 5y² = 1 ⟹ 5y² = 8, no integer solution (5 ∤ 8)
    have : 5 * b.y ^ 2 = 8 := by nlinarith
    omega
  · -- b.x = 4: 16 - 5y² = 1 ⟹ y² = 3, not a perfect square
    have hy2 : b.y ^ 2 = 3 := by nlinarith
    have h_ub' : 4 * b.y ≤ 7 := by nlinarith [sq_nonneg (b.y - 2)]
    have h_lb' : -4 * b.y ≤ 7 := by nlinarith [sq_nonneg (b.y + 2)]
    have h_ub : b.y ≤ 1 := by omega
    have h_lb : -1 ≤ b.y := by omega
    interval_cases b.y <;> norm_num at hy2
  · -- b.x = 5: 25 - 5y² = 1 ⟹ 5y² = 24, no integer solution (5 ∤ 24)
    have : 5 * b.y ^ 2 = 24 := by nlinarith
    omega
  · -- b.x = 6: 36 - 5y² = 1 ⟹ y² = 7, not a perfect square
    have hy2 : b.y ^ 2 = 7 := by nlinarith
    have h_ub' : 6 * b.y ≤ 16 := by nlinarith [sq_nonneg (b.y - 3)]
    have h_lb' : -6 * b.y ≤ 16 := by nlinarith [sq_nonneg (b.y + 3)]
    have h_ub : b.y ≤ 2 := by omega
    have h_lb : -2 ≤ b.y := by omega
    interval_cases b.y <;> norm_num at hy2
  · -- b.x = 7: 49 - 5y² = 1 ⟹ 5y² = 48, no integer solution (5 ∤ 48)
    have : 5 * b.y ^ 2 = 48 := by nlinarith
    omega
  · -- b.x = 8: 64 - 5y² = 1 ⟹ 5y² = 63, no integer solution (5 ∤ 63)
    have : 5 * b.y ^ 2 = 63 := by nlinarith
    omega

/-! ## Tier 3: Full fundamental unit theorem -/

/-!
### Proof strategy: strong induction on `b.natAbs`

We prove: for any `(a, b : ℤ)` with `a² + ab - b² = ±1`,
the element `a + b·φ ∈ ℝ` equals `±φⁿ` for some `n : ℤ`.

**Key facts used:**
- `φ⁻¹ = φ - 1`: inverse of φ.
- `φ⁻¹ · (a + b·φ) = (b - a) + a·φ`: coordinate descent transformation.
- `N((b-a) + a·φ) = -(a² + ab - b²)`: norm under descent.
- No unit lies in `(1, φ)` (by `no_unit_in_one_phi`).
- `φ² = φ + 1` and `1 + φ = φ²`.

**Induction structure:**
- By symmetry, reduce to the case where `a + b·φ > 0`.
  (If `a + b·φ < 0`, negate to get `-(a + b·φ) = (-a) + (-b)·φ`, same norm, positive.)
- Further reduce to `a + b·φ ≥ 1` (if between 0 and 1, take inverse which is in (1,∞)).
- Use `no_unit_in_one_phi` to show the unit is `≥ φ` (not in (1,φ)) or `= 1` (= φ⁰).
- If `u = 1 = φ⁰`, done.
- If `u ≥ φ`, apply `φ⁻¹` to reduce: `v = φ⁻¹·u = (b-a) + a·φ`, which has
  norm `-N(u) = ∓1` and we show `v > 0` and `b' = a.natAbs < b.natAbs`.
  By IH, `v = ±φᵐ`, so `u = φ·v = ±φᵐ⁺¹`.
-/

/-- Coordinate descent: φ⁻¹ · (a + b·φ) = (b - a) + a·φ -/
private lemma phi_inv_mul_coord (a b : ℤ) :
    goldenRatio⁻¹ * ((a : ℝ) + b * goldenRatio) =
      ((b - a : ℤ) : ℝ) + a * goldenRatio := by
  have hinv : goldenRatio⁻¹ = goldenRatio - 1 := phi_inv_eq
  have hsq : goldenRatio ^ 2 = goldenRatio + 1 := goldenRatio_sq
  push_cast
  rw [hinv]
  linear_combination (b : ℝ) * hsq

/-- Norm of descended element: N((b-a) + a·φ) = -(a² + ab - b²) -/
private lemma norm_descent (a b : ℤ) :
    (b - a) ^ 2 + (b - a) * a - a ^ 2 = -(a ^ 2 + a * b - b ^ 2) := by ring

-- Helper: if a+b·φ > 1, by no_unit_in_one_phi, the only valid integers give a+b·φ ≥ φ when b ≠ 0.

/-- The key positivity fact for descent: when u ≥ φ > 1, φ⁻¹·u > 0 and smaller -/
private lemma phi_inv_mul_lt (u : ℝ) (hu : goldenRatio ≤ u) :
    goldenRatio⁻¹ * u < u := by
  have hphi_inv_lt1 : goldenRatio⁻¹ < 1 := by
    rw [phi_inv_eq]; nlinarith [goldenRatio_gt_one, phi_is_unit]
  calc goldenRatio⁻¹ * u < 1 * u := by
        apply mul_lt_mul_of_pos_right hphi_inv_lt1
        linarith [goldenRatio_pos]
    _ = u := one_mul u

/-- When the norm is ±1 and u = a+b*φ ≥ φ, the conjugate satisfies |ub| ≤ 1/φ < 1. -/
private lemma conj_small_when_u_ge_phi (a b : ℤ)
    (hN : a ^ 2 + a * b - b ^ 2 = 1 ∨ a ^ 2 + a * b - b ^ 2 = -1)
    (hu_ge_phi : goldenRatio ≤ (a : ℝ) + b * goldenRatio) :
    |((a : ℝ) + b * goldenConj)| ≤ goldenRatio - 1 := by
  set u := (a : ℝ) + b * goldenRatio
  set ub := (a : ℝ) + b * goldenConj
  have hNorm : u * ub = (a ^ 2 + a * b - b ^ 2 : ℤ) := norm_form_identity a b
  have hu_pos : 0 < u := by linarith [goldenRatio_pos]
  have hphi_gt1 : (1 : ℝ) < goldenRatio := goldenRatio_gt_one
  rcases hN with hNp | hNn
  · -- N = 1: ub = 1/u, |ub| = 1/u ≤ 1/φ = φ-1
    have hprod : u * ub = 1 := by
      simp only [hNp] at hNorm; push_cast at hNorm; linarith
    have hub_pos : 0 < ub := by
      have hprod' : 0 < u * ub := hprod ▸ one_pos
      exact (mul_pos_iff.mp hprod').elim (fun h => h.2) (fun h => absurd h.1 (not_lt.mpr hu_pos.le))
    rw [abs_of_pos hub_pos]
    -- ub ≤ φ-1. Proof: ub*φ ≤ ub*u = 1 = φ*(φ-1), so ub ≤ φ-1.
    nlinarith [mul_le_mul_of_nonneg_left hu_ge_phi hub_pos.le, mul_comm u ub, phi_is_unit]
  · -- N = -1: ub = -1/u, |ub| = 1/u ≤ 1/φ = φ-1
    have hprod : u * ub = -1 := by
      simp only [hNn] at hNorm; push_cast at hNorm; linarith
    have hub_neg : ub < 0 := by
      have hmul_neg : u * ub < 0 := by linarith [hprod]
      rcases mul_neg_iff.mp hmul_neg with ⟨_, h⟩ | ⟨h, _⟩
      · exact h
      · exact absurd h (not_lt.mpr hu_pos.le)
    rw [abs_of_neg hub_neg, neg_le]
    -- -ub ≤ φ-1. Proof: (-ub)*φ ≤ (-ub)*u = 1 = φ*(φ-1), so -ub ≤ φ-1.
    nlinarith [mul_le_mul_of_nonneg_left hu_ge_phi (neg_nonneg.mpr hub_neg.le),
               mul_comm u ub, phi_is_unit]

/-- When the norm is ±1 and u = a+b*φ ≥ φ, we have b > 0. -/
private lemma b_pos_when_u_ge_phi (a b : ℤ)
    (hN : a ^ 2 + a * b - b ^ 2 = 1 ∨ a ^ 2 + a * b - b ^ 2 = -1)
    (hu_ge_phi : goldenRatio ≤ (a : ℝ) + b * goldenRatio) :
    0 < b := by
  by_contra hb_neg
  push_neg at hb_neg
  -- b ≤ 0.
  -- Case b = 0: a+b*φ = a, N = a², so a = ±1. Then a + 0*φ = ±1 < φ ≤ u. Contradiction.
  -- Case b < 0: u = a + b*φ ≤ a (since b*φ ≤ 0). For u ≥ φ: a ≥ φ > 1, so a ≥ 2.
  --   ub = a + b*ψ. Since ψ < 0 and b < 0: b*ψ > 0. So ub = a + b*ψ > a ≥ 2.
  --   u*ub ≥ φ * 2 > 2 > 1 = |N|. Contradiction.
  have hb_le0 : b ≤ 0 := hb_neg
  rcases (le_iff_lt_or_eq.mp hb_le0) with hb_lt0 | hb0
  · -- b < 0
    have hb_r : (b : ℝ) < 0 := by exact_mod_cast hb_lt0
    -- a ≥ φ from u = a + b*φ ≥ φ and b*φ < 0
    have ha_r : goldenRatio < (a : ℝ) := by
      have : (b : ℝ) * goldenRatio < 0 := mul_neg_of_neg_of_pos hb_r goldenRatio_pos
      linarith
    -- ub = a + b*ψ > a (since b*ψ > 0)
    have hbpsi_pos : 0 < (b : ℝ) * goldenConj := mul_pos_of_neg_of_neg hb_r goldenConj_lt_zero
    have hub_gt_a : (a : ℝ) < (a : ℝ) + b * goldenConj := by linarith
    -- u * ub > φ * φ > 1
    have hu_pos : 0 < (a : ℝ) + b * goldenRatio := by linarith [goldenRatio_pos]
    have hub_pos : 0 < (a : ℝ) + b * goldenConj := by linarith [hub_gt_a, ha_r, goldenRatio_pos]
    have hprod_lb : 1 < ((a : ℝ) + b * goldenRatio) * ((a : ℝ) + b * goldenConj) := by
      calc ((a : ℝ) + b * goldenRatio) * ((a : ℝ) + b * goldenConj)
          ≥ goldenRatio * ((a : ℝ) + b * goldenConj) :=
            mul_le_mul_of_nonneg_right hu_ge_phi (le_of_lt hub_pos)
        _ > goldenRatio * (a : ℝ) := by
            apply mul_lt_mul_of_pos_left hub_gt_a goldenRatio_pos
        _ > goldenRatio * goldenRatio := by
            apply mul_lt_mul_of_pos_left ha_r goldenRatio_pos
        _ > 1 := by nlinarith [goldenRatio_gt_one]
    -- But norm = ±1
    have hNorm : ((a : ℝ) + b * goldenRatio) * ((a : ℝ) + b * goldenConj) =
        (a ^ 2 + a * b - b ^ 2 : ℤ) := norm_form_identity a b
    rcases hN with hNp | hNn
    · simp only [hNp] at hNorm; push_cast at hNorm; linarith
    · simp only [hNn] at hNorm; push_cast at hNorm; linarith
  · -- b = 0
    have hb_zero : b = 0 := hb0
    -- N = a²+0-0 = a² = ±1; use ring_nf to normalize polynomial form
    rw [hb_zero] at hN
    ring_nf at hN
    -- hN : a^2 = 1 ∨ a^2 = -1
    have haq : a ^ 2 = 1 := by
      rcases hN with h | h
      · exact h
      · linarith [sq_nonneg a]
    have ha_one : a = 1 ∨ a = -1 := by
      have hfact : (a - 1) * (a + 1) = 0 := by nlinarith
      rcases mul_eq_zero.mp hfact with h | h <;> omega
    rw [hb_zero] at hu_ge_phi
    simp at hu_ge_phi
    rcases ha_one with rfl | rfl
    · -- a = 1: u = 1 < φ. Contradiction.
      simp at hu_ge_phi
      linarith [goldenRatio_gt_one]
    · -- a = -1: u = -1 < φ. Contradiction.
      simp at hu_ge_phi
      linarith [goldenRatio_pos]

/-- When the norm is ±1, u = a+b*φ ≥ φ, and b.natAbs ≥ 2, we have a.natAbs < b.natAbs. -/
private lemma natAbs_a_lt_natAbs_b (a b : ℤ)
    (hN : a ^ 2 + a * b - b ^ 2 = 1 ∨ a ^ 2 + a * b - b ^ 2 = -1)
    (hu_ge_phi : goldenRatio ≤ (a : ℝ) + b * goldenRatio)
    (hb2 : 2 ≤ b.natAbs) :
    a.natAbs < b.natAbs := by
  -- We show: 0 ≤ a and a < b (both as integers).
  -- Step 1: b > 0 (proved above)
  have hb_pos : 0 < b := b_pos_when_u_ge_phi a b hN hu_ge_phi
  have hb_pos_r : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb_pos
  have hb_ge1_int : (1 : ℤ) ≤ b := hb_pos
  have hb_ge2_int : (2 : ℤ) ≤ b := by
    have h2n : (2 : ℕ) ≤ b.natAbs := hb2
    omega
  have hb_ge2_r : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb_ge2_int
  -- Step 2: |ub| ≤ φ-1 < 1, where ub = a + b*ψ
  have hub_small := conj_small_when_u_ge_phi a b hN hu_ge_phi
  -- The conjugate ub = a + b*ψ. Since ψ = 1 - φ, ub = (a+b) - b*φ.
  -- From |ub| ≤ φ-1 < 1:  -(φ-1) ≤ ub ≤ φ-1.
  -- i.e., -(φ-1) ≤ a + b*(1-φ) ≤ φ-1.
  -- Left side: a+b-b*φ ≥ -(φ-1) = 1-φ → a+b ≥ b*φ + 1-φ = (b-1)*φ+1.
  -- Right side: a+b-b*φ ≤ φ-1 → a+b ≤ b*φ + φ-1 = (b+1)*φ-1.
  -- Step 3: 0 ≤ a
  -- goldenConj = 1 - φ, so |ub| = |a + b*(1-φ)| ≤ φ-1.
  -- Lower bound: a + b*(1-φ) ≥ -(φ-1). So a ≥ -(φ-1) - b*(1-φ) = (b-1)*(φ-1) ≥ 0 (b ≥ 1).
  have hpsi_eq : goldenConj = 1 - goldenRatio := by linarith [golden_sum]
  have hphi_minus_one_pos : (0 : ℝ) < goldenRatio - 1 := by linarith [goldenRatio_gt_one]
  have ha_lb : (0 : ℝ) ≤ (a : ℝ) := by
    have hub_lb : -(goldenRatio - 1) ≤ (a : ℝ) + b * goldenConj :=
      abs_le.mp hub_small |>.1
    rw [hpsi_eq] at hub_lb
    have hb_ge1_r : (1 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb_ge1_int
    nlinarith [mul_nonneg (show (0:ℝ) ≤ (b:ℝ) - 1 by linarith) hphi_minus_one_pos.le]
  -- Step 4: a < b
  -- Upper bound: a + b*(1-φ) ≤ φ-1. With b ≤ a (contradiction): b*(2-φ) ≤ φ-1.
  -- But b ≥ 2 and 2*(2-φ) > φ-1 (since 3φ < 5, provable from φ^2 = φ+1 and φ > 1).
  have ha_lt_b : (a : ℝ) < b := by
    have hub_ub' : (a : ℝ) + b * (1 - goldenRatio) ≤ goldenRatio - 1 := by
      have := abs_le.mp hub_small |>.2; rwa [← hpsi_eq]
    nlinarith [phi_is_unit, goldenRatio_gt_one, hb_ge2_r, hub_ub']
  -- Step 5: Convert to natAbs using omega
  have ha_ge0 : 0 ≤ a := by exact_mod_cast ha_lb
  have ha_lt_b_int : a < b := by exact_mod_cast ha_lt_b
  omega

/-- **Fundamental unit theorem for ℤ[φ].**
    Every element `a + b·φ ∈ ℝ` with norm `a² + ab - b² = ±1` equals `±φⁿ` for some `n : ℤ`. -/
theorem beal_fundamental_unit_sqrt5 (a b : ℤ)
    (hN : a ^ 2 + a * b - b ^ 2 = 1 ∨ a ^ 2 + a * b - b ^ 2 = -1) :
    ∃ n : ℤ, ((a : ℝ) + b * goldenRatio = goldenRatio ^ n ∨
              (a : ℝ) + b * goldenRatio = -(goldenRatio ^ n)) := by
  -- We prove a stronger auxiliary statement by strong induction on b.natAbs.
  -- The aux: for (a, b) with N(a+bφ) = ±1 and u = a+bφ > 0, ∃ n : ℤ, u = φⁿ.
  -- Then the main statement follows by sign analysis.
  --
  -- First, reduce to the case u > 0.
  -- If u = a + b*φ = 0: then N(u) = 0, but N = ±1. Contradiction.
  -- If u > 0: apply the aux.
  -- If u < 0: then -u = (-a) + (-b)*φ > 0, N(-u) = N(u) = ±1. By aux, -u = φⁿ.
  --           So u = -φⁿ.
  --
  -- The auxiliary with strong induction:
  suffices aux : ∀ (n : ℕ) (a b : ℤ),
      b.natAbs = n →
      (a ^ 2 + a * b - b ^ 2 = 1 ∨ a ^ 2 + a * b - b ^ 2 = -1) →
      (0 : ℝ) < (a : ℝ) + b * goldenRatio →
      ∃ m : ℤ, (a : ℝ) + b * goldenRatio = goldenRatio ^ m by
    -- Use aux to prove main statement
    -- Case u > 0: directly.
    -- Case u < 0: negate.
    -- Case u = 0: impossible (N = 0 ≠ ±1).
    have hNorm : ((a : ℝ) + b * goldenRatio) * ((a : ℝ) + b * goldenConj) =
        (a ^ 2 + a * b - b ^ 2 : ℤ) := norm_form_identity a b
    by_cases hu_pos : (0 : ℝ) < (a : ℝ) + b * goldenRatio
    · -- u > 0: apply aux.
      obtain ⟨m, hm⟩ := aux b.natAbs a b rfl hN hu_pos
      exact ⟨m, Or.inl hm⟩
    · by_cases hu_neg : (a : ℝ) + b * goldenRatio < 0
      · -- u < 0: apply aux to (-a, -b).
        have hN' : (-a) ^ 2 + (-a) * (-b) - (-b) ^ 2 = 1 ∨
                   (-a) ^ 2 + (-a) * (-b) - (-b) ^ 2 = -1 := by
          simp only [neg_mul, neg_neg, mul_neg]; ring_nf; ring_nf at hN; exact hN
        have hu_neg_pos : (0 : ℝ) < ((-a : ℤ) : ℝ) + (-b : ℤ) * goldenRatio := by
          push_cast; linarith
        have hnatAbs : (-b : ℤ).natAbs = b.natAbs := Int.natAbs_neg b
        obtain ⟨m, hm⟩ := aux b.natAbs (-a) (-b) hnatAbs hN' hu_neg_pos
        push_cast at hm
        exact ⟨m, Or.inr (by linarith)⟩
      · -- u = 0: N = 0, contradiction.
        push_neg at hu_pos hu_neg
        have hu_zero : (a : ℝ) + b * goldenRatio = 0 := le_antisymm hu_pos hu_neg
        -- N = u * ub = 0 * ub = 0, but N = ±1.
        have hN_zero : (a ^ 2 + a * b - b ^ 2 : ℤ) = 0 := by
          have h : (0 : ℝ) = ((a ^ 2 + a * b - b ^ 2 : ℤ) : ℝ) := by
            have := hNorm
            rw [hu_zero, zero_mul] at this
            exact this
          exact_mod_cast h.symm
        rcases hN with h | h <;> omega
  -- Prove the auxiliary by strong induction on n = b.natAbs.
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
  intro a b hb_natAbs hN hu_pos
  -- We have: b.natAbs = n, N = ±1, u = a + b*φ > 0.
  -- We need: ∃ m, u = φᵐ.
  --
  -- Step 1: Is u ≥ φ? If not, then 0 < u < φ.
  --   If 0 < u ≤ 1: take inverse. 1 ≤ u⁻¹ = φ^{-1}·... wait, φ⁻¹·u is the conjugate step.
  --   Actually: if 0 < u < 1, then 1/u > 1. But 1/u is NOT of the form a'+b'φ easily.
  --   Better: if 0 < u ≤ 1, then u⁻¹ ≥ 1. Since N(u⁻¹) = N(u)⁻¹ = ±1 still...
  --   Actually we need to be more careful. Let's use the following:
  --   If u < 1: then the conjugate ub = N/u, so |ub| = |N|/u > 1. And ub could be > 1 or < -1.
  --   If 0 < u < 1 and N = 1: ub = 1/u > 1. So ub is the unit with norm 1 and ub > φ (by no_unit).
  --   But ub = a + b*ψ. Hmm.
  --   Better approach: use the fact that if 0 < u ≤ 1, we can write u = φ^{-k} * (some u' ≥ 1).
  --
  -- SIMPLIFICATION: Instead of handling 0 < u < 1 separately, observe that
  -- there's a bijection: u → u⁻¹ preserves |norm| and maps (0,1) to (1,∞).
  -- So WLOG we may assume u ≥ 1.
  -- If u = 1: (a,b) = (1,0), u = φ⁰.
  -- If u > 1: no_unit_in_one_phi ⟹ u ≥ φ.
  --
  -- But wait: if 0 < u < 1, can we still do induction?
  -- u = a + b*φ where a,b might be negative or zero.
  -- If 0 < u < 1: b ≤ 0 (since otherwise b*φ ≥ φ > 1 and a ≥ 0 would give u ≥ φ > 1).
  -- If b = 0: u = a, 0 < a < 1. No integer. Contradiction.
  -- If b < 0: Then |b| ≥ 1. And b*φ < 0. So a > 0 (to keep u > 0).
  --   The conjugate ub = a + b*ψ where ψ ∈ (-1, 0). So b*ψ > 0 (b < 0, ψ < 0).
  --   ub = a + b*ψ > a ≥ 1 (since a ≥ 1 as integer with a > b*(-φ) ≥ φ).
  --   Hmm this is getting complicated.
  --
  -- KEY INSIGHT: Instead of considering u > 0 and doing casework on u vs φ,
  -- let's prove a COMBINED statement by induction: any unit is ±φⁿ.
  -- The induction step is: if u ≥ φ, then φ⁻¹u = v is a unit with smaller b.natAbs, done by IH.
  -- The base cases cover b.natAbs = 0 and b.natAbs = 1 directly.
  --
  -- Case analysis on n = b.natAbs:
  subst hb_natAbs
  rcases Nat.eq_zero_or_pos b.natAbs with hb0 | hb_pos
  · -- Case b.natAbs = 0: b = 0.
    have hb : b = 0 := Int.natAbs_eq_zero.mp hb0
    subst hb
    -- N = a²
    ring_nf at hN
    -- hN : a^2 = 1 ∨ a^2 = -1
    have ha_sq : a ^ 2 = 1 := by
      rcases hN with h | h
      · exact h
      · linarith [sq_nonneg a]
    have ha_one : a = 1 ∨ a = -1 := by
      have hfact : (a - 1) * (a + 1) = 0 := by linear_combination ha_sq
      rcases mul_eq_zero.mp hfact with h | h <;> omega
    simp only [Int.cast_zero, zero_mul, add_zero] at hu_pos ⊢
    rcases ha_one with rfl | rfl
    · exact ⟨0, by simp⟩
    · -- a = -1: u = -1 < 0. Contradicts hu_pos.
      norm_num at hu_pos
  · -- Case b.natAbs ≥ 1.
    rcases Nat.eq_or_lt_of_le hb_pos with h1 | h2
    · -- b.natAbs = 1: b = 1 or b = -1.
      have hb_cases : b = 1 ∨ b = -1 := Int.natAbs_eq_iff.mp (h1.symm)
      rcases hb_cases with rfl | rfl
      · -- b = 1: N = a²+a-1 = ±1. Solve: a=1 gives N=1, a=0 gives N=-1, a=-2 gives N=1, a=-1 gives N=-1.
        -- More carefully: a² + a - 1 = 1 → a²+a-2=0 → (a+2)(a-1)=0 → a=1 or a=-2.
        --                a² + a - 1 = -1 → a²+a=0 → a(a+1)=0 → a=0 or a=-1.
        -- u = a + φ > 0.
        -- Check each case:
        -- a=1: u = 1+φ = φ² > 0. u = φ². ✓ n=2.
        -- a=-2: u = -2+φ = φ-2 < 0 (since φ < 2). Contradicts hu_pos.
        -- a=0: u = φ > 0. u = φ¹. ✓ n=1.
        -- a=-1: u = -1+φ = φ-1 = φ⁻¹ > 0. u = φ⁻¹ = φ^{-1}. ✓ n=-1.
        simp only [Int.cast_one, mul_one] at hu_pos ⊢
        -- N = a²+a-1 = ±1
        simp only [mul_one] at hN
        have ha_cases : a = 1 ∨ a = -2 ∨ a = 0 ∨ a = -1 := by
          rcases hN with hNp | hNn
          · -- a²+a-1 = 1 → a²+a = 2 → a=1 or a=-2
            have : a ^ 2 + a - 2 = 0 := by linarith
            have : (a - 1) * (a + 2) = 0 := by ring_nf; linarith
            rcases mul_eq_zero.mp this with h | h <;> omega
          · -- a²+a-1 = -1 → a²+a = 0 → a(a+1)=0
            have : a * (a + 1) = 0 := by nlinarith
            rcases mul_eq_zero.mp this with h | h <;> omega
        rcases ha_cases with rfl | rfl | rfl | rfl
        · -- a=1: u = 1+φ = φ², n=2
          exact ⟨2, by push_cast; simp only [zpow_ofNat]; linarith [goldenRatio_sq]⟩
        · -- a=-2: u = -2+φ < 0, contradicts hu_pos
          push_cast at hu_pos; linarith [phi_lt_two]
        · -- a=0: u = φ, n=1
          exact ⟨1, by push_cast; simp⟩
        · -- a=-1: u = φ-1 = φ⁻¹ = φ^{-1}
          push_cast
          exact ⟨-1, by
            simp only [zpow_neg, zpow_one]
            linarith [phi_inv_eq]⟩
      · -- b = -1: N = a²-a-1 = ±1. And u = a - φ > 0, so a > φ > 1, a ≥ 2.
        -- a²-a-1 = 1 → a²-a-2=0 → (a-2)(a+1)=0 → a=2 or a=-1.
        -- a²-a-1 = -1 → a²-a=0 → a(a-1)=0 → a=0 or a=1.
        -- u = a - φ > 0 → a > φ → a ≥ 2. So a=2 only.
        -- Check: a=2, b=-1: N = 4-2-1 = 1, u = 2-φ = 2-φ.
        --   φ = (1+√5)/2 ≈ 1.618. u = 2 - 1.618 = 0.382 = φ-1 = φ⁻¹ = 1/φ... wait.
        --   u = 2 - φ ≈ 0.382 = φ - 1 (since φ ≈ 1.618, φ-1 ≈ 0.618). Hmm let me compute:
        --   Actually 2 - φ = 2 - (1+√5)/2 = (4-1-√5)/2 = (3-√5)/2 ≈ (3-2.236)/2 ≈ 0.382.
        --   And φ⁻¹ = φ-1 = (1+√5)/2 - 1 = (-1+√5)/2 ≈ 0.618. So 2-φ ≠ φ⁻¹.
        --   Let me check: (2-φ)(2-ψ) = 4 - 2φ - 2ψ + φψ = 4 - 2(φ+ψ) + φψ = 4 - 2 + (-1) = 1. So N=1. ✓
        --   2 - φ = ? in terms of powers of φ.
        --   φ^{-2} = (φ-1)^2 = φ²-2φ+1 = (φ+1)-2φ+1 = 2-φ. ✓ So u = φ^{-2}. n=-2.
        -- Other cases with b=-1, a > φ:
        -- a=-1: u=-1-φ < 0. ✗
        -- a=0: u = -φ < 0. ✗
        -- a=1: u = 1-φ < 0 (since φ > 1). ✗
        simp only [Int.cast_neg, Int.cast_one, neg_mul, one_mul] at hu_pos ⊢
        -- u = a - φ > 0, N = a²-a-1 = ±1
        ring_nf at hN
        have ha_cases : a = 2 ∨ a = -1 ∨ a = 0 ∨ a = 1 := by
          rcases hN with hNp | hNn
          · have : (a - 2) * (a + 1) = 0 := by nlinarith
            rcases mul_eq_zero.mp this with h | h <;> omega
          · have : a * (a - 1) = 0 := by nlinarith
            rcases mul_eq_zero.mp this with h | h <;> omega
        -- u = a - φ > 0
        have hu_eq : (a : ℝ) - goldenRatio = (a : ℝ) + (-1 : ℤ) * goldenRatio := by push_cast; ring
        rcases ha_cases with rfl | rfl | rfl | rfl
        · -- a=2: u = 2-φ = φ^{-2}
          have hv : (2 : ℝ) - goldenRatio = goldenRatio ^ (-2 : ℤ) := by
            simp only [zpow_neg, zpow_ofNat]
            rw [show goldenRatio ^ 2 = goldenRatio + 1 from goldenRatio_sq]
            -- Goal: 2 - φ = (φ+1)⁻¹
            rw [← one_div, eq_div_iff (show goldenRatio + 1 ≠ 0 from by linarith [goldenRatio_pos])]
            linear_combination -goldenRatio_sq
          push_cast
          exact ⟨-2, by linarith [hv]⟩
        · -- a=-1: u=-1-φ < 0. Contradiction.
          push_cast at hu_pos; linarith [goldenRatio_pos]
        · -- a=0: u = -φ < 0. Contradiction.
          push_cast at hu_pos; linarith [goldenRatio_pos]
        · -- a=1: u = 1-φ < 0. Contradiction.
          push_cast at hu_pos; linarith [goldenRatio_gt_one]
    · -- b.natAbs ≥ 2 (inductive step)
      -- If u ≥ φ: do descent.
      -- If 0 < u < φ: impossible by no_unit_in_one_phi (if u > 1) or handle u ≤ 1.
      -- First show u ≥ φ or u = 1 or u ∈ (0,1):
      -- Since u > 0 and no_unit_in_one_phi prevents u ∈ (1,φ), we have: u ≤ 1 or u ≥ φ.
      by_cases h_ge_phi : goldenRatio ≤ (a : ℝ) + b * goldenRatio
      · -- u ≥ φ: do the descent step.
        -- Descent: v = φ⁻¹·u = (b-a) + a·φ, with N(v) = -N(u) = ∓1, v > 0, a.natAbs < b.natAbs.
        have hv_coord : goldenRatio⁻¹ * ((a : ℝ) + b * goldenRatio) =
            ((b - a : ℤ) : ℝ) + a * goldenRatio := phi_inv_mul_coord a b
        have hv_norm : (b - a) ^ 2 + (b - a) * a - a ^ 2 = 1 ∨
                       (b - a) ^ 2 + (b - a) * a - a ^ 2 = -1 := by
          rw [norm_descent a b]
          rcases hN with h | h <;> simp [h]
        have hv_pos : 0 < ((b - a : ℤ) : ℝ) + a * goldenRatio := by
          rw [← hv_coord]
          apply mul_pos
          · rw [phi_inv_eq]; linarith [goldenRatio_gt_one]
          · linarith [goldenRatio_pos]
        have hna_lt_nb : a.natAbs < b.natAbs := natAbs_a_lt_natAbs_b a b hN h_ge_phi (by omega : 2 ≤ b.natAbs)
        -- Apply IH to (b-a, a) with (b-a).natAbs... wait, we need a.natAbs < b.natAbs.
        -- The IH is on the first argument (n), and we need n' = a.natAbs < b.natAbs = n.
        obtain ⟨m, hm⟩ := ih a.natAbs hna_lt_nb (b - a) a rfl hv_norm hv_pos
        -- u = φ · v = φ · φᵐ = φᵐ⁺¹
        exact ⟨m + 1, by
          have : (a : ℝ) + b * goldenRatio = goldenRatio * (((b - a : ℤ) : ℝ) + a * goldenRatio) := by
            rw [← hv_coord]
            field_simp [goldenRatio_ne_zero]
          rw [this, hm, mul_comm, zpow_add_one₀ goldenRatio_ne_zero]⟩
      · -- 0 < u < φ: handle by showing u ∈ (0, 1] or u ∈ (1, φ).
        push_neg at h_ge_phi
        -- u ∈ (0, φ). By no_unit_in_one_phi, u ∉ (1, φ).
        -- So either u ≤ 1 or u = 1 (we need to split at 1).
        by_cases h_gt_one : (1 : ℝ) < (a : ℝ) + b * goldenRatio
        · -- u ∈ (1, φ): impossible.
          exact absurd (no_unit_in_one_phi a b hN h_gt_one h_ge_phi) (by trivial)
        · -- u ≤ 1. Since u > 0: 0 < u ≤ 1.
          push_neg at h_gt_one
          -- Sub-case: u = 1 or u < 1.
          by_cases h_eq_one : (a : ℝ) + b * goldenRatio = 1
          · -- u = 1 = φ⁰.
            exact ⟨0, by simp [h_eq_one]⟩
          · -- u < 1. Since u > 0: the inverse u⁻¹ = 1/u > 1.
            -- Also u⁻¹ = (1/u). We can write 1/u = N(u)/u = ub (if N=1) or -ub (if N=-1).
            -- Better: the inverse of u = a+bφ in ℤ[φ] is given by:
            -- If N = 1: u⁻¹ = ub = a + b*ψ (the conjugate).
            -- If N = -1: u⁻¹ = -ub = -a - b*ψ.
            -- But these may not be of the form a'+b'φ easily.
            -- Alternative: use the UNIT LAW. u * (unit in ℤ[φ]) = 1.
            -- The unit group of ℤ[φ] is generated by φ, so φ⁻¹ = φ-1 is also a unit.
            -- φ⁻¹ = (goldenRatio - 1) and N(φ-1) = ...
            -- (φ-1)*ψ-conjugate = (φ-1) + (ψ-1)... hmm not the right form.
            --
            -- Let me use a different approach: reduce to u⁻¹.
            -- u⁻¹ is the image of u under the unit inverse map.
            -- If u = a + b*φ and N(u) = 1: u⁻¹ = a + b*ψ (conj) in ℤ[φ].
            --   But ψ = 1 - φ, so a + b*ψ = (a+b) + (-b)*φ. Coords: (a+b, -b).
            -- If N(u) = -1: u⁻¹ = -(a + b*ψ) = (-a-b) + b*φ. Coords: (-a-b, b).
            --
            -- Check N of these:
            -- For N=1, inverse coords (a+b, -b): N = (a+b)² + (a+b)(-b) - (-b)² = a²+2ab+b²-ab-b²-b² = a²+ab-b² = 1. ✓
            -- For N=-1, inverse coords (-a-b, b): N = (-a-b)²+(-a-b)b-b² = a²+2ab+b²-ab-b²-b² = a²+ab-b² = -1. ✓
            --
            -- So: u⁻¹ is a+bφ for new integer coords, and u > 0 implies u⁻¹ > 0.
            -- Now u ∈ (0,1) means u⁻¹ > 1.
            -- We need to show that the new b.natAbs for u⁻¹ is LESS than b.natAbs for u.
            -- For N=1: new b' = -b. So b'.natAbs = b.natAbs. SAME! This doesn't decrease.
            -- Hmm. So we can't just invert.
            --
            -- The REAL approach: instead of just inducing on b.natAbs,
            -- we use the POSITIVITY CONDITION. If u > 0, we can multiply by powers of φ
            -- until we're in [φ⁰, φ¹) = [1, φ). Since u ≠ 1 (u < 1) and u ≠ φ (u < φ),
            -- we must reach exactly u = φⁿ for some n.
            --
            -- But formalizing this "multiply by powers of φ until in [1,φ)" is essentially
            -- the same as the descent algorithm but going UP, not down.
            --
            -- For u ∈ (0, 1): φ·u ∈ (0, φ). And φ·u has norm -N(u) (since N(φ)=-1). Hmm.
            -- Actually N(φ) = φ*ψ = -1 ≠ 1. So multiplying by φ changes the norm.
            -- But our theorem allows N = ±1, so this is fine!
            --
            -- For 0 < u < 1: v = φ·u. N(v) = N(φ)·N(u) = (-1)·(±1) = ∓1. So |N(v)| = 1. ✓
            -- v = φ·(a+bφ) = aφ + bφ² = aφ + b(φ+1) = b + (a+b)φ. Coords: (b, a+b).
            -- b.natAbs of new = (a+b).natAbs. We need (a+b).natAbs < b.natAbs.
            -- But 0 < a+bφ < 1. So a > 0 or a+bφ > 0 with b < 0.
            -- If b > 0: a + bφ < 1, bφ < 1 - a ≤ 1 (if a ≥ 0). And a < 1 - bφ < 1 (a=0).
            --   If b=1: 0 < a+φ < 1 → a < 1-φ < 0. So a ≤ -1. a=-1: u = φ-1 = 1/φ ≈ 0.618. But we're in b.natAbs ≥ 2.
            --   If b ≥ 2: bφ ≥ 2φ > 1+φ > 1, so a + bφ < 1 requires a < 1-bφ < 1-1-φ < 0. So a ≤ -2.
            --   New b' = a+b. Since a ≤ -2 and b ≥ 2: a+b could be anything.
            --   Hmm, this direction also doesn't easily terminate.
            --
            -- CONCLUSION: The strong induction on b.natAbs is NOT the right approach for 0 < u < 1.
            -- We need a different proof strategy.
            --
            -- BETTER STRATEGY: Prove the result in two stages:
            --   Stage 1: Every unit u > 1 equals φⁿ for n ≥ 1 (by descent induction).
            --   Stage 2: Every unit u > 0 with u < 1 equals φⁿ for n ≤ -1 (since 1/u > 1).
            --   Stage 3: u = 1 = φ⁰.
            --
            -- The key is that "inversion" in ℤ[φ] gives new coordinates:
            -- If u = a+bφ with N=1: u⁻¹ = a+b + (-b)φ. New (a',b') = (a+b, -b).
            -- If u = a+bφ with N=-1: u⁻¹ = -(a+b) + b*φ. New (a',b') = (-(a+b), b).
            --
            -- For INDUCTION when u ∈ (0,1): u⁻¹ ∈ (1,∞) > 1.
            -- If u⁻¹ > φ: by Stage 1, u⁻¹ = φᵐ for some m ≥ 1. So u = φ⁻ᵐ. Done.
            -- If u⁻¹ = 1: then u = 1 (already handled).
            -- If u⁻¹ ∈ (1,φ): impossible by no_unit_in_one_phi (applied to u⁻¹).
            --
            -- So the correct aux is:
            -- (∀ u > 1 with N=±1, u = φⁿ for n ≥ 1) → (∀ u > 0 with N=±1, u = φⁿ).
            --
            -- And for u > 1: use DESCENT to reduce to u ∈ [φ,φ²) → ... → base.
            --
            -- The induction for u > 1 terminates because descent strictly decreases u:
            -- v = φ⁻¹·u < u (since φ⁻¹ < 1).
            -- We need: v > 0 and v ≥ 1 (or handle the terminal case v = 1).
            -- v = φ⁻¹·u > 0 (since both positive). ✓
            -- If v ∈ (1,φ): impossible. So v ≥ φ or v ≤ 1.
            -- If v ≤ 1: then v = 1 = φ⁰, so u = φ·v = φ¹. Done.
            -- Actually v could be in (0,1) as well!
            -- If v ∈ (0,1): we can no longer descend (need v ≥ φ for descent).
            -- Hmm. But v = φ⁻¹·u, N(v) = -N(u). If u > φ: v = φ⁻¹·u > φ⁻¹·φ = 1.
            -- If u = φ exactly: v = 1 = φ⁰.
            -- So for u ≥ φ: v = φ⁻¹·u ≥ 1. ✓
            -- If v = 1: u = φ¹. Done.
            -- If v > 1: by no_unit_in_one_phi, v ≥ φ. Apply descent again.
            -- Each descent reduces u by factor φ⁻¹, eventually hitting (0,φ].
            -- At u in (1,φ]: by no_unit_in_one_phi, this region (1,φ) is impossible.
            --   So u ∈ {values equal to φ}? But φ is irrational, not in ℤ[φ] as an integer combo...
            -- Wait! φ = 0 + 1·φ ∈ ℤ[φ] with a=0, b=1. N(φ) = φ*ψ = -1. ✓
            -- And after one descent from u ≥ φ², we get v = φ⁻¹·u ≥ φ ≥ φ... we could get v = φ.
            -- That's fine: v = φ = φ¹, so u = φ·φ = φ².
            --
            -- OK so the CORRECT strong induction is: induction on (u : ℝ), but this needs
            -- a well-ordering. We need a discrete measure.
            --
            -- Actually: when u ≥ φ and N=±1, the descent gives v = φ⁻¹·u with:
            -- - v = (b-a) + a·φ (new coordinates (b-a, a))
            -- - a.natAbs < b.natAbs (proved in natAbs_a_lt_natAbs_b)
            -- - v > 0 (since φ⁻¹ > 0 and u > 0)
            -- So v's b-coordinate has natAbs = a.natAbs < b.natAbs = u's b-coordinate natAbs.
            --
            -- And when u ∈ (0,1): we're in the case where the b.natAbs might NOT decrease after
            -- "going up" by φ. So the induction on b.natAbs isn't the right measure for 0 < u < 1.
            --
            -- SOLUTION: Change the auxiliary lemma to require u ≥ 1.
            -- Then:
            -- - u = 1: done (φ⁰).
            -- - u ∈ (1,φ): impossible.
            -- - u ≥ φ: descent to v = φ⁻¹·u. v > 0, and v ≥ 1?
            --   v = φ⁻¹·u ≥ φ⁻¹·φ = 1. ✓ (since u ≥ φ).
            -- So the auxiliary says: "u ≥ 1, N=±1 ⟹ u = φⁿ" with induction on b.natAbs.
            -- And if v ≥ 1 is assured, then v's coordinates have natAbs strictly smaller!
            -- By IH (applied to v = (b-a)+aφ with a.natAbs < b.natAbs): v = φᵐ. So u = φᵐ⁺¹.
            --
            -- For the main theorem: if u > 0, then either u ≥ 1 or u ∈ (0,1).
            -- If u ∈ (0,1): u⁻¹ > 1. And u⁻¹ = ub or -ub as computed above.
            -- Specifically: if N=1, u⁻¹ = ub = (a+b) + (-b)φ. b' = -b, b'.natAbs = b.natAbs.
            -- BUT: is u⁻¹ ≥ 1? u ∈ (0,1) → u⁻¹ > 1 ≥ 1. ✓
            -- Can we apply the auxiliary to u⁻¹? We need u⁻¹ ≥ 1. ✓ And N(u⁻¹) = N(u)⁻¹ = N(u).
            -- Actually N(u⁻¹) = 1/N(u). If N=1: N(u⁻¹) = 1. If N=-1: N(u⁻¹) = -1. ✓
            -- But b.natAbs for u⁻¹ = b.natAbs for u (for N=1 case). SAME. So induction doesn't work directly.
            --
            -- FINAL SOLUTION: Change the auxiliary to:
            -- "u ≥ 1, N(a,b)=±1, a+bφ=u ⟹ ∃ n ≥ 0, u = φⁿ"
            -- Induction on n = b.natAbs where for u ≥ φ, descent gives v with strictly smaller natAbs.
            -- For u ∈ [1, φ): by no_unit_in_one_phi impossible unless u=1.
            --   But u=1 and N=±1: if N=1, b=0, a=1 (u=1=φ⁰). If N=-1: a²=−1 impossible.
            -- So u ∈ [1, φ) with N=±1 means u=1. ✓
            --
            -- And for the FULL theorem: if u > 0, either u ≥ 1 or u ∈ (0,1).
            -- If u ∈ (0,1): let's examine b.natAbs.
            --   b=0: u=a, 0<a<1 impossible (a integer).
            --   b=1: u=a+φ ∈ (0,1): a+φ < 1 → a < 1-φ < 0. So a=-1: u=φ-1≈0.618. u⁻¹=1/(φ-1)=φ/(φ-1)·... hmm.
            --     φ-1 = φ⁻¹ (by phi_inv_eq!). So u = φ⁻¹ = φ^{-1}. N(φ⁻¹) = N(φ)⁻¹...
            --     Actually u = φ-1 = 0+1·φ - 1 = (-1)+1·φ. So (a,b)=(-1,1). N = 1 -1 -1 = -1. ✓ u = φ^{-1}. Done.
            --   b=-1: u=a-φ ∈ (0,1): a-φ > 0 → a > φ → a ≥ 2. a-φ < 1 → a < 1+φ ≈ 2.618 → a=2. u=2-φ=φ^{-2}. Done.
            --   For |b| ≥ 2: 0 < a + bφ < 1 and |b| ≥ 2. By the same natAbs argument?
            --
            -- Actually here is the key insight I was missing:
            -- When 0 < u < 1 with b.natAbs ≥ 2: by IH (for b.natAbs ≥ 1 or some appropriate measure)?
            -- Wait: if 0 < u < 1 and N=1: u⁻¹ = ub = (a+b) + (-b)φ.
            --   u⁻¹ > 1. New b' = -b. b'.natAbs = b.natAbs. SAME. No progress.
            -- If 0 < u < 1 and N=-1: u⁻¹ = -ub = (-a-b) + b·φ.
            --   u⁻¹ > 1. New b' = b. b'.natAbs = b.natAbs. SAME. No progress.
            --
            -- SO: for b.natAbs ≥ 2 and 0 < u < 1 case, inversion doesn't help.
            -- We need a completely different argument.
            --
            -- THE TRULY CORRECT PROOF: Induct on b.natAbs, but in the u ∈ (0,1) sub-case,
            -- MULTIPLY by φ (not divide) to go to v = φ·u > u. v has new b' = a+b.
            -- We need (a+b).natAbs < b.natAbs. Is this true?
            --
            -- 0 < u < 1 means 0 < a + bφ < 1.
            -- For b > 0: bφ > 0, so a + bφ < 1 means a < 1 - bφ < 1 - b (since φ > 1). So a ≤ -b.
            --   Also a + bφ > 0: a > -bφ. Since a is an integer: a ≥ -(b*something).
            --   a + b ≤ a + b ≤ (1 - bφ) + b = 1 - b(φ-1) = 1 - b/φ < 1 (since b/φ > 0).
            --   And a + b ≥ (-bφ) + b = b(1-φ) = -b(φ-1) < 0 (since b ≥ 1 and φ-1 > 0).
            --   So a+b ∈ (−b/φ, 1). For b ≥ 2: |a+b| < b (since |a+b| ≤ max(|b/φ|, 0) = b/φ < b). ✓!
            --   More precisely: |a+b| ≤ b(φ-1) = b/φ < b. So (a+b).natAbs < b.natAbs = b. ✓
            -- For b < 0: by symmetry (negate everything).
            --
            -- So the correct split is:
            -- If u ≥ φ: use DESCENT (divide by φ). (b-a).natAbs = a.natAbs < b.natAbs. ✓
            -- If 0 < u < 1: use ASCENT (multiply by φ). (a+b).natAbs < b.natAbs. ✓
            -- If u ∈ (1,φ): impossible by no_unit_in_one_phi.
            -- If u = 1: φ⁰.
            -- Base cases: b.natAbs = 0, b.natAbs = 1.
            --
            -- THIS is the correct induction!
            --
            -- NOW: Let me formalize the ascent step.
            -- Ascent: φ·(a+bφ) = aφ + bφ² = aφ + b(φ+1) = b + (a+b)φ. New coords: (b, a+b).
            -- N(b + (a+b)φ) = b²+b(a+b)-(a+b)² = b²+ab+b²-a²-2ab-b² = b²-a²-ab = -(a²+ab-b²) = -N(u). ✓
            -- And (a+b).natAbs < b.natAbs (proved above for 0 < u < 1, b > 0).
            --
            -- Let me now restart the induction step cleanly.
            --
            -- CASE: b.natAbs ≥ 2, 0 < u < 1.
            -- We do the ASCENT: v = φ·u = b + (a+b)φ > 0.
            -- N(v) = -N(u) = ∓1 (still a unit). ✓
            -- New b' = a+b, and (a+b).natAbs < b.natAbs.
            -- By IH: v = φᵐ for some m. So u = φ^{m-1}.
            --
            -- But wait, v = φᵐ means φ·u = φᵐ means u = φ^{m-1}. ✓
            --
            -- One issue: v might be ≥ 0 but we need v > 0.
            -- v = φ·u > 0 since φ > 0 and u > 0. ✓
            --
            -- So the CORRECT proof structure (replacing the sorry and all my broken stuff):
            -- We prove aux(n): ∀ a b, b.natAbs = n, N=±1, u > 0 ⟹ ∃ m, u = φᵐ.
            -- Base: n=0 and n=1 handled directly.
            -- Step n ≥ 2:
            --   If u ≥ φ: descent, natAbs decreases (to a.natAbs < n). Apply IH.
            --   If u = 1: φ⁰.
            --   If u ∈ (1,φ): impossible.
            --   If u ∈ (0,1): ascent, natAbs decreases (to (a+b).natAbs < n). Apply IH.
            --
            -- The current proof attempt already handles u ≥ φ correctly!
            -- The issue is the u ∈ (0,1) subcase, which I've arrived at here.
            --
            -- Let me implement the ascent step now.
            --
            -- First: show (a+b).natAbs < b.natAbs when 0 < u < 1 and b.natAbs ≥ 2.
            have hu_lt_one : (a : ℝ) + b * goldenRatio < 1 :=
              h_gt_one.lt_of_ne h_eq_one
            -- The ascent step: v = φ * u = b + (a+b)*φ
            -- First prove the key: (a+b).natAbs < b.natAbs
            have h2_le : (2 : ℕ) ≤ b.natAbs := h2
            have hb_ne_zero : b ≠ 0 := by
              intro hb_zero; simp [hb_zero] at h2_le
            have hphi_lt2 : goldenRatio < 2 := phi_lt_two
            have hphi_gt1 : (1 : ℝ) < goldenRatio := goldenRatio_gt_one
            -- Determine the sign of b
            have hb_sign : 0 < b ∨ b < 0 := by
              rcases Int.lt_or_lt_of_ne hb_ne_zero with h | h
              · right; exact h
              · left; exact h
            -- Key inequality: (a+b).natAbs < b.natAbs
            -- We show signed integer bounds and use omega.
            have hab_natAbs_lt : (a + b).natAbs < b.natAbs := by
              rcases hb_sign with hb_pos | hb_neg
              · -- b > 0 case: show -b < a+b < b (integers)
                have hbabs : (b.natAbs : ℤ) = b := Int.natAbs_of_nonneg hb_pos.le
                have hb_pos_r : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb_pos
                have hb_ge2_r : (2 : ℝ) ≤ (b : ℝ) := by
                  have hb_ge2_int : (2 : ℤ) ≤ b := by
                    have : (2 : ℤ) ≤ b.natAbs := by exact_mod_cast h2_le
                    rwa [hbabs] at this
                  exact_mod_cast hb_ge2_int
                -- -b < a+b iff -2b < a: from hu_pos: a + b*φ > 0 and b*φ < b*2, so a+b*2 > 0
                have hab_lb : -(b : ℤ) < a + b := by
                  have h_prod : (b : ℝ) * goldenRatio < (b : ℝ) * 2 :=
                    mul_lt_mul_of_pos_left hphi_lt2 hb_pos_r
                  have h : (-2 : ℝ) * (b : ℝ) < (a : ℝ) := by linarith
                  have h' : (-2 : ℤ) * b < a := by exact_mod_cast h
                  linarith
                -- a+b < b iff a < 0: from hu_lt_one: a < 1-b*φ < 1-b*1 = 1-b ≤ -1 < 0
                have hab_ub : a + b < b := by
                  have h_prod : (b : ℝ) * 1 < (b : ℝ) * goldenRatio :=
                    mul_lt_mul_of_pos_left hphi_gt1 hb_pos_r
                  have h : (a : ℝ) < 0 := by linarith
                  have h' : a < (0 : ℤ) := by exact_mod_cast h
                  linarith
                omega
              · -- b < 0 case: show b < a+b < -b (integers)
                have hbabs : (b.natAbs : ℤ) = -b := by omega
                have hb_neg_r : (b : ℝ) < 0 := by exact_mod_cast hb_neg
                have hb_le_neg2_r : (b : ℝ) ≤ -2 := by
                  have hb_le : b ≤ -2 := by
                    have : (2 : ℤ) ≤ (-b) := by
                      have : (2 : ℤ) ≤ b.natAbs := by exact_mod_cast h2_le
                      omega
                    omega
                  exact_mod_cast hb_le
                -- b < a+b iff 0 < a: from hu_pos: 0 < a + b*φ and b*φ < 0, so 0 < a
                have hab_lb : b < a + b := by
                  have h_bphi : (b : ℝ) * goldenRatio < 0 :=
                    mul_neg_of_neg_of_pos hb_neg_r goldenRatio_pos
                  have h : (0 : ℝ) < (a : ℝ) := by linarith
                  have h' : (0 : ℤ) < a := by exact_mod_cast h
                  linarith
                -- a+b < -b: from hu_lt_one: a < 1-b*φ ≤ 1+2*|b| < 2*|b| = -2b...
                -- More precisely: a ≤ -2b and a ≠ -2b (from norm condition).
                have hab_ub : a + b < -b := by
                  have ha_le : a ≤ -2 * b := by
                    -- b*2 < b*φ (b<0, φ<2 flips), so a+b*2 < a+b*φ < 1, so a+2b<1, so a≤-2b
                    have h_prod : (b : ℝ) * 2 < (b : ℝ) * goldenRatio :=
                      mul_lt_mul_of_neg_left hphi_lt2 hb_neg_r
                    have h_real : (a : ℝ) + (b : ℝ) * 2 < 1 := by linarith
                    have h_int : a + b * 2 < (1 : ℤ) := by exact_mod_cast h_real
                    linarith
                  have ha_ne : a ≠ -2 * b := by
                    intro heq
                    have hN_val : a ^ 2 + a * b - b ^ 2 = b ^ 2 := by rw [heq]; ring
                    have hb2_ge4 : (4 : ℤ) ≤ b ^ 2 := by
                      have hb_le : b ≤ -2 := by exact_mod_cast hb_le_neg2_r
                      nlinarith [sq_nonneg b]
                    rcases hN with hNp | hNn <;> omega
                  omega
                omega
            -- Now do the ascent: v = φ * u = b + (a+b)*φ
            -- Algebraic identity: φ * (a + b*φ) = b + (a+b)*φ (using φ² = φ+1)
            have hascent_eq : (b : ℝ) + (↑(a + b)) * goldenRatio =
                goldenRatio * ((a : ℝ) + b * goldenRatio) := by
              push_cast
              -- Goal: b + (a + b)*φ = φ*(a + b*φ) = a*φ + b*φ²
              -- Using φ² = φ+1: a*φ + b*(φ+1) = b + (a+b)*φ ✓
              have hsq : goldenRatio ^ 2 = goldenRatio + 1 := goldenRatio_sq
              linear_combination -(b : ℝ) * hsq
            -- Norm of v: b² + b*(a+b) - (a+b)² = -(a² + a*b - b²)
            have hv_norm : (b : ℤ) ^ 2 + b * (a + b) - (a + b) ^ 2 = 1 ∨
                           (b : ℤ) ^ 2 + b * (a + b) - (a + b) ^ 2 = -1 := by
              have : (b : ℤ) ^ 2 + b * (a + b) - (a + b) ^ 2 = -(a ^ 2 + a * b - b ^ 2) := by ring
              rcases hN with hNp | hNn
              · right; linarith
              · left; linarith
            -- v > 0: φ * u > 0
            have hv_pos : (0 : ℝ) < (b : ℝ) + (↑(a + b)) * goldenRatio := by
              rw [hascent_eq]
              exact mul_pos goldenRatio_pos hu_pos
            -- Apply IH to (b, a+b) with (a+b).natAbs < b.natAbs
            obtain ⟨m, hm⟩ := ih (a + b).natAbs hab_natAbs_lt b (a + b) rfl hv_norm hv_pos
            -- v = φ^m, so u = φ^(m-1) since φ * u = v = φ^m
            exact ⟨m - 1, by
              have hphi_ne : goldenRatio ≠ 0 := goldenRatio_ne_zero
              -- φ * u = v = φ^m  (using hascent_eq and hm)
              have hphi_u : goldenRatio * ((a : ℝ) + b * goldenRatio) = goldenRatio ^ m := by
                rw [← hascent_eq]; exact hm
              -- u = φ^(m-1): use zpow_sub_one₀ to rewrite RHS, then cancel φ
              rw [zpow_sub_one₀ hphi_ne]
              calc (a : ℝ) + b * goldenRatio
                  = goldenRatio⁻¹ * (goldenRatio * ((a : ℝ) + b * goldenRatio)) := by
                      field_simp [hphi_ne]
                _ = goldenRatio⁻¹ * goldenRatio ^ m := by rw [hphi_u]
                _ = goldenRatio ^ m * goldenRatio⁻¹ := by ring⟩

end BealFundamentalUnitPell

end

section AxiomCheck
open BealFundamentalUnitPell
#print axioms goldenRatio_gt_one
#print axioms goldenRatio_sq_eq
#print axioms phi_is_unit
#print axioms phi_inv_eq
#print axioms norm_form_identity
#print axioms sqrt5_gt_two
#print axioms sqrt5_lt_three
#print axioms two_phi_sub_one
#print axioms one_div_phi
#print axioms phi_plus_inv
#print axioms no_unit_in_one_phi
#print axioms pell5_prop
#print axioms pell5_fundamental_solution
#print axioms beal_fundamental_unit_sqrt5
-- All: [propext, Classical.choice, Quot.sound] — axiom-clean.
end AxiomCheck
