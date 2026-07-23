import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic

/-!
# No unit of ℤ[φ] lies strictly between 1 and φ

Minimality argument for the fundamental unit of ℤ[φ] = ℤ[(1+√5)/2]:
if u = a + b·φ is a unit with norm N(u) = a²+ab-b² = 1 and u ∈ (1, φ) in the real
embedding, then we derive a contradiction.

**Proof:** Since u·ū = 1 (where ū = a+b·ψ, ψ = (1-√5)/2 is the Galois conjugate),
ū = 1/u ∈ (1/φ, 1). Then b·√5 = u - ū ∈ (0, φ - 1/φ) = (0, 1) (since φ - 1/φ = 1).
But b is an integer: b > 0 (from b·√5 > 0) and b ≥ 1, so b·√5 ≥ √5 > 2 > 1.
Contradiction with b·√5 < 1. □

This establishes φ as the minimal unit > 1 of ℤ[φ], i.e., the fundamental unit.
-/

open Real

namespace BealMinimalityNormArg

open scoped goldenRatio

/-! ### Numeric bounds -/

/-- √5 > 2, since 5 > 4 and the square root is increasing. -/
theorem sqrt5_gt_two : (2 : ℝ) < Real.sqrt 5 := by
  rw [Real.lt_sqrt (by norm_num)]
  norm_num

/-- φ - φ⁻¹ = 1. Equivalently, φ(φ-1) = 1, i.e., φ² - φ = 1, i.e., φ² = φ+1. -/
theorem goldenRatio_sub_inv : φ - φ⁻¹ = 1 := by
  have hpos : (0 : ℝ) < φ := goldenRatio_pos
  have hne : φ ≠ 0 := ne_of_gt hpos
  have key : φ * (φ - φ⁻¹) = φ * 1 := by
    rw [mul_sub, mul_inv_cancel₀ hne, mul_one]
    linear_combination goldenRatio_sq
  exact mul_left_cancel₀ hne key

/-! ### The minimality lemma -/

/-- For integers `a b : ℤ` with `a² + a*b - b² = 1` (norm-1 unit of ℤ[φ]),
the real value `a + b·φ` cannot lie strictly in `(1, φ)`. -/
theorem no_norm_one_unit_in_one_phi (a b : ℤ)
    (hN : (a : ℤ) ^ 2 + a * b - b ^ 2 = 1)
    (h1 : (1 : ℝ) < (a : ℝ) + b * φ)
    (h2 : (a : ℝ) + b * φ < φ) :
    False := by
  set u := (a : ℝ) + b * φ with hu_def
  set uc := (a : ℝ) + b * Real.goldenConj with huc_def
  have hu_pos : 0 < u := lt_trans one_pos h1
  -- (1) u * uc = a² + ab(φ+ψ) + b²(φψ) = a² + ab·1 + b²·(-1) = a²+ab-b² = 1
  have hprod : u * uc = 1 := by
    have hN' : (a : ℝ) ^ 2 + (a : ℝ) * b - (b : ℝ) ^ 2 = 1 := by exact_mod_cast hN
    have expand : u * uc = (a : ℝ)^2 + (a : ℝ)*(b : ℝ)*(φ + Real.goldenConj) +
                           (b : ℝ)^2*(φ * Real.goldenConj) := by
      simp only [hu_def, huc_def]; ring
    rw [expand, goldenRatio_add_goldenConj, goldenRatio_mul_goldenConj]
    linarith [hN']
  -- (2) uc = 1/u
  have hu_ne : u ≠ 0 := ne_of_gt hu_pos
  have huc_eq : uc = u⁻¹ := by
    apply mul_left_cancel₀ hu_ne
    rw [mul_inv_cancel₀ hu_ne]
    exact hprod
  -- (3) uc ∈ (φ⁻¹, 1): below 1 since u > 1; above φ⁻¹ since u < φ
  have huc_lt1 : uc < 1 := by
    rw [huc_eq]; exact inv_lt_one_of_one_lt₀ h1
  have huc_gt : φ⁻¹ < uc := by
    rw [huc_eq]; exact (inv_lt_inv₀ goldenRatio_pos hu_pos).2 h2
  -- (4) u - uc = b·√5 (conjugate difference)
  have hdiff : u - uc = (b : ℝ) * Real.sqrt 5 := by
    simp only [hu_def, huc_def]
    linear_combination (b : ℝ) * goldenRatio_sub_goldenConj
  -- (5) b·√5 ∈ (0, 1): positive since u > 1 > uc; bounded above by φ - φ⁻¹ = 1
  have hbsq5_pos : 0 < (b : ℝ) * Real.sqrt 5 := by linarith [hdiff, huc_lt1, h1]
  have hbsq5_lt1 : (b : ℝ) * Real.sqrt 5 < 1 := by
    have hgap : u - uc < φ - φ⁻¹ := by linarith [huc_gt, h2]
    linarith [hdiff, goldenRatio_sub_inv]
  -- (6) b ≥ 1 (integer, > 0 from b·√5 > 0)
  have hb_pos : 0 < (b : ℝ) := by
    have h0 : (0 : ℝ) * Real.sqrt 5 < (b : ℝ) * Real.sqrt 5 := by
      simpa using hbsq5_pos
    exact lt_of_mul_lt_mul_right h0 (Real.sqrt_nonneg 5)
  have hb_ge1 : (1 : ℝ) ≤ (b : ℝ) := by
    have : 1 ≤ b := by
      have hbZ : 0 < (b : ℤ) := by exact_mod_cast hb_pos
      omega
    exact_mod_cast this
  -- (7) Contradiction: b·√5 ≥ √5 > 2 > 1, but b·√5 < 1
  have hbsq5_ge_sq5 : Real.sqrt 5 ≤ (b : ℝ) * Real.sqrt 5 :=
    le_mul_of_one_le_left (Real.sqrt_nonneg 5) hb_ge1
  linarith [sqrt5_gt_two]

/-! ### The norm -1 case -/

/-- For integers `a b : ℤ` with `a² + a*b - b² = -1` (norm -1 unit of ℤ[φ]),
the real value `a + b·φ` cannot lie strictly in `(1, φ)`.

Proof: u·ū = -1 means ū = -1/u < 0. Then b·√5 = u - ū = u + 1/u.
By AM-GM, u + 1/u > 2 (since u ≠ 1). Also u + 1/u < φ + 1/φ = φ + (φ-1) = 2φ-1 = √5.
So b·√5 ∈ (2, √5), forcing b ∈ (2/√5, 1). No integer b. -/
theorem no_norm_neg_one_unit_in_one_phi (a b : ℤ)
    (hN : (a : ℤ) ^ 2 + a * b - b ^ 2 = -1)
    (h1 : (1 : ℝ) < (a : ℝ) + b * φ)
    (h2 : (a : ℝ) + b * φ < φ) :
    False := by
  set u := (a : ℝ) + b * φ with hu_def
  set uc := (a : ℝ) + b * Real.goldenConj with huc_def
  have hu_pos : 0 < u := lt_trans one_pos h1
  have hu_gt1 : 1 < u := h1
  -- u * uc = a²+ab-b² = -1
  have hprod : u * uc = -1 := by
    have hN' : (a : ℝ) ^ 2 + (a : ℝ) * b - (b : ℝ) ^ 2 = -1 := by exact_mod_cast hN
    have expand : u * uc = (a : ℝ)^2 + (a : ℝ)*(b : ℝ)*(φ + Real.goldenConj) +
                           (b : ℝ)^2*(φ * Real.goldenConj) := by
      simp only [hu_def, huc_def]; ring
    rw [expand, goldenRatio_add_goldenConj, goldenRatio_mul_goldenConj]
    linarith [hN']
  -- u * uc = -1 and u > 0 means uc < 0
  have huc_neg : uc < 0 := by
    have : 0 < u * (-uc) := by nlinarith [hprod]
    have : 0 < -uc := by
      exact pos_of_mul_pos_right this (le_of_lt hu_pos)
    linarith
  -- u - uc = b * √5
  have hdiff : u - uc = (b : ℝ) * Real.sqrt 5 := by
    simp only [hu_def, huc_def]
    linear_combination (b : ℝ) * goldenRatio_sub_goldenConj
  -- b * √5 = u - uc > u > 1 > 0, so b > 0, b ≥ 1
  have hbsq5_pos : 0 < (b : ℝ) * Real.sqrt 5 := by linarith [hdiff, huc_neg]
  have hb_pos : 0 < (b : ℝ) := by
    have h0 : (0 : ℝ) * Real.sqrt 5 < (b : ℝ) * Real.sqrt 5 := by simpa using hbsq5_pos
    exact lt_of_mul_lt_mul_right h0 (Real.sqrt_nonneg 5)
  have hb_ge1 : (1 : ℝ) ≤ (b : ℝ) := by
    have : 1 ≤ b := by
      have hbZ : 0 < (b : ℤ) := by exact_mod_cast hb_pos
      omega
    exact_mod_cast this
  -- b * √5 = u - uc < φ - uc. Since uc < 0 < u and u < φ:
  -- Actually: b * √5 = u + |uc| < φ + φ⁻¹. And φ + φ⁻¹ = φ + (φ-1) = 2φ-1 = √5.
  -- Key: b * √5 < √5, so b < 1. Contradiction with b ≥ 1.
  have hphi_plus_inv : φ + φ⁻¹ = Real.sqrt 5 := by
    rw [inv_goldenRatio]  -- φ⁻¹ = -ψ
    linarith [goldenRatio_sub_goldenConj]
  -- u * uc = -1 and u > 1 means uc = -1/u ∈ (-1, 0)
  have huc_gt_neg1 : -1 < uc := by
    have hu_ne : u ≠ 0 := ne_of_gt hu_pos
    have : u * uc = -1 := hprod
    have : uc = -u⁻¹ := by
      rw [← neg_eq_iff_eq_neg]
      apply mul_left_cancel₀ hu_ne
      rw [mul_neg, mul_inv_cancel₀ hu_ne]
      linarith
    rw [this]
    have : 0 < u⁻¹ := inv_pos.mpr hu_pos
    have : u⁻¹ < 1 := inv_lt_one_of_one_lt₀ hu_gt1
    linarith
  -- b * √5 = u - uc = u + u⁻¹ (since uc = -u⁻¹), and u ↦ u + u⁻¹ is *increasing* on
  -- u > 1 (its minimum sits at u = 1): (φ-u)(uφ-1) > 0 since u < φ (first factor > 0)
  -- and u, φ > 1 hence uφ > 1 (second factor > 0), which rearranges to exactly
  -- u + u⁻¹ < φ + φ⁻¹ = √5. (An earlier version of this file tried to bound uc
  -- directly from u < φ alone, which gives uc's bound in the *wrong* direction for
  -- this step — u < φ alone only pins uc < 1-φ, an upper bound, when what's needed
  -- here is a lower bound on uc; monotonicity of u + u⁻¹ is the fix.)
  have huc_eq2 : uc = -u⁻¹ := by
    have hu_ne : u ≠ 0 := ne_of_gt hu_pos
    rw [← neg_eq_iff_eq_neg]
    apply mul_left_cancel₀ hu_ne
    rw [mul_neg, mul_inv_cancel₀ hu_ne]
    linarith [hprod]
  have hbsq5_lt_sq5 : (b : ℝ) * Real.sqrt 5 < Real.sqrt 5 := by
    rw [← hdiff, huc_eq2, sub_neg_eq_add, ← hphi_plus_inv]
    have hune : u ≠ 0 := ne_of_gt hu_pos
    have hφne : φ ≠ 0 := ne_of_gt goldenRatio_pos
    have hprod_pos : (0 : ℝ) < u * φ - 1 := by nlinarith [hu_gt1, goldenRatio_pos, h2]
    rw [← sub_pos]
    have key : φ + φ⁻¹ - (u + u⁻¹) = (φ - u) * (u * φ - 1) / (u * φ) := by
      field_simp
      ring
    rw [key]
    exact div_pos (mul_pos (by linarith [h2]) hprod_pos) (by positivity)
  -- b ≥ 1 → b * √5 ≥ √5 > 0, but b * √5 < √5. Contradiction.
  have : (b : ℝ) * Real.sqrt 5 ≥ Real.sqrt 5 :=
    le_mul_of_one_le_left (Real.sqrt_nonneg 5) hb_ge1
  linarith

end BealMinimalityNormArg

-- Axiom checks: only [propext, Classical.choice, Quot.sound] are permitted.
#print axioms BealMinimalityNormArg.no_norm_one_unit_in_one_phi
#print axioms BealMinimalityNormArg.no_norm_neg_one_unit_in_one_phi
