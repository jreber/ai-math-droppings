import Propositio.Collatz.PowGapCapstone120
import Mathlib.Tactic

/-!
# Normalization: a tiny-constant effective measure `C/aᵘ ⟹ PowGap`

The honest oSALIKHOV effective irrationality measure of `log₂3` has the *right* exponent
`μ ≈ 51.85` but an astronomically tiny constant `C ≈ 10⁻¹²³` (the `logb23` transform uses
`A' = A/log2 ≈ 56.1`, so `1/C = 2·B·Q²·(2A')ˢ ≈ 10¹²³`).  It therefore *fails* the `2/C ≤ 100`
hypothesis of `CollatzPowGapCapstone120.powGap_of_logb23_measure_denom` **directly**.

This file supplies the previously-missing wire.  By raising the exponent to a natural `M` with
`100^{M−μ} ≥ 1/C` (true at `M = 120`, `μ ≈ 51.85`, since `100^{68} ≫ 10¹²³`), the polynomial
`1/aᴹ` dominates `C/aᵘ` for **all** `a > 100` — there is **no** uncovered finite window (the
earlier KB belief in a "`[1280, 10¹⁰⁰]` gap" was wrong: `1/aᴹ ≤ C/aᵘ` is monotone on `a > 100`
once it holds at `a = 100`).  We then feed the *normalized* constant `C' = 1` (so `2/C' = 2 ≤ 100`)
into the `M = 120` capstone.

`powGap_of_tiny_measure` is `Den`-independent and axiom-clean; it converts any small-constant
measure into `PowGap`.  Closing the full chain still needs the numeric certificate
`1/C ≤ 100^{M−μ}` instantiated on the real engine output, which flows from the `DenIntN` bound —
the prize's remaining wall — but the structural wire here is complete.
-/

namespace CollatzPowGapNormalize

/-- **Tiny-constant normalization ⟹ `PowGap`.**  From an effective denominator-height measure
`C / aᵘ ≤ |log₂3 − k/a|` (for `a > 100`) with an *arbitrarily small* `C > 0`, pick a natural
exponent `M` with `μ ≤ M ≤ 120` large enough that `1/C ≤ 100^{M−μ}`; then Collatz `PowGap`
holds.  This removes the tiny-`C` obstruction (`1/C ≈ 10¹²³`) that the capstone's `2/C ≤ 100`
hypothesis cannot absorb, by normalizing the constant to `1` at the cost of a larger (still
`≤ 120`) exponent. -/
theorem powGap_of_tiny_measure (C μ : ℝ) (M : ℕ)
    (hC : 0 < C) (hμM : μ ≤ (M : ℝ)) (hM1 : 1 ≤ M) (hM : M ≤ 120)
    (hNorm : 1 / C ≤ (100 : ℝ) ^ ((M : ℝ) - μ))
    (h : ∀ (k a : ℕ), 100 < a → C / (a : ℝ) ^ μ ≤ |Real.logb 2 3 - (k : ℝ) / (a : ℝ)|) :
    CollatzDescentDichotomy.PowGap := by
  apply CollatzPowGapCapstone120.powGap_of_logb23_measure_denom 1 M (by norm_num) (by norm_num)
    hM1 hM
  intro k a ha
  -- `A := (a:ℝ) > 100`
  have hA100 : (100 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  have hA0 : (0 : ℝ) < (a : ℝ) := by linarith
  have hAge100 : (100 : ℝ) ≤ (a : ℝ) := le_of_lt hA100
  have hMμ : (0 : ℝ) ≤ (M : ℝ) - μ := by linarith
  have hAμ : (0 : ℝ) < (a : ℝ) ^ μ := Real.rpow_pos_of_pos hA0 μ
  have hAM : (0 : ℝ) < (a : ℝ) ^ M := pow_pos hA0 M
  -- Step 1: `1/C ≤ a^(M−μ)` (base monotonicity from `100 ≤ a`).
  have hpow_ge : (1 : ℝ) / C ≤ (a : ℝ) ^ ((M : ℝ) - μ) := by
    calc (1 : ℝ) / C ≤ (100 : ℝ) ^ ((M : ℝ) - μ) := hNorm
      _ ≤ (a : ℝ) ^ ((M : ℝ) - μ) := Real.rpow_le_rpow (by norm_num) hAge100 hMμ
  -- Step 2: `1 ≤ C · a^(M−μ)`.
  have h1 : (1 : ℝ) ≤ C * (a : ℝ) ^ ((M : ℝ) - μ) := by
    have := mul_le_mul_of_nonneg_left hpow_ge hC.le
    rwa [mul_one_div, div_self hC.ne'] at this
  -- Step 3: the normalized comparison `1 / aᴹ ≤ C / aᵘ`.
  have hnorm_le : (1 : ℝ) / (a : ℝ) ^ M ≤ C / (a : ℝ) ^ μ := by
    rw [le_div_iff₀ hAμ, one_div, inv_mul_eq_div, div_le_iff₀ hAM, ← Real.rpow_natCast (a : ℝ) M]
    -- ⊢ a^μ ≤ C * a^(M:ℝ)
    have hcombine : (a : ℝ) ^ μ * (a : ℝ) ^ ((M : ℝ) - μ) = (a : ℝ) ^ ((M : ℝ)) := by
      rw [← Real.rpow_add hA0]; congr 1; ring
    calc (a : ℝ) ^ μ = (a : ℝ) ^ μ * 1 := (mul_one _).symm
      _ ≤ (a : ℝ) ^ μ * (C * (a : ℝ) ^ ((M : ℝ) - μ)) :=
            mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hA0.le μ)
      _ = C * ((a : ℝ) ^ μ * (a : ℝ) ^ ((M : ℝ) - μ)) := by ring
      _ = C * (a : ℝ) ^ ((M : ℝ)) := by rw [hcombine]
  exact le_trans hnorm_le (h k a ha)

end CollatzPowGapNormalize
