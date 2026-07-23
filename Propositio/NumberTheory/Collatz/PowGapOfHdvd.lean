import Propositio.NumberTheory.Diophantine.OSalikhovAssembly
import Propositio.NumberTheory.Diophantine.OSalikhovCertificate
import Propositio.NumberTheory.Diophantine.OSalikhovDenBoundReduced
import Propositio.NumberTheory.Diophantine.IrrMeasureCombination
import Propositio.NumberTheory.Collatz.PowGapNormalize
import Propositio.NumberTheory.Diophantine.OSalikhovIntCoord
import Propositio.NumberTheory.Diophantine.LcmGrowthBound
import Mathlib.Tactic

/-!
# Collatz `PowGap` (no Baker) from the single elementary divisibility `hdvd`

This is the capstone of the μ(log₂3) prize line.  It shows that the full Collatz
`PowGap` (the power-gap dichotomy, with **no** appeal to Baker's theorem) follows from the
single elementary `p`-adic divisibility

  `hdvd : ∀ m, DenIntN m ∣ 3ᵐ · 30 · lcm(1..2m)`.

The chain is:

  `hdvd`
    → `DenR n ≤ 6·30ⁿ`                                       (OSalikhovDenBoundReduced)
    → the four two-log "form" clauses with CONCRETE constants
        `A = 38.88`, `B = 2.7·10⁹`, `ρ = 0.81`, `Q = 45000`  (interface_clauses_c30)
    → an effective irrationality measure of `log₂3`
        `C₀/q^(1+s) ≤ |log₂3 − p/q|`, `s = log Q / log ρ⁻¹`  (logb23_measure_of_twolog_forms_const)
    → Collatz `PowGap` via the tiny-constant normalization at `M = 120`
        (numeric certificate `1/C₀ ≤ 100^{119−s}`)            (powGap_of_tiny_measure).

Acceptable axioms: `propext, Classical.choice, Quot.sound` plus the `native_decide`/`ofReduceBool`
census axioms inherited from the Den bound.  No `sorryAx`.
-/

namespace CollatzPowGapOfHdvd

open OSalikhovIntCoord OSalikhovAssembly OSalikhovTwoLog OSalikhovDenDvd LcmGrowthBound

/-- **Collatz `PowGap` from the single elementary divisibility `hdvd`.** -/
theorem collatz_powGap_of_hdvd
    (hdvd : ∀ m, DenIntN m ∣ 3 ^ m * 30 * lcmUpto (2 * m)) :
    CollatzDescentDichotomy.PowGap := by
  -- Step A: the four form clauses with concrete witnesses (Den := DenR, D := 6).
  obtain ⟨hsmall, hwpos, hwden, hdet⟩ :=
    interface_clauses_c30 DenR 6 (by norm_num) DenR_pos (DenR_bound_30_of_hdvd hdvd)
      vInt wInt vInt_cast_DenR wInt_cast_DenR E1_decomp E2_decomp
  -- Step B: the effective irrationality measure with CONCRETE constants.
  have hmeas := IrrMeasureCombination.logb23_measure_of_twolog_forms_const
    vInt wInt (8 * 6 * (810 / 1000)) (10000 * 6 * 30 * 1500) (810 / 1000) 45000
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hsmall hwpos hwden hdet
  -- Abbreviate the constants (this folds the matching subterms inside `hmeas`).
  set A : ℝ := 8 * 6 * (810 / 1000) with hAdef          -- = 38.88
  set B : ℝ := 10000 * 6 * 30 * 1500 with hBdef         -- = 2.7e9
  set ρ : ℝ := 810 / 1000 with hρdef
  set Q : ℝ := 45000 with hQdef
  set s : ℝ := Real.log Q / Real.log ρ⁻¹ with hsdef
  set A' : ℝ := A / Real.log 2 with hA'def
  set C₀ : ℝ := 1 / (2 * B * Q ^ 2 * (2 * A') ^ s) with hC₀def
  -- Now `hmeas : ∀ p q, 1 ≤ q → 1 ≤ 2*A'*q → C₀ / q^(1+s) ≤ |logb 2 3 - p/q|`.
  -- Basic positivity / numeric facts.
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2lt1 : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
  have hlog2gt : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hρinv : ρ⁻¹ = (1000 / 810 : ℝ) := by rw [hρdef]; norm_num
  have hlogρinv_pos : 0 < Real.log ρ⁻¹ := by rw [hρinv]; exact Real.log_pos (by norm_num)
  -- `A = 38.88`, so `A' = 38.88 / log 2`, `A' ≥ 1` and `1 ≤ 2*A' ≤ 113`.
  have hAval : A = 38.88 := by rw [hAdef, hρdef]; norm_num
  have hA'_ge1 : (1 : ℝ) ≤ A' := by
    rw [hA'def, hAval, le_div_iff₀ hlog2pos]; nlinarith [hlog2lt1]
  have h2A'_ge1 : (1 : ℝ) ≤ 2 * A' := by nlinarith [hA'_ge1]
  have h2A'_nonneg : (0 : ℝ) ≤ 2 * A' := by linarith
  have h2A'_pos : (0 : ℝ) < 2 * A' := by linarith
  have h2A'_le : 2 * A' ≤ 113 := by
    rw [hA'def, hAval,
        show (2 : ℝ) * (38.88 / Real.log 2) = (77.76 : ℝ) / Real.log 2 by ring,
        div_le_iff₀ hlog2pos]
    nlinarith [hlog2gt]
  -- `s ≤ 51` and `0 ≤ s`.
  have hs_le51 : s ≤ 51 := by
    rw [hsdef, div_le_iff₀ hlogρinv_pos, hQdef, hρinv]
    have hpow : (45000 : ℝ) ≤ (1000 / 810 : ℝ) ^ 51 := by norm_num
    have hlog_ineq : Real.log 45000 ≤ Real.log ((1000 / 810 : ℝ) ^ 51) :=
      Real.log_le_log (by norm_num) hpow
    rw [Real.log_pow] at hlog_ineq; push_cast at hlog_ineq ⊢; linarith
  have hs_nonneg : 0 ≤ s := by
    rw [hsdef]
    exact div_nonneg (by rw [hQdef]; exact Real.log_nonneg (by norm_num)) hlogρinv_pos.le
  -- `C₀ > 0`.
  have hC₀_pos : 0 < C₀ := by
    rw [hC₀def]
    have h1 : (0 : ℝ) < 2 * B * Q ^ 2 := by rw [hBdef, hQdef]; positivity
    have h2 : (0 : ℝ) < (2 * A') ^ s := Real.rpow_pos_of_pos h2A'_pos s
    positivity
  -- `1/C₀ = 2*B*Q^2*(2*A')^s`.
  have hinvC₀ : 1 / C₀ = 2 * B * Q ^ 2 * (2 * A') ^ s := by rw [hC₀def, one_div_one_div]
  -- `(2*A')^s ≤ 113^51`.
  have hbase_pow : (2 * A') ^ s ≤ (113 : ℝ) ^ (51 : ℕ) := by
    have step1 : (2 * A') ^ s ≤ (2 * A') ^ (51 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le h2A'_ge1 hs_le51
    have step2 : (2 * A') ^ (51 : ℝ) ≤ (113 : ℝ) ^ (51 : ℝ) :=
      Real.rpow_le_rpow h2A'_nonneg h2A'_le (by norm_num)
    have step3 : (113 : ℝ) ^ (51 : ℝ) = (113 : ℝ) ^ (51 : ℕ) := by
      rw [← Real.rpow_natCast (113 : ℝ) 51]; norm_num
    linarith [step1, step2, step3.le, step3.ge]
  -- `1/C₀ ≤ 2*B*Q^2*113^51`.
  have hinvC₀_le : 1 / C₀ ≤ 2 * B * Q ^ 2 * (113 : ℝ) ^ (51 : ℕ) := by
    rw [hinvC₀]
    have hfac_nonneg : (0 : ℝ) ≤ 2 * B * Q ^ 2 := by rw [hBdef, hQdef]; positivity
    exact mul_le_mul_of_nonneg_left hbase_pow hfac_nonneg
  -- The big integer certificate: `2*B*Q^2*113^51 ≤ 100^68`.
  have hcert : 2 * B * Q ^ 2 * (113 : ℝ) ^ (51 : ℕ) ≤ (100 : ℝ) ^ (68 : ℕ) := by
    rw [hBdef, hQdef]; norm_num
  -- Step C: the measure obligation `h` in `(k a : ℕ)` form, exponent `μ = 1+s`.
  have h : ∀ (k a : ℕ), 100 < a →
      C₀ / (a : ℝ) ^ (1 + s) ≤ |Real.logb 2 3 - (k : ℝ) / (a : ℝ)| := by
    intro k a ha
    have haZ : (1 : ℤ) ≤ (a : ℤ) := by exact_mod_cast (by omega : 1 ≤ a)
    have ha100R : (100 : ℝ) < (a : ℝ) := by exact_mod_cast ha
    have hsecond : (1 : ℝ) ≤ 2 * A' * ((a : ℤ) : ℝ) := by
      have hcast : (((a : ℤ)) : ℝ) = (a : ℝ) := by push_cast; ring
      rw [hcast]
      have h1a : (1 : ℝ) ≤ (a : ℝ) := by linarith [ha100R]
      calc (1 : ℝ) = 1 * 1 := by ring
        _ ≤ 2 * A' * (a : ℝ) := mul_le_mul h2A'_ge1 h1a (by norm_num) (by linarith [h2A'_ge1])
    have hkey := hmeas (k : ℤ) (a : ℤ) haZ hsecond
    have hkc : (((k : ℤ)) : ℝ) = (k : ℝ) := by push_cast; ring
    have hac : (((a : ℤ)) : ℝ) = (a : ℝ) := by push_cast; ring
    rw [hkc, hac] at hkey
    exact hkey
  -- Assemble via `powGap_of_tiny_measure` with `C := C₀`, `μ := 1+s`, `M := 120`.
  refine CollatzPowGapNormalize.powGap_of_tiny_measure C₀ (1 + s) 120
    hC₀_pos ?_ (by norm_num) (by norm_num) ?_ h
  · -- `μ ≤ M`:  `1 + s ≤ 120`.
    push_cast; linarith [hs_le51]
  · -- `1/C₀ ≤ 100^(120 - (1+s))`.
    have hgoaleq : ((120 : ℕ) : ℝ) - (1 + s) = (120 : ℝ) - (1 + s) := by push_cast; ring
    rw [hgoaleq]
    have h100 : (100 : ℝ) ^ (68 : ℕ) ≤ (100 : ℝ) ^ ((120 : ℝ) - (1 + s)) := by
      rw [← Real.rpow_natCast (100 : ℝ) 68]
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast; linarith [hs_le51]
    calc 1 / C₀ ≤ 2 * B * Q ^ 2 * (113 : ℝ) ^ (51 : ℕ) := hinvC₀_le
      _ ≤ (100 : ℝ) ^ (68 : ℕ) := hcert
      _ ≤ (100 : ℝ) ^ ((120 : ℝ) - (1 + s)) := h100

#print axioms collatz_powGap_of_hdvd

end CollatzPowGapOfHdvd
