import Mathlib.Analysis.SpecialFunctions.Stirling

/-!
# An explicit Stirling **upper** bound on `log n!`

Mathlib proves an explicit Stirling **lower** bound (`Stirling.le_log_factorial_stirling`:
`n·log n − n + ½·log n + ½·log(2π) ≤ log n!`) but **no** explicit upper bound — only the
asymptotic equivalence `factorial_isEquivalent_stirling`.  This file fills that gap:

`log n! ≤ n·log n − n + ½·log n + 1`  for `n ≥ 1`.

The constant `1` comes from `stirlingSeq n ≤ stirlingSeq 1 = e/√2` (the Stirling sequence is
antitone and `log(e/√2) = 1 − ½·log 2`), composed with `log_stirlingSeq_formula`.  Together with
the mathlib lower bound this gives a two-sided estimate with the **same** main term
`n·log n − n + ½·log n`, the input the Chebyshev-30 `M`-size bound needs (the `n log n` and `−n`
terms cancel by the period-30 weight balance, leaving the entropy constant `A ≈ 0.921`).
-/

namespace CollatzChebyshev30

open Real

/-- `log (stirlingSeq 1) = 1 − ½·log 2` (i.e. `stirlingSeq 1 = e/√2`). -/
theorem log_stirlingSeq_one : Real.log (Stirling.stirlingSeq 1) = 1 - 1 / 2 * Real.log 2 := by
  rw [Stirling.log_stirlingSeq_formula]
  simp only [Nat.factorial_one, Nat.cast_one, Real.log_one, mul_one]
  rw [Real.log_div (by norm_num) (Real.exp_ne_zero 1), Real.log_one, Real.log_exp]
  ring

/-- **Explicit Stirling upper bound** (absent from mathlib): for `n ≥ 1`,
`log n! ≤ n·log n − n + ½·log n + 1`. -/
theorem log_factorial_le {n : ℕ} (hn : 1 ≤ n) :
    Real.log (Nat.factorial n : ℝ) ≤ n * Real.log n - n + Real.log n / 2 + 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  -- `stirlingSeq (k+1) ≤ stirlingSeq 1` by antitonicity of `stirlingSeq ∘ succ`.
  have hseq : Stirling.stirlingSeq (k + 1) ≤ Stirling.stirlingSeq 1 := by
    have := Stirling.stirlingSeq'_antitone (Nat.zero_le k)
    simpa [Function.comp] using this
  have hpos : (0 : ℝ) < Stirling.stirlingSeq (k + 1) := Stirling.stirlingSeq'_pos k
  have hlogseq : Real.log (Stirling.stirlingSeq (k + 1)) ≤ 1 - 1 / 2 * Real.log 2 := by
    calc Real.log (Stirling.stirlingSeq (k + 1)) ≤ Real.log (Stirling.stirlingSeq 1) :=
          Real.log_le_log hpos hseq
      _ = 1 - 1 / 2 * Real.log 2 := log_stirlingSeq_one
  -- expand `log_stirlingSeq_formula` at `n = k+1`.
  have hform := Stirling.log_stirlingSeq_formula (k + 1)
  have hcast : (0 : ℝ) < ((k : ℝ) + 1) := by positivity
  have hexpd : Real.log (((k : ℝ) + 1) / Real.exp 1) = Real.log ((k : ℝ) + 1) - 1 := by
    rw [Real.log_div (by positivity) (Real.exp_ne_zero 1), Real.log_exp]
  have hexpm : Real.log (2 * ((k : ℝ) + 1)) = Real.log 2 + Real.log ((k : ℝ) + 1) := by
    rw [Real.log_mul (by norm_num) (by positivity)]
  push_cast at hform ⊢
  rw [hexpd, hexpm] at hform
  nlinarith [hform, hlogseq]

/-- Re-export of the mathlib explicit Stirling **lower** bound, paired with `log_factorial_le`. -/
theorem le_log_factorial {n : ℕ} (hn : 1 ≤ n) :
    n * Real.log n - n + Real.log n / 2 + Real.log (2 * Real.pi) / 2 ≤ Real.log (Nat.factorial n : ℝ) :=
  Stirling.le_log_factorial_stirling (by omega)

end CollatzChebyshev30
