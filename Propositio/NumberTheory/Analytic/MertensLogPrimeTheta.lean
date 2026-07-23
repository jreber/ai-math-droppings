import Propositio.NumberTheory.Analytic.MertensLogPrimeLower
import Propositio.NumberTheory.Analytic.MertensLogPrimeUpper
import Mathlib.Analysis.Asymptotics.Theta
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Mertens' first theorem in order-of-magnitude form: `Σ_{p ≤ n} (log p)/p = Θ(log n)`

This capstone combines the two one-sided Mertens-type estimates already proved in this tree:

* `MertensLogPrimeLower.mertensSum_ge` : `∃ c > 0, ∃ N, ∀ n ≥ N, c·log n ≤ mertensSum n`
  (the lower half, with `c = 1/4`, `N = 8`), and
* `MertensLogPrimeUpper.mertensSum_le` : `∃ C, ∃ N, ∀ n ≥ N, mertensSum n ≤ log n + C`
  (the upper half, with `C = log 4`, `N = 1`),

into the asymptotic statement that the Mertens prime sum has logarithmic order:

`Σ_{p ≤ n} (log p)/p  =Θ[atTop]  log n`.

## Main results

* `MertensLogPrimeTheta.mertensSum_nonneg`     : `0 ≤ mertensSum n`.
* `MertensLogPrimeTheta.mertensSum_isBigO_log` : `mertensSum =O[atTop] log`.
* `MertensLogPrimeTheta.log_isBigO_mertensSum` : `log =O[atTop] mertensSum`.
* `MertensLogPrimeTheta.mertensSum_isTheta`    : `mertensSum =Θ[atTop] log`.
-/

open Asymptotics Filter

namespace MertensLogPrimeTheta

/-- The Mertens prime sum is nonnegative: it is a sum of terms `log p / p` with `p ≥ 2`,
each of which is `≥ 0`. -/
lemma mertensSum_nonneg (n : ℕ) : 0 ≤ MertensLogPrimeLower.mertensSum n := by
  unfold MertensLogPrimeLower.mertensSum
  apply Finset.sum_nonneg
  intro p hp
  rw [Finset.mem_filter] at hp
  have hpp : p.Prime := hp.2
  apply div_nonneg
  · exact Real.log_nonneg (by exact_mod_cast hpp.one_lt.le)
  · exact Nat.cast_nonneg p

/-- **Upper order bound:** `mertensSum n = O(log n)` as `n → ∞`.
From `mertensSum n ≤ log n + C` and `log n ≥ 1` (for `n ≥ 3`),
`mertensSum n ≤ (1 + |C|)·log n`. -/
theorem mertensSum_isBigO_log :
    (fun n : ℕ => MertensLogPrimeLower.mertensSum n) =O[atTop] (fun n : ℕ => Real.log n) := by
  obtain ⟨C, N, hC⟩ := MertensLogPrimeUpper.mertensSum_le
  rw [Asymptotics.isBigO_iff]
  refine ⟨1 + |C|, ?_⟩
  filter_upwards [eventually_ge_atTop (max N 3)] with n hn
  have hN : N ≤ n := le_trans (le_max_left _ _) hn
  have hn3 : 3 ≤ n := le_trans (le_max_right _ _) hn
  have hn3r : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn3
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  -- `log n ≥ 1` because `e < 3 ≤ n`.
  have hlogn1 : 1 ≤ Real.log n := by
    rw [Real.le_log_iff_exp_le hnpos]
    have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
    linarith
  have hlognnn : (0 : ℝ) ≤ Real.log n := by linarith
  have hub := hC n hN
  have hms := mertensSum_nonneg n
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hms, abs_of_nonneg hlognnn]
  -- `mertensSum n ≤ log n + C ≤ log n + |C| ≤ log n + |C|·log n = (1+|C|)·log n`.
  have hCle : C ≤ |C| := le_abs_self C
  have hCmul : |C| ≤ |C| * Real.log n := by
    nlinarith [mul_le_mul_of_nonneg_left hlogn1 (abs_nonneg C)]
  nlinarith [hub, hCle, hCmul]

/-- **Lower order bound:** `log n = O(mertensSum n)` as `n → ∞`.
From `c·log n ≤ mertensSum n` we get `log n ≤ (1/c)·mertensSum n`. -/
theorem log_isBigO_mertensSum :
    (fun n : ℕ => Real.log n) =O[atTop] (fun n : ℕ => MertensLogPrimeLower.mertensSum n) := by
  obtain ⟨c, hcpos, N, hc⟩ := MertensLogPrimeLower.mertensSum_ge
  rw [Asymptotics.isBigO_iff]
  refine ⟨1 / c, ?_⟩
  filter_upwards [eventually_ge_atTop (max N 1)] with n hn
  have hN : N ≤ n := le_trans (le_max_left _ _) hn
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  have hlognnn : (0 : ℝ) ≤ Real.log n :=
    Real.log_nonneg (by exact_mod_cast hn1)
  have hlow := hc n hN
  have hms := mertensSum_nonneg n
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hlognnn, abs_of_nonneg hms]
  rw [one_div_mul_eq_div, le_div_iff₀ hcpos]
  nlinarith [hlow]

/-- **Mertens' first theorem (order-of-magnitude form).**
The Mertens prime sum has logarithmic order:

`Σ_{p ≤ n} (log p)/p  =Θ[atTop]  log n`. -/
theorem mertensSum_isTheta :
    Asymptotics.IsTheta Filter.atTop
      (fun n : ℕ => MertensLogPrimeLower.mertensSum n)
      (fun n : ℕ => Real.log n) :=
  ⟨mertensSum_isBigO_log, log_isBigO_mertensSum⟩

end MertensLogPrimeTheta
