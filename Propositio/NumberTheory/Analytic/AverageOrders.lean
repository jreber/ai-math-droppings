/-
# Average-order limit theorems

Two average-order LIMIT corollaries of the asymptotic-with-error-term lemmas
`SigmaSummatory.sigma_summatory_asymptotic` and
`TotientSummatory.totient_summatory_asymptotic`.

* `sigma_average_tendsto`: `(∑_{n=1}^N σ(n)) / N²` tends to `π²/12`.
* `totient_average_tendsto`: `(∑_{n=1}^N φ(n)) / N²` tends to `3/π²`.

Both are obtained by dividing the respective `O(N log N)` error bound by `N²`
and squeezing the resulting deviation to `0` — the same move as
`DensityLimits.coprime_pairs_density_tendsto`.
-/
import Propositio.NumberTheory.Analytic.SigmaSummatory
import Propositio.NumberTheory.Analytic.TotientSummatory
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Analysis.SpecificLimits.Basic

open Filter Topology
open scoped ArithmeticFunction.sigma

namespace AverageOrders

/-- The average order of `σ`: `(∑_{n=1}^N σ(n)) / N²` tends to `π²/12`. -/
theorem sigma_average_tendsto :
    Filter.Tendsto
      (fun N : ℕ => (∑ n ∈ Finset.Icc 1 N, (σ 1 n : ℝ)) / (N : ℝ) ^ 2)
      Filter.atTop (nhds (Real.pi ^ 2 / 12)) := by
  obtain ⟨C, N₀, hC⟩ := SigmaSummatory.sigma_summatory_asymptotic
  -- `C·log N / N → 0`.
  have hlog : Filter.Tendsto (fun N : ℕ => Real.log N / (N : ℝ)) Filter.atTop (nhds 0) := by
    have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
      tendsto_natCast_atTop_atTop
    refine h.congr (fun N => ?_)
    simp
  have hError :
      Filter.Tendsto (fun N : ℕ => C * (Real.log N / (N : ℝ))) Filter.atTop (nhds 0) := by
    simpa using hlog.const_mul C
  -- The deviation `Σ/N² - π²/12` tends to `0`.
  have hDev :
      Filter.Tendsto
        (fun N : ℕ =>
          (∑ n ∈ Finset.Icc 1 N, (σ 1 n : ℝ)) / (N : ℝ) ^ 2 - Real.pi ^ 2 / 12)
        Filter.atTop (nhds 0) := by
    rw [tendsto_zero_iff_abs_tendsto_zero]
    refine squeeze_zero' (g := fun N : ℕ => C * (Real.log N / (N : ℝ))) ?_ ?_ ?_
    · exact Eventually.of_forall (fun N => abs_nonneg _)
    · filter_upwards [Filter.eventually_ge_atTop (max N₀ 1)] with N hN
      have hN0 : N₀ ≤ N := le_trans (le_max_left _ _) hN
      have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
      have hNR : (0 : ℝ) < N := by exact_mod_cast hN1
      have hNne : (N : ℝ) ≠ 0 := ne_of_gt hNR
      have hN2R : (0 : ℝ) < (N : ℝ) ^ 2 := by positivity
      have hbound := hC N hN0
      simp only [Function.comp_apply]
      have e1 :
          (∑ n ∈ Finset.Icc 1 N, (σ 1 n : ℝ)) / (N : ℝ) ^ 2 - Real.pi ^ 2 / 12
            = ((∑ n ∈ Finset.Icc 1 N, (σ 1 n : ℝ))
                - Real.pi ^ 2 / 12 * (N : ℝ) ^ 2) / (N : ℝ) ^ 2 := by
        field_simp
      rw [e1, abs_div, abs_of_pos hN2R]
      have eqC : C * ((N : ℝ) * Real.log N) / (N : ℝ) ^ 2
            = C * (Real.log N / (N : ℝ)) := by
        field_simp
      rw [← eqC]
      exact (div_le_div_iff_of_pos_right hN2R).mpr hbound
    · exact hError
  -- Add back the constant `π²/12`.
  have h := hDev.add_const (Real.pi ^ 2 / 12)
  simpa using h

/-- The average order of `φ`: `(∑_{n=1}^N φ(n)) / N²` tends to `3/π²`. -/
theorem totient_average_tendsto :
    Filter.Tendsto
      (fun N : ℕ => (∑ n ∈ Finset.Icc 1 N, (Nat.totient n : ℝ)) / (N : ℝ) ^ 2)
      Filter.atTop (nhds (3 / Real.pi ^ 2)) := by
  obtain ⟨C, N₀, hC⟩ := TotientSummatory.totient_summatory_asymptotic
  -- `C·log N / N → 0`.
  have hlog : Filter.Tendsto (fun N : ℕ => Real.log N / (N : ℝ)) Filter.atTop (nhds 0) := by
    have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
      tendsto_natCast_atTop_atTop
    refine h.congr (fun N => ?_)
    simp
  have hError :
      Filter.Tendsto (fun N : ℕ => C * (Real.log N / (N : ℝ))) Filter.atTop (nhds 0) := by
    simpa using hlog.const_mul C
  -- The deviation `Φ/N² - 3/π²` tends to `0`.
  have hDev :
      Filter.Tendsto
        (fun N : ℕ =>
          (∑ n ∈ Finset.Icc 1 N, (Nat.totient n : ℝ)) / (N : ℝ) ^ 2 - 3 / Real.pi ^ 2)
        Filter.atTop (nhds 0) := by
    rw [tendsto_zero_iff_abs_tendsto_zero]
    refine squeeze_zero' (g := fun N : ℕ => C * (Real.log N / (N : ℝ))) ?_ ?_ ?_
    · exact Eventually.of_forall (fun N => abs_nonneg _)
    · filter_upwards [Filter.eventually_ge_atTop (max N₀ 1)] with N hN
      have hN0 : N₀ ≤ N := le_trans (le_max_left _ _) hN
      have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
      have hNR : (0 : ℝ) < N := by exact_mod_cast hN1
      have hNne : (N : ℝ) ≠ 0 := ne_of_gt hNR
      have hN2R : (0 : ℝ) < (N : ℝ) ^ 2 := by positivity
      have hbound := hC N hN0
      simp only [Function.comp_apply]
      have e1 :
          (∑ n ∈ Finset.Icc 1 N, (Nat.totient n : ℝ)) / (N : ℝ) ^ 2 - 3 / Real.pi ^ 2
            = ((∑ n ∈ Finset.Icc 1 N, (Nat.totient n : ℝ))
                - 3 / Real.pi ^ 2 * (N : ℝ) ^ 2) / (N : ℝ) ^ 2 := by
        field_simp
      rw [e1, abs_div, abs_of_pos hN2R]
      have eqC : C * ((N : ℝ) * Real.log N) / (N : ℝ) ^ 2
            = C * (Real.log N / (N : ℝ)) := by
        field_simp
      rw [← eqC]
      exact (div_le_div_iff_of_pos_right hN2R).mpr hbound
    · exact hError
  -- Add back the constant `3/π²`.
  have h := hDev.add_const (3 / Real.pi ^ 2)
  simpa using h

end AverageOrders

-- Axiom audit: both depend only on [propext, Classical.choice, Quot.sound].
#print axioms AverageOrders.sigma_average_tendsto
#print axioms AverageOrders.totient_average_tendsto
