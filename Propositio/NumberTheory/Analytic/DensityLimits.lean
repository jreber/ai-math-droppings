/-
# Density limit theorems

Two density-LIMIT corollaries of the asymptotic-with-error-term lemmas
`SquarefreeCount.squarefree_count_asymptotic` and
`CoprimePairsDensity.coprime_pairs_count_asymptotic`.

* `squarefree_density_tendsto`: the density of squarefree numbers in `[1,N]`
  tends to `6/π²`.
* `coprime_pairs_density_tendsto`: the density of coprime pairs in `[1,N]²`
  tends to `6/π²`.

Both are obtained by dividing the respective error bound by `N` (resp. `N²`)
and squeezing the resulting deviation to `0`.
-/
import Propositio.NumberTheory.Analytic.SquarefreeCount
import Propositio.NumberTheory.Analytic.CoprimePairsDensity
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Analysis.SpecificLimits.Basic

open Filter Topology

namespace DensityLimits

/-- The density of squarefree integers in `[1,N]` tends to `6/π²`. -/
theorem squarefree_density_tendsto :
    Filter.Tendsto
      (fun N : ℕ => (((Finset.Icc 1 N).filter Squarefree).card : ℝ) / (N : ℝ))
      Filter.atTop (nhds (6 / Real.pi ^ 2)) := by
  obtain ⟨C, N₀, hC⟩ := SquarefreeCount.squarefree_count_asymptotic
  -- The deviation `count/N - 6/π²` tends to `0`.
  have hDev :
      Filter.Tendsto
        (fun N : ℕ =>
          (((Finset.Icc 1 N).filter Squarefree).card : ℝ) / (N : ℝ) - 6 / Real.pi ^ 2)
        Filter.atTop (nhds 0) := by
    rw [tendsto_zero_iff_abs_tendsto_zero]
    refine squeeze_zero' (g := fun N : ℕ => C / Real.sqrt N) ?_ ?_ ?_
    · exact Eventually.of_forall (fun N => abs_nonneg _)
    · filter_upwards [Filter.eventually_ge_atTop (max N₀ 1)] with N hN
      have hN0 : N₀ ≤ N := le_trans (le_max_left _ _) hN
      have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
      have hNR : (0 : ℝ) < N := by exact_mod_cast hN1
      have hNne : (N : ℝ) ≠ 0 := ne_of_gt hNR
      have hsqrtpos : (0 : ℝ) < Real.sqrt N := Real.sqrt_pos.mpr hNR
      have hsqrtne : Real.sqrt (N : ℝ) ≠ 0 := ne_of_gt hsqrtpos
      have hsq : Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ) = N :=
        Real.mul_self_sqrt (le_of_lt hNR)
      have hbound := hC N hN0
      simp only [Function.comp_apply]
      have e1 :
          (((Finset.Icc 1 N).filter Squarefree).card : ℝ) / (N : ℝ) - 6 / Real.pi ^ 2
            = ((((Finset.Icc 1 N).filter Squarefree).card : ℝ) - 6 / Real.pi ^ 2 * (N : ℝ))
              / (N : ℝ) := by
        field_simp
      rw [e1, abs_div, abs_of_pos hNR]
      have eqC : C * Real.sqrt (N : ℝ) / (N : ℝ) = C / Real.sqrt (N : ℝ) := by
        rw [div_eq_div_iff hNne hsqrtne, mul_assoc, hsq]
      rw [← eqC]
      exact (div_le_div_iff_of_pos_right hNR).mpr hbound
    · -- `C / √N → 0` since `√N → ∞`.
      exact Filter.Tendsto.const_div_atTop
        (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop) C
  -- Add back the constant `6/π²`.
  have h := hDev.add_const (6 / Real.pi ^ 2)
  simpa using h

/-- The density of coprime pairs in `[1,N]²` tends to `6/π²`. -/
theorem coprime_pairs_density_tendsto :
    Filter.Tendsto
      (fun N : ℕ =>
        (((Finset.Icc 1 N ×ˢ Finset.Icc 1 N).filter
            (fun p => Nat.Coprime p.1 p.2)).card : ℝ) / (N : ℝ) ^ 2)
      Filter.atTop (nhds (6 / Real.pi ^ 2)) := by
  obtain ⟨C, N₀, hC⟩ := CoprimePairsDensity.coprime_pairs_count_asymptotic
  -- `C·log N / N → 0`.
  have hlog : Filter.Tendsto (fun N : ℕ => Real.log N / (N : ℝ)) Filter.atTop (nhds 0) := by
    have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
      tendsto_natCast_atTop_atTop
    refine h.congr (fun N => ?_)
    simp
  have hError :
      Filter.Tendsto (fun N : ℕ => C * (Real.log N / (N : ℝ))) Filter.atTop (nhds 0) := by
    simpa using hlog.const_mul C
  -- The deviation `P/N² - 6/π²` tends to `0`.
  have hDev :
      Filter.Tendsto
        (fun N : ℕ =>
          (((Finset.Icc 1 N ×ˢ Finset.Icc 1 N).filter
              (fun p => Nat.Coprime p.1 p.2)).card : ℝ) / (N : ℝ) ^ 2 - 6 / Real.pi ^ 2)
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
          (((Finset.Icc 1 N ×ˢ Finset.Icc 1 N).filter
              (fun p => Nat.Coprime p.1 p.2)).card : ℝ) / (N : ℝ) ^ 2 - 6 / Real.pi ^ 2
            = ((((Finset.Icc 1 N ×ˢ Finset.Icc 1 N).filter
                (fun p => Nat.Coprime p.1 p.2)).card : ℝ)
                - 6 / Real.pi ^ 2 * (N : ℝ) ^ 2) / (N : ℝ) ^ 2 := by
        field_simp
      rw [e1, abs_div, abs_of_pos hN2R]
      have eqC : C * ((N : ℝ) * Real.log N) / (N : ℝ) ^ 2
            = C * (Real.log N / (N : ℝ)) := by
        field_simp
      rw [← eqC]
      exact (div_le_div_iff_of_pos_right hN2R).mpr hbound
    · exact hError
  -- Add back the constant `6/π²`.
  have h := hDev.add_const (6 / Real.pi ^ 2)
  simpa using h

end DensityLimits

-- Axiom audit: both depend only on [propext, Classical.choice, Quot.sound].
#print axioms DensityLimits.squarefree_density_tendsto
#print axioms DensityLimits.coprime_pairs_density_tendsto
