import Propositio.NumberTheory.Analytic.DivisorSummatory
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# The Dirichlet divisor average

Dirichlet's divisor theorem gives `∑_{n ≤ N} d(n) = N log N + O(N)`
(`DivisorSummatory.divisor_summatory_asymptotic`).  Dividing through by `N log N`
shows the *average* number of divisors over `[1, N]`, normalized by `log N`,
tends to `1`:

`(∑_{n ≤ N} d(n)) / (N log N) → 1`.

The proof is the standard "divide and squeeze": from `|D(N) − N log N| ≤ C·N` we
get `|D(N)/(N log N) − 1| ≤ C / log N`, which tends to `0`.
-/

namespace DivisorAverage

open Filter

/-- **Dirichlet divisor average.** The average number of divisors over `[1, N]`,
normalized by `log N`, tends to `1`. -/
theorem divisor_average_tendsto :
    Filter.Tendsto
      (fun N : ℕ => (∑ n ∈ Finset.Icc 1 N, (n.divisors.card : ℝ)) / ((N : ℝ) * Real.log N))
      Filter.atTop (nhds 1) := by
  obtain ⟨C, N₀, hC⟩ := DivisorSummatory.divisor_summatory_asymptotic
  -- Abbreviation for the summatory divisor function as a real number.
  set S : ℕ → ℝ := fun N => ∑ n ∈ Finset.Icc 1 N, (n.divisors.card : ℝ) with hS
  -- The centered quantity `S N / (N log N) − 1` tends to `0`.
  have key : Tendsto (fun N : ℕ => S N / ((N : ℝ) * Real.log N) - 1) atTop (nhds 0) := by
    rw [tendsto_zero_iff_abs_tendsto_zero]
    -- Squeeze: `0 ≤ |·| ≤ C / log N → 0`.
    refine squeeze_zero' (g := fun N : ℕ => C / Real.log N) ?_ ?_ ?_
    · filter_upwards with N using abs_nonneg _
    · filter_upwards [eventually_ge_atTop (max N₀ 2)] with N hN
      have hN0 : N₀ ≤ N := le_of_max_le_left hN
      have hN2 : (2 : ℕ) ≤ N := le_of_max_le_right hN
      have hNR : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN2
      have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
      have h1N : (1 : ℝ) < (N : ℝ) := by linarith
      have hLpos : 0 < Real.log N := Real.log_pos h1N
      have hprodpos : 0 < (N : ℝ) * Real.log N := mul_pos hNpos hLpos
      have hprod_ne : (N : ℝ) * Real.log N ≠ 0 := ne_of_gt hprodpos
      -- Rewrite the centered quantity as a single fraction.
      have hrw : S N / ((N : ℝ) * Real.log N) - 1
          = (S N - (N : ℝ) * Real.log N) / ((N : ℝ) * Real.log N) := by
        field_simp
      -- Bound the absolute value.
      show |S N / ((N : ℝ) * Real.log N) - 1| ≤ C / Real.log N
      rw [hrw, abs_div, abs_of_pos hprodpos]
      calc |S N - (N : ℝ) * Real.log N| / ((N : ℝ) * Real.log N)
          ≤ (C * (N : ℝ)) / ((N : ℝ) * Real.log N) := by
            gcongr
            exact hC N hN0
        _ = C / Real.log N := by
            rw [mul_comm C (N : ℝ), mul_div_mul_left C (Real.log N) (ne_of_gt hNpos)]
    · exact (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).const_div_atTop C
  -- Add back the constant `1`.
  have := key.add_const 1
  simpa using this

#print axioms divisor_average_tendsto

end DivisorAverage
