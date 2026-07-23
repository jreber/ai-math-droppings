import Propositio.NumberTheory.Analytic.OmegaSummatory
import Propositio.NumberTheory.Analytic.BigOmegaSummatory
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Average order of `ω` and `Ω` (Hardy–Ramanujan, ratio form)

The average order of both the number-of-distinct-prime-factors function `ω(n)`
(`Nat.primeFactors.card`) and the number-of-prime-factors-with-multiplicity function
`Ω(n)` (`(Nat.primeFactorsList n).length`) is `log log n`:

`(∑_{n ≤ N} ω(n)) / (N · log log N) → 1`,
`(∑_{n ≤ N} Ω(n)) / (N · log log N) → 1`.

Both follow by the standard "divide and squeeze" from the summatory asymptotics
`OmegaSummatory.omega_summatory_asymptotic` and
`BigOmegaSummatory.bigOmega_summatory_asymptotic`, each of the form
`|S N − N · log log N| ≤ C · N` (leading coefficient exactly `1` on `N · log log N`).
Dividing by `N · log log N` gives `|S N / (N · log log N) − 1| ≤ C / log log N → 0`,
exactly mirroring `MertensSecond.mertens_second_tendsto`.
-/

namespace PrimeFactorAverage

open Filter

/-- Generic "divide and squeeze" packaging: if `S` satisfies `|S N − N · log log N| ≤ C · N`
eventually, then `S N / (N · log log N) → 1`. -/
theorem ratio_tendsto_one_of_summatory (S : ℕ → ℝ) (C : ℝ) (N₀ : ℕ)
    (hbound : ∀ N : ℕ, N₀ ≤ N → |S N - N * Real.log (Real.log N)| ≤ C * N) :
    Filter.Tendsto
      (fun N : ℕ => S N / ((N : ℝ) * Real.log (Real.log N)))
      Filter.atTop (nhds 1) := by
  -- A nonnegative two-sided constant.
  set M : ℝ := max C 0 with hM
  have hMnn : (0 : ℝ) ≤ M := le_max_right _ _
  -- The centered quantity `S N / (N · log log N) − 1` tends to `0`.
  have key : Tendsto
      (fun N : ℕ => S N / ((N : ℝ) * Real.log (Real.log N)) - 1) atTop (nhds 0) := by
    rw [tendsto_zero_iff_abs_tendsto_zero]
    refine squeeze_zero' (g := fun N : ℕ => M / Real.log (Real.log N)) ?_ ?_ ?_
    · filter_upwards with N using abs_nonneg _
    · filter_upwards [eventually_ge_atTop (max N₀ 3)] with N hN
      have hN0 : N₀ ≤ N := le_of_max_le_left hN
      have hN3 : 3 ≤ N := le_of_max_le_right hN
      have hNR : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN3
      have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
      -- `log log N > 0` since `N ≥ 3 > e`.
      have hexp : Real.exp 1 < (N : ℝ) := by
        have h := Real.exp_one_lt_d9
        linarith
      have hlogN1 : 1 < Real.log N := (Real.lt_log_iff_exp_lt hNpos).mpr hexp
      have hLpos : 0 < Real.log (Real.log N) := Real.log_pos hlogN1
      have hDpos : 0 < (N : ℝ) * Real.log (Real.log N) := mul_pos hNpos hLpos
      -- Bound `|S N − N · log log N| ≤ M · N`.
      have hb := hbound N hN0
      have hCM : C ≤ M := le_max_left _ _
      have hbM : |S N - (N : ℝ) * Real.log (Real.log N)| ≤ M * N := by
        refine le_trans hb ?_
        gcongr
      -- Rewrite the centered quantity as a single fraction and bound it.
      show |S N / ((N : ℝ) * Real.log (Real.log N)) - 1| ≤ M / Real.log (Real.log N)
      have hrw : S N / ((N : ℝ) * Real.log (Real.log N)) - 1
          = (S N - (N : ℝ) * Real.log (Real.log N))
              / ((N : ℝ) * Real.log (Real.log N)) := by
        field_simp
      rw [hrw, abs_div, abs_of_pos hDpos]
      have hNne : (N : ℝ) ≠ 0 := ne_of_gt hNpos
      calc |S N - (N : ℝ) * Real.log (Real.log N)| / ((N : ℝ) * Real.log (Real.log N))
          ≤ (M * N) / ((N : ℝ) * Real.log (Real.log N)) := by gcongr
        _ = M / Real.log (Real.log N) := by
              have hLne : Real.log (Real.log N) ≠ 0 := ne_of_gt hLpos
              field_simp
    · exact (Real.tendsto_log_atTop.comp
        (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).const_div_atTop M
  -- Add back the constant `1`.
  have h := key.add_const 1
  have hfun : (fun N : ℕ => S N / ((N : ℝ) * Real.log (Real.log N)) - 1 + 1)
      = fun N : ℕ => S N / ((N : ℝ) * Real.log (Real.log N)) := by funext N; ring
  rw [hfun, zero_add] at h
  exact h

/-- **Average order of `ω`.**  The summatory `∑_{n ≤ N} ω(n)`, normalized by
`N · log log N`, tends to `1`. -/
theorem omega_average_tendsto :
    Filter.Tendsto
      (fun N : ℕ => (∑ n ∈ Finset.Icc 1 N, (n.primeFactors.card : ℝ))
                      / ((N : ℝ) * Real.log (Real.log N)))
      Filter.atTop (nhds 1) := by
  obtain ⟨C, N₀, hbound⟩ := OmegaSummatory.omega_summatory_asymptotic
  exact ratio_tendsto_one_of_summatory
    (fun N => ∑ n ∈ Finset.Icc 1 N, (n.primeFactors.card : ℝ)) C N₀ hbound

/-- **Average order of `Ω`.**  The summatory `∑_{n ≤ N} Ω(n)`, normalized by
`N · log log N`, tends to `1`. -/
theorem bigOmega_average_tendsto :
    Filter.Tendsto
      (fun N : ℕ => (∑ n ∈ Finset.Icc 1 N, ((Nat.primeFactorsList n).length : ℝ))
                      / ((N : ℝ) * Real.log (Real.log N)))
      Filter.atTop (nhds 1) := by
  obtain ⟨C, N₀, hbound⟩ := BigOmegaSummatory.bigOmega_summatory_asymptotic
  exact ratio_tendsto_one_of_summatory
    (fun N => ∑ n ∈ Finset.Icc 1 N, ((Nat.primeFactorsList n).length : ℝ)) C N₀ hbound

#print axioms omega_average_tendsto
#print axioms bigOmega_average_tendsto

end PrimeFactorAverage
