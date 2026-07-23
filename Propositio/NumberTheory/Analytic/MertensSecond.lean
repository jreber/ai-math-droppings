import Propositio.NumberTheory.Analytic.MertensReciprocalLower
import Propositio.NumberTheory.Analytic.MertensReciprocalUpper
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Mertens' second theorem (asymptotic-ratio form)

Combining the two halves of Mertens' second theorem,
`MertensReciprocalLower.key` (`log log n − 1 ≤ Σ_{p ≤ n} 1/p`, `n ≥ 3`) and
`MertensReciprocalUpper.sum_reciprocal_primes_le` (`Σ_{p ≤ n} 1/p ≤ log log n + C`),
both with coefficient exactly `1` on `log log n`, we obtain the asymptotic-ratio statement

`(Σ_{p ≤ n} 1/p) / log log n → 1`.

The proof is the standard "divide and squeeze": eventually
`|S n − log log n| ≤ M` for a constant `M`, hence `|S n / log log n − 1| ≤ M / log log n`,
and `log log n → ∞` (so `M / log log n → 0`).
-/

namespace MertensSecond

open Filter

/-- **Mertens' second theorem (ratio form).**  The partial sums of prime reciprocals,
normalized by `log log n`, tend to `1`. -/
theorem mertens_second_tendsto :
    Filter.Tendsto
      (fun n : ℕ => (∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 : ℝ) / p)
                      / Real.log (Real.log n))
      Filter.atTop (nhds 1) := by
  -- The prime-reciprocal partial sum.
  set S : ℕ → ℝ :=
    fun n => ∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 : ℝ) / p with hS
  -- Lower bound with coefficient exactly `1`: `log log n − 1 ≤ S n` for `n ≥ 3`.
  have hlo : ∀ n : ℕ, 3 ≤ n → Real.log (Real.log n) - 1 ≤ S n := by
    intro n hn
    have hk := MertensReciprocalLower.key n hn
    have hset : (n + 1).primesBelow = (Finset.range (n + 1)).filter Nat.Prime := rfl
    rw [hset] at hk
    have heq : S n = ∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime, ((p : ℝ))⁻¹ :=
      Finset.sum_congr rfl (fun p _ => one_div _)
    rw [heq]; exact hk
  -- Upper bound: `S n ≤ log log n + C_hi` for `n ≥ N_hi`.
  obtain ⟨C_hi, N_hi, hhi⟩ := MertensReciprocalUpper.sum_reciprocal_primes_le
  -- A single two-sided constant.
  set M : ℝ := max 1 C_hi with hM
  -- The centered quantity `S n / log log n − 1` tends to `0`.
  have key : Tendsto (fun n : ℕ => S n / Real.log (Real.log n) - 1) atTop (nhds 0) := by
    rw [tendsto_zero_iff_abs_tendsto_zero]
    refine squeeze_zero' (g := fun n : ℕ => M / Real.log (Real.log n)) ?_ ?_ ?_
    · filter_upwards with n using abs_nonneg _
    · filter_upwards [eventually_ge_atTop (max 3 N_hi)] with n hn
      have hn3 : 3 ≤ n := le_of_max_le_left hn
      have hnhi : N_hi ≤ n := le_of_max_le_right hn
      have hnR : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn3
      have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
      -- `log log n > 0` since `n ≥ 3 > e`.
      have hexp : Real.exp 1 < (n : ℝ) := by
        have h := Real.exp_one_lt_d9
        linarith
      have hlogn1 : 1 < Real.log n := (Real.lt_log_iff_exp_lt hnpos).mpr hexp
      have hLpos : 0 < Real.log (Real.log n) := Real.log_pos hlogn1
      -- Two-sided bound on `S n − log log n`.
      have hMbound : |S n - Real.log (Real.log n)| ≤ M := by
        rw [abs_le]
        refine ⟨?_, ?_⟩
        · have := hlo n hn3
          have h1M : (1 : ℝ) ≤ M := le_max_left _ _
          linarith
        · have := hhi n hnhi
          have hCM : C_hi ≤ M := le_max_right _ _
          linarith
      -- Rewrite the centered quantity as a single fraction and bound it.
      show |S n / Real.log (Real.log n) - 1| ≤ M / Real.log (Real.log n)
      have hrw : S n / Real.log (Real.log n) - 1
          = (S n - Real.log (Real.log n)) / Real.log (Real.log n) := by
        field_simp
      rw [hrw, abs_div, abs_of_pos hLpos]
      gcongr
    · exact (Real.tendsto_log_atTop.comp
        (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).const_div_atTop M
  -- Add back the constant `1`.
  have h := key.add_const 1
  have hfun : (fun n : ℕ => S n / Real.log (Real.log n) - 1 + 1)
      = fun n : ℕ => S n / Real.log (Real.log n) := by funext n; ring
  rw [hfun, zero_add] at h
  exact h

#print axioms mertens_second_tendsto

end MertensSecond
