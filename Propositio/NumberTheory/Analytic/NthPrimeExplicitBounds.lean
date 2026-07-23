import Propositio.NumberTheory.Analytic.NthPrimeGrowth

/-!
# Explicit two-sided bound on the `n`th prime

Repackaging the asymptotic `NthPrimeGrowth.nth_prime_isTheta` (`pₙ = Θ(n log n)`)
as an explicit, existentially quantified two-sided inequality: there are positive
constants `c₁, c₂` and a threshold `N₀` with

`c₁ · (n log n) ≤ pₙ ≤ c₂ · (n log n)`  for all `n ≥ N₀`,

where `pₙ = Nat.nth Nat.Prime n`.

The constants come directly from the two `IsBigO` halves of the `Θ` statement
(`NthPrimeGrowth.nth_prime_isBigO` and `.nth_prime_isBigO_lower`), whose
`Asymptotics.isBigO_iff` form supplies a constant and (via
`Filter.eventually_atTop`) a threshold for each direction.  We take
`c₂ = |Ku| + 1`, `c₁ = 1 / (|Kl| + 1)` (padded so positivity is immediate) and
`N₀` the maximum of the two thresholds and `1` (so that `log n ≥ 0`, making the
`IsBigO` norms coincide with the values).
-/

open Asymptotics Filter Real

namespace NthPrimeExplicitBounds

/-- **Explicit two-sided bound on the `n`th prime.** There exist positive constants
`c₁, c₂` and a threshold `N₀` such that for all `n ≥ N₀`,
`c₁ · (n log n) ≤ pₙ ≤ c₂ · (n log n)`.  This is the explicit repackaging of
`NthPrimeGrowth.nth_prime_isTheta`. -/
theorem nth_prime_explicit_two_sided :
    ∃ c₁ c₂ : ℝ, ∃ N₀ : ℕ, 0 < c₁ ∧ 0 < c₂ ∧
      ∀ n : ℕ, N₀ ≤ n →
        c₁ * ((n : ℝ) * Real.log n) ≤ (Nat.nth Nat.Prime n : ℝ) ∧
        (Nat.nth Nat.Prime n : ℝ) ≤ c₂ * ((n : ℝ) * Real.log n) := by
  -- Extract the upper `IsBigO` constant and threshold.
  obtain ⟨Ku, hKu⟩ := Asymptotics.isBigO_iff.mp NthPrimeGrowth.nth_prime_isBigO
  obtain ⟨Nu, hNu⟩ := Filter.eventually_atTop.mp hKu
  -- Extract the lower `IsBigO` constant and threshold.
  obtain ⟨Kl, hKl⟩ := Asymptotics.isBigO_iff.mp NthPrimeGrowth.nth_prime_isBigO_lower
  obtain ⟨Nl, hNl⟩ := Filter.eventually_atTop.mp hKl
  refine ⟨1 / (|Kl| + 1), |Ku| + 1, max (max Nu Nl) 1, ?_, ?_, ?_⟩
  · positivity
  · positivity
  · intro n hn
    have hnNu : Nu ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
    have hnNl : Nl ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
    have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
    have hn1R : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
    have hlogn : 0 ≤ Real.log n := Real.log_nonneg hn1R
    have hnLnonneg : 0 ≤ (n : ℝ) * Real.log n := by positivity
    have hpnonneg : 0 ≤ (Nat.nth Nat.Prime n : ℝ) := Nat.cast_nonneg _
    -- Upper bound (norms collapse to values since both sides are nonnegative).
    have hu := hNu n hnNu
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hpnonneg,
        abs_of_nonneg hnLnonneg] at hu
    -- Lower bound.
    have hl := hNl n hnNl
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hnLnonneg,
        abs_of_nonneg hpnonneg] at hl
    refine ⟨?_, ?_⟩
    · -- `c₁ · (n log n) ≤ pₙ`, from `n log n ≤ Kl · pₙ ≤ (|Kl|+1) · pₙ`.
      have hA : (0 : ℝ) < |Kl| + 1 := by positivity
      have h1 : (n : ℝ) * Real.log n ≤ (|Kl| + 1) * (Nat.nth Nat.Prime n : ℝ) := by
        have hstep : Kl * (Nat.nth Nat.Prime n : ℝ)
            ≤ (|Kl| + 1) * (Nat.nth Nat.Prime n : ℝ) := by
          apply mul_le_mul_of_nonneg_right _ hpnonneg
          have := le_abs_self Kl; linarith
        linarith [hl, hstep]
      rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hA]
      linarith [h1, mul_comm (|Kl| + 1) (Nat.nth Nat.Prime n : ℝ)]
    · -- `pₙ ≤ c₂ · (n log n)`, from `pₙ ≤ Ku · (n log n) ≤ (|Ku|+1) · (n log n)`.
      have hstep : Ku * ((n : ℝ) * Real.log n)
          ≤ (|Ku| + 1) * ((n : ℝ) * Real.log n) := by
        apply mul_le_mul_of_nonneg_right _ hnLnonneg
        have := le_abs_self Ku; linarith
      linarith [hu, hstep]

end NthPrimeExplicitBounds
