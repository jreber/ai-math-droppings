import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Prime.Factorial

/-!
# A Mertens-type lower bound `Σ_{p ≤ n} (log p)/p ≥ c·log n`

This file proves a one-sided (lower) version of Mertens' first theorem.  Mathlib has no
Mertens-type estimate for `Σ_{p ≤ x} (log p)/p`, so this is a genuine gap-filling result.

Mertens' first theorem states `Σ_{p ≤ x} (log p)/p = log x + O(1)`; here we prove the lower
half with an explicit constant:

`mertensSum n = Σ_{p ≤ n, p prime} (log p)/p ≥ (1/4)·log n`  for all `n ≥ 8`.

## Proof outline (the classical `log(n!)` two-ways argument)

1. **Factorization identity.**  `log(n!) = Σ_p v_p(n!)·log p` over the prime support of `n!`
   (`Real.log_nat_eq_sum_factorization`).
2. **Legendre upper bound.**  `v_p(n!) ≤ n/(p-1)` (mathlib
   `Nat.factorization_factorial_le_div_pred`).  In the multiplicative form
   `v_p(n!)·(p-1) ≤ n`, this gives `v_p(n!)·log p ≤ 2n·(log p / p)` termwise, hence
   `log(n!) ≤ 2n·mertensSum n` (`log_factorial_le_two_mul_mertens`).
3. **Stirling lower bound.**  `n·log n − n ≤ log(n!)` (from mathlib
   `Stirling.le_log_factorial_stirling`, dropping the nonnegative `½log n` and `½log(2π)` tails).
4. **Combine.**  `n·log n − n ≤ 2n·mertensSum n`, so `mertensSum n ≥ (log n − 1)/2`, which is
   `≥ (1/4)·log n` once `log n ≥ 2`, i.e. for `n ≥ 8` (since `e² < 8`).
-/

open Real Finset

namespace MertensLogPrimeLower

/-- The Mertens prime sum `Σ_{p ≤ n, p prime} (log p)/p`. -/
noncomputable def mertensSum (n : ℕ) : ℝ :=
  ∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime, Real.log p / p

/-- The prime support of `n!` is contained in the primes `≤ n` (in fact equal). -/
lemma support_subset (n : ℕ) :
    (Nat.factorial n).factorization.support ⊆ (Finset.range (n + 1)).filter Nat.Prime := by
  intro p hp
  rw [Nat.support_factorization, Nat.mem_primeFactors] at hp
  obtain ⟨hpp, hdvd, _⟩ := hp
  rw [Finset.mem_filter, Finset.mem_range]
  have hpn : p ≤ n := (Nat.Prime.dvd_factorial hpp).mp hdvd
  exact ⟨by omega, hpp⟩

/-- Termwise Legendre bound: for a prime `p`,
`v_p(n!)·log p ≤ 2n·(log p / p)`.  The crux is `v_p(n!)·(p-1) ≤ n`. -/
lemma term_bound (n p : ℕ) (hpp : p.Prime) :
    (((Nat.factorial n).factorization p : ℝ)) * Real.log p
      ≤ 2 * (n : ℝ) * (Real.log p / p) := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
  have hppos : (0 : ℝ) < (p : ℝ) := by linarith
  have hlogp : 0 ≤ Real.log p := Real.log_nonneg (by linarith)
  -- `v_p(n!) ≤ n/(p-1)` in `ℕ`, multiplicative form `v_p(n!)·(p-1) ≤ n`.
  have hvp_nat : (Nat.factorial n).factorization p ≤ n / (p - 1) :=
    Nat.factorization_factorial_le_div_pred hpp n
  have hp1pos : 0 < p - 1 := by have := hpp.two_le; omega
  have hmul_nat : (Nat.factorial n).factorization p * (p - 1) ≤ n :=
    (Nat.le_div_iff_mul_le hp1pos).mp hvp_nat
  -- cast to `ℝ` (division-free): `v_p(n!)·(p-1) ≤ n`.
  have hvpnn : (0 : ℝ) ≤ ((Nat.factorial n).factorization p : ℝ) := by positivity
  have hcast : ((Nat.factorial n).factorization p : ℝ) * ((p : ℝ) - 1) ≤ (n : ℝ) := by
    have : (((Nat.factorial n).factorization p * (p - 1) : ℕ) : ℝ) ≤ ((n : ℕ) : ℝ) := by
      exact_mod_cast hmul_nat
    rw [Nat.cast_mul, Nat.cast_sub hpp.one_lt.le, Nat.cast_one] at this
    linarith [this]
  -- `v_p(n!)·p ≤ 2n`.
  have hvpp : ((Nat.factorial n).factorization p : ℝ) * (p : ℝ) ≤ 2 * (n : ℝ) := by
    nlinarith [hcast, hvpnn, hp2,
      mul_nonneg hvpnn (by linarith : (0 : ℝ) ≤ (p : ℝ) - 2)]
  -- conclude termwise, clearing the `/p`.
  rw [show 2 * (n : ℝ) * (Real.log p / p) = (2 * (n : ℝ) * Real.log p) / p by ring,
      le_div_iff₀ hppos]
  nlinarith [mul_le_mul_of_nonneg_right hvpp hlogp, hlogp]

/-- **Upper bound via Legendre:** `log(n!) ≤ 2n·mertensSum n`. -/
theorem log_factorial_le_two_mul_mertens (n : ℕ) :
    Real.log (Nat.factorial n) ≤ 2 * (n : ℝ) * mertensSum n := by
  rw [Real.log_nat_eq_sum_factorization, Finsupp.sum]
  unfold mertensSum
  rw [Finset.mul_sum]
  calc
    ∑ p ∈ (Nat.factorial n).factorization.support,
        ((Nat.factorial n).factorization p : ℝ) * Real.log p
        ≤ ∑ p ∈ (Nat.factorial n).factorization.support,
            2 * (n : ℝ) * (Real.log p / p) := by
          apply Finset.sum_le_sum
          intro p hp
          rw [Nat.support_factorization, Nat.mem_primeFactors] at hp
          exact term_bound n p hp.1
    _ ≤ ∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime,
            2 * (n : ℝ) * (Real.log p / p) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (support_subset n)
          intro p hp _
          rw [Finset.mem_filter] at hp
          have hpp : p.Prime := hp.2
          have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpp.pos
          have hlogp : 0 ≤ Real.log p :=
            Real.log_nonneg (by exact_mod_cast hpp.one_lt.le)
          have : 0 ≤ Real.log p / p := div_nonneg hlogp (le_of_lt hppos)
          positivity

/-- **Mertens-type lower bound.**  There is a positive constant `c` (here `1/4`) and a
threshold `N` (here `8`) such that `Σ_{p ≤ n} (log p)/p ≥ c·log n` for all `n ≥ N`. -/
theorem mertensSum_ge :
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → c * Real.log n ≤ mertensSum n := by
  refine ⟨1 / 4, by norm_num, 8, ?_⟩
  intro n hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    have : (8 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  -- Stirling lower bound and our Legendre upper bound.
  have hstir := Stirling.le_log_factorial_stirling (show n ≠ 0 by omega)
  have hupper := log_factorial_le_two_mul_mertens n
  -- `log n ≥ 2` because `e² < 8 ≤ n`.
  have hlogn2 : 2 ≤ Real.log n := by
    have hexp2 : Real.exp 2 ≤ 8 := by
      have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
        rw [← Real.exp_add]; norm_num
      have he := Real.exp_one_lt_d9
      have hp := Real.exp_pos 1
      nlinarith [he, hp]
    have h8n : (8 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    rw [Real.le_log_iff_exp_le hnpos]
    linarith
  have hlognpos : 0 ≤ Real.log n := by linarith
  -- `log(2π)/2 ≥ 0`.
  have hlog2pi : 0 ≤ Real.log (2 * Real.pi) / 2 := by
    apply div_nonneg _ (by norm_num)
    apply Real.log_nonneg
    nlinarith [Real.pi_gt_three]
  -- drop the nonnegative Stirling tails: `n·log n − n ≤ 2n·mertensSum n`.
  have hkey : (n : ℝ) * Real.log n - (n : ℝ) ≤ 2 * (n : ℝ) * mertensSum n := by
    have hchain := le_trans hstir hupper
    linarith [hlognpos, hlog2pi, hchain]
  -- conclude `mertensSum n ≥ (1/4)·log n`.
  nlinarith [hkey, hnpos, hlogn2,
    mul_nonneg hnpos.le (sub_nonneg.mpr hlogn2)]

end MertensLogPrimeLower
