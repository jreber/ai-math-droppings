import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Propositio.NumberTheory.Analytic.MertensReciprocalUpper
import Propositio.NumberTheory.Analytic.MertensReciprocalLower

/-!
# Average order of `ω(n)`: `Σ_{n ≤ N} ω(n) = N·log log N + O(N)`

`ω(n)` (mathlib `n.primeFactors.card`) counts the **distinct** prime divisors of `n`.
This file fills a mathlib gap by proving its summatory function has the classical
asymptotic with leading term `N·log log N` and a two-sided `O(N)` error, using our
two-sided Mertens' second theorem (`MertensReciprocalUpper.sum_reciprocal_primes_le`
together with `MertensReciprocalLower.key`, both with leading constant `1`).

## Proof outline

1. **Dirichlet hyperbola / order swap (`sum_omega_eq_sum_floor`).**
   `ω(n) = Σ_{p ∣ n, p prime} 1`, so summing over `n ≤ N` and swapping the order of
   summation gives `Σ_{n ≤ N} ω(n) = Σ_{p ≤ N} #{n ∈ [1,N] : p ∣ n} = Σ_{p ≤ N} ⌊N/p⌋`.
   The inner count is `Nat.Ioc_filter_dvd_card_eq_div` ( `= N / p` ).

2. **Floor → reciprocal.**  `0 ≤ N/p − ⌊N/p⌋ ≤ 1`, and there are `≤ N` primes in `[1,N]`,
   so `|Σ_{p ≤ N} ⌊N/p⌋ − N·Σ_{p ≤ N} 1/p| ≤ N`.

3. **Mertens' second (two-sided).**  `|Σ_{p ≤ N} 1/p − log log N| ≤ max C₁ 1` for `N` large,
   hence `|N·Σ 1/p − N·log log N| ≤ N·max C₁ 1`.

Combining, `|Σ_{n ≤ N} ω(n) − N·log log N| ≤ (1 + max C₁ 1)·N`.
-/

open Real Finset

namespace OmegaSummatory

/-- The prime index set `[1,N]` filtered to primes equals the `range (N+1)` version used by
the Mertens lemmas (the only difference, `0`, is not prime). -/
theorem primeFilter_Icc_eq_range (N : ℕ) :
    (Finset.Icc 1 N).filter Nat.Prime = (Finset.range (N + 1)).filter Nat.Prime := by
  ext p
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_range]
  constructor
  · rintro ⟨⟨_, hpN⟩, hp⟩; exact ⟨by omega, hp⟩
  · rintro ⟨hpN, hp⟩; exact ⟨⟨hp.one_lt.le, by omega⟩, hp⟩

/-- **The order-swap identity.**  `Σ_{n=1}^{N} ω(n) = Σ_{p ≤ N, p prime} ⌊N/p⌋`.
Reusable: this is the Dirichlet-hyperbola swap `Σ_n Σ_{p ∣ n} = Σ_p Σ_{p ∣ n}`. -/
theorem sum_omega_eq_sum_floor (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, n.primeFactors.card
      = ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, N / p := by
  -- Write `ω(n)` as a sum of ones over its prime factors.
  have hcard : ∀ n ∈ Finset.Icc 1 N,
      n.primeFactors.card = ∑ _p ∈ n.primeFactors, 1 :=
    fun n _ => Finset.card_eq_sum_ones _
  rw [Finset.sum_congr rfl hcard]
  -- Swap the order of summation.
  rw [Finset.sum_comm' (t' := (Finset.Icc 1 N).filter Nat.Prime)
        (s' := fun p => (Finset.Icc 1 N).filter (fun n => p ∣ n))
        (f := fun _ _ => 1)
        (h := by
          intro n p
          simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_primeFactors]
          constructor
          · rintro ⟨⟨h1, hN⟩, hp, hdvd, _⟩
            exact ⟨⟨⟨h1, hN⟩, hdvd⟩, ⟨hp.one_lt.le, le_trans (Nat.le_of_dvd (by omega) hdvd) hN⟩, hp⟩
          · rintro ⟨⟨⟨h1, hN⟩, hdvd⟩, _, hp⟩
            exact ⟨⟨h1, hN⟩, hp, hdvd, by omega⟩)]
  -- Each inner sum is the count of multiples of `p` in `[1,N]`, namely `N / p`.
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [← Finset.card_eq_sum_ones]
  have hIoc : Finset.Icc 1 N = Finset.Ioc 0 N := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  rw [hIoc]
  exact Nat.Ioc_filter_dvd_card_eq_div N p

/-- **Average order of `ω`.**  There is a constant `C` and threshold `N₀` such that for all
`N ≥ N₀`, `|Σ_{n=1}^{N} ω(n) − N·log log N| ≤ C·N`.  Leading term exactly `N·log log N`,
two-sided error `O(N)`. -/
theorem omega_summatory_asymptotic :
    ∃ C : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      |(∑ n ∈ Finset.Icc 1 N, (n.primeFactors.card : ℝ))
          - N * Real.log (Real.log N)| ≤ C * N := by
  obtain ⟨C₁, N₁, hUp⟩ := MertensReciprocalUpper.sum_reciprocal_primes_le
  refine ⟨1 + max C₁ 1, max N₁ 3, ?_⟩
  intro N hN
  have hN1 : N₁ ≤ N := le_trans (le_max_left _ _) hN
  have hN3 : 3 ≤ N := le_trans (le_max_right _ _) hN
  set Sset := (Finset.Icc 1 N).filter Nat.Prime with hSset
  -- The two reciprocal/floor sums.
  set M : ℝ := ∑ p ∈ Sset, (1 : ℝ) / p with hM
  set T : ℝ := ∑ p ∈ Sset, ((N / p : ℕ) : ℝ) with hT
  -- `Σ ω(n)` equals the floor sum `T` (cast of the order-swap identity).
  have hST : (∑ n ∈ Finset.Icc 1 N, (n.primeFactors.card : ℝ)) = T := by
    rw [hT]
    rw [show (∑ n ∈ Finset.Icc 1 N, (n.primeFactors.card : ℝ))
          = ((∑ n ∈ Finset.Icc 1 N, n.primeFactors.card : ℕ) : ℝ) from by push_cast; rfl]
    rw [sum_omega_eq_sum_floor N]
    push_cast
    rfl
  -- Bridge `Sset` to the `range (N+1)` index set used by Mertens.
  have hbridge : Sset = (Finset.range (N + 1)).filter Nat.Prime := primeFilter_Icc_eq_range N
  -- Per-prime fractional part bounds: `0 ≤ N/p − ⌊N/p⌋ ≤ 1`.
  have hfrac0 : ∀ p ∈ Sset, 0 ≤ (N : ℝ) / p - ((N / p : ℕ) : ℝ) := by
    intro p _
    have := (Nat.cast_div_le (α := ℝ) (m := N) (n := p))
    linarith
  have hfrac1 : ∀ p ∈ Sset, (N : ℝ) / p - ((N / p : ℕ) : ℝ) ≤ 1 := by
    intro p hp
    rw [hSset, Finset.mem_filter] at hp
    have hpp : p.Prime := hp.2
    have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpp.pos
    have hdmR : (p : ℝ) * ((N / p : ℕ) : ℝ) + ((N % p : ℕ) : ℝ) = (N : ℝ) := by
      exact_mod_cast Nat.div_add_mod N p
    have hmodR : ((N % p : ℕ) : ℝ) < (p : ℝ) := by exact_mod_cast Nat.mod_lt N hpp.pos
    have hgoal : (N : ℝ) / p ≤ ((N / p : ℕ) : ℝ) + 1 := by
      rw [div_le_iff₀ hp0]
      nlinarith [hdmR, hmodR]
    linarith
  -- Number of primes in `[1,N]` is `≤ N`.
  have hScard : Sset.card ≤ N := by
    calc Sset.card ≤ (Finset.Icc 1 N).card := Finset.card_filter_le _ _
      _ = N := by rw [Nat.card_Icc]; omega
  -- Step 2: `|T − N·M| ≤ N`.
  have hAdiff : |T - (N : ℝ) * M| ≤ (N : ℝ) := by
    have heq : (N : ℝ) * M - T = ∑ p ∈ Sset, ((N : ℝ) / p - ((N / p : ℕ) : ℝ)) := by
      rw [hM, hT, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun p _ => by rw [mul_one_div])
    have hnonneg : 0 ≤ (N : ℝ) * M - T := by
      rw [heq]; exact Finset.sum_nonneg hfrac0
    have hle : (N : ℝ) * M - T ≤ (N : ℝ) := by
      rw [heq]
      calc ∑ p ∈ Sset, ((N : ℝ) / p - ((N / p : ℕ) : ℝ))
          ≤ ∑ _p ∈ Sset, (1 : ℝ) := Finset.sum_le_sum hfrac1
        _ = (Sset.card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
        _ ≤ (N : ℝ) := by exact_mod_cast hScard
    rw [abs_sub_comm, abs_of_nonneg hnonneg]
    exact hle
  -- Step 3: two-sided Mertens, `|M − log log N| ≤ max C₁ 1`.
  have hMup : M ≤ Real.log (Real.log N) + C₁ := by
    have h := hUp N hN1
    rw [hM, hbridge]; exact h
  have hMlow : Real.log (Real.log N) - 1 ≤ M := by
    have hk := MertensReciprocalLower.key N hN3
    rw [show (N + 1).primesBelow = (Finset.range (N + 1)).filter Nat.Prime from rfl] at hk
    have hconv : ∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime, ((p : ℝ))⁻¹ = M := by
      rw [hM, hbridge]
      exact Finset.sum_congr rfl (fun p _ => by rw [one_div])
    rwa [hconv] at hk
  have hMabs : |M - Real.log (Real.log N)| ≤ max C₁ 1 := by
    rw [abs_le]
    exact ⟨by linarith [hMlow, le_max_right C₁ 1], by linarith [hMup, le_max_left C₁ 1]⟩
  -- Combine.
  have hNnonneg : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hMterm : |(N : ℝ) * M - (N : ℝ) * Real.log (Real.log N)| ≤ (N : ℝ) * max C₁ 1 := by
    rw [← mul_sub, abs_mul, abs_of_nonneg hNnonneg]
    exact mul_le_mul_of_nonneg_left hMabs hNnonneg
  calc |(∑ n ∈ Finset.Icc 1 N, (n.primeFactors.card : ℝ))
          - (N : ℝ) * Real.log (Real.log N)|
      = |(T - (N : ℝ) * M) + ((N : ℝ) * M - (N : ℝ) * Real.log (Real.log N))| := by
        rw [hST]; congr 1; ring
    _ ≤ |T - (N : ℝ) * M| + |(N : ℝ) * M - (N : ℝ) * Real.log (Real.log N)| := abs_add_le _ _
    _ ≤ (N : ℝ) + (N : ℝ) * max C₁ 1 := by linarith [hAdiff, hMterm]
    _ = (1 + max C₁ 1) * (N : ℝ) := by ring

end OmegaSummatory
