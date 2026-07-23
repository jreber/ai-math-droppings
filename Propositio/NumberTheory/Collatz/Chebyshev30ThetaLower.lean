import Propositio.NumberTheory.Collatz.Chebyshev30M
import Mathlib.NumberTheory.Chebyshev

/-!
# Chebyshev-30: the `θ`-lower bound `θ(N) − θ(N/6) ≤ log M(N)`

The lower half of the per-step factorial inequality `hstep`.  `θ(N) − θ(⌊N/6⌋)` is the sum of
`log p` over primes `p ∈ (N/6, N]`; every such `p` divides `M(N)` (`prime_dvd_M`), hence appears in
`M(N)`'s factorization with multiplicity `≥ 1`, so `Σ_{N/6 < p ≤ N} log p ≤ Σ_p v_p(M)·log p =
log M(N)` (`Real.log_nat_eq_sum_factorization`).  Combined with the size bound `log M(N) ≤ A·N`
(B1's elementary `M(N) ≤ (2√2)^N`, queued) this discharges `hstep` for `theta_le_of_step`.
-/

namespace CollatzChebyshev30

open Chebyshev Finset

theorem theta_sub_le_logM (N : ℕ) :
    θ (N : ℝ) - θ ((N / 6 : ℕ) : ℝ) ≤ Real.log (M N) := by
  -- θ at a natural argument is the filtered-`Ioc` prime sum.
  have hθ : ∀ m : ℕ, θ (m : ℝ) = ∑ p ∈ (Finset.Ioc 0 m).filter Nat.Prime, Real.log (p : ℝ) := by
    intro m; rw [Chebyshev.theta, Nat.floor_natCast]
  have hsub : (Finset.Ioc 0 (N / 6)).filter Nat.Prime ⊆ (Finset.Ioc 0 N).filter Nat.Prime := by
    apply Finset.filter_subset_filter
    apply Finset.Ioc_subset_Ioc_right
    exact Nat.div_le_self N 6
  rw [hθ, hθ, ← Finset.sum_sdiff_eq_sub hsub]
  -- Each prime in the difference set divides `M N`, so it sits in the factorization support.
  set D := (Finset.Ioc 0 N).filter Nat.Prime \ (Finset.Ioc 0 (N / 6)).filter Nat.Prime with hD
  have hmem : ∀ p ∈ D, p.Prime ∧ p ≤ N ∧ N < 6 * p := by
    intro p hp
    rw [hD, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_filter, Finset.mem_Ioc,
        Finset.mem_Ioc] at hp
    obtain ⟨⟨⟨hp0, hpN⟩, hpp⟩, hnt⟩ := hp
    refine ⟨hpp, hpN, ?_⟩
    -- p ∉ Ioc 0 (N/6) ∧ prime ⇒ p > N/6 ⇒ N < 6p
    have hgt : N / 6 < p := by
      by_contra h
      exact hnt ⟨⟨hp0, by omega⟩, hpp⟩
    omega
  have hdvd : ∀ p ∈ D, p ∣ M N := fun p hp =>
    let ⟨hpp, hpN, hlt⟩ := hmem p hp; prime_dvd_M N p hpp hpN hlt
  -- `∑_{p ∈ D} log p ≤ ∑_{p ∈ D} v_p(M)·log p ≤ ∑_{support} v_p(M)·log p = log M`.
  rw [Real.log_nat_eq_sum_factorization, Finsupp.sum]
  have hstep1 : ∑ p ∈ D, Real.log (p : ℝ)
      ≤ ∑ p ∈ D, ((M N).factorization p : ℝ) * Real.log (p : ℝ) := by
    apply Finset.sum_le_sum
    intro p hp
    obtain ⟨hpp, _, _⟩ := hmem p hp
    have hv : 1 ≤ (M N).factorization p :=
      (Nat.Prime.dvd_iff_one_le_factorization hpp (M_pos N).ne').mp (hdvd p hp)
    have hlogp : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hpp.one_lt.le)
    nlinarith [hlogp, (by exact_mod_cast hv : (1 : ℝ) ≤ ((M N).factorization p : ℝ))]
  refine hstep1.trans ?_
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · -- D ⊆ factorization support
    intro p hp
    obtain ⟨hpp, _, _⟩ := hmem p hp
    rw [Nat.support_factorization, Nat.mem_primeFactors]
    exact ⟨hpp, hdvd p hp, (M_pos N).ne'⟩
  · intro p _ _
    have hlog : 0 ≤ Real.log (p : ℝ) := by
      rcases Nat.eq_zero_or_pos p with h | h
      · simp [h]
      · exact Real.log_nonneg (by exact_mod_cast h)
    positivity

end CollatzChebyshev30
