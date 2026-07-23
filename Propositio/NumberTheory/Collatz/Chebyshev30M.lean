import Propositio.NumberTheory.Collatz.Chebyshev30
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Data.Nat.Factorization.Basic

/-!
# Chebyshev-30: the integer `M(N)` (integrality of the factorial ratio)

The Chebyshev weight `χ ≥ 0` (`chiW_nonneg`) is exactly the statement that the factorial ratio
`M(N) = N!·(N/30)! / ((N/2)!·(N/3)!·(N/5)!)` is a genuine integer: for every prime `p`,
`v_p(M_den) ≤ v_p(M_num)` because, by Legendre, `v_p(M_num) − v_p(M_den) = Σ_k χ(⌊N/pᵏ⌋) ≥ 0`.

`M` is defined for **every** natural `N` (not just even ones): the telescoping `θ(x) ≤ θ(x/6) + A·x`
requires `hstep` at every `N = ⌊x⌋`, so the integer `M(N)` and the `θ`-lower bound must be general.

This file proves integrality (`M_den_dvd_M_num`, `M_pos`) and the `θ`-lower-bound gateway
`prime_dvd_M` (every prime in `(N/6, N]` divides `M(N)`).  The valuation *formula*, the assembled
`θ`-lower bound, and the Stirling upper bound (`stirling_M_bound`) are the remaining queued bricks.
-/

namespace CollatzChebyshev30

open Nat Finset

/-- Numerator of the Chebyshev-30 integer: `N! · (N/30)!`. -/
def M_num (N : ℕ) : ℕ := N ! * (N / 30)!

/-- Denominator of the Chebyshev-30 integer: `(N/2)! · (N/3)! · (N/5)!`. -/
def M_den (N : ℕ) : ℕ := (N / 2)! * (N / 3)! * (N / 5)!

lemma M_num_pos (N : ℕ) : 0 < M_num N := by unfold M_num; positivity
lemma M_den_pos (N : ℕ) : 0 < M_den N := by unfold M_den; positivity

/-- **Pointwise valuation comparison** `v_p(M_den) ≤ v_p(M_num)` for every prime `p`, the core of
integrality.  Each factorial's `p`-valuation is its Legendre sum `∑_k ⌊·/pᵏ⌋`; the nested-floor
identity collapses every term to `⌊N/pᵏ⌋` divided by `2,3,5,30`, and `χ ≥ 0` (`chiW_nonneg`) gives
the per-term inequality `m/2 + m/3 + m/5 ≤ m + m/30`. -/
theorem factorization_M_den_le_M_num (N p : ℕ) (hp : p.Prime) :
    (M_den N).factorization p ≤ (M_num N).factorization p := by
  set b := Nat.log p N + 1 with hb_def
  have hb_num : Nat.log p N < b := Nat.lt_succ_self _
  have hub : ∀ d : ℕ, Nat.log p (N / d) < b := fun d =>
    Nat.lt_succ_of_le (Nat.log_mono_right (Nat.div_le_self _ _))
  have nest : ∀ d k : ℕ, N / d / p ^ k = N / p ^ k / d := fun d k => by
    rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, Nat.mul_comm d (p ^ k)]
  have hMnum : (M_num N).factorization p
      = ∑ k ∈ Ico 1 b, N / p ^ k / 1 + ∑ k ∈ Ico 1 b, N / p ^ k / 30 := by
    unfold M_num
    rw [Nat.factorization_mul (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _),
        Finsupp.add_apply, Nat.factorization_factorial hp hb_num,
        Nat.factorization_factorial hp (hub 30)]
    simp_rw [nest, Nat.div_one]
  have hMden : (M_den N).factorization p
      = ∑ k ∈ Ico 1 b, N / p ^ k / 2 + ∑ k ∈ Ico 1 b, N / p ^ k / 3
        + ∑ k ∈ Ico 1 b, N / p ^ k / 5 := by
    unfold M_den
    rw [Nat.factorization_mul
          (mul_ne_zero (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _))
          (Nat.factorial_ne_zero _),
        Finsupp.add_apply,
        Nat.factorization_mul (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _),
        Finsupp.add_apply,
        Nat.factorization_factorial hp (hub 2),
        Nat.factorization_factorial hp (hub 3),
        Nat.factorization_factorial hp (hub 5)]
    simp_rw [nest]
  rw [hMnum, hMden, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro k _
  have h := chiW_nonneg (N / p ^ k)
  unfold chiW at h
  omega

/-- **`M_den ∣ M_num`** — the factorial ratio is a genuine integer. -/
theorem M_den_dvd_M_num (N : ℕ) : M_den N ∣ M_num N := by
  rw [← Nat.factorization_le_iff_dvd (M_den_pos N).ne' (M_num_pos N).ne']
  intro p
  by_cases hp : p.Prime
  · exact factorization_M_den_le_M_num N p hp
  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]

/-- The Chebyshev-30 integer `M(N) = N!·(N/30)! / ((N/2)!·(N/3)!·(N/5)!)`. -/
def M (N : ℕ) : ℕ := M_num N / M_den N

/-- `M(N) > 0`. -/
theorem M_pos (N : ℕ) : 0 < M N :=
  Nat.div_pos (Nat.le_of_dvd (M_num_pos N) (M_den_dvd_M_num N)) (M_den_pos N)

/-- `M(N) · M_den = M_num` (the ratio is exact, no truncation). -/
theorem M_mul_den (N : ℕ) : M N * M_den N = M_num N :=
  Nat.div_mul_cancel (M_den_dvd_M_num N)

/-- **Every prime `p ∈ (N/6, N]` divides `M(N)`.**  Such `p` has `⌊N/p⌋ ∈ {1,…,5}`, so the
`k = 1` Legendre term contributes `χ(⌊N/p⌋) = 1` to `v_p(M_num) − v_p(M_den)` (others `≥ 0`),
forcing `v_p(M) ≥ 1`.  This is the engine of the `θ(x) − θ(x/6) ≤ log M(x)` lower bound. -/
theorem prime_dvd_M (N p : ℕ) (hp : p.Prime) (hhi : p ≤ N) (hlo : N < 6 * p) :
    p ∣ M N := by
  have hppos : 0 < p := hp.pos
  have hm1lo : 1 ≤ N / p := Nat.div_pos hhi hppos
  have hm1hi : N / p ≤ 5 := by
    have h6 : N / p < 6 := (Nat.div_lt_iff_lt_mul hppos).mpr (by omega)
    omega
  have hstrict : (M_den N).factorization p < (M_num N).factorization p := by
    set b := Nat.log p N + 1 with hb_def
    have hb_num : Nat.log p N < b := Nat.lt_succ_self _
    have hub : ∀ d : ℕ, Nat.log p (N / d) < b := fun d =>
      Nat.lt_succ_of_le (Nat.log_mono_right (Nat.div_le_self _ _))
    have nest : ∀ d k : ℕ, N / d / p ^ k = N / p ^ k / d := fun d k => by
      rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, Nat.mul_comm d (p ^ k)]
    have hMnum : (M_num N).factorization p
        = ∑ k ∈ Finset.Ico 1 b, (N / p ^ k + N / p ^ k / 30) := by
      unfold M_num
      rw [Nat.factorization_mul (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _),
          Finsupp.add_apply, Nat.factorization_factorial hp hb_num,
          Nat.factorization_factorial hp (hub 30), Finset.sum_add_distrib]
      simp_rw [nest]
    have hMden : (M_den N).factorization p
        = ∑ k ∈ Finset.Ico 1 b, (N / p ^ k / 2 + N / p ^ k / 3 + N / p ^ k / 5) := by
      unfold M_den
      rw [Nat.factorization_mul
            (mul_ne_zero (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _))
            (Nat.factorial_ne_zero _),
          Finsupp.add_apply,
          Nat.factorization_mul (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _),
          Finsupp.add_apply,
          Nat.factorization_factorial hp (hub 2),
          Nat.factorization_factorial hp (hub 3),
          Nat.factorization_factorial hp (hub 5),
          Finset.sum_add_distrib, Finset.sum_add_distrib]
      simp_rw [nest]
    rw [hMnum, hMden]
    apply Finset.sum_lt_sum
    · intro k _; omega
    · refine ⟨1, ?_, ?_⟩
      · simp only [Finset.mem_Ico]
        exact ⟨le_refl 1, by have := Nat.log_pos hp.one_lt hhi; omega⟩
      · simp only [pow_one]; omega
  have hfact : 0 < (M N).factorization p := by
    rw [M, Nat.factorization_div (M_den_dvd_M_num N), Finsupp.tsub_apply]
    omega
  exact (Nat.Prime.dvd_iff_one_le_factorization hp (M_pos N).ne').mpr hfact

end CollatzChebyshev30
