import Propositio.Collatz.Chebyshev30M
-- No other imports needed: CollatzChebyshev30M already pulls in
-- Mathlib.Data.Nat.Choose.Factorization and Mathlib.Data.Nat.Factorization.Basic.

/-!
# p-adic valuation formula for M(N)

This file proves the exact Legendre–chiW formula for `v_p(M(N))`:

  `v_p(M(N)) = ∑_{k=1}^{⌊log_p N⌋} χ(⌊N/pᵏ⌋)`

and the logarithmic upper bound `v_p(M(N)) ≤ ⌊log_p N⌋`.

The proof reuses the same Legendre-sum computations as
`factorization_M_den_le_M_num` in `CollatzChebyshev30M`, now assembled
pointwise in ℤ using the identity

  `v_p(M_num) - v_p(M_den) = ∑_k χ(⌊N/pᵏ⌋)`.
-/

namespace CollatzChebyshev30

open Nat Finset

/-- **p-adic valuation formula for M(N)** (exact Legendre–chiW identity).

Every prime `p` and every natural `N` satisfy
`v_p(M(N)) = ∑_{k=1}^{⌊log_p N⌋} χ(⌊N/pᵏ⌋)`. -/
theorem padicValNat_M (N p : ℕ) (hp : p.Prime) :
    ((M N).factorization p : ℤ) = ∑ k ∈ Finset.Ico 1 (Nat.log p N + 1), chiW (N / p ^ k) := by
  set b := Nat.log p N + 1 with hb_def
  have hb_num : Nat.log p N < b := Nat.lt_succ_self _
  have hub : ∀ d : ℕ, Nat.log p (N / d) < b := fun d =>
    Nat.lt_succ_of_le (Nat.log_mono_right (Nat.div_le_self _ _))
  have nest : ∀ d k : ℕ, N / d / p ^ k = N / p ^ k / d := fun d k => by
    rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, Nat.mul_comm d (p ^ k)]
  -- Compute factorization of M_num at p
  have hMnum : (M_num N).factorization p
      = ∑ k ∈ Finset.Ico 1 b, (N / p ^ k + N / p ^ k / 30) := by
    unfold M_num
    rw [Nat.factorization_mul (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _),
        Finsupp.add_apply, Nat.factorization_factorial hp hb_num,
        Nat.factorization_factorial hp (hub 30), Finset.sum_add_distrib]
    simp_rw [nest]
  -- Compute factorization of M_den at p
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
  -- From M N * M_den N = M_num N, extract the factorization addition identity
  have hfact : (M N).factorization p + (M_den N).factorization p =
      (M_num N).factorization p := by
    have heq : (M N * M_den N).factorization p = (M_num N).factorization p := by
      rw [M_mul_den]
    rw [Nat.factorization_mul (M_pos N).ne' (M_den_pos N).ne', Finsupp.add_apply] at heq
    exact heq
  -- Cast to ℤ: (M N).factorization p = (M_num N).factorization p - (M_den N).factorization p
  have hM_int : ((M N).factorization p : ℤ) =
      ((M_num N).factorization p : ℤ) - ((M_den N).factorization p : ℤ) := by
    omega
  -- Substitute and simplify pointwise
  rw [hM_int, hMnum, hMden]
  push_cast
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  unfold chiW
  push_cast
  ring

/-- **Factorization logarithmic upper bound**: `v_p(M(N)) ≤ ⌊log_p N⌋`.

Since `χ ≤ 1` everywhere and the sum has `⌊log_p N⌋` terms. -/
theorem factorization_M_le_log (N p : ℕ) (hp : p.Prime) :
    (M N).factorization p ≤ Nat.log p N := by
  -- Suffices to show the inequality in ℤ (avoid cast issues)
  suffices h : ((M N).factorization p : ℤ) ≤ (Nat.log p N : ℤ) by exact_mod_cast h
  rw [padicValNat_M N p hp]
  -- Each χ(⌊N/pᵏ⌋) ≤ 1, so the sum is ≤ the number of terms
  have h1 : ∑ k ∈ Finset.Ico 1 (Nat.log p N + 1), chiW (N / p ^ k)
            ≤ ∑ k ∈ Finset.Ico 1 (Nat.log p N + 1), (1 : ℤ) :=
    Finset.sum_le_sum (fun k _ => chiW_le_one _)
  -- The sum of 1s equals the cardinality, which is Nat.log p N
  have h2 : ∑ k ∈ Finset.Ico 1 (Nat.log p N + 1), (1 : ℤ) = (Nat.log p N : ℤ) := by
    have hc : (Finset.Ico 1 (Nat.log p N + 1)).card = Nat.log p N := by
      simp [Nat.card_Ico]
    rw [Finset.sum_const, hc]
    simp
  linarith

#print axioms padicValNat_M

end CollatzChebyshev30
