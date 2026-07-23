import Propositio.NumberTheory.Diophantine.DiagonalIntegralLog2TwoAdic
import Mathlib.Tactic

/-!
# Coefficient bound `|cₖ| ≤ 6ⁿ` for the diagonal `log 2` integral

`cₖ = coeff k ((X−1)ⁿ(2−X)ⁿ) ∈ ℤ`.  Each coefficient is dominated in absolute value by the
corresponding coefficient of the **nonnegative-coefficient** polynomial `(X+1)ⁿ(X+2)ⁿ`
(termwise, via the convolution triangle inequality and `|(X−1)ⁿ.coeff i| = (X+1)ⁿ.coeff i`,
`|(2−X)ⁿ.coeff j| = (X+2)ⁿ.coeff j`), and a single nonnegative coefficient is at most the sum of
all of them, i.e. the evaluation at `1`: `(X+1)ⁿ(X+2)ⁿ` at `1` is `2ⁿ·3ⁿ = 6ⁿ`.

This is the denominator-bound input `aₙ = Dₙ·cₙ ≤ B·Qⁿ` for
`IrrMeasureCombination.irrationality_measure_le` (combined with `lcmUpto n ≤ (4e⁴)ⁿ`).
-/

namespace DiagonalIntegralLog2

open Polynomial

private theorem hC2 : (C (2 : ℤ) : ℤ[X]) = 2 := map_ofNat C 2

/-- `|((X−1)ⁿ).coeff i| = ((X+1)ⁿ).coeff i = C(n,i)`. -/
theorem abs_coeff_X_sub_one_pow (n i : ℕ) :
    |((X - 1 : ℤ[X]) ^ n).coeff i| = ((X + 1 : ℤ[X]) ^ n).coeff i := by
  have e1 : ((X - 1 : ℤ[X]) ^ n).coeff i = (-1) ^ (n - i) * (n.choose i : ℤ) := by
    rw [show (X - 1 : ℤ[X]) = X + C (-1) by rw [C_neg, C_1]; ring, coeff_X_add_C_pow]
  have e2 : ((X + 1 : ℤ[X]) ^ n).coeff i = (n.choose i : ℤ) := by
    rw [show (X + 1 : ℤ[X]) = X + C 1 by rw [C_1], coeff_X_add_C_pow]; simp
  rw [e1, e2, abs_mul, abs_pow]; norm_num

/-- `|((2−X)ⁿ).coeff j| = ((X+2)ⁿ).coeff j = 2^(n−j)·C(n,j)`. -/
theorem abs_coeff_two_sub_X_pow (n j : ℕ) :
    |((2 - X : ℤ[X]) ^ n).coeff j| = ((X + 2 : ℤ[X]) ^ n).coeff j := by
  have hpe : (2 - X : ℤ[X]) ^ n = (-1 : ℤ[X]) ^ n * (X - 2) ^ n := by
    rw [show (2 - X : ℤ[X]) = -(X - 2) by ring, neg_pow]
  have hxm2 : ((X - 2 : ℤ[X]) ^ n).coeff j = (-2) ^ (n - j) * (n.choose j : ℤ) := by
    rw [show (X - 2 : ℤ[X]) = X + C (-2) by rw [C_neg, hC2]; ring, coeff_X_add_C_pow]
  have hxp2 : ((X + 2 : ℤ[X]) ^ n).coeff j = 2 ^ (n - j) * (n.choose j : ℤ) := by
    rw [show (X + 2 : ℤ[X]) = X + C 2 by rw [hC2], coeff_X_add_C_pow]
  rw [hpe, hxp2]
  rcases Nat.even_or_odd n with he | ho
  · rw [he.neg_one_pow, one_mul, hxm2, abs_mul, abs_pow]; norm_num
  · rw [ho.neg_one_pow, neg_one_mul, coeff_neg, hxm2, abs_neg, abs_mul, abs_pow]; norm_num

/-- The dominating polynomial `(X+1)ⁿ(X+2)ⁿ` has nonnegative coefficients. -/
theorem coeff_dom_nonneg (n k : ℕ) :
    0 ≤ ((X + 1 : ℤ[X]) ^ n * (X + 2) ^ n).coeff k := by
  rw [coeff_mul]
  apply Finset.sum_nonneg
  rintro ⟨i, j⟩ _
  have hi : (0 : ℤ) ≤ ((X + 1 : ℤ[X]) ^ n).coeff i := by
    rw [show (X + 1 : ℤ[X]) = X + C 1 by rw [C_1], coeff_X_add_C_pow]; positivity
  have hj : (0 : ℤ) ≤ ((X + 2 : ℤ[X]) ^ n).coeff j := by
    rw [show (X + 2 : ℤ[X]) = X + C 2 by rw [hC2], coeff_X_add_C_pow]; positivity
  exact mul_nonneg hi hj

/-- **Termwise domination.**  `|cₖ| ≤ ((X+1)ⁿ(X+2)ⁿ).coeff k`. -/
theorem abs_coeff_le_dom (n k : ℕ) :
    |((X - 1 : ℤ[X]) ^ n * (2 - X) ^ n).coeff k|
      ≤ ((X + 1 : ℤ[X]) ^ n * (X + 2) ^ n).coeff k := by
  rw [coeff_mul, coeff_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  apply Finset.sum_le_sum
  rintro ⟨i, j⟩ _
  rw [abs_mul, abs_coeff_X_sub_one_pow, abs_coeff_two_sub_X_pow]

/-- **The coefficient bound `|cₖ| ≤ 6ⁿ`.** -/
theorem abs_coeff_le_six_pow (n k : ℕ) :
    |((X - 1 : ℤ[X]) ^ n * (2 - X) ^ n).coeff k| ≤ 6 ^ n := by
  refine (abs_coeff_le_dom n k).trans ?_
  set Q : ℤ[X] := (X + 1 : ℤ[X]) ^ n * (X + 2) ^ n with hQ
  have hdeg : Q.natDegree < Q.natDegree + 1 := Nat.lt_succ_self _
  have hcoeff_le : Q.coeff k ≤ ∑ i ∈ Finset.range (Q.natDegree + 1), Q.coeff i := by
    by_cases hk : k ≤ Q.natDegree
    · refine Finset.single_le_sum (f := fun i => Q.coeff i) (fun i _ => ?_)
        (Finset.mem_range.mpr (by omega))
      exact coeff_dom_nonneg n i
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
      exact Finset.sum_nonneg (fun i _ => coeff_dom_nonneg n i)
  have heval : ∑ i ∈ Finset.range (Q.natDegree + 1), Q.coeff i = Q.eval 1 := by
    rw [Polynomial.eval_eq_sum_range' hdeg]; simp
  have hval : Q.eval 1 = 6 ^ n := by
    rw [hQ]; simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_add,
      Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_ofNat]
    rw [← mul_pow]; norm_num
  exact hcoeff_le.trans (le_of_eq (heval.trans hval))

end DiagonalIntegralLog2
