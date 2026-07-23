/-
Zsygmondy cyclotomic gearbox brick.

Homogeneous cyclotomic factorization evaluated at an integer point:
for `n ≥ 1` and integer `a`,

  ∏_{d ∣ n} (cyclotomic d ℤ).eval a = a ^ n - 1.

This is `Polynomial.prod_cyclotomic_eq_X_pow_sub_one` (the polynomial identity
`∏ d ∈ n.divisors, cyclotomic d R = X ^ n - 1`) pushed through `Polynomial.eval a`,
which is a ring homomorphism.
-/
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic

open Polynomial

theorem prod_eval_cyclotomic_eq (n : ℕ) (hn : 0 < n) (a : ℤ) :
    ∏ d ∈ n.divisors, (Polynomial.cyclotomic d ℤ).eval a = a ^ n - 1 := by
  have hpoly : ∏ d ∈ n.divisors, Polynomial.cyclotomic d ℤ = X ^ n - 1 :=
    Polynomial.prod_cyclotomic_eq_X_pow_sub_one hn ℤ
  have := congrArg (Polynomial.eval a) hpoly
  simpa [Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_one] using this
