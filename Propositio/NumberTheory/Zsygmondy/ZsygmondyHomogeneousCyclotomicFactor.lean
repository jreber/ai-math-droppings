/-
Zsygmondy homogeneous cyclotomic gearbox brick (two-variable generalization).

Homogeneous two-variable cyclotomic factorization, integer-clean, no division:

  `Phi n a b := MvPolynomial.eval ![a, b]
    ((Polynomial.cyclotomic n ℤ).homogenize (Polynomial.cyclotomic n ℤ).natDegree)`

Then for `n ≥ 1`:

  `a ^ n - b ^ n = ∏ d ∈ n.divisors, Phi d a b`.

This is the exact two-variable generalization of the existing `b = 1` brick
`ZsygmondyCyclotomicFactor.prod_eval_cyclotomic_eq`, obtained by pushing the
polynomial identity `∏ d ∈ n.divisors, cyclotomic d ℤ = X ^ n - 1`
(`Polynomial.prod_cyclotomic_eq_X_pow_sub_one`) through `Polynomial.homogenize`
(`Mathlib/Algebra/Polynomial/Homogenize.lean`) and then evaluating at `(a, b)`.
-/
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.Algebra.Polynomial.Homogenize

open Polynomial

namespace ZsygmondyHomogeneousCyclotomicFactor

/-- The homogeneous bivariate cyclotomic factor evaluated at `(a, b)`. -/
noncomputable def Phi (n : ℕ) (a b : ℤ) : ℤ :=
  MvPolynomial.eval ![a, b]
    ((Polynomial.cyclotomic n ℤ).homogenize (Polynomial.cyclotomic n ℤ).natDegree)

/-- The exponent sum over the natural degrees of the cyclotomic factors of `n`
equals `n` itself (since `natDegree (cyclotomic d ℤ) = totient d` and
`∑ d ∈ n.divisors, totient d = n`). -/
private lemma sum_natDegree_cyclotomic (n : ℕ) :
    ∑ d ∈ n.divisors, (Polynomial.cyclotomic d ℤ).natDegree = n := by
  simp_rw [Polynomial.natDegree_cyclotomic]
  exact Nat.sum_totient n

/-- The polynomial-level homogeneous factorization: homogenizing
`∏ d ∈ n.divisors, cyclotomic d ℤ = X ^ n - 1` at degree `n` gives
`X 0 ^ n - X 1 ^ n` on one side and `∏ d ∈ n.divisors, homogenize (cyclotomic d ℤ) (natDegree ..)`
on the other. -/
private lemma homogenize_prod_cyclotomic (n : ℕ) (hn : 0 < n) :
    (MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) ℤ) ^ n - MvPolynomial.X 1 ^ n =
      ∏ d ∈ n.divisors, (Polynomial.cyclotomic d ℤ).homogenize (Polynomial.cyclotomic d ℤ).natDegree := by
  have h1 : ∏ d ∈ n.divisors, Polynomial.cyclotomic d ℤ = X ^ n - 1 :=
    Polynomial.prod_cyclotomic_eq_X_pow_sub_one hn ℤ
  have h2 : ∑ d ∈ n.divisors, (Polynomial.cyclotomic d ℤ).natDegree = n :=
    sum_natDegree_cyclotomic n
  have h3 :
      (∏ d ∈ n.divisors, Polynomial.cyclotomic d ℤ).homogenize
          (∑ d ∈ n.divisors, (Polynomial.cyclotomic d ℤ).natDegree) =
        ∏ d ∈ n.divisors, (Polynomial.cyclotomic d ℤ).homogenize (Polynomial.cyclotomic d ℤ).natDegree :=
    Polynomial.homogenize_finsetProd (fun i _ => le_refl _)
  rw [h1, h2] at h3
  rw [← h3]
  rw [Polynomial.homogenize_sub, Polynomial.homogenize_X_pow (le_refl n), Polynomial.homogenize_one]
  simp

/-- The main theorem: the homogeneous two-variable cyclotomic factorization,
evaluated at any integer point `(a, b)`. -/
theorem prod_Phi_eq (n : ℕ) (hn : 0 < n) (a b : ℤ) :
    a ^ n - b ^ n = ∏ d ∈ n.divisors, Phi d a b := by
  have h := congrArg (MvPolynomial.eval (![a, b] : Fin 2 → ℤ)) (homogenize_prod_cyclotomic n hn)
  simp only [map_sub, map_pow, MvPolynomial.eval_X, map_prod] at h
  simpa [Phi, Matrix.cons_val_zero, Matrix.cons_val_one] using h

/-- Sanity-check regression test: at `b = 1`, `Phi n a 1` recovers the plain
cyclotomic evaluation `(cyclotomic n ℤ).eval a`, matching the existing
`b = 1` brick `ZsygmondyCyclotomicFactor.prod_eval_cyclotomic_eq`. -/
theorem Phi_one_eq (n : ℕ) (a : ℤ) :
    Phi n a 1 = (Polynomial.cyclotomic n ℤ).eval a := by
  unfold Phi
  have hn : (Polynomial.cyclotomic n ℤ).natDegree ≤ (Polynomial.cyclotomic n ℤ).natDegree := le_refl _
  have hg : (![a, 1] : Fin 2 → ℤ) 1 = 1 := by simp
  have h := Polynomial.eval₂_homogenize_of_eq_one hn (RingHom.id ℤ) (![a, 1] : Fin 2 → ℤ) hg
  simp only [MvPolynomial.eval₂_id, Matrix.cons_val_zero, Polynomial.eval₂_id] at h
  exact h

end ZsygmondyHomogeneousCyclotomicFactor
