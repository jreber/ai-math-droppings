import Mathlib.NumberTheory.FLT.Polynomial

/-!
# The function-field analogue of Beal's conjecture (Lean 4 / mathlib)

**Beal's conjecture** asserts that `A^x + B^y = C^z` with exponents `x, y, z ≥ 3`
and pairwise-coprime positive integers `A, B, C` has no nontrivial solutions —
equivalently, any solution forces `A, B, C` to share a common prime factor. Over
the integers this is **OPEN**.

Over a polynomial ring `k[X]` (with `k` a field) the analogue is a **THEOREM**.
The reason is the polynomial Fermat–Catalan / `abc` theorem (Mason–Stothers),
which mathlib provides as `Polynomial.flt_catalan`: the equation
`u·a^p + v·b^q + w·c^r = 0` over `k[X]` with nonzero coefficients, coprime
`a, b`, and the *genus* condition `q*r + r*p + p*q ≤ p*q*r` (equivalently
`1/p + 1/q + 1/r ≤ 1`) has only constant solutions.

This file specializes that engine to the **Beal exponent range** `min(x,y,z) ≥ 3`.
When all exponents are `≥ 3` the genus condition holds automatically
(`1/x + 1/y + 1/z ≤ 1/3 + 1/3 + 1/3 = 1`), so every coprime polynomial Beal
solution is constant; dropping coprimality, every *nonconstant* solution must
have `a, b` sharing a common factor — the function-field form of Beal's "common
factor" assertion.

## Novelty

This is **NEW** in this repository. Mathlib supplies only the equal-exponent
Fermat statement `Polynomial.flt` (the case `x = y = z = n`); it does not package
a Beal-range (`min ≥ 3`, possibly distinct exponents) specialization. The genus
lemma `genus_ineq_of_three_le` and the Beal packagings below are the new content.

## Main results

* `genus_ineq_of_three_le` — for `x, y, z ≥ 3`, the genus inequality
  `y*z + z*x + x*y ≤ x*y*z` holds (this is `1/x + 1/y + 1/z ≤ 1`).
* `polynomial_beal_coprime` — coprime form: a coprime polynomial Beal solution
  `a^x + b^y = c^z` (exponents `≥ 3`, exponents nonzero in `k`) has
  `a, b, c` all constant.
* `polynomial_beal` — the headline "common factor" form: a *nonconstant*
  polynomial Beal solution cannot have `a, b` coprime.
* `polynomial_beal_charZero` — the clean characteristic-zero statement (over
  `ℚ`, `ℝ`, `ℂ`, …), where the `(x : k) ≠ 0` hypotheses are automatic.

The whole development reduces to `Polynomial.flt_catalan` (Mason–Stothers) and
elementary arithmetic; it is axiom-clean
(`propext`, `Classical.choice`, `Quot.sound` only).
-/

namespace BealPolynomial

open Polynomial

variable {k : Type*} [Field k]

/-- The **genus inequality** for the Beal exponent range: if `x, y, z ≥ 3` then
`y*z + z*x + x*y ≤ x*y*z`. This is exactly `1/x + 1/y + 1/z ≤ 1`, the hypothesis
required by `Polynomial.flt_catalan`. Since each exponent is `≥ 3`, multiplying
`3 ≤ z`, `3 ≤ x`, `3 ≤ y` by `x*y`, `y*z`, `z*x` respectively and summing gives
`3·(yz + zx + xy) ≤ 3·xyz`. -/
theorem genus_ineq_of_three_le {x y z : ℕ} (hx : 3 ≤ x) (hy : 3 ≤ y) (hz : 3 ≤ z) :
    y * z + z * x + x * y ≤ x * y * z := by
  nlinarith [Nat.mul_le_mul_right (x * y) hz, Nat.mul_le_mul_right (y * z) hx,
    Nat.mul_le_mul_right (z * x) hy]

/-- **Polynomial Beal, coprime form.** Over a field `k`, a coprime polynomial
solution `a^x + b^y = c^z` with exponents `x, y, z ≥ 3` (each nonzero in `k`) and
`a, b, c ≠ 0` forces `a, b, c` to all be constant (`natDegree = 0`).

This is the Beal exponent-range specialization of `Polynomial.flt_catalan`
(Mason–Stothers): the genus condition `1/x + 1/y + 1/z ≤ 1` holds automatically
when `min(x,y,z) ≥ 3`, supplied here by `genus_ineq_of_three_le`. -/
theorem polynomial_beal_coprime {x y z : ℕ} (hx : 3 ≤ x) (hy : 3 ≤ y) (hz : 3 ≤ z)
    (chx : (x : k) ≠ 0) (chy : (y : k) ≠ 0) (chz : (z : k) ≠ 0)
    {a b c : k[X]} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hab : IsCoprime a b)
    (heq : a ^ x + b ^ y = c ^ z) :
    a.natDegree = 0 ∧ b.natDegree = 0 ∧ c.natDegree = 0 := by
  -- Rewrite `a^x + b^y = c^z` into the `C u·a^x + C v·b^y + C w·c^z = 0` form.
  rw [← sub_eq_zero, ← one_mul (a ^ x), ← one_mul (b ^ y), ← one_mul (c ^ z),
    sub_eq_add_neg, ← neg_mul] at heq
  have hone : (1 : k[X]) = C 1 := by rfl
  have hneg_one : (-1 : k[X]) = C (-1) := by simp only [map_neg, map_one]
  simp_rw [hneg_one, hone] at heq
  -- Apply Fermat–Catalan with `p,q,r := x,y,z` and `u,v,w := 1,1,-1`.
  apply flt_catalan (by omega) (by omega) (by omega)
    (genus_ineq_of_three_le hx hy hz) chx chy chz ha hb hc hab
    one_ne_zero one_ne_zero (neg_ne_zero.mpr one_ne_zero) heq

/-- **Polynomial Beal, headline "common factor" form.** Over a field `k`, a
*nonconstant* polynomial Beal solution `a^x + b^y = c^z` (exponents `x, y, z ≥ 3`,
each nonzero in `k`, with `a, b, c ≠ 0` and at least one of `a, b, c` nonconstant)
cannot have `a, b` coprime.

This is the function-field analogue of Beal's conjecture: just as a nontrivial
integer Beal solution must have its bases share a common prime factor, a
nontrivial polynomial Beal solution must have its bases share a common factor
(here recorded as the failure of coprimality of `a` and `b`). Contrapositive of
`polynomial_beal_coprime`. -/
theorem polynomial_beal {x y z : ℕ} (hx : 3 ≤ x) (hy : 3 ≤ y) (hz : 3 ≤ z)
    (chx : (x : k) ≠ 0) (chy : (y : k) ≠ 0) (chz : (z : k) ≠ 0)
    {a b c : k[X]} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hnt : a.natDegree ≠ 0 ∨ b.natDegree ≠ 0 ∨ c.natDegree ≠ 0)
    (heq : a ^ x + b ^ y = c ^ z) :
    ¬ IsCoprime a b := by
  intro hab
  obtain ⟨da, db, dc⟩ :=
    polynomial_beal_coprime hx hy hz chx chy chz ha hb hc hab heq
  rcases hnt with h | h | h
  · exact h da
  · exact h db
  · exact h dc

/-- **Polynomial Beal over a characteristic-zero field.** Specialization of
`polynomial_beal_coprime` to `[CharZero k]` (e.g. `k = ℚ, ℝ, ℂ`), where the
`(x : k) ≠ 0` side conditions are discharged automatically. This is the cleanest
statement that Beal's conjecture *holds* for `k[X]` over a characteristic-zero
field: any coprime solution with exponents `≥ 3` is constant. -/
theorem polynomial_beal_charZero [CharZero k] {x y z : ℕ}
    (hx : 3 ≤ x) (hy : 3 ≤ y) (hz : 3 ≤ z)
    {a b c : k[X]} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hab : IsCoprime a b)
    (heq : a ^ x + b ^ y = c ^ z) :
    a.natDegree = 0 ∧ b.natDegree = 0 ∧ c.natDegree = 0 :=
  polynomial_beal_coprime hx hy hz
    (Nat.cast_ne_zero.mpr (by omega)) (Nat.cast_ne_zero.mpr (by omega))
    (Nat.cast_ne_zero.mpr (by omega)) ha hb hc hab heq

end BealPolynomial
