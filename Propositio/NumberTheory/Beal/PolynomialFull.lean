import Mathlib.NumberTheory.FLT.Polynomial
import Propositio.NumberTheory.Beal.Polynomial

/-!
# The full function-field Fermat–Catalan / Beal common-factor theorem (Lean 4 / mathlib)

This file proves the **strongest** function-field analogue of Beal's conjecture
available from mathlib's Mason–Stothers engine: the full **Fermat–Catalan**
theorem over a polynomial ring `k[X]`, stated directly in terms of the *genus
condition*

  `y*z + z*x + x*y ≤ x*y*z`   (equivalently `1/x + 1/y + 1/z ≤ 1`).

This subsumes two earlier results:

* mathlib's equal-exponent statement `Polynomial.flt` (the case `x = y = z = n`,
  `n ≥ 3`), and `fermatLastTheoremWith'_polynomial` (its gcd-extraction form);
* this repository's Beal-range statement `BealPolynomial.polynomial_beal`
  (the case `min(x,y,z) ≥ 3`), which is the special case of the genus condition
  obtained from `genus_ineq_of_three_le`.

The genus condition is *strictly weaker* than `min ≥ 3`: it admits the famous
mixed exponent triples with `1/x + 1/y + 1/z ≤ 1` that include a `2`, e.g.
`(2,3,7)`, `(2,4,5)`, `(2,3,8)`, `(2,4,6)`, `(3,3,4)`, … — none of which lie in
the Beal range. So the results below cover genuinely more cases than
`BealPolynomial.polynomial_beal`.

## Main results (namespace `BealPolynomialFull`)

* `polynomial_fermatCatalan_coprime` — coprime form: a coprime polynomial
  solution `a^x + b^y = c^z` with the genus condition (and exponents nonzero in
  `k`) forces `a, b, c` all constant.
* `polynomial_fermatCatalan` — **headline common-factor form**: a *nonconstant*
  polynomial solution cannot have `a, b` coprime. The literal Beal/Fermat–Catalan
  claim with coprimality dropped.
* `polynomial_fermatCatalan_common_factor` — **explicit common-factor
  extraction**: from any nonconstant solution it produces an explicit nonconstant
  `d := gcd a b` with `a = d * a'`, `b = d * b'`, and `d ∣ c ^ z`. This mirrors
  `fermatLastTheoremWith'_polynomial`'s gcd-extraction, adapted to *mixed*
  exponents (see the note there on why the clean `d ∣ c` of the equal-exponent
  case must weaken to `d ∣ c ^ z` here).
* `polynomial_beal_range_corollary` — re-derives `BealPolynomial`'s `min ≥ 3`
  result as a one-line corollary, exhibiting the new theorem as a strict
  generalization.
* `polynomial_fermatCatalan_charZero` — the clean characteristic-zero version
  (over `ℚ`, `ℝ`, `ℂ`, …), where the `(x : k) ≠ 0` side conditions vanish.

The whole development reduces to `Polynomial.flt_catalan` (Mason–Stothers) and
elementary arithmetic; it is axiom-clean
(`propext`, `Classical.choice`, `Quot.sound` only).
-/

namespace BealPolynomialFull

open Polynomial

variable {k : Type*} [Field k]

/-- **Full Fermat–Catalan, coprime form.** Over a field `k`, a coprime polynomial
solution `a^x + b^y = c^z` with the *genus condition*
`y*z + z*x + x*y ≤ x*y*z` (i.e. `1/x + 1/y + 1/z ≤ 1`), nonzero exponents in `k`,
and `a, b, c ≠ 0`, forces `a, b, c` to all be constant (`natDegree = 0`).

This is the direct specialization of `Polynomial.flt_catalan` (Mason–Stothers) to
the `1·a^x + 1·b^y + (-1)·c^z = 0` shape. It takes the genus inequality as a
*hypothesis*, rather than deriving it from `min(x,y,z) ≥ 3` as
`BealPolynomial.polynomial_beal_coprime` does — hence it covers the full
Fermat–Catalan range, including mixed triples such as `(2,3,7)`. -/
theorem polynomial_fermatCatalan_coprime {x y z : ℕ}
    (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0)
    (hgenus : y * z + z * x + x * y ≤ x * y * z)
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
  apply flt_catalan hx hy hz hgenus chx chy chz ha hb hc hab
    one_ne_zero one_ne_zero (neg_ne_zero.mpr one_ne_zero) heq

/-- **Full Fermat–Catalan, headline common-factor form.** Over a field `k`, a
*nonconstant* polynomial solution `a^x + b^y = c^z` satisfying the genus condition
`y*z + z*x + x*y ≤ x*y*z` (exponents nonzero in `k`, `a, b, c ≠ 0`, at least one
of `a, b, c` nonconstant) cannot have `a, b` coprime.

This is the function-field analogue of Beal's conjecture in its strongest form:
just as a nontrivial integer Fermat–Catalan solution must have its bases share a
common prime factor, a nontrivial polynomial solution must have its bases share a
common factor (recorded here as the failure of coprimality of `a` and `b`).
Contrapositive of `polynomial_fermatCatalan_coprime`. -/
theorem polynomial_fermatCatalan {x y z : ℕ}
    (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0)
    (hgenus : y * z + z * x + x * y ≤ x * y * z)
    (chx : (x : k) ≠ 0) (chy : (y : k) ≠ 0) (chz : (z : k) ≠ 0)
    {a b c : k[X]} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hnt : a.natDegree ≠ 0 ∨ b.natDegree ≠ 0 ∨ c.natDegree ≠ 0)
    (heq : a ^ x + b ^ y = c ^ z) :
    ¬ IsCoprime a b := by
  intro hab
  obtain ⟨da, db, dc⟩ :=
    polynomial_fermatCatalan_coprime hx hy hz hgenus chx chy chz ha hb hc hab heq
  rcases hnt with h | h | h
  · exact h da
  · exact h db
  · exact h dc

/-- **Full Fermat–Catalan, explicit common-factor extraction.** Dropping
coprimality entirely: from any *nonconstant* polynomial solution `a^x + b^y = c^z`
satisfying the genus condition, we extract an explicit, genuinely **nonconstant**
common factor `d := gcd a b` together with cofactors `a'`, `b'` such that

  `a = d * a'`,   `b = d * b'`,   and   `d ∣ c ^ z`.

Thus every nonconstant solution is built on a nontrivial common factor `d` of the
two summand bases; in particular `a` and `b` are not coprime, and `d` divides
`c ^ z` (so every irreducible factor of `d` divides `c`).

This mirrors `fermatLastTheoremWith'_polynomial`'s gcd-extraction
(`Mathlib.NumberTheory.FLT.Polynomial`), adapted to **mixed exponents**. Note the
deliberate weakening `d ∣ c ^ z` rather than the equal-exponent case's clean
`d ∣ c`: with distinct exponents the left side
`d^x · a'^x + d^y · b'^y` only exposes the common power `d ^ min(x,y)` rather than
a clean `d ^ n`, so the integrally-closed `pow_dvd_pow` argument that yields
`d ∣ c` for equal exponents does not transfer. `d ∣ c ^ z` is the cleanest
faithful conclusion (every prime factor of `d` still divides `c`); the
nonconstancy of `d` is the substantive "shared common factor" content. -/
theorem polynomial_fermatCatalan_common_factor {x y z : ℕ}
    (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0)
    (hgenus : y * z + z * x + x * y ≤ x * y * z)
    (chx : (x : k) ≠ 0) (chy : (y : k) ≠ 0) (chz : (z : k) ≠ 0)
    {a b c : k[X]} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hnt : a.natDegree ≠ 0 ∨ b.natDegree ≠ 0 ∨ c.natDegree ≠ 0)
    (heq : a ^ x + b ^ y = c ^ z) :
    ∃ d a' b' : k[X], d.natDegree ≠ 0 ∧ a = d * a' ∧ b = d * b' ∧ d ∣ c ^ z := by
  classical
  set d := gcd a b with hd_def
  obtain ⟨a', eq_a⟩ := gcd_dvd_left a b
  obtain ⟨b', eq_b⟩ := gcd_dvd_right a b
  -- `d ∣ c ^ z`: `d ∣ a`, `d ∣ b` gives `d ∣ a^x + b^y = c^z`.
  have hda : d ∣ a := gcd_dvd_left a b
  have hdb : d ∣ b := gcd_dvd_right a b
  have hdcz : d ∣ c ^ z := by
    rw [← heq]
    exact dvd_add (hda.pow hx) (hdb.pow hy)
  -- `d` is nonconstant: otherwise `a, b` would be coprime, contradicting `polynomial_fermatCatalan`.
  refine ⟨d, a', b', ?_, eq_a, eq_b, hdcz⟩
  intro hd0
  -- A constant gcd of nonzero polynomials is a unit, so `a, b` are coprime.
  have hcop : IsCoprime a b := by
    have hdunit : IsUnit d := by
      have hdne : d ≠ 0 := gcd_ne_zero_of_left ha
      rw [Polynomial.natDegree_eq_zero] at hd0
      obtain ⟨e, he⟩ := hd0
      have hene : e ≠ 0 := by
        rintro rfl
        simp [map_zero] at he
        exact hdne he.symm
      rw [← he]
      exact (Polynomial.isUnit_C).mpr (isUnit_iff_ne_zero.mpr hene)
    exact (gcd_isUnit_iff a b).mp (hd_def ▸ hdunit)
  exact polynomial_fermatCatalan hx hy hz hgenus chx chy chz ha hb hc hnt heq hcop

/-- **Beal-range corollary.** The original Beal exponent-range result
`BealPolynomial.polynomial_beal_coprime` (`min(x,y,z) ≥ 3`) is recovered as a
one-line corollary of the full Fermat–Catalan theorem
`polynomial_fermatCatalan_coprime`, by feeding the genus inequality through
`BealPolynomial.genus_ineq_of_three_le`. This exhibits the new theorem as a
*strict* generalization of the previous repository result. -/
theorem polynomial_beal_range_corollary {x y z : ℕ}
    (hx : 3 ≤ x) (hy : 3 ≤ y) (hz : 3 ≤ z)
    (chx : (x : k) ≠ 0) (chy : (y : k) ≠ 0) (chz : (z : k) ≠ 0)
    {a b c : k[X]} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hab : IsCoprime a b)
    (heq : a ^ x + b ^ y = c ^ z) :
    a.natDegree = 0 ∧ b.natDegree = 0 ∧ c.natDegree = 0 :=
  polynomial_fermatCatalan_coprime (by omega) (by omega) (by omega)
    (BealPolynomial.genus_ineq_of_three_le hx hy hz) chx chy chz ha hb hc hab heq

/-- **Full Fermat–Catalan over a characteristic-zero field.** Specialization of
`polynomial_fermatCatalan_coprime` to `[CharZero k]` (e.g. `k = ℚ, ℝ, ℂ`), where
the `(x : k) ≠ 0` side conditions are discharged automatically. The cleanest
statement that the full Fermat–Catalan theorem *holds* over `k[X]` for a
characteristic-zero field: any coprime solution with `1/x + 1/y + 1/z ≤ 1` is
constant. -/
theorem polynomial_fermatCatalan_charZero [CharZero k] {x y z : ℕ}
    (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0)
    (hgenus : y * z + z * x + x * y ≤ x * y * z)
    {a b c : k[X]} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hab : IsCoprime a b)
    (heq : a ^ x + b ^ y = c ^ z) :
    a.natDegree = 0 ∧ b.natDegree = 0 ∧ c.natDegree = 0 :=
  polynomial_fermatCatalan_coprime hx hy hz hgenus
    (Nat.cast_ne_zero.mpr hx) (Nat.cast_ne_zero.mpr hy)
    (Nat.cast_ne_zero.mpr hz) ha hb hc hab heq

end BealPolynomialFull
