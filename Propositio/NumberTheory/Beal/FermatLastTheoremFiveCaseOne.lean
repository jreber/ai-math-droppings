import Mathlib.RingTheory.Int.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Fermat's Last Theorem for exponent 5, Case I — building blocks

Fermat's Last Theorem for the exponent `5` splits classically (Sophie Germain / Legendre /
Dirichlet, 1825) into two cases:

* **Case I**: `5 ∤ ABC`. Elementary infinite descent in ordinary integers, using an
  auxiliary prime `q = 11` (Sophie Germain's criterion) plus a factorization/coprimality
  argument on `A^5 + B^5 = (A+B)·(A^4 - A^3B + A^2B^2 - AB^3 + B^4)`.
* **Case II**: `5 ∣ ABC`. Needs descent in the ring of integers of `ℚ(√5)` (the golden-ratio
  unit `φ`); out of scope here.

This file assembles the **elementary, self-contained ingredients of the classical Case I
argument** (H.M. Edwards, *Fermat's Last Theorem: A Genetic Introduction to Algebraic Number
Theory*, Ch. 3):

1. `sophie_germain_ne_mod_eleven` / `sophie_germain_dvd_prod` — Sophie Germain's auxiliary
   condition (i) for `p = 5`, `q = 11`: mod `11`, a sum of three nonzero fifth powers is never
   `≡ 0`. Equivalently, `11 ∣ x^5 + y^5 + z^5` forces `11` to divide one of `x, y, z`.
   (`11 = 2·5 + 1` is prime, and the fifth-power residues mod `11` are `{0, 1, 10}`; no two of
   `{1, 10}` sum to a third, mod `11`.)
2. `five_not_fifth_power_mod_eleven` — Sophie Germain's auxiliary condition (ii): `5` is not a
   fifth-power residue mod `11`.
3. `quintic_sum_factorization` — the algebraic identity
   `x^5 + y^5 = (x + y) · (x^4 - x^3y + x^2y^2 - xy^3 + y^4)`.
4. `quintic_factor_gcd_dvd_five` — if `x, y` are coprime, every common divisor of `x + y` and
   the quartic cofactor `x^4 - x^3y + x^2y^2 - xy^3 + y^4` divides `5` (proved via the
   polynomial identity `x^4 - x^3y + x^2y^2 - xy^3 + y^4 = 5x^4 + (x+y)·(-4x^3+3x^2y-2xy^2+y^3)`
   and coprimality of `x + y` with `x`).
5. `quintic_factors_coprime_of_not_five_dvd` — the coprimality upgrade: when additionally
   `5 ∤ (x + y)`, the two factors `x + y` and the quartic cofactor are fully coprime.
6. `quintic_factors_eq_pow_of_coprime` — when `x + y` and the quartic cofactor are coprime and
   `x^5 + y^5 = c^5`, unique factorization (`Int.eq_pow_of_mul_eq_pow_odd`, exponent `5` odd)
   extracts each factor as an exact fifth power: `x + y = d^5` and the quartic cofactor `= e^5`.

**Update (2026-07-10): Case I is now fully closed**, in the companion file
`FermatLastTheoremFiveCaseOneDescent.lean` — see `fermat_five_case_one` there. The route taken
is *not* the genetic/infinite-descent construction speculated below; it turns out Sophie
Germain's Theorem itself (via the auxiliary prime `q = 11`, applied directly using exactly the
two facts `sophie_germain_dvd_prod` and `five_not_fifth_power_mod_eleven` from this file) gives
a complete, *finite* contradiction with no descent and no case split on `5 ∣ (x+y)`. The
paragraph immediately below records the originally-anticipated (and, as it turns out,
unnecessary) route, kept for historical/scoping context:

~~The full classical Case I proof continues past step 6 with a genetic/explicit construction of
a *strictly smaller* Case-I solution from `d, e` (using the `11`-divisibility located by step 1
and ruled out on one branch by step 2), assembled via strong induction on `|ABC|` to complete an
infinite-descent contradiction — this final assembly (and the parallel `5 ∣ (x+y)` sub-case,
where the gcd bound of step 4 is exactly `5` rather than `1`) was not attempted in this file.~~
The lemmas in *this* file remain exactly as before (each independently real, no `sorry`, no
project axiom); only the scope note above is updated.
-/

namespace FermatLastTheoremFiveCaseOne

/-- **Sophie Germain's auxiliary condition (i), mod form.** Over `ZMod 11`, a sum of three
nonzero fifth powers is never `0`. (`11 = 2·5+1` is prime; the fifth-power residues mod `11`
are `{0, 1, 10}`, and no two of the nonzero residues `{1, 10}` sum to a third nonzero
fifth-power residue.) A finite, fully decidable fact. -/
theorem sophie_germain_ne_mod_eleven :
    ∀ a b c : ZMod 11, a ≠ 0 → b ≠ 0 → c ≠ 0 → a ^ 5 + b ^ 5 + c ^ 5 ≠ 0 := by decide

/-- **Sophie Germain's auxiliary condition (i), integer form.** If `11 ∣ x^5 + y^5 + z^5`
then `11` divides at least one of `x, y, z`. Equivalently: for a Case-I solution
(`x^5+y^5+z^5 = 0`), `11` must divide `xyz`. -/
theorem sophie_germain_dvd_prod {x y z : ℤ} (h : (11 : ℤ) ∣ x ^ 5 + y ^ 5 + z ^ 5) :
    (11 : ℤ) ∣ x ∨ (11 : ℤ) ∣ y ∨ (11 : ℤ) ∣ z := by
  by_contra hcon
  rw [not_or, not_or] at hcon
  obtain ⟨hx, hy, hz⟩ := hcon
  have hx' : (x : ZMod 11) ≠ 0 := by
    simpa [ZMod.intCast_zmod_eq_zero_iff_dvd] using hx
  have hy' : (y : ZMod 11) ≠ 0 := by
    simpa [ZMod.intCast_zmod_eq_zero_iff_dvd] using hy
  have hz' : (z : ZMod 11) ≠ 0 := by
    simpa [ZMod.intCast_zmod_eq_zero_iff_dvd] using hz
  have hsum : ((x : ZMod 11)) ^ 5 + (y : ZMod 11) ^ 5 + (z : ZMod 11) ^ 5 = 0 := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd (x ^ 5 + y ^ 5 + z ^ 5) 11).mpr h
    push_cast at this
    exact this
  exact sophie_germain_ne_mod_eleven _ _ _ hx' hy' hz' hsum

/-- **Sophie Germain's auxiliary condition (ii).** `5` is not a fifth-power residue mod `11`
(the fifth-power residues mod `11` are exactly `{0, 1, 10}`). -/
theorem five_not_fifth_power_mod_eleven : ¬ ∃ a : ZMod 11, a ^ 5 = 5 := by decide

/-- The classical factorization of a sum of fifth powers. -/
theorem quintic_sum_factorization (x y : ℤ) :
    x ^ 5 + y ^ 5 = (x + y) * (x ^ 4 - x ^ 3 * y + x ^ 2 * y ^ 2 - x * y ^ 3 + y ^ 4) := by
  ring

/-- The key polynomial identity behind the Case-I gcd bound: the quartic cofactor is
`5x^4` modulo `(x+y)`. -/
theorem quintic_cofactor_identity (x y : ℤ) :
    x ^ 4 - x ^ 3 * y + x ^ 2 * y ^ 2 - x * y ^ 3 + y ^ 4
      = 5 * x ^ 4 + (x + y) * (-4 * x ^ 3 + 3 * x ^ 2 * y - 2 * x * y ^ 2 + y ^ 3) := by
  ring

/-- `x` and `x + y` are coprime whenever `x` and `y` are (Bézout coefficients transfer
directly: if `u·x + v·y = 1` then `v·(x+y) + (u-v)·x = 1`). -/
theorem isCoprime_add_self_left {x y : ℤ} (h : IsCoprime x y) : IsCoprime (x + y) x := by
  obtain ⟨u, v, huv⟩ := h
  exact ⟨v, u - v, by linear_combination huv⟩

/-- **Case-I gcd bound.** If `x, y` are coprime integers, every common divisor of `x + y`
and the quartic cofactor `x^4 - x^3y + x^2y^2 - xy^3 + y^4` divides `5`. -/
theorem quintic_factor_gcd_dvd_five {x y d : ℤ} (hxy : IsCoprime x y)
    (hd1 : d ∣ x + y) (hd2 : d ∣ x ^ 4 - x ^ 3 * y + x ^ 2 * y ^ 2 - x * y ^ 3 + y ^ 4) :
    d ∣ 5 := by
  have hcop : IsCoprime (x + y) (x ^ 4) := (isCoprime_add_self_left hxy).pow_right
  have hcopd : IsCoprime d (x ^ 4) := hcop.of_isCoprime_of_dvd_left hd1
  have hd5x4 : d ∣ 5 * x ^ 4 := by
    have : d ∣ (x ^ 4 - x ^ 3 * y + x ^ 2 * y ^ 2 - x * y ^ 3 + y ^ 4)
        - (x + y) * (-4 * x ^ 3 + 3 * x ^ 2 * y - 2 * x * y ^ 2 + y ^ 3) :=
      hd2.sub (hd1.mul_right _)
    have heq : (x ^ 4 - x ^ 3 * y + x ^ 2 * y ^ 2 - x * y ^ 3 + y ^ 4)
        - (x + y) * (-4 * x ^ 3 + 3 * x ^ 2 * y - 2 * x * y ^ 2 + y ^ 3) = 5 * x ^ 4 := by
      linear_combination quintic_cofactor_identity x y
    rwa [heq] at this
  exact hcopd.dvd_of_dvd_mul_right hd5x4

/-- **Coprimality upgrade.** If additionally `5 ∤ (x+y)`, the sum `x+y` and the quartic
cofactor are fully coprime (every common divisor divides `5` by the previous lemma, and a
divisor of `x+y` dividing `5` but with `5 ∤ (x+y)` cannot be a multiple of `5`, so the gcd is
exactly `1`). -/
theorem quintic_factors_coprime_of_not_five_dvd {x y : ℤ} (hxy : IsCoprime x y)
    (h5 : ¬ (5 : ℤ) ∣ x + y) :
    IsCoprime (x + y) (x ^ 4 - x ^ 3 * y + x ^ 2 * y ^ 2 - x * y ^ 3 + y ^ 4) := by
  rw [Int.isCoprime_iff_gcd_eq_one]
  set g : ℕ := Int.gcd (x + y) (x ^ 4 - x ^ 3 * y + x ^ 2 * y ^ 2 - x * y ^ 3 + y ^ 4) with hg
  have hgd1 : (g : ℤ) ∣ x + y := Int.gcd_dvd_left ..
  have hgd2 : (g : ℤ) ∣ x ^ 4 - x ^ 3 * y + x ^ 2 * y ^ 2 - x * y ^ 3 + y ^ 4 :=
    Int.gcd_dvd_right ..
  have hg5 : (g : ℤ) ∣ 5 := quintic_factor_gcd_dvd_five hxy hgd1 hgd2
  have hg5' : g ∣ 5 := by exact_mod_cast hg5
  rcases (Nat.Prime.eq_one_or_self_of_dvd (by norm_num) g hg5') with h1 | h5eq
  · exact h1
  · exfalso; apply h5; rw [h5eq] at hgd1; exact_mod_cast hgd1

/-- **Fifth-power factor extraction.** When `x, y` are coprime, `5 ∤ (x+y)`, and
`x^5 + y^5 = c^5`, the coprime factorization forces each factor to be an exact fifth power:
`x + y = d^5` for some `d`, and the quartic cofactor `= e^5` for some `e`. This is the
"unique factorization" step of the classical Case-I descent (no ideal theory needed, since
the factorization is over ordinary `ℤ`). -/
theorem quintic_factors_eq_pow_of_coprime {x y c : ℤ} (hxy : IsCoprime x y)
    (h5 : ¬ (5 : ℤ) ∣ x + y) (heq : x ^ 5 + y ^ 5 = c ^ 5) :
    (∃ d : ℤ, x + y = d ^ 5) ∧
      ∃ e : ℤ, x ^ 4 - x ^ 3 * y + x ^ 2 * y ^ 2 - x * y ^ 3 + y ^ 4 = e ^ 5 := by
  have hcop := quintic_factors_coprime_of_not_five_dvd hxy h5
  have hfact : (x + y) * (x ^ 4 - x ^ 3 * y + x ^ 2 * y ^ 2 - x * y ^ 3 + y ^ 4) = c ^ 5 := by
    rw [← quintic_sum_factorization]; exact heq
  exact Int.eq_pow_of_mul_eq_pow_odd hcop (by decide) hfact

end FermatLastTheoremFiveCaseOne
