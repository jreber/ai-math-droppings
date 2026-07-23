import Propositio.Beal.Radical
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# The ABC-quality lower bound for Beal solutions (Lean 4)

This file proves the **ABC-quality lower bound**: *every primitive Beal solution
`Aˣ + Bʸ = Cᶻ` is an ABC triple of quality `q > 1`*, in the sharp integer form

  `radical(Aˣ · Bʸ · Cᶻ) < Cᶻ`.

Recall the ABC-quality of a coprime triple `a + b = c` is
`q = log c / log radical(a·b·c)`; quality `q > 1` is exactly `radical(abc) < c`.
So this file establishes that the (entire) Beal value `Cᶻ` strictly dominates the
radical of the Beal product — the quantitative heart of the implication
**ABC ⟹ Beal**. The unconditional ABC conjecture only asserts that `q ≤ 1 + ε`
fails for finitely many triples; here we show, unconditionally, that *every*
primitive Beal solution lands in the regime `q > 1`. So Beal solutions are exactly
the ABC-*exceptional* triples, the ones the ABC conjecture forbids from being
abundant. This connects directly to the project's empirical ABC-quality-ceiling
program (`docs/threads/beal/abc-quality-*`), which measures how high `q` climbs.

## The argument

For a primitive solution `Aˣ + Bʸ = Cᶻ` with `A, B, C ≥ 2` and exponents `≥ 3`:

* Each summand is below the value: `Aˣ < Cᶻ` and `Bʸ < Cᶻ`.
* Taking real `x`-th / `y`-th roots, `A < C^(z/x)` and `B < C^(z/y)` (strict,
  base monotonicity of `Real.rpow`). With `C = C¹` this gives the **strict**
  product bound `A·B·C < C^(z/x + z/y + 1)` (`abc_lt_rpow`).
* Since `min(x,y,z) ≥ 3`, the genus inequality `y·z + x·z + x·y ≤ x·y·z`
  (`BealPolynomial.genus_ineq_of_three_le`) is exactly `1/x + 1/y + 1/z ≤ 1`,
  i.e. `z/x + z/y + 1 ≤ z`. As `C ≥ 2 > 1`, exponent-monotonicity of `rpow` gives
  `C^(z/x + z/y + 1) ≤ C^z`. Hence `A·B·C < Cᶻ` (`abc_lt_c_pow`).
* Finally `radical(Aˣ Bʸ Cᶻ) = radical(A·B·C) ≤ A·B·C < Cᶻ`, the headline
  `beal_radical_lt_c`.
* Since `A ≥ 2` contributes a prime to the radical, `2 ≤ radical(Aˣ Bʸ Cᶻ)`, and
  the log form `1 < log(Cᶻ) / log(radical(Aˣ Bʸ Cᶻ))` follows
  (`beal_quality_gt_one`), the literal "quality `> 1`" statement.

## Contents
* `abc_lt_c_pow` — the **core inequality** `A·B·C < Cᶻ`.
* `beal_radical_lt_c` — **headline**: `radical(Aˣ Bʸ Cᶻ) < Cᶻ` (quality `q > 1`).
* `beal_quality_gt_one` — the explicit log form `1 < log(Cᶻ)/log(radical …)`.

Dependency policy: mathlib4 permitted (user authorization 2026-05-17). Use
`lake env lean BealABCQuality.lean` to typecheck.
-/

namespace BealABCQuality

open scoped Real

/-! ## 1. A base is bounded by a fractional power of `C`

The generalized cube-root bound: from `Aˣ < Cᶻ` with `x ≥ 3` we get `A < C^(z/x)`
over `ℝ` (not just `C^(z/3)`). We keep the exponent `x` rather than collapsing to
`3`, because the sharp product exponent `z/x + z/y + 1` is what makes
`z/x + z/y + 1 ≤ z` hold for `min(x,y,z) ≥ 3`. -/

/-- **Base bound.** If `1 ≤ x`, `1 ≤ A`, `2 ≤ C`, and `Aˣ < Cᶻ`, then over `ℝ`
`A < C^(z/x)`. (Apply `t ↦ t^(1/x)`, strictly monotone on nonneg reals, to
`Aˣ < Cᶻ`.) -/
theorem base_lt_rpow {A C x z : ℕ}
    (hx : 1 ≤ x) (hA : 1 ≤ A) (hC : 2 ≤ C) (hpow : A ^ x < C ^ z) :
    (A : ℝ) < (C : ℝ) ^ ((z : ℝ) / x) := by
  have hAR0 : (0 : ℝ) ≤ (A : ℝ) := by positivity
  have hCR0 : (0 : ℝ) ≤ (C : ℝ) := by positivity
  have hxR : (0 : ℝ) < (x : ℝ) := by exact_mod_cast hx
  -- Present `Aˣ < Cᶻ` over ℝ as rpow with real exponents.
  have hpow' : (A : ℝ) ^ (x : ℝ) < (C : ℝ) ^ (z : ℝ) := by
    rw [Real.rpow_natCast, Real.rpow_natCast]
    exact_mod_cast hpow
  -- Apply t ↦ t^(1/x), strictly monotone on nonneg reals.
  have hmono := Real.rpow_lt_rpow (z := (1 / x : ℝ)) (by positivity) hpow' (by positivity)
  rw [← Real.rpow_mul hAR0, ← Real.rpow_mul hCR0] at hmono
  rw [show (x : ℝ) * (1 / x) = 1 by field_simp, Real.rpow_one] at hmono
  rw [show (z : ℝ) * (1 / x) = (z : ℝ) / x by ring] at hmono
  exact hmono

/-! ## 2. The product of bases is below a fractional power of `C` -/

/-- **Product bound.** For a primitive Beal solution with `A, B ≥ 1`, `C ≥ 2`,
exponents `x, y ≥ 1`, and `Aˣ < Cᶻ`, `Bʸ < Cᶻ`, the product of bases satisfies
`A·B·C < C^(z/x + z/y + 1)` over `ℝ` (strict, from the strict base bounds). -/
theorem abc_lt_rpow {A B C x y z : ℕ}
    (hx : 1 ≤ x) (hy : 1 ≤ y) (hA : 1 ≤ A) (hB : 1 ≤ B) (hC : 2 ≤ C)
    (hAx : A ^ x < C ^ z) (hBy : B ^ y < C ^ z) :
    (A * B * C : ℝ) < (C : ℝ) ^ ((z : ℝ) / x + (z : ℝ) / y + 1) := by
  have hCR1 : (1 : ℝ) ≤ (C : ℝ) := by exact_mod_cast (by omega : 1 ≤ C)
  have hCpos : (0 : ℝ) < (C : ℝ) := by linarith
  have hBR1 : (1 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB
  have hAlt : (A : ℝ) < (C : ℝ) ^ ((z : ℝ) / x) := base_lt_rpow hx hA hC hAx
  have hBlt : (B : ℝ) < (C : ℝ) ^ ((z : ℝ) / y) := base_lt_rpow hy hB hC hBy
  -- A·B < C^(z/x) · C^(z/y)
  have hAB : (A : ℝ) * (B : ℝ) < (C : ℝ) ^ ((z : ℝ) / x) * (C : ℝ) ^ ((z : ℝ) / y) := by
    have hrpy : (0 : ℝ) < (C : ℝ) ^ ((z : ℝ) / y) := Real.rpow_pos_of_pos hCpos _
    calc (A : ℝ) * (B : ℝ)
        < (C : ℝ) ^ ((z : ℝ) / x) * (B : ℝ) :=
          mul_lt_mul_of_pos_right hAlt (by linarith)
      _ ≤ (C : ℝ) ^ ((z : ℝ) / x) * (C : ℝ) ^ ((z : ℝ) / y) :=
          mul_le_mul_of_nonneg_left (le_of_lt hBlt) (le_of_lt (Real.rpow_pos_of_pos hCpos _))
  -- Now A·B·C < C^(z/x) · C^(z/y) · C = C^(z/x + z/y + 1).
  have hABC : (A : ℝ) * (B : ℝ) * (C : ℝ)
      < (C : ℝ) ^ ((z : ℝ) / x) * (C : ℝ) ^ ((z : ℝ) / y) * (C : ℝ) :=
    mul_lt_mul_of_pos_right hAB hCpos
  have hrhs : (C : ℝ) ^ ((z : ℝ) / x) * (C : ℝ) ^ ((z : ℝ) / y) * (C : ℝ)
      = (C : ℝ) ^ ((z : ℝ) / x + (z : ℝ) / y + 1) := by
    nth_rewrite 3 [← Real.rpow_one (C : ℝ)]
    rw [← Real.rpow_add hCpos, ← Real.rpow_add hCpos]
  calc (A * B * C : ℝ) = (A : ℝ) * (B : ℝ) * (C : ℝ) := by norm_cast
    _ < (C : ℝ) ^ ((z : ℝ) / x) * (C : ℝ) ^ ((z : ℝ) / y) * (C : ℝ) := hABC
    _ = (C : ℝ) ^ ((z : ℝ) / x + (z : ℝ) / y + 1) := hrhs

/-! ## 3. The genus inequality in real fractional form -/

/-- **Genus inequality, real form.** For `x, y, z ≥ 3`, the product exponent is
bounded by `z`: `z/x + z/y + 1 ≤ z` over `ℝ`. This is exactly
`1/x + 1/y + 1/z ≤ 1`; it follows from the natural-number genus inequality
`y·z + x·z + x·y ≤ x·y·z` (`BealPolynomial.genus_ineq_of_three_le`). -/
theorem exp_sum_le {x y z : ℕ} (hx : 3 ≤ x) (hy : 3 ≤ y) (hz : 3 ≤ z) :
    (z : ℝ) / x + (z : ℝ) / y + 1 ≤ (z : ℝ) := by
  have hxR : (0 : ℝ) < (x : ℝ) := by exact_mod_cast (by omega : 0 < x)
  have hyR : (0 : ℝ) < (y : ℝ) := by exact_mod_cast (by omega : 0 < y)
  have hzR : (0 : ℝ) < (z : ℝ) := by exact_mod_cast (by omega : 0 < z)
  -- y·z + x·z + x·y ≤ x·y·z over ℕ, hence over ℝ.  This is the genus inequality
  -- `1/x + 1/y + 1/z ≤ 1`; multiply `3 ≤ z`, `3 ≤ x`, `3 ≤ y` by `xy`, `yz`, `zx`
  -- and sum (the pattern of `BealPolynomial.genus_ineq_of_three_le`, inlined here
  -- to keep the import surface to `BealRadical` only).
  have hgenus : y * z + x * z + x * y ≤ x * y * z := by
    nlinarith [Nat.mul_le_mul_right (x * y) hz, Nat.mul_le_mul_right (y * z) hx,
      Nat.mul_le_mul_right (z * x) hy]
  have hgenusR : (y : ℝ) * z + (x : ℝ) * z + (x : ℝ) * y ≤ (x : ℝ) * y * z := by
    exact_mod_cast hgenus
  rw [div_add_div _ _ (ne_of_gt hxR) (ne_of_gt hyR), div_add' _ _ _ (by positivity),
      div_le_iff₀ (by positivity)]
  nlinarith [hgenusR]

/-! ## 4. Core inequality: the product of bases is below the value -/

/-- **Core inequality.** Every primitive Beal solution `Aˣ + Bʸ = Cᶻ` with
`A, B, C ≥ 2` and exponents `x, y, z ≥ 3` satisfies, over `ℕ`,

  `A·B·C < Cᶻ`.

The product of the *bases* is strictly below the (huge) value `Cᶻ`. Proof: over
`ℝ`, `A·B·C < C^(z/x + z/y + 1) ≤ C^z` by `abc_lt_rpow` and `exp_sum_le`; cast
back to `ℕ`. -/
theorem abc_lt_c_pow {A B C x y z : ℕ}
    (hA : 2 ≤ A) (hB : 2 ≤ B) (hC : 2 ≤ C)
    (hx : 3 ≤ x) (hy : 3 ≤ y) (hz : 3 ≤ z)
    (h : A ^ x + B ^ y = C ^ z) : A * B * C < C ^ z := by
  -- Each summand is below the value.
  have hBy0 : 0 < B ^ y := pow_pos (by omega) y
  have hAx0 : 0 < A ^ x := pow_pos (by omega) x
  have hAx : A ^ x < C ^ z := by omega
  have hBy : B ^ y < C ^ z := by omega
  -- Product bound and genus bound over ℝ.
  have hprod : (A * B * C : ℝ) < (C : ℝ) ^ ((z : ℝ) / x + (z : ℝ) / y + 1) :=
    abc_lt_rpow (by omega) (by omega) (by omega) (by omega) hC hAx hBy
  have hCR1 : (1 : ℝ) ≤ (C : ℝ) := by exact_mod_cast (by omega : 1 ≤ C)
  have hmono : (C : ℝ) ^ ((z : ℝ) / x + (z : ℝ) / y + 1) ≤ (C : ℝ) ^ (z : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hCR1 (exp_sum_le hx hy hz)
  -- Combine to a strict real bound, then cast back.
  have hCz_rpow : (C : ℝ) ^ (z : ℝ) = ((C ^ z : ℕ) : ℝ) := by
    rw [Real.rpow_natCast]; push_cast; rfl
  have hreal : (A * B * C : ℝ) < ((C ^ z : ℕ) : ℝ) := by
    rw [← hCz_rpow]; exact lt_of_lt_of_le hprod hmono
  have : ((A * B * C : ℕ) : ℝ) < ((C ^ z : ℕ) : ℝ) := by push_cast at hreal ⊢; linarith
  exact_mod_cast this

/-! ## 5. Headline: the ABC-quality lower bound -/

/-- **Headline — the ABC-quality lower bound.** Every primitive Beal solution
`Aˣ + Bʸ = Cᶻ` with `A, B, C ≥ 2` and exponents `x, y, z ≥ 3` satisfies

  `radical(Aˣ · Bʸ · Cᶻ) < Cᶻ`,

i.e. ABC-quality `q = log(Cᶻ) / log(radical(Aˣ Bʸ Cᶻ)) > 1`. The radical of the
Beal product equals `radical(A·B·C) ≤ A·B·C` (`BealRadical.radical_beal_eq`,
`BealRadical.radical_le_self`), which the core inequality `abc_lt_c_pow` places
strictly below the value `Cᶻ`. So **every** primitive Beal solution is an ABC
triple of quality strictly above `1` — exactly an ABC-exceptional triple. -/
theorem beal_radical_lt_c {A B C x y z : ℕ}
    (hA : 2 ≤ A) (hB : 2 ≤ B) (hC : 2 ≤ C)
    (hx : 3 ≤ x) (hy : 3 ≤ y) (hz : 3 ≤ z)
    (h : A ^ x + B ^ y = C ^ z) :
    BealRadical.radical (A ^ x * B ^ y * C ^ z) < C ^ z := by
  -- radical(Aˣ Bʸ Cᶻ) = radical(ABC) ≤ ABC.
  have hrad_eq : BealRadical.radical (A ^ x * B ^ y * C ^ z)
      = BealRadical.radical (A * B * C) :=
    BealRadical.radical_beal_eq (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega)
  have hABCpos : 0 < A * B * C := by positivity
  have hrad_le : BealRadical.radical (A * B * C) ≤ A * B * C :=
    BealRadical.radical_le_self hABCpos
  -- ABC < Cᶻ.
  have hlt : A * B * C < C ^ z := abc_lt_c_pow hA hB hC hx hy hz h
  calc BealRadical.radical (A ^ x * B ^ y * C ^ z)
      = BealRadical.radical (A * B * C) := hrad_eq
    _ ≤ A * B * C := hrad_le
    _ < C ^ z := hlt

/-! ## 6. The explicit log form: quality `> 1` -/

/-- The radical of a Beal product is at least `2`: `2 ≤ radical(Aˣ Bʸ Cᶻ)`. Since
`A ≥ 2`, `A` has a prime factor, which divides `Aˣ ∣ Aˣ Bʸ Cᶻ`, hence lies in the
prime-factor set of the product; that prime is `≥ 2` and divides the radical. -/
theorem two_le_radical {A B C x y z : ℕ}
    (hA : 2 ≤ A) (hB : 2 ≤ B) (hC : 2 ≤ C) (hx : 3 ≤ x) :
    2 ≤ BealRadical.radical (A ^ x * B ^ y * C ^ z) := by
  -- A prime `p` dividing `A` lies in the prime factors of the product.
  obtain ⟨p, hp, hpA⟩ := (Nat.exists_prime_and_dvd (by omega : A ≠ 1))
  have hprodne : A ^ x * B ^ y * C ^ z ≠ 0 := by positivity
  have hpdvd : p ∣ A ^ x * B ^ y * C ^ z :=
    Dvd.dvd.mul_right (Dvd.dvd.mul_right (hpA.trans (dvd_pow_self A (by omega))) _) _
  have hmem : p ∈ (A ^ x * B ^ y * C ^ z).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hp, hpdvd, hprodne⟩
  -- p divides the radical, and p ≥ 2.
  have hpdvdrad : p ∣ BealRadical.radical (A ^ x * B ^ y * C ^ z) :=
    Finset.dvd_prod_of_mem _ hmem
  have hradpos : 0 < BealRadical.radical (A ^ x * B ^ y * C ^ z) :=
    BealRadical.radical_pos (by positivity)
  have hple : p ≤ BealRadical.radical (A ^ x * B ^ y * C ^ z) :=
    Nat.le_of_dvd hradpos hpdvdrad
  exact le_trans hp.two_le hple

/-- **Quality `> 1`, the explicit log form.** Every primitive Beal solution
`Aˣ + Bʸ = Cᶻ` (with `A, B, C ≥ 2`, exponents `x, y, z ≥ 3`) has ABC-quality
strictly above `1`:

  `1 < log(Cᶻ) / log(radical(Aˣ · Bʸ · Cᶻ))`.

Both `radical(…)` and `Cᶻ` exceed `1`, so their logs are positive, and
`radical(…) < Cᶻ` (the headline `beal_radical_lt_c`) gives
`log(radical) < log(Cᶻ)`, whence the quotient exceeds `1`. -/
theorem beal_quality_gt_one {A B C x y z : ℕ}
    (hA : 2 ≤ A) (hB : 2 ≤ B) (hC : 2 ≤ C)
    (hx : 3 ≤ x) (hy : 3 ≤ y) (hz : 3 ≤ z)
    (h : A ^ x + B ^ y = C ^ z) :
    1 < Real.log ((C ^ z : ℕ) : ℝ)
          / Real.log (BealRadical.radical (A ^ x * B ^ y * C ^ z) : ℝ) := by
  have hradlt : BealRadical.radical (A ^ x * B ^ y * C ^ z) < C ^ z :=
    beal_radical_lt_c hA hB hC hx hy hz h
  have hrad2 : 2 ≤ BealRadical.radical (A ^ x * B ^ y * C ^ z) :=
    two_le_radical hA hB hC hx
  -- Real bookkeeping: radical ≥ 2 and Cᶻ > radical, both > 1.
  have hradR2 : (2 : ℝ) ≤ (BealRadical.radical (A ^ x * B ^ y * C ^ z) : ℝ) := by
    exact_mod_cast hrad2
  have hradR1 : (1 : ℝ) < (BealRadical.radical (A ^ x * B ^ y * C ^ z) : ℝ) := by linarith
  have hcastlt : (BealRadical.radical (A ^ x * B ^ y * C ^ z) : ℝ) < ((C ^ z : ℕ) : ℝ) := by
    exact_mod_cast hradlt
  -- Positive denominator, larger numerator.
  have hlogden : 0 < Real.log (BealRadical.radical (A ^ x * B ^ y * C ^ z) : ℝ) :=
    Real.log_pos hradR1
  have hlognum : Real.log (BealRadical.radical (A ^ x * B ^ y * C ^ z) : ℝ)
      < Real.log ((C ^ z : ℕ) : ℝ) :=
    Real.log_lt_log (by linarith) hcastlt
  rw [lt_div_iff₀ hlogden, one_mul]
  exact hlognum

end BealABCQuality
