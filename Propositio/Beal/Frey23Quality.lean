import Propositio.Beal.Radical
import Propositio.Beal.RadicalAPI
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# The ABC-quality lower bound for signature-`(2,3,n)` solutions (Lean 4)

This file is the signature-`(2, 3, n)` analogue of `BealABCQuality.lean`. It proves
the **ABC-quality lower bound** for solutions of the generalized-Fermat equation

  `a² + b³ = c^n`,

namely, in the sharp integer form,

  `radical(a² · b³ · cⁿ) < cⁿ`.

Recall the ABC-quality of a coprime triple `u + v = w` is
`q = log w / log radical(u·v·w)`; quality `q > 1` is exactly `radical(uvw) < w`.
So this file establishes that the entire value `cⁿ` strictly dominates the radical
of the `(2,3,n)` product — the quantitative statement that these solutions are also
**ABC-exceptional triples**, the ones the ABC conjecture forbids from being
abundant. It is the `(2,3,n)` counterpart of `BealABCQuality.beal_radical_lt_c`,
and it ties Line 4's `(2,3,n)` Frey/Mordell curve (`BealFrey23`,
`BealFrey23Radical`) back to Line 2's ABC backbone: the same family whose Frey
discriminant is supported only on `{2,3} ∪ primes(c)` is shown here to be
ABC-extreme. It connects to the project's empirical ABC-quality-ceiling program
(`docs/threads/beal/abc-quality-*`), which measures how high `q` climbs over the
`(2,3,n)` family.

## The argument

For a solution `a² + b³ = cⁿ` with `a, b, c ≥ 2` and `n ≥ 6`:

* Each summand is below the value: `a² < cⁿ` and `b³ < cⁿ`.
* Taking real square / cube roots, `a < c^(n/2)` and `b < c^(n/3)` (strict, base
  monotonicity of `Real.rpow`). With `c = c¹` this gives the **strict** product
  bound `a·b·c < c^(n/2 + n/3 + 1)` (`abc_lt_rpow_23`).
* The genus inequality `1/2 + 1/3 + 1/n ≤ 1`, i.e. `n/2 + n/3 + 1 ≤ n`, holds
  exactly for `n ≥ 6` (`exp_sum_le_23`). As `c ≥ 2 > 1`, exponent-monotonicity of
  `rpow` gives `c^(n/2 + n/3 + 1) ≤ cⁿ`. Hence `a·b·c < cⁿ` (`abc_lt_23`).
* Finally `radical(a² b³ cⁿ) = radical(a·b·c) ≤ a·b·c < cⁿ`, the headline
  `radical_lt_23`. (The radical equality is exponent-blind:
  `BealRadical.radical_beal_eq` with `x:=2, y:=3, z:=n`.)

The genus threshold is `n ≥ 6` for `radical < cⁿ` (`1/2+1/3+1/n ≤ 1 ⟺ n ≥ 6`);
the Fermat–Catalan hyperbolic range `1/2+1/3+1/n < 1` needs `n ≥ 7`. We state the
ABC-quality bound at `n ≥ 6`, which is the exact threshold for the radical estimate.

## Contents
* `radical_23_eq` — exponent-blind: `radical(a² b³ cⁿ) = radical(a·b·c)`.
* `abc_lt_23` — the **core inequality** `a·b·c < cⁿ` (for `n ≥ 6`).
* `radical_lt_23` — **headline**: `radical(a² b³ cⁿ) < cⁿ` (ABC-quality `q > 1`).
* `quality_gt_one_23` — the explicit log form `1 < log(cⁿ)/log(radical …)`.

Dependency policy: mathlib4 permitted (user authorization 2026-05-17). Use
`lake env lean BealFrey23Quality.lean` to typecheck.
-/

namespace BealFrey23Quality

open scoped Real

/-! ## 1. The exponent-blind radical identity for the `(2,3,n)` product -/

/-- **Radical equality (exponent-blind).** For nonzero bases `a, b, c` and `n ≠ 0`,
`radical(a² · b³ · cⁿ) = radical(a·b·c)`, with **no coprimality** among `a, b, c`.
This is `BealRadical.radical_beal_eq` specialized to the signature `(2, 3, n)`
(`x := 2`, `y := 3`, `z := n`); the exponents drop out by exponent-blindness of the
radical. -/
theorem radical_23_eq {a b c n : ℕ}
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hn : n ≠ 0) :
    BealRadical.radical (a ^ 2 * b ^ 3 * c ^ n) = BealRadical.radical (a * b * c) :=
  BealRadical.radical_beal_eq ha hb hc (by norm_num) (by norm_num) hn

/-! ## 2. A base is bounded by a fractional power of `c`

The generalized-root bound: from `aᵏ < cⁿ` with `k ≥ 1` we get `a < c^(n/k)` over
`ℝ`. Mirrors `BealABCQuality.base_lt_rpow`. -/

/-- **Base bound.** If `1 ≤ k`, `1 ≤ a`, `2 ≤ c`, and `aᵏ < cⁿ`, then over `ℝ`
`a < c^(n/k)`. (Apply `t ↦ t^(1/k)`, strictly monotone on nonneg reals, to
`aᵏ < cⁿ`.) -/
theorem base_lt_rpow {a c k n : ℕ}
    (hk : 1 ≤ k) (ha : 1 ≤ a) (hc : 2 ≤ c) (hpow : a ^ k < c ^ n) :
    (a : ℝ) < (c : ℝ) ^ ((n : ℝ) / k) := by
  have haR0 : (0 : ℝ) ≤ (a : ℝ) := by positivity
  have hcR0 : (0 : ℝ) ≤ (c : ℝ) := by positivity
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hpow' : (a : ℝ) ^ (k : ℝ) < (c : ℝ) ^ (n : ℝ) := by
    rw [Real.rpow_natCast, Real.rpow_natCast]
    exact_mod_cast hpow
  have hmono := Real.rpow_lt_rpow (z := (1 / k : ℝ)) (by positivity) hpow' (by positivity)
  rw [← Real.rpow_mul haR0, ← Real.rpow_mul hcR0] at hmono
  rw [show (k : ℝ) * (1 / k) = 1 by field_simp, Real.rpow_one] at hmono
  rw [show (n : ℝ) * (1 / k) = (n : ℝ) / k by ring] at hmono
  exact hmono

/-! ## 3. The product of bases is below a fractional power of `c` -/

/-- **Product bound.** For `a, b ≥ 1`, `c ≥ 2`, and `a² < cⁿ`, `b³ < cⁿ`, the
product of bases satisfies `a·b·c < c^(n/2 + n/3 + 1)` over `ℝ` (strict, from the
strict base bounds). Mirrors `BealABCQuality.abc_lt_rpow` with `x := 2, y := 3`. -/
theorem abc_lt_rpow_23 {a b c n : ℕ}
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 2 ≤ c)
    (ha2 : a ^ 2 < c ^ n) (hb3 : b ^ 3 < c ^ n) :
    (a * b * c : ℝ) < (c : ℝ) ^ ((n : ℝ) / 2 + (n : ℝ) / 3 + 1) := by
  have hcR1 : (1 : ℝ) ≤ (c : ℝ) := by exact_mod_cast (by omega : 1 ≤ c)
  have hcpos : (0 : ℝ) < (c : ℝ) := by linarith
  have hbR1 : (1 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have halt : (a : ℝ) < (c : ℝ) ^ ((n : ℝ) / 2) := by
    have := base_lt_rpow (k := 2) (by norm_num) ha hc ha2
    simpa using this
  have hblt : (b : ℝ) < (c : ℝ) ^ ((n : ℝ) / 3) := by
    have := base_lt_rpow (k := 3) (by norm_num) hb hc hb3
    simpa using this
  -- a·b < c^(n/2) · c^(n/3)
  have hab : (a : ℝ) * (b : ℝ) < (c : ℝ) ^ ((n : ℝ) / 2) * (c : ℝ) ^ ((n : ℝ) / 3) := by
    calc (a : ℝ) * (b : ℝ)
        < (c : ℝ) ^ ((n : ℝ) / 2) * (b : ℝ) :=
          mul_lt_mul_of_pos_right halt (by linarith)
      _ ≤ (c : ℝ) ^ ((n : ℝ) / 2) * (c : ℝ) ^ ((n : ℝ) / 3) :=
          mul_le_mul_of_nonneg_left (le_of_lt hblt) (le_of_lt (Real.rpow_pos_of_pos hcpos _))
  have habc : (a : ℝ) * (b : ℝ) * (c : ℝ)
      < (c : ℝ) ^ ((n : ℝ) / 2) * (c : ℝ) ^ ((n : ℝ) / 3) * (c : ℝ) :=
    mul_lt_mul_of_pos_right hab hcpos
  have hrhs : (c : ℝ) ^ ((n : ℝ) / 2) * (c : ℝ) ^ ((n : ℝ) / 3) * (c : ℝ)
      = (c : ℝ) ^ ((n : ℝ) / 2 + (n : ℝ) / 3 + 1) := by
    nth_rewrite 3 [← Real.rpow_one (c : ℝ)]
    rw [← Real.rpow_add hcpos, ← Real.rpow_add hcpos]
  calc (a * b * c : ℝ) = (a : ℝ) * (b : ℝ) * (c : ℝ) := by norm_cast
    _ < (c : ℝ) ^ ((n : ℝ) / 2) * (c : ℝ) ^ ((n : ℝ) / 3) * (c : ℝ) := habc
    _ = (c : ℝ) ^ ((n : ℝ) / 2 + (n : ℝ) / 3 + 1) := hrhs

/-! ## 4. The genus inequality in real fractional form -/

/-- **Genus inequality, real form.** For `n ≥ 6`, the product exponent is bounded
by `n`: `n/2 + n/3 + 1 ≤ n` over `ℝ`. This is exactly `1/2 + 1/3 + 1/n ≤ 1`, whose
threshold is `n ≥ 6` (the spherical-to-hyperbolic boundary of signature `(2,3,n)`).
-/
theorem exp_sum_le_23 {n : ℕ} (hn : 6 ≤ n) :
    (n : ℝ) / 2 + (n : ℝ) / 3 + 1 ≤ (n : ℝ) := by
  have hnR : (6 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  -- n/2 + n/3 + 1 = 5n/6 + 1 ≤ n ⟺ 6 ≤ n.
  nlinarith [hnR]

/-! ## 5. Core inequality: the product of bases is below the value -/

/-- **Core inequality.** Every `(2,3,n)` solution `a² + b³ = cⁿ` with `a, b, c ≥ 2`
and `n ≥ 6` satisfies, over `ℕ`,

  `a·b·c < cⁿ`.

The product of the *bases* is strictly below the value `cⁿ`. Proof: over `ℝ`,
`a·b·c < c^(n/2 + n/3 + 1) ≤ cⁿ` by `abc_lt_rpow_23` and `exp_sum_le_23`; cast back
to `ℕ`. -/
theorem abc_lt_23 {a b c n : ℕ}
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c) (hn : 6 ≤ n)
    (hab : a ^ 2 < c ^ n) (hbb : b ^ 3 < c ^ n) :
    a * b * c < c ^ n := by
  have hprod : (a * b * c : ℝ) < (c : ℝ) ^ ((n : ℝ) / 2 + (n : ℝ) / 3 + 1) :=
    abc_lt_rpow_23 (by omega) (by omega) hc hab hbb
  have hcR1 : (1 : ℝ) ≤ (c : ℝ) := by exact_mod_cast (by omega : 1 ≤ c)
  have hmono : (c : ℝ) ^ ((n : ℝ) / 2 + (n : ℝ) / 3 + 1) ≤ (c : ℝ) ^ (n : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hcR1 (exp_sum_le_23 hn)
  have hCn_rpow : (c : ℝ) ^ (n : ℝ) = ((c ^ n : ℕ) : ℝ) := by
    rw [Real.rpow_natCast]; push_cast; rfl
  have hreal : (a * b * c : ℝ) < ((c ^ n : ℕ) : ℝ) := by
    rw [← hCn_rpow]; exact lt_of_lt_of_le hprod hmono
  have : ((a * b * c : ℕ) : ℝ) < ((c ^ n : ℕ) : ℝ) := by push_cast at hreal ⊢; linarith
  exact_mod_cast this

/-! ## 6. Headline: the ABC-quality lower bound for the `(2,3,n)` family -/

/-- **Headline — the `(2,3,n)` ABC-quality lower bound.** Every solution
`a² + b³ = cⁿ` with `a, b, c ≥ 2`, `n ≥ 6`, and each summand below the value
(`a² < cⁿ`, `b³ < cⁿ`) satisfies

  `radical(a² · b³ · cⁿ) < cⁿ`,

i.e. ABC-quality `q = log(cⁿ) / log(radical(a² b³ cⁿ)) > 1`. The radical of the
`(2,3,n)` product equals `radical(a·b·c) ≤ a·b·c` (`radical_23_eq`,
`BealRadical.radical_le_self`), which the core inequality `abc_lt_23` places
strictly below the value `cⁿ`. So **every** such `(2,3,n)` solution is an ABC triple
of quality strictly above `1` — an ABC-exceptional triple, just like the cube/Beal
solutions of `BealABCQuality.beal_radical_lt_c`. The hypotheses `a² < cⁿ`, `b³ < cⁿ`
hold automatically for any genuine solution with `a, b ≥ 2` (each summand is a
proper part of the sum); they are stated explicitly to keep the bound self-contained.
-/
theorem radical_lt_23 {a b c : ℕ} {n : ℕ}
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c) (hn : 6 ≤ n)
    (hab : a ^ 2 < c ^ n) (hbb : b ^ 3 < c ^ n)
    (h : a ^ 2 + b ^ 3 = c ^ n) :
    BealRadical.radical (a ^ 2 * b ^ 3 * c ^ n) < c ^ n := by
  have hrad_eq : BealRadical.radical (a ^ 2 * b ^ 3 * c ^ n)
      = BealRadical.radical (a * b * c) :=
    radical_23_eq (by omega) (by omega) (by omega) (by omega)
  have hABCpos : 0 < a * b * c := by positivity
  have hrad_le : BealRadical.radical (a * b * c) ≤ a * b * c :=
    BealRadical.radical_le_self hABCpos
  have hlt : a * b * c < c ^ n := abc_lt_23 ha hb hc hn hab hbb
  calc BealRadical.radical (a ^ 2 * b ^ 3 * c ^ n)
      = BealRadical.radical (a * b * c) := hrad_eq
    _ ≤ a * b * c := hrad_le
    _ < c ^ n := hlt

/-! ## 7. The explicit log form: quality `> 1` -/

/-- The radical of a `(2,3,n)` product is at least `2`: `2 ≤ radical(a² b³ cⁿ)`,
for `a, b, c ≥ 2` and `n ≥ 1`. Since `a ≥ 2`, `a` has a prime factor, which divides
`a² ∣ a² b³ cⁿ`, hence lies in the prime-factor set of the product; that prime is
`≥ 2` and divides the radical. -/
theorem two_le_radical_23 {a b c n : ℕ}
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c) (hn : 1 ≤ n) :
    2 ≤ BealRadical.radical (a ^ 2 * b ^ 3 * c ^ n) := by
  obtain ⟨p, hp, hpa⟩ := (Nat.exists_prime_and_dvd (by omega : a ≠ 1))
  have hprod : a ^ 2 * b ^ 3 * c ^ n ≠ 0 := by positivity
  have hpdvd : p ∣ a ^ 2 * b ^ 3 * c ^ n :=
    Dvd.dvd.mul_right (Dvd.dvd.mul_right (hpa.trans (dvd_pow_self a (by norm_num))) _) _
  have hmem : p ∈ (a ^ 2 * b ^ 3 * c ^ n).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hp, hpdvd, hprod⟩
  have hpdvdrad : p ∣ BealRadical.radical (a ^ 2 * b ^ 3 * c ^ n) :=
    Finset.dvd_prod_of_mem _ hmem
  have hradpos : 0 < BealRadical.radical (a ^ 2 * b ^ 3 * c ^ n) :=
    BealRadical.radical_pos (Nat.pos_of_ne_zero hprod)
  exact le_trans hp.two_le (Nat.le_of_dvd hradpos hpdvdrad)

/-- **Quality `> 1`, the explicit log form.** Every `(2,3,n)` solution
`a² + b³ = cⁿ` (with `a, b, c ≥ 2`, `n ≥ 6`, and each summand below the value) has
ABC-quality strictly above `1`:

  `1 < log(cⁿ) / log(radical(a² · b³ · cⁿ))`.

Both `radical(…)` and `cⁿ` exceed `1`, so their logs are positive, and
`radical(…) < cⁿ` (the headline `radical_lt_23`) gives `log(radical) < log(cⁿ)`,
whence the quotient exceeds `1`. -/
theorem quality_gt_one_23 {a b c : ℕ} {n : ℕ}
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c) (hn : 6 ≤ n)
    (hab : a ^ 2 < c ^ n) (hbb : b ^ 3 < c ^ n)
    (h : a ^ 2 + b ^ 3 = c ^ n) :
    1 < Real.log ((c ^ n : ℕ) : ℝ)
          / Real.log (BealRadical.radical (a ^ 2 * b ^ 3 * c ^ n) : ℝ) := by
  have hradlt : BealRadical.radical (a ^ 2 * b ^ 3 * c ^ n) < c ^ n :=
    radical_lt_23 ha hb hc hn hab hbb h
  have hrad2 : 2 ≤ BealRadical.radical (a ^ 2 * b ^ 3 * c ^ n) :=
    two_le_radical_23 ha hb hc (by omega)
  have hradR2 : (2 : ℝ) ≤ (BealRadical.radical (a ^ 2 * b ^ 3 * c ^ n) : ℝ) := by
    exact_mod_cast hrad2
  have hradR1 : (1 : ℝ) < (BealRadical.radical (a ^ 2 * b ^ 3 * c ^ n) : ℝ) := by linarith
  have hcastlt : (BealRadical.radical (a ^ 2 * b ^ 3 * c ^ n) : ℝ) < ((c ^ n : ℕ) : ℝ) := by
    exact_mod_cast hradlt
  have hlogden : 0 < Real.log (BealRadical.radical (a ^ 2 * b ^ 3 * c ^ n) : ℝ) :=
    Real.log_pos hradR1
  have hlognum : Real.log (BealRadical.radical (a ^ 2 * b ^ 3 * c ^ n) : ℝ)
      < Real.log ((c ^ n : ℕ) : ℝ) :=
    Real.log_lt_log (by linarith) hcastlt
  rw [lt_div_iff₀ hlogden, one_mul]
  exact hlognum

end BealFrey23Quality
