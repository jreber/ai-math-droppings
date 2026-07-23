import Propositio.Beal.Radical

/-!
# The Frey discriminant has radical `2·rad(A·B·C)` (Lean 4 / mathlib)

This file connects the **Hellegouarch–Frey curve** of `BealFreyGeneral.lean`
(Line 4 of the program) to the **integer radical** of `BealRadical.lean`
(Line 2) by proving the small-conductor / bad-prime-support fact that powers the
modular method.

The general Frey curve attached to a putative Beal solution `A^x + B^y = C^z`
has discriminant (over ℚ)

  `Δ = 16·(A^x·B^y·C^z)²`.

The arithmetically meaningful object is the integer `Δ_int := 16·(A^x B^y C^z)²`,
and its radical governs the **bad primes** of the curve (those at which `E` has
bad reduction), which in turn carry the support of the conductor. The headline:

  `rad(16·(A^x B^y C^z)²) = 2·rad(A·B·C)`   (when `2 ∤ A·B·C`),

equivalently the prime support is `{2} ∪ primeFactors(A·B·C)`. The radical is
**exponent-blind and squarefree-kernel**, so the `16 = 2⁴` and the squaring and
all the Beal exponents collapse: only the bare primes `2`, and the primes
dividing `A·B·C`, survive.

## Why this is the input to the modular method

This **small conductor support** is precisely what Ribet level-lowering
consumes: the weight-`2` newform attached to `E` (via modularity) has level
dividing a power of `2` times `rad(A·B·C)`. The level-lowering theorem strips the
primes dividing `A·B·C` (which divide the discriminant to high Beal powers but
the conductor only to first order), forcing a newform of impossibly small level —
the contradiction that finishes the modular argument. The fact that the bad-prime
support is *exactly* `{2} ∪ primes(A·B·C)`, with no contribution from the huge
exponents `x, y, z`, is what makes this collapse possible.

## Contents

* `radical_two` — `rad(2) = 2`.
* `radical_two_pow_mul_sq` — `rad(16·N²) = rad(2·N)`: the radical is square- and
  `2⁴`-blind.
* `frey_bad_primes` — the bad-prime support statement:
  `(16·(A^x B^y C^z)²).primeFactors = insert 2 (A·B·C).primeFactors`.
* `frey_disc_radical` — **headline**: `rad(16·(A^x B^y C^z)²) = 2·rad(A·B·C)`.

Match the house style of `BealRadical.lean` / `BealEisenstein.lean`.
-/

namespace BealFreyRadical

open BealRadical Finset

/-! ## 1. The radical of `2` -/

/-- `rad(2) = 2`: the radical of a prime is itself, since `primeFactors 2 = {2}`. -/
theorem radical_two : radical 2 = 2 := by
  unfold radical
  rw [Nat.Prime.primeFactors (by norm_num : Nat.Prime 2)]
  simp

/-! ## 2. The radical is `2⁴`- and square-blind

`rad(16·N²) = rad(2·N)`: the constant `16 = 2⁴` and the squaring contribute only
their bare prime `2` and the primes of `N`, exactly the prime support of `2·N`.
This is the exponent-blindness of `primeFactors` applied to the `2`-part and to
`N`. -/

/-- `rad(16·N²) = rad(2·N)` for `N ≠ 0`. Both sides have prime support
`{2} ∪ primeFactors N`: on the left from `16 = 2⁴` (whose primeFactors is `{2}`)
and `N²` (same primeFactors as `N`); on the right from `2` and `N`. The radical,
a product over the prime support, therefore agrees. -/
theorem radical_two_pow_mul_sq {N : ℕ} (hN : N ≠ 0) :
    radical (16 * N ^ 2) = radical (2 * N) := by
  unfold radical
  have h16 : (16 : ℕ) = 2 ^ 4 := by norm_num
  rw [h16,
    Nat.primeFactors_mul (by positivity) (pow_ne_zero 2 hN),
    Nat.primeFactors_mul (by norm_num : (2 : ℕ) ≠ 0) hN,
    Nat.primeFactors_pow 2 (by norm_num : (4 : ℕ) ≠ 0),
    Nat.primeFactors_pow N (by norm_num : (2 : ℕ) ≠ 0)]

/-! ## 3. The bad-prime support of the Frey discriminant

The cleaner "conductor support ⊆ {2} ∪ primes(ABC)" statement: the prime support
of `Δ_int = 16·(A^x B^y C^z)²` is exactly `insert 2 (primeFactors(ABC))`. When
`2 ∤ A·B·C` the inserted `2` is genuinely new, but the equation holds regardless
of disjointness. -/

/-- **Bad-prime support.** The prime support of the Frey discriminant
`Δ_int = 16·(A^x B^y C^z)²` is exactly `{2} ∪ primeFactors(A·B·C)`:

  `(16·(A^x B^y C^z)²).primeFactors = insert 2 (A·B·C).primeFactors`.

The `16 = 2⁴` contributes the bare prime `2`; the squaring and the Beal exponents
`x, y, z` all drop out by exponent-blindness of `primeFactors`
(`primeFactors_beal_eq`), leaving the primes of `A·B·C`. No coprimality is needed
(the equation holds even when `2 ∣ A·B·C`, in which case the `insert` is
redundant). This is the support that the conductor of `E` is built on. -/
theorem frey_bad_primes {A B C x y z : ℕ}
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) :
    (16 * (A ^ x * B ^ y * C ^ z) ^ 2).primeFactors
      = insert 2 (A * B * C).primeFactors := by
  have hN : A ^ x * B ^ y * C ^ z ≠ 0 :=
    mul_ne_zero (mul_ne_zero (pow_ne_zero _ hA) (pow_ne_zero _ hB)) (pow_ne_zero _ hC)
  have h16 : (16 : ℕ) = 2 ^ 4 := by norm_num
  rw [h16,
    Nat.primeFactors_mul (by positivity) (pow_ne_zero 2 hN),
    Nat.primeFactors_pow 2 (by norm_num : (4 : ℕ) ≠ 0),
    Nat.primeFactors_pow _ (by norm_num : (2 : ℕ) ≠ 0),
    Nat.Prime.primeFactors (by norm_num : Nat.Prime 2),
    primeFactors_beal_eq hA hB hC hx hy hz]
  rw [Finset.insert_eq]

/-! ## 4. The headline: the Frey discriminant radical -/

/-- **Headline.** The Frey discriminant `Δ_int = 16·(A^x B^y C^z)²` has radical

  `rad(16·(A^x B^y C^z)²) = 2·rad(A·B·C)`

whenever `2 ∤ A·B·C` (and the bases / exponents are nonzero). Its bad primes are
*exactly* `2` and the primes dividing `A·B·C`.

Proof. `radical_two_pow_mul_sq` collapses `rad(16·N²)` to `rad(2·N)` with
`N := A^x B^y C^z`. From `2 ∤ A·B·C` we get `2 ∤ A, B, C`, hence (as `2` is
prime) `Coprime 2 A, 2 B, 2 C`, and so `Coprime 2 N`; `radical_coprime_mul`
splits `rad(2·N) = rad 2 · rad N`. Finally `rad 2 = 2` (`radical_two`) and
`rad N = rad(A·B·C)` (`radical_beal_eq`, the exponent-blindness headline of
`BealRadical`).

This is the small-conductor support that Ribet level-lowering consumes — the
newform level divides `2^? · rad(A·B·C)` — which is why the modular method can
finish. -/
theorem frey_disc_radical {A B C x y z : ℕ}
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0)
    (h2 : ¬ 2 ∣ (A * B * C)) :
    radical (16 * (A ^ x * B ^ y * C ^ z) ^ 2) = 2 * radical (A * B * C) := by
  have hN : A ^ x * B ^ y * C ^ z ≠ 0 :=
    mul_ne_zero (mul_ne_zero (pow_ne_zero _ hA) (pow_ne_zero _ hB)) (pow_ne_zero _ hC)
  -- `2 ∤ A·B·C` ⟹ `2 ∤ A, B, C` ⟹ `Coprime 2 A, 2 B, 2 C`.
  have hp2 : Nat.Prime 2 := by norm_num
  have hnAB : ¬ 2 ∣ (A * B) := fun hd => h2 (hd.mul_right C)
  have hnA : ¬ 2 ∣ A := fun hd => hnAB (hd.mul_right B)
  have hnB : ¬ 2 ∣ B := fun hd => hnAB (Dvd.dvd.mul_left hd A)
  have hnC : ¬ 2 ∣ C := fun hd => h2 (Dvd.dvd.mul_left hd (A * B))
  have cA : Nat.Coprime 2 A := (hp2.coprime_iff_not_dvd).mpr hnA
  have cB : Nat.Coprime 2 B := (hp2.coprime_iff_not_dvd).mpr hnB
  have cC : Nat.Coprime 2 C := (hp2.coprime_iff_not_dvd).mpr hnC
  have cN : Nat.Coprime 2 (A ^ x * B ^ y * C ^ z) :=
    ((cA.pow_right x).mul_right (cB.pow_right y)).mul_right (cC.pow_right z)
  -- Collapse `rad(16·N²) = rad(2·N) = rad 2 · rad N = 2 · rad(ABC)`.
  rw [radical_two_pow_mul_sq hN, radical_coprime_mul cN, radical_two,
    radical_beal_eq hA hB hC hx hy hz]

end BealFreyRadical
