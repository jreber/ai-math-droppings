import Propositio.Beal.Radical
import Propositio.Beal.RadicalAPI

/-!
# The (2,3,n) Frey discriminant has radical `6·rad(c)` (Lean 4 / mathlib)

This file connects the **signature-`(2,3,n)` Frey curve** of `BealFrey23.lean`
(Line 4 of the program) to the **integer radical** of `BealRadical.lean`
(Line 2) by proving the small-conductor / bad-prime-support fact that powers the
modular method for the most-studied generalized-Fermat signature.

For a putative solution `a² + b³ = cⁿ` the Hellegouarch–Frey curve of signature
`(2,3,n)` has discriminant (over ℚ)

  `Δ = −1728·cⁿ = −2⁶·3³·cⁿ`.

The arithmetically meaningful object is the integer `Δ_int := 1728·cⁿ = 2⁶·3³·cⁿ`,
and its radical governs the **bad primes** of the curve (those at which `E` has bad
reduction), which in turn carry the support of the conductor. The headline:

  `rad(1728·cⁿ) = 6·rad(c)`   (when `gcd(6, c) = 1`),

equivalently the prime support is `{2, 3} ∪ primeFactors(c)`. The radical is
**exponent-blind and squarefree-kernel**, so the `1728 = 2⁶·3³` and the Beal
exponent `n` collapse: only the bare primes `2`, `3`, and the primes dividing `c`
survive.

## Why this is the input to the modular method

This **small conductor support** is precisely what Ribet level-lowering consumes:
the weight-`2` newform attached to `E` (via modularity) has level dividing a power
of `2·3` times `rad(c)`. The level-lowering theorem strips the primes dividing `c`
(which divide the discriminant to high Beal power `n` but the conductor only to
first order), forcing a newform of impossibly small level — the contradiction that
finishes the modular argument. The fact that the bad-prime support is *exactly*
`{2, 3} ∪ primes(c)`, with no contribution from the huge exponent `n`, is what
makes this collapse possible.

This parallels `BealFreyRadical.lean` for the cube-sum (signature-`(x,y,z)`)
curve and connects `BealFrey23.lean` (Line 4) to `BealRadical.lean` (Line 2).

## Contents

* `radical_six` — `rad(6) = 6`.
* `radical_1728_mul_pow` — `rad(1728·cⁿ) = rad(6·c)`: the radical is `2⁶·3³`- and
  exponent-blind.
* `frey23_disc_radical` — **headline**: `rad(1728·cⁿ) = 6·rad(c)` (`gcd(6,c)=1`).
* `frey23_bad_primes` — the bad-prime support statement:
  `(1728·cⁿ).primeFactors = insert 2 (insert 3 c.primeFactors)`.

Match the house style of `BealFreyRadical.lean` / `BealRadical.lean`.
-/

namespace BealFrey23Radical

open BealRadical Finset

/-! ## 1. The radical of `6` -/

/-- `rad(6) = 6`: `6 = 2·3` is squarefree, so its radical is itself. Split off the
coprime factors `2` and `3` with `radical_coprime_mul`, then evaluate each prime
radical with `radical_prime`. -/
theorem radical_six : radical 6 = 6 := by
  have h6 : (6 : ℕ) = 2 * 3 := by norm_num
  rw [h6, radical_coprime_mul (by norm_num : Nat.Coprime 2 3),
    BealRadicalAPI.radical_prime (by norm_num : Nat.Prime 2),
    BealRadicalAPI.radical_prime (by norm_num : Nat.Prime 3)]

/-! ## 2. The radical is `2⁶·3³`- and exponent-blind

`rad(1728·cⁿ) = rad(6·c)`: the constant `1728 = 2⁶·3³` and the power `cⁿ`
contribute only their bare primes `{2, 3}` and the primes of `c`, exactly the
prime support of `6·c`. This is the exponent-blindness of `primeFactors` applied
to the `{2,3}`-part and to `c`. -/

/-- `rad(1728·cⁿ) = rad(6·c)` for `n ≠ 0`, `c ≠ 0`. Both sides have prime support
`{2, 3} ∪ primeFactors c`: on the left from `1728 = 2⁶·3³` (whose primeFactors is
`{2,3}`) and `cⁿ` (same primeFactors as `c`); on the right from `6 = 2·3` and `c`.
The radical, a product over the prime support, therefore agrees. -/
theorem radical_1728_mul_pow {c n : ℕ} (hn : n ≠ 0) (hc : c ≠ 0) :
    radical (1728 * c ^ n) = radical (6 * c) := by
  unfold radical
  have h1728 : (1728 : ℕ) = 2 ^ 6 * 3 ^ 3 := by norm_num
  have h6 : (6 : ℕ) = 2 * 3 := by norm_num
  rw [h1728, h6,
    Nat.primeFactors_mul (by positivity) (pow_ne_zero n hc),
    Nat.primeFactors_mul (by positivity) (by positivity),
    Nat.primeFactors_pow 2 (by norm_num : (6 : ℕ) ≠ 0),
    Nat.primeFactors_pow 3 (by norm_num : (3 : ℕ) ≠ 0),
    Nat.primeFactors_pow c hn,
    Nat.primeFactors_mul (by positivity) hc,
    Nat.primeFactors_mul (by norm_num : (2 : ℕ) ≠ 0) (by norm_num : (3 : ℕ) ≠ 0)]

/-! ## 3. The headline: the `(2,3,n)` Frey discriminant radical -/

/-- **Headline.** The signature-`(2,3,n)` Frey discriminant
`Δ_int = 1728·cⁿ = 2⁶·3³·cⁿ` has radical

  `rad(1728·cⁿ) = 6·rad(c)`

whenever `gcd(6, c) = 1` (and `c`, `n` nonzero). Its bad primes are *exactly* `2`,
`3`, and the primes dividing `c`.

Proof. `radical_1728_mul_pow` collapses `rad(1728·cⁿ)` to `rad(6·c)`. From
`gcd(6, c) = 1`, `radical_coprime_mul` splits `rad(6·c) = rad 6 · rad c`. Finally
`rad 6 = 6` (`radical_six`).

This is the small-conductor support that Ribet level-lowering consumes — the
newform level divides `2^?·3^? · rad(c)` — which is why the modular method can
finish for the `(2,3,n)` signature. -/
theorem frey23_disc_radical {c n : ℕ} (hn : n ≠ 0) (hc : c ≠ 0)
    (h6 : Nat.Coprime 6 c) :
    radical (1728 * c ^ n) = 6 * radical c := by
  rw [radical_1728_mul_pow hn hc, radical_coprime_mul h6, radical_six]

/-! ## 4. The bad-prime support of the `(2,3,n)` Frey discriminant

The cleaner "conductor support ⊆ {2,3} ∪ primes(c)" statement: the prime support
of `Δ_int = 1728·cⁿ` is exactly `insert 2 (insert 3 (primeFactors c))`. When
`gcd(6, c) = 1` the inserted `2, 3` are genuinely new, but the equation holds
regardless of disjointness. -/

/-- **Bad-prime support.** The prime support of the `(2,3,n)` Frey discriminant
`Δ_int = 1728·cⁿ` is exactly `{2, 3} ∪ primeFactors(c)`:

  `(1728·cⁿ).primeFactors = insert 2 (insert 3 c.primeFactors)`.

The `1728 = 2⁶·3³` contributes the bare primes `2, 3`; the Beal exponent `n` drops
out by exponent-blindness of `primeFactors`. No coprimality is needed (the equation
holds even when `2` or `3` divides `c`, in which case the `insert`s are redundant).
This is the support that the conductor of `E` is built on. -/
theorem frey23_bad_primes {c n : ℕ} (hn : n ≠ 0) (hc : c ≠ 0) :
    (1728 * c ^ n).primeFactors = insert 2 (insert 3 c.primeFactors) := by
  have h1728 : (1728 : ℕ) = 2 ^ 6 * 3 ^ 3 := by norm_num
  rw [h1728,
    Nat.primeFactors_mul (by positivity) (pow_ne_zero n hc),
    Nat.primeFactors_mul (by positivity) (by positivity),
    Nat.primeFactors_pow 2 (by norm_num : (6 : ℕ) ≠ 0),
    Nat.primeFactors_pow 3 (by norm_num : (3 : ℕ) ≠ 0),
    Nat.primeFactors_pow c hn,
    Nat.Prime.primeFactors (by norm_num : Nat.Prime 2),
    Nat.Prime.primeFactors (by norm_num : Nat.Prime 3)]
  rw [Finset.insert_eq, Finset.insert_eq, Finset.union_assoc]

end BealFrey23Radical
