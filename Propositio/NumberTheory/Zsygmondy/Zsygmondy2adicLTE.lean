/-
# Lifting-the-Exponent (LTE) lemma for the prime `p = 2`

The 2-adic valuation engine underlying Zsygmondy's primitive-prime-divisor
theorem.  For odd naturals `a > b ≥ 1`:

  * `n` odd   ⟹  `v₂(aⁿ − bⁿ) = v₂(a − b)`
  * `n` even  ⟹  `v₂(aⁿ − bⁿ) = v₂(a − b) + v₂(a + b) + v₂(n) − 1`

where `v₂ = padicValNat 2` is the 2-adic valuation.

These are faithful repackagings of mathlib's
`padicValNat.pow_two_sub_pow` (even case) and
`emultiplicity_pow_sub_pow_of_prime` instantiated at the prime `2`
(odd case), stated in the clean natural-number valuation form.
-/
import Mathlib.NumberTheory.Multiplicity
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.RingTheory.Multiplicity

open scoped Classical

namespace Zsygmondy2adicLTE

/-- **LTE for `p = 2`, odd exponent.**  For odd naturals `a > b` and odd `n`,
the 2-adic valuation of `aⁿ − bⁿ` equals that of `a − b`. -/
theorem v2_pow_sub_pow_odd {a b n : ℕ} (ha : Odd a) (hb : Odd b) (hab : b < a)
    (hn : Odd n) :
    padicValNat 2 (a ^ n - b ^ n) = padicValNat 2 (a - b) := by
  have _h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn0 : n ≠ 0 := by have := Nat.odd_iff.mp hn; omega
  have hpow : b ^ n < a ^ n := Nat.pow_lt_pow_left hab hn0
  -- the 2-adic data, transported to `ℤ`
  have hxy : (2 : ℤ) ∣ (a : ℤ) - b := by
    have h1 := Nat.odd_iff.mp ha; have h2 := Nat.odd_iff.mp hb; omega
  have hx : ¬ (2 : ℤ) ∣ (a : ℤ) := by
    have h1 := Nat.odd_iff.mp ha; omega
  have hni : ¬ (2 : ℤ) ∣ (n : ℤ) := by
    have := Nat.odd_iff.mp hn; omega
  -- pass to `ℕ∞`-valued `emultiplicity`, then to `ℤ`, and apply the LTE engine
  rw [← Nat.cast_inj (R := ℕ∞),
      padicValNat_eq_emultiplicity (Nat.sub_ne_zero_of_lt hpow),
      padicValNat_eq_emultiplicity (Nat.sub_ne_zero_of_lt hab),
      ← Int.natCast_emultiplicity, ← Int.natCast_emultiplicity,
      Nat.cast_sub hpow.le, Nat.cast_sub hab.le]
  push_cast
  exact emultiplicity_pow_sub_pow_of_prime Int.prime_two hxy hx hni

/-- **LTE for `p = 2`, even exponent.**  For odd naturals `a > b` and even `n ≠ 0`,
`v₂(aⁿ − bⁿ) = v₂(a − b) + v₂(a + b) + v₂(n) − 1`. -/
theorem v2_pow_sub_pow_even {a b n : ℕ} (ha : Odd a) (hb : Odd b) (hab : b < a)
    (hn : n ≠ 0) (hne : Even n) :
    padicValNat 2 (a ^ n - b ^ n) =
      padicValNat 2 (a - b) + padicValNat 2 (a + b) + padicValNat 2 n - 1 := by
  have hxy : 2 ∣ a - b := by
    have h1 := Nat.odd_iff.mp ha; have h2 := Nat.odd_iff.mp hb; omega
  have hx : ¬ 2 ∣ a := by have := Nat.odd_iff.mp ha; omega
  -- mathlib's `+ 1` form of LTE-2 (even case)
  have hkey := padicValNat.pow_two_sub_pow hab hxy hx hn hne
  omega

end Zsygmondy2adicLTE
