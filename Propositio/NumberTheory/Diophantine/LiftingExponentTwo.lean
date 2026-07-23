/-
# Lifting the Exponent at p = 2, in padicValNat (v₂) form over ℕ

First brick of the Zsygmondy program (queue item conj-2026-06-29-006).

For odd naturals `a > b` and `v₂ = padicValNat 2`:

* `n` even, `n ≠ 0`:  `v₂ (a^n - b^n) = v₂ (a - b) + v₂ (a + b) + v₂ n - 1`
* `n` odd:            `v₂ (a^n - b^n) = v₂ (a - b)`

Subtraction is ℕ-subtraction; it is honest because `b < a` gives `b^n < a^n`,
and in the even case the right side genuinely has `v₂ (a-b) + v₂ (a+b) + v₂ n ≥ 1`
(indeed `≥ 3`), so the `- 1` never truncates.

mathlib already contains the LTE core:
* even case: `padicValNat.pow_two_sub_pow` (stated with `+ 1` on the left);
* odd case: derived here from `emultiplicity_pow_sub_pow_of_prime` over ℤ
  (the geometric-sum factor is odd when `n` is odd and `a, b` are odd).
This file translates both into the clean v₂ arithmetic form needed downstream.
-/
import Mathlib.NumberTheory.Multiplicity

namespace LiftingExponentTwo

/-- **LTE at 2, odd exponent**: for odd naturals `b < a` and odd `n`,
`v₂ (a^n - b^n) = v₂ (a - b)`. -/
theorem padicValNat_two_pow_sub_pow_of_odd {a b : ℕ} (hba : b < a)
    (ha : Odd a) (hb : Odd b) {n : ℕ} (hn : Odd n) :
    padicValNat 2 (a ^ n - b ^ n) = padicValNat 2 (a - b) := by
  have ha1 : a % 2 = 1 := Nat.odd_iff.mp ha
  have hb1 : b % 2 = 1 := Nat.odd_iff.mp hb
  have hn1 : n % 2 = 1 := Nat.odd_iff.mp hn
  have hn0 : n ≠ 0 := by omega
  have hpow : b ^ n < a ^ n := Nat.pow_lt_pow_left hba hn0
  -- the three hypotheses of `emultiplicity_pow_sub_pow_of_prime` over ℤ
  have hxy : (2 : ℤ) ∣ (a : ℤ) - b := by omega
  have hx : ¬(2 : ℤ) ∣ (a : ℤ) := by omega
  have hn2 : ¬(2 : ℤ) ∣ (n : ℤ) := by omega
  have key : emultiplicity (2 : ℤ) ((a : ℤ) ^ n - (b : ℤ) ^ n)
      = emultiplicity (2 : ℤ) ((a : ℤ) - b) :=
    emultiplicity_pow_sub_pow_of_prime Int.prime_two hxy hx hn2
  -- transfer ℤ-emultiplicity back to ℕ-emultiplicity
  have e1 : ((a ^ n - b ^ n : ℕ) : ℤ) = (a : ℤ) ^ n - (b : ℤ) ^ n := by
    rw [Int.ofNat_sub hpow.le]; push_cast; ring
  have e2 : ((a - b : ℕ) : ℤ) = (a : ℤ) - b := Int.ofNat_sub hba.le
  rw [← e1, ← e2, show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num,
    Int.natCast_emultiplicity, Int.natCast_emultiplicity] at key
  -- and ℕ-emultiplicity to padicValNat
  have h1 : a ^ n - b ^ n ≠ 0 := Nat.sub_ne_zero_of_lt hpow
  have h2 : a - b ≠ 0 := Nat.sub_ne_zero_of_lt hba
  rw [← Nat.cast_inj (R := ℕ∞), padicValNat_eq_emultiplicity h1,
    padicValNat_eq_emultiplicity h2]
  exact key

/-- **LTE at 2, even exponent**: for odd naturals `b < a` and even `n ≠ 0`,
`v₂ (a^n - b^n) = v₂ (a - b) + v₂ (a + b) + v₂ n - 1`.
The `- 1` is ℕ-subtraction but never truncates, since `v₂ n ≥ 1`. -/
theorem padicValNat_two_pow_sub_pow_of_even {a b : ℕ} (hba : b < a)
    (ha : Odd a) (hb : Odd b) {n : ℕ} (hn0 : n ≠ 0) (hn : Even n) :
    padicValNat 2 (a ^ n - b ^ n)
      = padicValNat 2 (a - b) + padicValNat 2 (a + b) + padicValNat 2 n - 1 := by
  have ha1 : a % 2 = 1 := Nat.odd_iff.mp ha
  have hb1 : b % 2 = 1 := Nat.odd_iff.mp hb
  have hx : ¬2 ∣ a := by omega
  have hxy : 2 ∣ a - b := by omega
  have hmain := padicValNat.pow_two_sub_pow hba hxy hx hn0 hn
  have hvn : 1 ≤ padicValNat 2 n := one_le_padicValNat_of_dvd hn0 hn.two_dvd
  omega

end LiftingExponentTwo
