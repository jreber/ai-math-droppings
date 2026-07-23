import Mathlib.Data.Nat.Factorization.Basic
import Propositio.NumberTheory.Beal.UnitsDensityGeneral
import Propositio.NumberTheory.Beal.TwoDensity
import Propositio.NumberTheory.Beal.TwoAdicIso

/-!
# Complete Beal-local unit-group density at ANY modulus (NEW, no LaTTe sibling)

NEW (no LaTTe sibling) — complete Beal-local unit-group density at ANY modulus,
assembling the odd (`BealUnitsDensityGeneral`) and 2-adic
(`BealTwoDensity`/`BealTwoAdicIso`) pieces via units-CRT.

For any modulus `n > 0`, write `n = 2^a · m` with `m` odd
(`a = n.factorization 2 = padicValNat 2 n`, `m = ordCompl[2] n`;
`Nat.ordProj_mul_ordCompl_eq_self` and `2^a ⊥ m` via `Nat.coprime_ordCompl`).
Since `2^a` and `m` are coprime, units-CRT multiplicativity
(`BealUnitsDensityGeneral.units_pair_solution_count_mul`) gives

  `Nat.card (USolSet n x y) = Nat.card (USolSet (2^a) x y) · Nat.card (USolSet m x y)`.

The odd factor is `units_pair_solution_count_odd`; the 2-adic factor is a case
split on the 2-adic valuation `a`:

* `a = 0` : `(ZMod 1)ˣ` trivial   → `1`                         (`units_pair_solution_count_one`)
* `a = 1` : `(ZMod 2)ˣ` trivial   → `1`                         (`BealTwoDensity.units_two_one_count`)
* `a = 2` : `(ZMod 4)ˣ` cyclic    → `2 · gcd(2, g)`             (`BealTwoDensity.units_four_count`)
* `a ≥ 3` : `(ZMod 2^a)ˣ` wild     → `(2·gcd(2,g)) · (2^(a-2)·gcd(2^(a-2),g))`
                                       (`BealTwoAdicIso.units_two_pow_count_ge_three`)

where `g = gcd x y`. This is the FULL Beal-local unit-group density at an
arbitrary modulus — every prior file handled either the odd part or a single
prime power; this one assembles them into one closed split.

## What is new here

* `twoFactorCount a x y` — the explicit closed value of `Nat.card (USolSet (2^a) x y)`
  by cases on the 2-adic valuation `a`.
* `units_two_pow_count` — the 2-adic count equals `twoFactorCount` for every `a`
  (all four cases sorry-free).
* `units_pair_solution_count_full` (**HEADLINE**) — for any `n > 0`,
  `Nat.card (USolSet n x y) = twoFactorCount a x y · (odd factorization product)`,
  the complete split at an arbitrary modulus.
-/

namespace BealUnitsDensityFull

open BealUnitsDensityGeneral BealTwoDensity

/-!
## 0. The explicit 2-adic factor, by cases on the 2-adic valuation
-/

/-- The explicit closed value of the 2-adic Beal count `Nat.card (USolSet (2^a) x y)`,
by cases on the 2-adic valuation `a` (`g = gcd x y`):

* `a = 0`: `1`              (`(ZMod 1)ˣ` trivial)
* `a = 1`: `1`              (`(ZMod 2)ˣ` trivial)
* `a = 2`: `2 · gcd(2, g)`  (`(ZMod 4)ˣ` cyclic of order 2)
* `a ≥ 3`: `(2·gcd(2,g)) · (2^(a-2)·gcd(2^(a-2),g))`   (`(ZMod 2^a)ˣ ≅ C₂ × C_{2^(a-2)}`) -/
def twoFactorCount (a x y : ℕ) : ℕ :=
  match a with
  | 0 => 1
  | 1 => 1
  | 2 => 2 * Nat.gcd 2 (Nat.gcd x y)
  | (a + 3) =>
      (2 * Nat.gcd 2 (Nat.gcd x y))
        * (2 ^ (a + 1) * Nat.gcd (2 ^ (a + 1)) (Nat.gcd x y))

/-- **The 2-adic factor is exactly `twoFactorCount` (all four cases, sorry-free).**
For every `a` and `x, y`, the Beal unit count over `(ZMod (2^a))ˣ` equals
`twoFactorCount a x y`. The four cases are dispatched to
`units_pair_solution_count_one` (`a=0`), `BealTwoDensity.units_two_one_count`
(`a=1`), `BealTwoDensity.units_four_count` (`a=2`) and
`BealTwoAdicIso.units_two_pow_count_ge_three` (`a≥3`). -/
theorem units_two_pow_count (a x y : ℕ) :
    Nat.card (USolSet (2 ^ a) x y) = twoFactorCount a x y := by
  match a with
  | 0 =>
      -- 2^0 = 1
      simp only [pow_zero, twoFactorCount]
      exact units_pair_solution_count_one x y
  | 1 =>
      -- 2^1 = 2
      simp only [pow_one, twoFactorCount]
      exact units_two_one_count x y
  | 2 =>
      -- 2^2 = 4
      show Nat.card (USolSet (2 ^ 2) x y) = _
      rw [show (2 : ℕ) ^ 2 = 4 by norm_num]
      exact units_four_count x y
  | (a + 3) =>
      -- a ≥ 3: the wild 2-adic case
      have h := BealTwoAdicIso.units_two_pow_count_ge_three (a + 3) (by omega) x y
      rw [show a + 3 - 2 = a + 1 by omega] at h
      simpa only [twoFactorCount] using h

/-!
## 1. HEADLINE — the complete split at an arbitrary modulus
-/

/-- **HEADLINE (NEW): complete Beal-local unit-group density at ANY modulus.**

For any `n > 0` and any `x, y`, write `a = n.factorization 2` (the 2-adic
valuation, `= padicValNat 2 n`) and `m = ordCompl[2] n` (the odd part). Then the
unit-group Beal count over `(ZMod n)ˣ` factors as the explicit 2-adic factor times
the odd factorization product:

`Nat.card (USolSet n x y)
   = twoFactorCount a x y
     * ∏ (p^k) in m.factorization, φ(p^k) · gcd(φ(p^k), gcd x y)`.

Assembled from `units_pair_solution_count_mul` (units-CRT multiplicativity over
the coprime split `n = 2^a · m`), `units_two_pow_count` (the explicit 2-adic
factor, all cases), and `units_pair_solution_count_odd` (the odd part). This is
the full Beal-local density at an arbitrary modulus — even or odd. -/
theorem units_pair_solution_count_full (n : ℕ) (hn : n ≠ 0) (x y : ℕ) :
    Nat.card (USolSet n x y)
      = twoFactorCount (n.factorization 2) x y
        * (ordCompl[2] n).factorization.prod fun p k =>
            Nat.totient (p ^ k) * Nat.gcd (Nat.totient (p ^ k)) (Nat.gcd x y) := by
  set a := n.factorization 2 with ha
  set m := ordCompl[2] n with hm
  -- `2^a · m = n`.
  have hsplit : 2 ^ a * m = n := Nat.ordProj_mul_ordCompl_eq_self n 2
  -- `2^a ⊥ m`.
  have hcop2 : Nat.Coprime 2 m := Nat.coprime_ordCompl Nat.prime_two hn
  have hcop : Nat.Coprime (2 ^ a) m := Nat.Coprime.pow_left a hcop2
  -- `m` is odd and nonzero.
  have hm0 : m ≠ 0 := (Nat.ordCompl_pos 2 hn).ne'
  have hmodd : Odd m := by
    rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero]
    exact Nat.not_dvd_ordCompl Nat.prime_two hn
  -- multiplicativity over the coprime split, then the two explicit factors.
  calc
    Nat.card (USolSet n x y)
        = Nat.card (USolSet (2 ^ a * m) x y) := by rw [hsplit]
      _ = Nat.card (USolSet (2 ^ a) x y) * Nat.card (USolSet m x y) :=
          units_pair_solution_count_mul (2 ^ a) m hcop x y
      _ = twoFactorCount a x y
            * ((m).factorization.prod fun p k =>
                Nat.totient (p ^ k) * Nat.gcd (Nat.totient (p ^ k)) (Nat.gcd x y)) := by
          rw [units_two_pow_count a x y,
            units_pair_solution_count_odd m hmodd hm0 x y]

end BealUnitsDensityFull
