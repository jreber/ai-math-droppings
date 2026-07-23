/-
Zsygmondy primitive-prime-congruence lemma.

If `p` is a primitive prime divisor of `Φ_n(a)` (i.e. `p ∣ Φ_n(a)` and `p ∤ n`), and `p` does
not divide `a` (so `a` is a unit modulo `p`), then `n ∣ p - 1`, equivalently `p ≡ 1 (mod n)`.

This is the classical congruence used in Zsygmondy's theorem: every primitive prime divisor of
`a^n - 1` is congruent to `1` modulo `n`.

Proof strategy, building on `ZsygmondyPrimitiveOrder`:
1. `primitive_order_of_dvd_cyclotomic` gives `orderOf (a : ZMod p) = n`.
2. `p ∤ a` shows `(a : ZMod p) ≠ 0`, via `ZMod.intCast_zmod_eq_zero_iff_dvd`.
3. Fermat's little theorem (`ZMod.orderOf_dvd_card_sub_one`) gives
   `orderOf (a : ZMod p) ∣ p - 1`.
4. Combine 1 and 3 to get `n ∣ p - 1`, and translate to `p ≡ 1 [MOD n]` via
   `Nat.modEq_iff_dvd'`.
-/
import Propositio.NumberTheory.Zsygmondy.ZsygmondyPrimitiveOrder
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Nat.ModEq

open Polynomial

/-- **Zsygmondy primitive-prime-congruence lemma.** If `p` is a prime dividing
`(cyclotomic n ℤ).eval a`, with `p ∤ n` (primitivity) and `p ∤ a` (so `a` is a unit mod `p`),
then `n ∣ p - 1`. -/
theorem primitive_prime_congr_one {n p : ℕ} (hn : 1 < n) [Fact p.Prime] (a : ℤ)
    (hp : (p : ℤ) ∣ (Polynomial.cyclotomic n ℤ).eval a) (hpn : ¬ p ∣ n)
    (hpa : ¬ (p : ℤ) ∣ a) :
    n ∣ (p - 1) := by
  have hord : orderOf (a : ZMod p) = n :=
    primitive_order_of_dvd_cyclotomic hn a hp hpn
  have ha0 : (a : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact hpa
  have hdvd : orderOf (a : ZMod p) ∣ p - 1 := ZMod.orderOf_dvd_card_sub_one ha0
  rwa [hord] at hdvd

/-- Corollary in the `Nat.ModEq` form: a primitive prime divisor `p` of `Φ_n(a)` (with
`p ∤ a`) satisfies `p ≡ 1 (mod n)`. -/
theorem primitive_prime_modEq_one {n p : ℕ} (hn : 1 < n) [Fact p.Prime] (a : ℤ)
    (hp : (p : ℤ) ∣ (Polynomial.cyclotomic n ℤ).eval a) (hpn : ¬ p ∣ n)
    (hpa : ¬ (p : ℤ) ∣ a) :
    p ≡ 1 [MOD n] := by
  have hdvd : n ∣ (p - 1) := primitive_prime_congr_one hn a hp hpn hpa
  exact ((Nat.modEq_iff_dvd' (Fact.out : p.Prime).one_lt.le).2 hdvd).symm
