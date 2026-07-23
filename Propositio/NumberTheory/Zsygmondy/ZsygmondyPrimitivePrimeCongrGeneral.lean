/-
Zsygmondy primitive-prime-congruence lemma — general-`b` port.

The two-variable generalization of `ZsygmondyPrimitivePrimeCongr.primitive_prime_congr_one`.

If `p` is a primitive prime divisor of `Phi n a b` (i.e. `p ∣ Phi n a b` and `p ∤ n`), and
`p` divides neither `a` nor `b` (so `a * b⁻¹` is a unit modulo `p`), then `n ∣ p - 1`,
equivalently `p ≡ 1 (mod n)`.

Proof strategy, building on `ZsygmondyPrimitiveOrderGeneral`:
1. `primitive_order_of_dvd_Phi_general` gives `orderOf ((a : ZMod p) * (b : ZMod p)⁻¹) = n`.
2. `p ∤ a`, `p ∤ b` show `(a : ZMod p) * (b : ZMod p)⁻¹ ≠ 0`.
3. Fermat's little theorem (`ZMod.orderOf_dvd_card_sub_one`) gives the order divides `p - 1`.
4. Combine 1 and 3 to get `n ∣ p - 1`, and translate to `p ≡ 1 [MOD n]`.
-/
import Propositio.NumberTheory.Zsygmondy.ZsygmondyPrimitiveOrderGeneral
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Nat.ModEq

open Polynomial ZsygmondyHomogeneousCyclotomicFactor

/-- **Zsygmondy primitive-prime-congruence lemma, general `b`.** If a prime `p` divides
`Phi n a b`, with `p ∤ n` (primitivity) and `p ∤ a`, `p ∤ b` (so `a * b⁻¹` is a unit mod
`p`), then `n ∣ p - 1`. -/
theorem primitive_prime_congr_one_general {n p : ℕ} (hn : 1 < n) [Fact p.Prime]
    (a b : ℤ) (hp : (p : ℤ) ∣ Phi n a b) (hpn : ¬ p ∣ n)
    (hpa : ¬ (p : ℤ) ∣ a) (hpb : ¬ (p : ℤ) ∣ b) :
    n ∣ (p - 1) := by
  have hord : orderOf ((a : ZMod p) * (b : ZMod p)⁻¹) = n :=
    primitive_order_of_dvd_Phi_general hn a b hpb hp hpn
  have ha0 : (a : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact hpa
  have hb0 : (b : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact hpb
  have hr0 : (a : ZMod p) * (b : ZMod p)⁻¹ ≠ 0 := mul_ne_zero ha0 (inv_ne_zero hb0)
  have hdvd : orderOf ((a : ZMod p) * (b : ZMod p)⁻¹) ∣ p - 1 :=
    ZMod.orderOf_dvd_card_sub_one hr0
  rwa [hord] at hdvd

/-- Corollary in `Nat.ModEq` form: a primitive prime divisor `p` of `Phi n a b` (with
`p ∤ a`, `p ∤ b`) satisfies `p ≡ 1 (mod n)`. -/
theorem primitive_prime_modEq_one_general {n p : ℕ} (hn : 1 < n) [Fact p.Prime]
    (a b : ℤ) (hp : (p : ℤ) ∣ Phi n a b) (hpn : ¬ p ∣ n)
    (hpa : ¬ (p : ℤ) ∣ a) (hpb : ¬ (p : ℤ) ∣ b) :
    p ≡ 1 [MOD n] := by
  have hdvd : n ∣ (p - 1) := primitive_prime_congr_one_general hn a b hp hpn hpa hpb
  exact ((Nat.modEq_iff_dvd' (Fact.out : p.Prime).one_lt.le).2 hdvd).symm
