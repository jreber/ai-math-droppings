/-
Zsygmondy divisor dichotomy: assembly brick.

Combines `primitive_prime_congr_one` (ZsygmondyPrimitivePrimeCongr) and
`intrinsic_order_dvd` (ZsygmondyIntrinsicFactor) into the clean statement that every prime
divisor `p` of `Φ_n(a)` (with `p ∤ a`) is either:
  - primitive: `n ∣ p - 1` (equivalently `p ≡ 1 (mod n)`), or
  - intrinsic: `p ∣ n`,
and in the intrinsic case the full structural information `n = orderOf (a : ZMod p) * p ^ k`
is available.

This is the case-split assembly of the two independently-proved halves: no new mathematical
content beyond `by_cases p ∣ n`.
-/
import Propositio.NumberTheory.Zsygmondy.ZsygmondyPrimitivePrimeCongr
import Propositio.NumberTheory.Zsygmondy.ZsygmondyIntrinsicFactor

open Polynomial

/-- **Zsygmondy divisor dichotomy.** Every prime `p` dividing `Φ_n(a)` (with `p ∤ a`) is either
a primitive prime divisor (`n ∣ p - 1`) or an intrinsic one (`p ∣ n`). -/
theorem prime_dvd_cyclotomic_dichotomy {n p : ℕ} (hn : 1 < n) [Fact p.Prime] (a : ℤ)
    (hpa : ¬ (p : ℤ) ∣ a) (hp : (p : ℤ) ∣ (Polynomial.cyclotomic n ℤ).eval a) :
    n ∣ (p - 1) ∨ p ∣ n := by
  by_cases hpn : p ∣ n
  · exact Or.inr hpn
  · exact Or.inl (primitive_prime_congr_one hn a hp hpn hpa)

/-- **Zsygmondy divisor dichotomy, strengthened.** Same dichotomy as
`prime_dvd_cyclotomic_dichotomy`, but the intrinsic branch is upgraded with the full
structural fact `n = orderOf (a : ZMod p) * p ^ k` from `intrinsic_order_dvd`. -/
theorem prime_dvd_cyclotomic_dichotomy_strong {n p : ℕ} (hn : 1 < n) [Fact p.Prime] (a : ℤ)
    (hpa : ¬ (p : ℤ) ∣ a) (hp : (p : ℤ) ∣ (Polynomial.cyclotomic n ℤ).eval a) :
    n ∣ (p - 1) ∨ (p ∣ n ∧ ∃ k : ℕ, n = orderOf (a : ZMod p) * p ^ k) := by
  by_cases hpn : p ∣ n
  · exact Or.inr ⟨hpn, intrinsic_order_dvd (by omega) a hpa hp⟩
  · exact Or.inl (primitive_prime_congr_one hn a hp hpn hpa)
