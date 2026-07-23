/-
Zsygmondy intrinsic (non-primitive) prime-factor structure lemma — general-`b` port.

The two-variable generalization of `ZsygmondyIntrinsicFactor.intrinsic_order_dvd`.

Statement: for a prime `p`, integers `a b` with `p ∤ a`, `p ∤ b`, and `n ≥ 1` with
`p ∣ Phi n a b` (the homogeneous bivariate cyclotomic factor), the multiplicative order
`d = orderOf ((a * b⁻¹ : ZMod p))` satisfies

  n = d · p ^ k   for some k ≥ 0,

exactly as in the `b = 1` case, with `a` replaced by the ratio `a * b⁻¹`.

Proof strategy: identical to `ZsygmondyIntrinsicFactor.intrinsic_order_dvd`, using
`dvd_Phi_iff_isRoot_cyclotomic` (`ZsygmondyPhiOrderBridge`) in place of the direct
`cyclotomic.eval_apply` cast to reduce `p ∣ Phi n a b` to `(a * b⁻¹ : ZMod p)` being a
root of `cyclotomic n (ZMod p)`, then running the same char-`p` cyclotomic factorization
argument (`isRoot_cyclotomic_prime_pow_mul_iff_of_charP`) on that root.
-/
import Propositio.NumberTheory.Zsygmondy.ZsygmondyPhiOrderBridge
import Mathlib.RingTheory.Polynomial.Cyclotomic.Expand
import Mathlib.Data.Nat.Factorization.Basic

open Polynomial ZsygmondyHomogeneousCyclotomicFactor

/-- **Zsygmondy intrinsic-factor structure lemma, general `b`.** For a prime `p`,
integers `a b` with `p ∤ b`, and `n ≥ 1` with `p ∣ Phi n a b`, the multiplicative order
`d = orderOf ((a : ZMod p) * (b : ZMod p)⁻¹)` satisfies `n = d · p ^ k` for some `k`. -/
theorem intrinsic_order_dvd_general {n p : ℕ} (hn : 0 < n) [Fact p.Prime] (a b : ℤ)
    (hpb : ¬ (p : ℤ) ∣ b) (hp : (p : ℤ) ∣ Phi n a b) :
    ∃ k : ℕ, n = orderOf ((a : ZMod p) * (b : ZMod p)⁻¹) * p ^ k := by
  have hx : (cyclotomic n (ZMod p)).IsRoot ((a : ZMod p) * (b : ZMod p)⁻¹) :=
    (dvd_Phi_iff_isRoot_cyclotomic a b hpb).mp hp
  obtain ⟨k, m, hpm, hfac⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd hn.ne' p (Fact.out : p.Prime).ne_one
  haveI : NeZero (m : ZMod p) := ⟨by rw [Ne, ZMod.natCast_eq_zero_iff]; exact hpm⟩
  rw [hfac] at hx
  have hprim : IsPrimitiveRoot ((a : ZMod p) * (b : ZMod p)⁻¹) m :=
    (isRoot_cyclotomic_prime_pow_mul_iff_of_charP).mp hx
  have hord : orderOf ((a : ZMod p) * (b : ZMod p)⁻¹) = m := hprim.eq_orderOf.symm
  exact ⟨k, by rw [hord, hfac, Nat.mul_comm]⟩

/-- Corollary: the multiplicative order of `a * b⁻¹` modulo `p` divides `n`. -/
theorem intrinsic_order_dvd_n_general {n p : ℕ} (hn : 0 < n) [Fact p.Prime] (a b : ℤ)
    (hpb : ¬ (p : ℤ) ∣ b) (hp : (p : ℤ) ∣ Phi n a b) :
    orderOf ((a : ZMod p) * (b : ZMod p)⁻¹) ∣ n := by
  obtain ⟨k, hk⟩ := intrinsic_order_dvd_general hn a b hpb hp
  exact ⟨p ^ k, hk⟩

/-- Corollary: every prime dividing `n / d` (the surplus over the order
`d = orderOf (a * b⁻¹ mod p)`) is `p` itself. -/
theorem intrinsic_quotient_prime_eq_general {n p : ℕ} (hn : 0 < n) [Fact p.Prime] (a b : ℤ)
    (hpb : ¬ (p : ℤ) ∣ b) (hp : (p : ℤ) ∣ Phi n a b)
    {q : ℕ} (hq : q.Prime) (hqdvd : q ∣ n / orderOf ((a : ZMod p) * (b : ZMod p)⁻¹)) :
    q = p := by
  obtain ⟨k, hk⟩ := intrinsic_order_dvd_general hn a b hpb hp
  have hdpos : 0 < orderOf ((a : ZMod p) * (b : ZMod p)⁻¹) := by
    rcases Nat.eq_zero_or_pos (orderOf ((a : ZMod p) * (b : ZMod p)⁻¹)) with h0 | h
    · rw [h0, Nat.zero_mul] at hk; exact absurd hk hn.ne'
    · exact h
  have hquot : n / orderOf ((a : ZMod p) * (b : ZMod p)⁻¹) = p ^ k := by
    rw [hk, Nat.mul_div_cancel_left _ hdpos]
  rw [hquot] at hqdvd
  exact (Nat.prime_dvd_prime_iff_eq hq (Fact.out : p.Prime)).mp
    (hq.dvd_of_dvd_pow hqdvd)
