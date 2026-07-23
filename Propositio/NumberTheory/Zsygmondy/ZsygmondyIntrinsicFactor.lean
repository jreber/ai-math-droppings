/-
Zsygmondy intrinsic (non-primitive) prime-factor structure lemma.

This is the companion to `primitive_prime_congr_one` (the case `p ∤ n`, where a prime
`p ∣ Φ_n(a)` satisfies `n ∣ p - 1`). Here we handle the general dichotomy, covering the
"intrinsic" case `p ∣ n` as well.

Statement: for a prime `p`, an integer `a` with `p ∤ a`, and `n ≥ 1` with
`p ∣ (cyclotomic n ℤ).eval a`, the multiplicative order `d = orderOf (a : ZMod p)` satisfies

  n = d · p ^ k   for some k ≥ 0,

i.e. the "prime-to-`p`" part of `n` is exactly `d = ord_p(a)`, and `n / d` is a power of `p`.
When `p ∤ n` this forces `k = 0` and recovers `d = n` (the primitive case); when `p ∣ n`
this pins down the extra factor as a pure power of `p`.

Proof strategy:
1. Work in `ZMod p`, a field (hence a domain of characteristic `p`).
2. `p ∣ Φ_n(a)` means `(a : ZMod p)` is a root of `cyclotomic n (ZMod p)`.
3. Decompose `n = p ^ k * m` with `p ∤ m` (`Nat.exists_eq_pow_mul_and_not_dvd`).
   Then `m ≠ 0`, so `NeZero (m : ZMod p)`.
4. `Polynomial.isRoot_cyclotomic_prime_pow_mul_iff_of_charP` (the char-`p` cyclotomic
   factorization `cyclotomic (p^k * m) = cyclotomic m ^ (p^k - p^{k-1})`) gives:
   a root of `cyclotomic (p^k * m)` over `ZMod p` is a *primitive* `m`-th root of unity.
5. `IsPrimitiveRoot.eq_orderOf` reads off `orderOf (a : ZMod p) = m`, so `n = m · p^k`.
-/
import Propositio.NumberTheory.Zsygmondy.ZsygmondyPrimitiveOrder
import Mathlib.RingTheory.Polynomial.Cyclotomic.Expand
import Mathlib.Data.Nat.Factorization.Basic

open Polynomial

/-- **Zsygmondy intrinsic-factor structure lemma.** For a prime `p`, an integer `a` with
`p ∤ a`, and `n ≥ 1` with `p ∣ (cyclotomic n ℤ).eval a`, the multiplicative order
`d = orderOf (a : ZMod p)` satisfies `n = d · p ^ k` for some `k`. Equivalently, `d ∣ n`
and `n / d` is a power of `p`: the prime-to-`p` part of `n` is exactly the order of `a` mod `p`.

This subsumes both cases of Zsygmondy's dichotomy: for a primitive prime (`p ∤ n`) it forces
`k = 0`, hence `d = n`; for an intrinsic prime (`p ∣ n`) it identifies the surplus as a pure
power of `p`. -/
theorem intrinsic_order_dvd {n p : ℕ} (hn : 0 < n) [Fact p.Prime] (a : ℤ)
    (_hpa : ¬ (p : ℤ) ∣ a) (hp : (p : ℤ) ∣ (Polynomial.cyclotomic n ℤ).eval a) :
    ∃ k : ℕ, n = orderOf (a : ZMod p) * p ^ k := by
  -- (a : ZMod p) is a root of the n-th cyclotomic polynomial over the field ZMod p.
  have hx : (cyclotomic n (ZMod p)).IsRoot (a : ZMod p) := by
    have heval := cyclotomic.eval_apply a n (Int.castRingHom (ZMod p))
    simp only [Int.coe_castRingHom] at heval
    have hzero : (((cyclotomic n ℤ).eval a : ℤ) : ZMod p) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hp
    show eval (a : ZMod p) (cyclotomic n (ZMod p)) = 0
    rw [heval, hzero]
  -- Split n into its p-part and its prime-to-p part: n = p ^ k * m with p ∤ m.
  obtain ⟨k, m, hpm, hfac⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd hn.ne' p (Fact.out : p.Prime).ne_one
  haveI : NeZero (m : ZMod p) := ⟨by rw [Ne, ZMod.natCast_eq_zero_iff]; exact hpm⟩
  -- Over ZMod p (char p, p ∤ m), a root of cyclotomic (p^k * m) is a primitive m-th root.
  rw [hfac] at hx
  have hprim : IsPrimitiveRoot (a : ZMod p) m :=
    (isRoot_cyclotomic_prime_pow_mul_iff_of_charP).mp hx
  have hord : orderOf (a : ZMod p) = m := hprim.eq_orderOf.symm
  exact ⟨k, by rw [hord, hfac, Nat.mul_comm]⟩

/-- Corollary: the multiplicative order of `a` modulo `p` divides `n`. -/
theorem intrinsic_order_dvd_n {n p : ℕ} (hn : 0 < n) [Fact p.Prime] (a : ℤ)
    (hpa : ¬ (p : ℤ) ∣ a) (hp : (p : ℤ) ∣ (Polynomial.cyclotomic n ℤ).eval a) :
    orderOf (a : ZMod p) ∣ n := by
  obtain ⟨k, hk⟩ := intrinsic_order_dvd hn a hpa hp
  exact ⟨p ^ k, hk⟩

/-- Corollary: every prime dividing `n / d` (the surplus over the order `d = orderOf (a mod p)`)
is `p` itself. This is the "the extra part is a power of `p`" reading of the structure lemma. -/
theorem intrinsic_quotient_prime_eq {n p : ℕ} (hn : 0 < n) [Fact p.Prime] (a : ℤ)
    (hpa : ¬ (p : ℤ) ∣ a) (hp : (p : ℤ) ∣ (Polynomial.cyclotomic n ℤ).eval a)
    {q : ℕ} (hq : q.Prime) (hqdvd : q ∣ n / orderOf (a : ZMod p)) :
    q = p := by
  obtain ⟨k, hk⟩ := intrinsic_order_dvd hn a hpa hp
  -- d = orderOf (a mod p) is positive (it divides n > 0).
  have hdpos : 0 < orderOf (a : ZMod p) := by
    rcases Nat.eq_zero_or_pos (orderOf (a : ZMod p)) with h0 | h
    · rw [h0, Nat.zero_mul] at hk; exact absurd hk hn.ne'
    · exact h
  -- n / d = p ^ k, so q ∣ p ^ k forces q = p.
  have hquot : n / orderOf (a : ZMod p) = p ^ k := by
    rw [hk, Nat.mul_div_cancel_left _ hdpos]
  rw [hquot] at hqdvd
  exact (Nat.prime_dvd_prime_iff_eq hq (Fact.out : p.Prime)).mp
    (hq.dvd_of_dvd_pow hqdvd)
