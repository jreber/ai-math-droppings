/-
Zsygmondy: existence of a primitive prime divisor of `a^n - b^n` — general-`b` port.

The two-variable generalization of `ZsygmondyPrimitiveExists`
(`primitive_prime_divisor_of_dvd_cyclotomic`, `intrinsic_prime_unique`,
`primitive_prime_exists_of_not_isPrimePow`), phrased throughout for the homogeneous
bivariate cyclotomic factor `Phi n a b` (`ZsygmondyHomogeneousCyclotomicFactor.Phi`) in
place of the univariate `(cyclotomic n ℤ).eval a` (= `Phi n a 1`, the `b = 1` case).

This is item (1) of the "What is NOT closed here" list in
`ZsygmondyExceptionalEndgameGeneral`: the general-`b` `Phi`-existence entry point, needed
to even REACH the "`Phi n a b` is a prime power `p^t`" hypothesis that the exceptional
endgame layers assume.

## What THIS FILE proves (real, sorry-free, axiom-clean)

* `not_dvd_base_of_dvd_Phi`: if `IsCoprime a b` and a prime `p ∣ Phi n a b` (`n ≥ 1`),
  then `p ∤ a` and `p ∤ b`. (General-`b` analogue of `not_dvd_base_of_dvd_cyclotomic`; the
  `b = 1` proof used `p ∣ a ⟹ p ∣ 1`, here it becomes `p ∣ a ∧ p ∣ b ⟹ IsUnit p` via
  coprimality.)

* `one_lt_natAbs_Phi`: for `n ≥ 2`, `1 ≤ b < a`, `1 < (Phi n a b).natAbs`. (Via the height
  lower bound `Phi_totient_lower_bound` from `ZsygmondyExceptionalEndgameGeneral`:
  `(a - b) ^ φ(n) < Phi n a b`, with `a - b ≥ 1`.)

* `primitive_prime_divisor_of_dvd_Phi`: for `n ≥ 2`, `IsCoprime a b`, if `p ∣ Phi n a b`
  and `p ∤ n`, then `p` is a *primitive prime divisor* of `a^n - b^n`. (Composes
  `primitive_order_of_dvd_Phi_general` with `primitive_iff_orderOf_eq_general`.)

* `intrinsic_prime_unique_general`: `Phi n a b` has at most one prime factor dividing `n`.

* `primitive_prime_exists_of_not_isPrimePow_general`: for `n ≥ 2`, `IsCoprime a b`,
  `1 ≤ b < a`, if `(Phi n a b).natAbs` is NOT a prime power, then `a^n - b^n` has a
  primitive prime divisor. This isolates exactly the size/height gap of the full general-`b`
  Zsygmondy theorem, exactly as the `b = 1` version did.
-/
import Propositio.NumberTheory.Zsygmondy.ZsygmondyHomogeneousCyclotomicFactor
import Propositio.NumberTheory.Zsygmondy.ZsygmondyPhiOrderBridge
import Propositio.NumberTheory.Zsygmondy.ZsygmondyOrderBridgeGeneral
import Propositio.NumberTheory.Zsygmondy.ZsygmondyIntrinsicFactorGeneral
import Propositio.NumberTheory.Zsygmondy.ZsygmondyPrimitiveOrderGeneral
import Propositio.NumberTheory.Zsygmondy.ZsygmondyExceptionalEndgameGeneral
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Data.Nat.Factorization.PrimePow

open Polynomial ZsygmondyHomogeneousCyclotomicFactor

namespace ZsygmondyPrimitiveExistsGeneral

/-- `Phi n a b` divides `a^n - b^n` (it is one factor of the product
`∏_{d ∣ n} Phi d a b = a^n - b^n`). -/
theorem Phi_dvd_pow_sub_pow {n : ℕ} (hn : 0 < n) (a b : ℤ) :
    Phi n a b ∣ a ^ n - b ^ n := by
  rw [prod_Phi_eq n hn a b]
  exact Finset.dvd_prod_of_mem _ (Nat.mem_divisors_self n hn.ne')

/-- **General-`b` `not_dvd_base`.** If `a, b` are coprime and a prime `p` divides
`Phi n a b` (`n ≥ 1`), then `p` divides neither `a` nor `b`. Proof: `Phi n a b ∣ a^n - b^n`,
so `p ∣ a^n - b^n`; if `p ∣ a` then `p ∣ b^n` hence `p ∣ b`, so `p` is a common divisor of
`a, b`, contradicting `IsCoprime a b` (would force `IsUnit p`). -/
theorem not_dvd_base_of_dvd_Phi {n p : ℕ} (hn : 0 < n) [Fact p.Prime] {a b : ℤ}
    (hcop : IsCoprime a b) (hp : (p : ℤ) ∣ Phi n a b) :
    ¬ (p : ℤ) ∣ a ∧ ¬ (p : ℤ) ∣ b := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp (Fact.out : p.Prime)
  have hpn1 : (p : ℤ) ∣ a ^ n - b ^ n := hp.trans (Phi_dvd_pow_sub_pow hn a b)
  refine ⟨?_, ?_⟩
  · intro ha
    have hpan : (p : ℤ) ∣ a ^ n := dvd_pow ha hn.ne'
    have hpbn : (p : ℤ) ∣ b ^ n := by
      have h := dvd_sub hpan hpn1
      rwa [show a ^ n - (a ^ n - b ^ n) = b ^ n from by ring] at h
    have hpb : (p : ℤ) ∣ b := hpZ.dvd_of_dvd_pow hpbn
    exact hpZ.not_unit (hcop.isUnit_of_dvd' ha hpb)
  · intro hb
    have hpbn : (p : ℤ) ∣ b ^ n := dvd_pow hb hn.ne'
    have hpan : (p : ℤ) ∣ a ^ n := by
      have h := dvd_add hpbn hpn1
      rwa [show b ^ n + (a ^ n - b ^ n) = a ^ n from by ring] at h
    have hpa : (p : ℤ) ∣ a := hpZ.dvd_of_dvd_pow hpan
    exact hpZ.not_unit (hcop.isUnit_of_dvd' hpa hb)

/-- **General-`b` growth helper.** For `n ≥ 2` and integers `1 ≤ b < a`,
`1 < (Phi n a b).natAbs`. In particular `Phi n a b` has a prime factor. -/
theorem one_lt_natAbs_Phi {n : ℕ} (hn : 1 < n) {a b : ℤ} (hb : 1 ≤ b) (hab : b < a) :
    1 < (Phi n a b).natAbs := by
  have hlb := ZsygmondyExceptionalEndgameGeneral.Phi_totient_lower_bound hn hb hab
  have hab1 : (1 : ℤ) ≤ a - b := by omega
  have hpow1 : (1 : ℤ) ≤ (a - b) ^ Nat.totient n := one_le_pow₀ hab1
  have hPhi2 : (2 : ℤ) ≤ Phi n a b := by linarith
  have : (2 : ℤ) ≤ (Phi n a b).natAbs := by
    have hnn : (0 : ℤ) ≤ Phi n a b := by linarith
    rw [Int.natAbs_of_nonneg hnn] at *
    exact_mod_cast hPhi2
  omega

/-- **General-`b` reduction lemma.** For `n ≥ 2`, `IsCoprime a b`, if a prime `p` divides
`Phi n a b` and `p ∤ n`, then `p` is a *primitive prime divisor* of `a^n - b^n`: it divides
`a^n - b^n` but none of `a^m - b^m` for `0 < m < n`. -/
theorem primitive_prime_divisor_of_dvd_Phi {n p : ℕ} (hn : 1 < n) [Fact p.Prime]
    {a b : ℤ} (hcop : IsCoprime a b) (hp : (p : ℤ) ∣ Phi n a b) (hpn : ¬ p ∣ n) :
    (p : ℤ) ∣ a ^ n - b ^ n ∧ ∀ m, 0 < m → m < n → ¬ (p : ℤ) ∣ a ^ m - b ^ m := by
  obtain ⟨hpa, hpb⟩ := not_dvd_base_of_dvd_Phi (by omega) hcop hp
  have hord : orderOf ((a : ZMod p) * (b : ZMod p)⁻¹) = n :=
    primitive_order_of_dvd_Phi_general hn a b hpb hp hpn
  exact (primitive_iff_orderOf_eq_general a b (by omega) hpa hpb).mpr hord

/-- **General-`b` uniqueness of the intrinsic prime.** `Phi n a b` (`n ≥ 2`, `IsCoprime a b`)
has at most one prime factor dividing `n`: if primes `p, q` both divide `Phi n a b` and both
divide `n`, then `p = q`. Same structure as the `b = 1` proof: an intrinsic prime `p` has
order `d = ord_p(a·b⁻¹)` dividing `p - 1`, and Fermat forces any other prime `q ∣ n` to
divide `d ≤ p - 1`, giving `q < p`; by symmetry `p < q`, contradiction. -/
theorem intrinsic_prime_unique_general {n : ℕ} (hn : 1 < n) {p q : ℕ}
    [Fact p.Prime] [Fact q.Prime] {a b : ℤ} (hcop : IsCoprime a b)
    (hpc : (p : ℤ) ∣ Phi n a b) (hpn : p ∣ n)
    (hqc : (q : ℤ) ∣ Phi n a b) (hqn : q ∣ n) :
    p = q := by
  by_contra hne
  have hn0 : 0 < n := by omega
  obtain ⟨hpa, hpb⟩ := not_dvd_base_of_dvd_Phi hn0 hcop hpc
  obtain ⟨hqa, hqb⟩ := not_dvd_base_of_dvd_Phi hn0 hcop hqc
  -- q < p : q divides the prime-to-p part of n, which is ord_p(a·b⁻¹) ≤ p - 1.
  have hqlt : q < p := by
    obtain ⟨k, hk⟩ := intrinsic_order_dvd_general hn0 a b hpb hpc
    have hr0 : (a : ZMod p) * (b : ZMod p)⁻¹ ≠ 0 := by
      have ha0 : (a : ZMod p) ≠ 0 := by
        rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact hpa
      have hb0 : (b : ZMod p) ≠ 0 := by
        rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact hpb
      exact mul_ne_zero ha0 (inv_ne_zero hb0)
    have hord_dvd : orderOf ((a : ZMod p) * (b : ZMod p)⁻¹) ∣ p - 1 :=
      ZMod.orderOf_dvd_card_sub_one hr0
    have hplt1 : 1 < p := (Fact.out : p.Prime).one_lt
    have hord_le : orderOf ((a : ZMod p) * (b : ZMod p)⁻¹) ≤ p - 1 :=
      Nat.le_of_dvd (by omega) hord_dvd
    have hqdvd_n : q ∣ orderOf ((a : ZMod p) * (b : ZMod p)⁻¹) * p ^ k := by
      rw [← hk]; exact hqn
    have hqord : q ∣ orderOf ((a : ZMod p) * (b : ZMod p)⁻¹) := by
      rcases (Nat.Prime.dvd_mul (Fact.out : q.Prime)).mp hqdvd_n with h | h
      · exact h
      · exact absurd ((Nat.prime_dvd_prime_iff_eq (Fact.out) (Fact.out)).mp
          ((Fact.out : q.Prime).dvd_of_dvd_pow h)) (Ne.symm hne)
    have hqpos : 0 < orderOf ((a : ZMod p) * (b : ZMod p)⁻¹) :=
      orderOf_pos_of_not_dvd_general hpa hpb
    have hqle : q ≤ orderOf ((a : ZMod p) * (b : ZMod p)⁻¹) := Nat.le_of_dvd hqpos hqord
    omega
  -- p < q by symmetry.
  have hplt : p < q := by
    obtain ⟨k, hk⟩ := intrinsic_order_dvd_general hn0 a b hqb hqc
    have hr0 : (a : ZMod q) * (b : ZMod q)⁻¹ ≠ 0 := by
      have ha0 : (a : ZMod q) ≠ 0 := by
        rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact hqa
      have hb0 : (b : ZMod q) ≠ 0 := by
        rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact hqb
      exact mul_ne_zero ha0 (inv_ne_zero hb0)
    have hord_dvd : orderOf ((a : ZMod q) * (b : ZMod q)⁻¹) ∣ q - 1 :=
      ZMod.orderOf_dvd_card_sub_one hr0
    have hqlt1 : 1 < q := (Fact.out : q.Prime).one_lt
    have hord_le : orderOf ((a : ZMod q) * (b : ZMod q)⁻¹) ≤ q - 1 :=
      Nat.le_of_dvd (by omega) hord_dvd
    have hpdvd_n : p ∣ orderOf ((a : ZMod q) * (b : ZMod q)⁻¹) * q ^ k := by
      rw [← hk]; exact hpn
    have hpord : p ∣ orderOf ((a : ZMod q) * (b : ZMod q)⁻¹) := by
      rcases (Nat.Prime.dvd_mul (Fact.out : p.Prime)).mp hpdvd_n with h | h
      · exact h
      · exact absurd ((Nat.prime_dvd_prime_iff_eq (Fact.out) (Fact.out)).mp
          ((Fact.out : p.Prime).dvd_of_dvd_pow h)) hne
    have hppos : 0 < orderOf ((a : ZMod q) * (b : ZMod q)⁻¹) :=
      orderOf_pos_of_not_dvd_general hqa hqb
    have hple : p ≤ orderOf ((a : ZMod q) * (b : ZMod q)⁻¹) := Nat.le_of_dvd hppos hpord
    omega
  omega

/-- **General-`b` existence, conditional on the honest size gap.** For `n ≥ 2`,
`IsCoprime a b`, integers `1 ≤ b < a`, if `(Phi n a b).natAbs` is *not* a prime power, then
`a^n - b^n` has a primitive prime divisor: a prime `p` with `p ∣ a^n - b^n` and
`p ∤ a^m - b^m` for every `0 < m < n`.

The `¬ IsPrimePow` hypothesis isolates exactly the size/height estimate that the full
general-`b` Zsygmondy theorem needs (and which is *not* assumed here): the intrinsic part of
`Phi n a b` is a single prime power (this is item (2), `padicValInt_Phi_intrinsic_le_one` in
`ZsygmondyLTEGeneral`), so once `(Phi n a b).natAbs` exceeds it — i.e. is not itself a prime
power — a primitive prime must appear. -/
theorem primitive_prime_exists_of_not_isPrimePow_general {n : ℕ} (hn : 1 < n) {a b : ℤ}
    (hb : 1 ≤ b) (hab : b < a) (hcop : IsCoprime a b)
    (hbig : ¬ IsPrimePow (Phi n a b).natAbs) :
    ∃ p : ℕ, p.Prime ∧ (p : ℤ) ∣ a ^ n - b ^ n ∧
      ∀ m, 0 < m → m < n → ¬ (p : ℤ) ∣ a ^ m - b ^ m := by
  by_contra hcon
  push_neg at hcon
  apply hbig
  rw [isPrimePow_iff_unique_prime_dvd]
  set M := (Phi n a b).natAbs with hMdef
  have hM1 : 1 < M := one_lt_natAbs_Phi hn hb hab
  -- Every prime factor of M divides n (else it would be a primitive prime divisor).
  have key : ∀ r, r.Prime → r ∣ M → r ∣ n := by
    intro r hrp hrM
    haveI : Fact r.Prime := ⟨hrp⟩
    have hrc : (r : ℤ) ∣ Phi n a b :=
      Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr hrM)
    by_contra hrn
    obtain ⟨h1, h2⟩ := primitive_prime_divisor_of_dvd_Phi hn hcop hrc hrn
    obtain ⟨m, hm0, hmn, hmd⟩ := hcon r hrp h1
    exact h2 m hm0 hmn hmd
  -- Existence of a prime factor of M.
  obtain ⟨p0, hp0prime, hp0dvd⟩ := Nat.exists_prime_and_dvd (by omega : M ≠ 1)
  refine ⟨p0, ⟨hp0prime, hp0dvd⟩, ?_⟩
  -- Uniqueness: any two prime factors of M both divide n, hence are equal.
  rintro q ⟨hqp, hqM⟩
  haveI : Fact q.Prime := ⟨hqp⟩
  haveI : Fact p0.Prime := ⟨hp0prime⟩
  have hqc : (q : ℤ) ∣ Phi n a b :=
    Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr hqM)
  have hp0c : (p0 : ℤ) ∣ Phi n a b :=
    Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr hp0dvd)
  exact intrinsic_prime_unique_general hn hcop hqc (key q hqp hqM) hp0c (key p0 hp0prime hp0dvd)

end ZsygmondyPrimitiveExistsGeneral
