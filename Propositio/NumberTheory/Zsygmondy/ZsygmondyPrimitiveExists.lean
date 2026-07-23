/-
Zsygmondy: existence of a primitive prime divisor — the algebraic core, plus an
honestly-conditional existence theorem.

Reusing the Zsygmondy gearbox already in this repo, this file assembles:

* **Target 4 (positivity / growth).** `one_lt_natAbs_cyclotomic_eval`: for `n ≥ 2` and an
  integer `a ≥ 2`, `1 < |Φ_n(a)|`.  So `Φ_n(a)` genuinely has a prime factor.
  (mathlib's `sub_one_lt_natAbs_cyclotomic_eval`.)

* **Target 3 (the reduction lemma — the high-value brick).**
  `primitive_prime_divisor_of_dvd_cyclotomic`: if a prime `p ∣ Φ_n(a)` with `p ∤ n`
  (`n ≥ 2`), then `p` is a *primitive prime divisor* of `a^n - 1` in the classical sense:
  `p ∣ a^n - 1` and `p ∤ a^m - 1` for every `0 < m < n`.  This bridges the intrinsic /
  order structure to the classical definition, by combining
  `primitive_order_of_dvd_cyclotomic` (order `= n`) with `primitive_iff_orderOf_eq`.

* **Uniqueness of the intrinsic prime.** `intrinsic_prime_unique`: `Φ_n(a)` has at most one
  prime factor that divides `n`.  Proof: an intrinsic prime `p` has order `d = n / p^k`, and
  Fermat forces `d ∣ p - 1`, so any *other* prime `q ∣ n` must divide `d ≤ p - 1`, giving
  `q < p`; by symmetry `p < q`, contradiction.

* **Target 2 (existence, conditional on the honest analytic gap).**
  `primitive_prime_exists_of_not_isPrimePow`: for `n ≥ 2`, `a ≥ 2`, if `|Φ_n(a)|` is NOT a
  prime power, then a primitive prime divisor of `a^n - 1` exists.  This isolates exactly the
  size/height gap of the full Zsygmondy theorem: showing `|Φ_n(a)|` is not a prime power (for
  `(n,a)` outside the classical exceptions) is the remaining analytic estimate.  No such bound
  is assumed here — it is left as the explicit `¬ IsPrimePow` hypothesis.
-/
import Propositio.NumberTheory.Zsygmondy.ZsygmondyCyclotomicFactor
import Propositio.NumberTheory.Zsygmondy.ZsygmondyOrderBridge
import Propositio.NumberTheory.Zsygmondy.ZsygmondyPrimitiveOrder
import Propositio.NumberTheory.Zsygmondy.ZsygmondyIntrinsicFactor
import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval
import Mathlib.Data.Nat.Factorization.PrimePow

open Polynomial

/-- If a prime `p` divides `Φ_n(a)` (`n ≥ 1`), then `p ∤ a`.  Indeed `Φ_n(a) ∣ a^n - 1`
(it is one factor of the product `∏_{d ∣ n} Φ_d(a) = a^n - 1`), so `p ∣ a^n - 1`; were
`p ∣ a` we would get `p ∣ a^n` and hence `p ∣ 1`. -/
theorem not_dvd_base_of_dvd_cyclotomic {n p : ℕ} (hn : 0 < n) [Fact p.Prime] (a : ℤ)
    (hp : (p : ℤ) ∣ (cyclotomic n ℤ).eval a) : ¬ (p : ℤ) ∣ a := by
  intro ha
  have hdvd_prod : (cyclotomic n ℤ).eval a ∣ a ^ n - 1 := by
    rw [← prod_eval_cyclotomic_eq n hn a]
    exact Finset.dvd_prod_of_mem _ (Nat.mem_divisors_self n hn.ne')
  have hpn1 : (p : ℤ) ∣ a ^ n - 1 := hp.trans hdvd_prod
  have hpan : (p : ℤ) ∣ a ^ n := dvd_pow ha hn.ne'
  have hone : (p : ℤ) ∣ 1 := by
    have h2 : (p : ℤ) ∣ a ^ n - (a ^ n - 1) := dvd_sub hpan hpn1
    have h3 : a ^ n - (a ^ n - 1) = 1 := by ring
    rwa [h3] at h2
  have hp1 : p ∣ 1 := by exact_mod_cast hone
  exact absurd (Nat.dvd_one.mp hp1) (Fact.out : p.Prime).one_lt.ne'

/-- **Target 4 (positivity / growth helper).** For `n ≥ 2` and an integer `a ≥ 2`,
`1 < |Φ_n(a)|`.  In particular `Φ_n(a)` has a prime factor.  Wraps mathlib's
`sub_one_lt_natAbs_cyclotomic_eval`. -/
theorem one_lt_natAbs_cyclotomic_eval {n : ℕ} (hn : 1 < n) {a : ℤ} (ha : 2 ≤ a) :
    1 < ((cyclotomic n ℤ).eval a).natAbs := by
  set q : ℕ := a.toNat with hq
  have hqa : (q : ℤ) = a := Int.toNat_of_nonneg (by omega)
  have hq2 : 2 ≤ q := by omega
  have hqne : q ≠ 1 := by omega
  have hbnd : q - 1 < ((cyclotomic n ℤ).eval (q : ℤ)).natAbs :=
    sub_one_lt_natAbs_cyclotomic_eval hn hqne
  rw [hqa] at hbnd
  omega

/-- **Target 3 (the reduction lemma).** For `n ≥ 2`, if a prime `p` divides `Φ_n(a)` and
`p ∤ n`, then `p` is a *primitive prime divisor* of `a^n - 1`: it divides `a^n - 1` but none of
`a^m - 1` for `0 < m < n`.  This is the bridge from the cyclotomic/order structure to the
classical "primitive prime divisor" definition. -/
theorem primitive_prime_divisor_of_dvd_cyclotomic {n p : ℕ} (hn : 1 < n) [Fact p.Prime]
    (a : ℤ) (hp : (p : ℤ) ∣ (cyclotomic n ℤ).eval a) (hpn : ¬ p ∣ n) :
    (p : ℤ) ∣ a ^ n - 1 ∧ ∀ m, 0 < m → m < n → ¬ (p : ℤ) ∣ a ^ m - 1 := by
  have hpa : ¬ (p : ℤ) ∣ a := not_dvd_base_of_dvd_cyclotomic (by omega) a hp
  have hord : orderOf (a : ZMod p) = n := primitive_order_of_dvd_cyclotomic hn a hp hpn
  exact (primitive_iff_orderOf_eq a hn.le hpa).mpr hord

/-- **Uniqueness of the intrinsic prime.** `Φ_n(a)` (`n ≥ 2`) has at most one prime factor
dividing `n`: if primes `p, q` both divide `Φ_n(a)` and both divide `n`, then `p = q`. -/
theorem intrinsic_prime_unique {n : ℕ} (hn : 1 < n) {p q : ℕ}
    [Fact p.Prime] [Fact q.Prime] (a : ℤ)
    (hpc : (p : ℤ) ∣ (cyclotomic n ℤ).eval a) (hpn : p ∣ n)
    (hqc : (q : ℤ) ∣ (cyclotomic n ℤ).eval a) (hqn : q ∣ n) :
    p = q := by
  by_contra hne
  have hn0 : 0 < n := by omega
  have hpa : ¬ (p : ℤ) ∣ a := not_dvd_base_of_dvd_cyclotomic hn0 a hpc
  have hqa : ¬ (q : ℤ) ∣ a := not_dvd_base_of_dvd_cyclotomic hn0 a hqc
  -- q < p : q divides the prime-to-p part of n, which is ord_p(a) ≤ p-1.
  have hqlt : q < p := by
    obtain ⟨k, hk⟩ := intrinsic_order_dvd hn0 a hpa hpc
    have ha0 : (a : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact hpa
    have hord_dvd : orderOf (a : ZMod p) ∣ p - 1 := ZMod.orderOf_dvd_card_sub_one ha0
    have hplt1 : 1 < p := (Fact.out : p.Prime).one_lt
    have hord_le : orderOf (a : ZMod p) ≤ p - 1 :=
      Nat.le_of_dvd (by omega) hord_dvd
    have hqdvd_n : q ∣ orderOf (a : ZMod p) * p ^ k := by rw [← hk]; exact hqn
    have hqord : q ∣ orderOf (a : ZMod p) := by
      rcases (Nat.Prime.dvd_mul (Fact.out : q.Prime)).mp hqdvd_n with h | h
      · exact h
      · exact absurd ((Nat.prime_dvd_prime_iff_eq (Fact.out) (Fact.out)).mp
          ((Fact.out : q.Prime).dvd_of_dvd_pow h)) (Ne.symm hne)
    have hqle : q ≤ orderOf (a : ZMod p) := Nat.le_of_dvd (orderOf_pos_of_not_dvd hpa) hqord
    omega
  -- p < q by symmetry.
  have hplt : p < q := by
    obtain ⟨k, hk⟩ := intrinsic_order_dvd hn0 a hqa hqc
    have ha0 : (a : ZMod q) ≠ 0 := by
      rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact hqa
    have hord_dvd : orderOf (a : ZMod q) ∣ q - 1 := ZMod.orderOf_dvd_card_sub_one ha0
    have hqlt1 : 1 < q := (Fact.out : q.Prime).one_lt
    have hord_le : orderOf (a : ZMod q) ≤ q - 1 :=
      Nat.le_of_dvd (by omega) hord_dvd
    have hpdvd_n : p ∣ orderOf (a : ZMod q) * q ^ k := by rw [← hk]; exact hpn
    have hpord : p ∣ orderOf (a : ZMod q) := by
      rcases (Nat.Prime.dvd_mul (Fact.out : p.Prime)).mp hpdvd_n with h | h
      · exact h
      · exact absurd ((Nat.prime_dvd_prime_iff_eq (Fact.out) (Fact.out)).mp
          ((Fact.out : p.Prime).dvd_of_dvd_pow h)) hne
    have hple : p ≤ orderOf (a : ZMod q) := Nat.le_of_dvd (orderOf_pos_of_not_dvd hqa) hpord
    omega
  omega

/-- **Target 2 (existence, conditional on the honest analytic gap).** For `n ≥ 2` and an
integer `a ≥ 2`, if `|Φ_n(a)|` is *not* a prime power, then `a^n - 1` has a primitive prime
divisor: a prime `p` with `p ∣ a^n - 1` and `p ∤ a^m - 1` for every `0 < m < n`.

The `¬ IsPrimePow` hypothesis isolates exactly the size/height estimate that the full
Zsygmondy theorem needs (and which is *not* assumed here): the intrinsic part of `Φ_n(a)` is a
single prime power, so once `|Φ_n(a)|` exceeds it — i.e. `|Φ_n(a)|` is not itself a prime
power — a primitive prime must appear. -/
theorem primitive_prime_exists_of_not_isPrimePow {n : ℕ} (hn : 1 < n) {a : ℤ} (ha : 2 ≤ a)
    (hbig : ¬ IsPrimePow ((cyclotomic n ℤ).eval a).natAbs) :
    ∃ p : ℕ, p.Prime ∧ (p : ℤ) ∣ a ^ n - 1 ∧
      ∀ m, 0 < m → m < n → ¬ (p : ℤ) ∣ a ^ m - 1 := by
  by_contra hcon
  push_neg at hcon
  -- hcon : ∀ p, p.Prime → (p:ℤ) ∣ a^n-1 → ∃ m, 0 < m ∧ m < n ∧ (p:ℤ) ∣ a^m-1
  apply hbig
  rw [isPrimePow_iff_unique_prime_dvd]
  set M := ((cyclotomic n ℤ).eval a).natAbs with hMdef
  have hM1 : 1 < M := one_lt_natAbs_cyclotomic_eval hn ha
  -- Every prime factor of M divides n (else it would be a primitive prime divisor).
  have key : ∀ r, r.Prime → r ∣ M → r ∣ n := by
    intro r hrp hrM
    haveI : Fact r.Prime := ⟨hrp⟩
    have hrc : (r : ℤ) ∣ (cyclotomic n ℤ).eval a :=
      Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr hrM)
    by_contra hrn
    obtain ⟨h1, h2⟩ := primitive_prime_divisor_of_dvd_cyclotomic hn a hrc hrn
    obtain ⟨m, hm0, hmn, hmd⟩ := hcon r hrp h1
    exact h2 m hm0 hmn hmd
  -- Existence of a prime factor of M.
  obtain ⟨p0, hp0prime, hp0dvd⟩ := Nat.exists_prime_and_dvd (by omega : M ≠ 1)
  refine ⟨p0, ⟨hp0prime, hp0dvd⟩, ?_⟩
  -- Uniqueness: any two prime factors of M both divide n, hence are equal.
  rintro q ⟨hqp, hqM⟩
  haveI : Fact q.Prime := ⟨hqp⟩
  haveI : Fact p0.Prime := ⟨hp0prime⟩
  have hqc : (q : ℤ) ∣ (cyclotomic n ℤ).eval a :=
    Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr hqM)
  have hp0c : (p0 : ℤ) ∣ (cyclotomic n ℤ).eval a :=
    Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr hp0dvd)
  exact intrinsic_prime_unique hn a hqc (key q hqp hqM) hp0c (key p0 hp0prime hp0dvd)
