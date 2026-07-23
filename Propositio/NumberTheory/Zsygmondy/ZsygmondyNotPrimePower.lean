/-
A clean corollary of `primitive_prime_exists_of_large_base` (Zsygmondy for a large base):
for `n ≥ 3` and integer base `a ≥ n + 1`, `a^n - 1` is NOT a prime power.

Proof sketch. Let `p` be the primitive prime divisor of `a^n - 1` furnished by
`primitive_prime_exists_of_large_base` (so `p ∣ a^n - 1` but `p` divides none of
`a^1 - 1, ..., a^{n-1} - 1`; in particular `p ∤ a - 1` since `1 < n`).

Suppose for contradiction `a^n - 1 = q^k` with `q` prime, `k > 0`. Since `a - 1 ∣ a^n - 1`
(standard geometric-sum divisibility), `a - 1 ∣ q^k`; since `a - 1 ≥ n ≥ 3 > 1`, the divisors
of `q^k` are exactly `q^0, ..., q^k`, so `a - 1 = q^j` for some `1 ≤ j ≤ k`, giving `q ∣ a - 1`.
On the other hand `p ∣ a^n - 1 = q^k` and `p` prime forces `p = q` (both prime, one divides a
power of the other). Combining: `p = q ∣ a - 1`, contradicting `p ∤ a - 1`.
-/
import Propositio.NumberTheory.Zsygmondy.ZsygmondyExistsLargeBase
import Mathlib.Algebra.IsPrimePow
import Mathlib.Algebra.Ring.GeomSum

/-- **Zsygmondy corollary: `a^n - 1` is not a prime power, for a large base.**
For `n ≥ 3` and integer base `a ≥ n + 1`, the natural number `(a^n - 1).natAbs` is not a
prime power (`IsPrimePow`). -/
theorem not_isPrimePow_pow_sub_one {n : ℕ} (hn : 3 ≤ n) {a : ℤ}
    (ha : (n : ℤ) + 1 ≤ a) :
    ¬ IsPrimePow (a ^ n - 1).natAbs := by
  intro hpp
  obtain ⟨q, k, hqprime, hk, hqk⟩ := (isPrimePow_nat_iff _).mp hpp
  -- basic bounds: `n ≥ 3` and `a ≥ n + 1 ≥ 4`.
  have hn3 : (3 : ℤ) ≤ (n : ℤ) := by exact_mod_cast hn
  have ha2 : (2 : ℤ) ≤ a := by omega
  -- `a^n - 1 > 0`, so we can identify `(a^n - 1).natAbs` with `a^n - 1` over ℤ.
  have ha1 : (1 : ℤ) ≤ a := by omega
  have hle : (2 : ℤ) ≤ a ^ n := le_trans ha2 (le_self_pow₀ ha1 (by omega))
  have hpow_pos : 0 < a ^ n - 1 := by omega
  have hcast : ((a ^ n - 1).natAbs : ℤ) = a ^ n - 1 := Int.natAbs_of_nonneg hpow_pos.le
  have heq : a ^ n - 1 = (q : ℤ) ^ k := by
    rw [← hcast, ← hqk]; push_cast; ring
  -- the primitive prime divisor `p` of `a^n - 1`.
  obtain ⟨p, hp, hpdvd, hprim⟩ := primitive_prime_exists_of_large_base hn ha
  -- `p ∤ a - 1`, since `1 < n` and `p` is primitive for exponent `n`.
  have hp_not_dvd_a1 : ¬ (p : ℤ) ∣ a - 1 := by
    have h1 := hprim 1 (by norm_num) (by omega)
    simpa using h1
  -- `a - 1 ∣ a^n - 1` (standard geometric-sum divisibility).
  have hsub_dvd : (a - 1) ∣ (a ^ n - 1) := sub_one_dvd_pow_sub_one a n
  -- `p ∣ q^k` (from `p ∣ a^n - 1 = q^k`), hence `p = q` since both are prime.
  have hpq : (p : ℤ) ∣ (q : ℤ) ^ k := heq ▸ hpdvd
  have hpq_nat : p ∣ q ^ k := by exact_mod_cast hpq
  have hp_eq_q : p = q := (Nat.prime_dvd_prime_iff_eq hp hqprime).mp (hp.dvd_of_dvd_pow hpq_nat)
  -- work in ℕ: let `A := a.toNat`, so `a = (A : ℤ)` since `a ≥ 0`.
  set A : ℕ := a.toNat with hA_def
  have hA : a = (A : ℤ) := (Int.toNat_of_nonneg (by omega)).symm
  have hA1_ge : 3 ≤ A - 1 := by
    have : (n : ℤ) + 1 ≤ (A : ℤ) := by rw [← hA]; exact ha
    have hAnat : n + 1 ≤ A := by exact_mod_cast this
    omega
  -- `a - 1 ∣ q^k` translates to `A - 1 ∣ q^k` in ℕ.
  have ha1_dvd_qk : (a - 1) ∣ (q : ℤ) ^ k := heq ▸ hsub_dvd
  have ha1_dvd_qk' : ((A - 1 : ℕ) : ℤ) ∣ (q : ℤ) ^ k := by
    have : ((A - 1 : ℕ) : ℤ) = a - 1 := by
      rw [hA]
      have : (1 : ℤ) ≤ (A : ℤ) := by
        have : (3 : ℕ) ≤ A - 1 := hA1_ge
        omega
      push_cast [Nat.cast_sub (by omega : 1 ≤ A)]
      ring
    rw [this]; exact ha1_dvd_qk
  have ha1_dvd_qk_nat : (A - 1) ∣ q ^ k := by exact_mod_cast ha1_dvd_qk'
  -- since `q` is prime, divisors of `q^k` are `q^j` for `j ≤ k`; `A - 1 ≥ 3 > 1` forces `j ≥ 1`.
  obtain ⟨j, hjk, hj_eq⟩ := (Nat.dvd_prime_pow hqprime).mp ha1_dvd_qk_nat
  have hj_pos : 0 < j := by
    rcases Nat.eq_zero_or_pos j with hj0 | hj0
    · exfalso; rw [hj0, pow_zero] at hj_eq; omega
    · exact hj0
  have hq_dvd_A1 : q ∣ (A - 1) := by
    rw [hj_eq]
    exact dvd_pow_self q (by omega)
  -- so `p = q ∣ A - 1`, i.e. `p ∣ a - 1` over ℤ — contradiction.
  have hp_dvd_A1 : p ∣ (A - 1) := hp_eq_q ▸ hq_dvd_A1
  have : (p : ℤ) ∣ a - 1 := by
    have hcast2 : ((A - 1 : ℕ) : ℤ) = a - 1 := by
      rw [hA]
      have h1A : (1 : ℤ) ≤ (A : ℤ) := by
        have : (3 : ℕ) ≤ A - 1 := hA1_ge
        omega
      push_cast [Nat.cast_sub (by omega : 1 ≤ A)]
      ring
    rw [← hcast2]
    exact_mod_cast hp_dvd_A1
  exact hp_not_dvd_a1 this
