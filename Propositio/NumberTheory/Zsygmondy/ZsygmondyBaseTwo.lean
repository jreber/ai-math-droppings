/-
Base-2 cyclotomic lower bound `n < Φ_n(2)`.

This file supplies the numeric fact needed to plug the `a = 2` gap in
`ZsygmondyHeightBound.cyclotomic_eval_totient_lower_bound` (which degenerates to the useless
`1 < Φ_n(2)` at `a = 2`, since `(a-1)^φ(n) = 1^φ(n) = 1`).  The full classical statement is

    ∀ n ≥ 2, n ≠ 6 → n < Φ_n(2)

(matching the classical Zsygmondy exception `(n,a) = (6,2)`, since `Φ_6(2) = 3 < 6`).

## Scope of this file

Proving the FULL statement above elementarily turns out to be substantially harder than the
odd-`n`/general-`a` machinery already on `main`: the natural strategy (strong induction on `n`
via `Φ_n(2) = (2^n - 1) / ∏_{d ∣ n, d < n} Φ_d(2)`, lower-bounding `Φ_n(2)` by upper-bounding the
proper-divisor product) requires a genuinely tight upper bound on `Φ_d(2)` for proper divisors
`d`.  The natural elementary candidate bounds fail:

  * The trivial bound `Φ_d(2) < 2^d` (from positivity of the *other* divisor-product factors)
    over-counts badly for `n` with a rich divisor lattice: e.g. for `n = 12` the crude product
    bound is `2^16 = 65536`, but the true proper-divisor product is `315` (a factor of ~200 off),
    because it ignores that intermediate factors like `Φ_6(2) = 3` are anomalously *small*.
  * The root-magnitude bound `Φ_d(2) ≤ 3^φ(d)` (`Polynomial.cyclotomic_eval_le_add_one_pow_totient`
    at `q = 2`, already in mathlib) is tight enough only when `φ(n)/n` is bounded away from `0`;
    for `n` with many small prime factors (e.g. primorial `n`), `φ(n)/n → 0` and the resulting
    bound `Φ_n(2) ≥ (2^n-1)/3^{n-φ(n)}` fails outright, even though the true value `Φ_n(2)` stays
    enormous (its true order of magnitude tracks `2^φ(n)`, not `3^φ(n)`).  Recovering the correct
    base-`2` (rather than base-`3`) asymptotic elementarily requires a genuine root-equidistribution
    / Mahler-measure argument that is well beyond a single elementary induction.

So the *general* statement is scoped down here to a still-substantial, cleanly provable family:
**`n` a prime power.**  Prime powers can never equal the classical exception `6 = 2·3` (not a
prime power), so no exceptional carve-out is needed, and the divisor lattice of `p^k` is a simple
chain `1, p, p², …, p^k`, avoiding the combinatorial blow-up above entirely: the exact formula
`Φ_{p^{n+1}}(x) = ∑_{i<p} (x^{p^n})^i` (`Polynomial.cyclotomic_prime_pow_eq_geom_sum`) reduces the
whole claim to an elementary comparison between an explicit geometric sum and a product of two
naturals, done by hand below (`key_bound`, `lt_two_pow_pred`, `two_mul_le_two_pow`).

The general (all `n ≥ 2`, `n ≠ 6`) statement remains open; see the failed-attempt record for the
obstruction detail.
-/
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval
import Mathlib.Algebra.IsPrimePow

namespace ZsygmondyBaseTwo

open Polynomial

/-- `2 * m ≤ 2 ^ m` for every `m ≥ 1`. -/
private theorem two_mul_le_two_pow {m : ℕ} (hm : 1 ≤ m) : 2 * m ≤ 2 ^ m := by
  have hlt : m - 1 < 2 ^ (m - 1) := Nat.lt_two_pow_self
  have heq : 2 ^ m = 2 * 2 ^ (m - 1) := by
    conv_lhs => rw [show m = (m - 1) + 1 from by omega]
    rw [pow_succ]; ring
  omega

/-- `p < 2 ^ (p - 1)` for `p ≥ 3`. -/
private theorem lt_two_pow_pred {p : ℕ} (hp3 : 3 ≤ p) : p < 2 ^ (p - 1) := by
  have hlt : p - 2 < 2 ^ (p - 2) := Nat.lt_two_pow_self
  have heq : 2 ^ (p - 1) = 2 * 2 ^ (p - 2) := by
    conv_lhs => rw [show p - 1 = (p - 2) + 1 from by omega]
    rw [pow_succ]; ring
  omega

/-- Key elementary bound: for `p ≥ 3` and `m ≥ p`, `p * m < 2 ^ (m * (p - 1))`.

Proof: `2^m > p` (via `p < 2^p ≤ 2^m`) and `2^m > m` (via `Nat.lt_two_pow_self`), so
`p * m < 2^m * m < 2^m * 2^m = 2^(2m) ≤ 2^(m(p-1))` (the last step using `p - 1 ≥ 2`). -/
private theorem key_bound {p m : ℕ} (hp3 : 3 ≤ p) (hmp : p ≤ m) :
    p * m < 2 ^ (m * (p - 1)) := by
  have hA : m < 2 ^ m := Nat.lt_two_pow_self
  have hB : p < 2 ^ p := Nat.lt_two_pow_self
  have hAB : (2 : ℕ) ^ p ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hmp
  have hpm : p < 2 ^ m := lt_of_lt_of_le hB hAB
  have hmpos : 0 < m := by omega
  have h2mpos : 0 < (2 : ℕ) ^ m := pow_pos (by norm_num) m
  have h1 : p * m < 2 ^ m * m := Nat.mul_lt_mul_of_pos_right hpm hmpos
  have h2 : 2 ^ m * m < 2 ^ m * 2 ^ m := Nat.mul_lt_mul_of_pos_left hA h2mpos
  have hchain : p * m < 2 ^ m * 2 ^ m := lt_trans h1 h2
  have hsplit : (2 : ℕ) ^ m * 2 ^ m = 2 ^ (2 * m) := by rw [two_mul, pow_add]
  rw [hsplit] at hchain
  have hp1 : 2 ≤ p - 1 := by omega
  have hexp : 2 * m ≤ m * (p - 1) := by
    calc 2 * m = m * 2 := by ring
      _ ≤ m * (p - 1) := Nat.mul_le_mul_left m hp1
  have hpow : (2 : ℕ) ^ (2 * m) ≤ 2 ^ (m * (p - 1)) := Nat.pow_le_pow_right (by norm_num) hexp
  exact lt_of_lt_of_le hchain hpow

/-- **Base-2 cyclotomic lower bound, prime-power case.**  For `n` a prime power,
`n < Φ_n(2)`.  (Prime powers are never `6 = 2·3`, so no exceptional carve-out is needed here;
see the file docstring for why the general `n ≥ 2, n ≠ 6` statement is out of scope.) -/
theorem cyclotomic_eval_two_gt_of_isPrimePow {n : ℕ} (hpp : IsPrimePow n) :
    (n : ℤ) < (cyclotomic n ℤ).eval 2 := by
  obtain ⟨p, k, hp, hk, hn⟩ := (isPrimePow_nat_iff n).mp hpp
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  subst hn
  haveI : Fact p.Prime := ⟨hp⟩
  have heval : (cyclotomic (p ^ (j + 1)) ℤ).eval 2
      = ∑ i ∈ Finset.range p, ((2 : ℤ) ^ p ^ j) ^ i := by
    rw [cyclotomic_prime_pow_eq_geom_sum hp, eval_finset_sum]
    exact Finset.sum_congr rfl fun i _ => by simp
  rw [heval]
  set m : ℕ := p ^ j with hm_def
  have hncast : ((p ^ (j + 1) : ℕ) : ℤ) = (p : ℤ) * (m : ℤ) := by
    have hnat : p ^ (j + 1) = p * m := by rw [hm_def, pow_succ]; ring
    exact_mod_cast hnat
  rw [hncast]
  rcases hp.eq_two_or_odd' with hp2 | hpodd
  · -- p = 2 : exact two-term evaluation
    subst hp2
    have hmm : m = 2 ^ j := hm_def
    have hmpos : 1 ≤ m := by rw [hmm]; exact Nat.one_le_two_pow
    have hsum : ∑ i ∈ Finset.range 2, ((2 : ℤ) ^ m) ^ i = 1 + (2 : ℤ) ^ m := by
      simp [Finset.sum_range_succ]
    rw [hsum]
    have hnat : 2 * m < 2 ^ m + 1 := by
      have := two_mul_le_two_pow hmpos
      omega
    have hcast2 : ((2 * m : ℕ) : ℤ) < ((2 ^ m + 1 : ℕ) : ℤ) := by exact_mod_cast hnat
    push_cast at hcast2
    omega
  · -- p odd (p ≥ 3) : bound via the top term of the geometric sum
    obtain ⟨t, ht⟩ := hpodd
    have h2le := hp.two_le
    have hp3 : 3 ≤ p := by omega
    have hppos : 0 < p := by omega
    have hmem : p - 1 ∈ Finset.range p := by
      rw [Finset.mem_range]; omega
    have hnonneg : ∀ i ∈ Finset.range p, (0 : ℤ) ≤ ((2 : ℤ) ^ m) ^ i := by
      intro i _; positivity
    have hsingle : ((2 : ℤ) ^ m) ^ (p - 1) ≤ ∑ i ∈ Finset.range p, ((2 : ℤ) ^ m) ^ i :=
      Finset.single_le_sum hnonneg hmem
    have hnat_bound : p * m < 2 ^ (m * (p - 1)) := by
      rcases Nat.eq_zero_or_pos j with hj0 | hjpos
      · have hm1 : m = 1 := by rw [hm_def, hj0, pow_zero]
        rw [hm1]
        simpa using lt_two_pow_pred hp3
      · have hmp : p ≤ m := by
          rw [hm_def]
          calc p = p ^ 1 := (pow_one p).symm
            _ ≤ p ^ j := Nat.pow_le_pow_right hp.pos hjpos
        exact key_bound hp3 hmp
    have hcast : ((p * m : ℕ) : ℤ) < ((2 ^ (m * (p - 1)) : ℕ) : ℤ) := by exact_mod_cast hnat_bound
    push_cast at hcast
    have hpow_eq : ((2 : ℤ) ^ m) ^ (p - 1) = (2 : ℤ) ^ (m * (p - 1)) := by
      rw [← pow_mul]
    calc (p : ℤ) * (m : ℤ) < (2 : ℤ) ^ (m * (p - 1)) := hcast
      _ = ((2 : ℤ) ^ m) ^ (p - 1) := hpow_eq.symm
      _ ≤ ∑ i ∈ Finset.range p, ((2 : ℤ) ^ m) ^ i := hsingle

end ZsygmondyBaseTwo
