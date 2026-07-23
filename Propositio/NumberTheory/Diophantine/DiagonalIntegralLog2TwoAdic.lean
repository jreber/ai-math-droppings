import Propositio.NumberTheory.Diophantine.DiagonalIntegralLog2
import Mathlib.Tactic

/-!
# The 2-adic miracle for the diagonal `log 2` integral coefficients

`DiagonalIntegralLog2.I_eq_rat_add_log` expresses the Alladi–Robinson diagonal integral as

  `Iₙ = cₙ·log 2 + ∑_{k≠n} cₖ·(2^(k−n) − 1)/(k − n)`,   `cₖ = coeff k ((X−1)ⁿ(2−X)ⁿ) ∈ ℤ`.

For the rational sum to be cleared into an **integer** linear form by `dₙ = lcm(1..n)` (and hence
yield a *convergent* irrationality-measure construction), the fractional powers `2^(k−n)` arising
for `k < n` must already be integral.  They are: this file proves the **2-adic divisibility**

  `2^(n−k) ∣ cₖ`   for `k ≤ n`,

which exactly cancels the `2^(n−k)` denominator of the `t = 2` endpoint term.  Without it the only
available clearing factor is `2ⁿ·lcm(1..n)`, whose size bound `(2·4·(3−2√2))ⁿ = 1.37ⁿ` *diverges*;
with it, the clearing factor is `lcm(1..n) ≤ 4ⁿ·(sub-exp)` and the form size is
`4ⁿ·(3−2√2)ⁿ = 0.686ⁿ → 0`.

The mechanism: every coefficient of `(2−X)ⁿ` of index `j` is divisible by `2^(n−j)`
(`two_pow_dvd_two_sub_X_pow_coeff`), and in the product `(X−1)ⁿ·(2−X)ⁿ` the `(2−X)ⁿ` factor
contributes an index `j ≤ k`, so `2^(n−k) ∣ 2^(n−j) ∣ cₖ`.
-/

namespace DiagonalIntegralLog2

open Polynomial

/-- **Every coefficient of `(2 − X)ⁿ` of index `j` is divisible by `2^(n−j)`.**
(For `j > n` the coefficient is `0`, divisible by everything, and `n − j = 0` in `ℕ`.)
Proof by induction on `n` via the recurrence `(2−X)ⁿ⁺¹ = 2·(2−X)ⁿ − X·(2−X)ⁿ`. -/
theorem two_pow_dvd_two_sub_X_pow_coeff (n j : ℕ) :
    (2 : ℤ) ^ (n - j) ∣ ((2 - X : ℤ[X]) ^ n).coeff j := by
  induction n generalizing j with
  | zero =>
    -- (2 - X)^0 = 1; coeff j 1 = if j = 0 then 1 else 0; `2^(0-j) = 1` divides both.
    rcases j with _ | j
    · simp
    · simp
  | succ n ih =>
    -- p := (2 - X)^n. (2 - X)^(n+1) = 2·p − X·p.
    set p : ℤ[X] := (2 - X : ℤ[X]) ^ n with hp
    have hC2 : (2 : ℤ[X]) = C 2 := by simp
    have hrec : ((2 - X : ℤ[X]) ^ (n + 1)).coeff j
        = 2 * p.coeff j - (X * p).coeff j := by
      rw [pow_succ, mul_comm ((2 - X : ℤ[X]) ^ n) (2 - X), ← hp, sub_mul, hC2,
        Polynomial.coeff_sub, Polynomial.coeff_C_mul]
    rw [hrec]
    rcases j with _ | j
    · -- j = 0 : (X·p).coeff 0 = 0, so the coeff is `2 · p.coeff 0`.
      rw [Polynomial.coeff_X_mul_zero, sub_zero, Nat.sub_zero]
      have h1 : (2 : ℤ) ^ (n - 0) ∣ p.coeff 0 := by simpa using ih 0
      calc (2 : ℤ) ^ (n + 1) = 2 * 2 ^ n := by ring
        _ ∣ 2 * p.coeff 0 := by
            rw [Nat.sub_zero] at h1; exact mul_dvd_mul_left 2 h1
    · -- j+1 : (X·p).coeff (j+1) = p.coeff j.
      rw [Polynomial.coeff_X_mul]
      have hA : (2 : ℤ) ^ (n + 1 - (j + 1)) ∣ 2 * p.coeff (j + 1) := by
        by_cases hjn : j + 1 ≤ n
        · -- n + 1 - (j+1) = (n - (j+1)) + 1
          have he : n + 1 - (j + 1) = (n - (j + 1)) + 1 := by omega
          rw [he, pow_succ, mul_comm]
          exact mul_dvd_mul (dvd_refl 2) (ih (j + 1))
        · -- j+1 > n ⟹ n+1-(j+1) = 0
          have : n + 1 - (j + 1) = 0 := by omega
          rw [this, pow_zero]; exact one_dvd _
      have hB : (2 : ℤ) ^ (n + 1 - (j + 1)) ∣ p.coeff j := by
        have he : n + 1 - (j + 1) = n - j := by omega
        rw [he]; exact ih j
      exact dvd_sub hA hB

/-- **The 2-adic miracle.**  `2^(n−k) ∣ cₖ` where `cₖ = coeff k ((X−1)ⁿ(2−X)ⁿ) ∈ ℤ`, for `k ≤ n`.
In the convolution `cₖ = ∑_{i+j=k} coeff i((X−1)ⁿ)·coeff j((2−X)ⁿ)` every `(2−X)ⁿ` index `j` is
`≤ k`, so `2^(n−k) ∣ 2^(n−j) ∣ coeff j((2−X)ⁿ)`.  (Stated for all `k`; the content is at `k ≤ n`,
since for `k > n` the exponent `n − k` is `0` and the divisibility is vacuous.) -/
theorem two_pow_dvd_coeff (n k : ℕ) :
    (2 : ℤ) ^ (n - k) ∣ ((X - 1 : ℤ[X]) ^ n * (2 - X) ^ n).coeff k := by
  rw [Polynomial.coeff_mul]
  apply Finset.dvd_sum
  rintro ⟨i, j⟩ hij
  have hijk : i + j = k := Finset.mem_antidiagonal.mp hij
  have hjk : j ≤ k := by omega
  have hpow : (2 : ℤ) ^ (n - k) ∣ (2 : ℤ) ^ (n - j) :=
    pow_dvd_pow 2 (Nat.sub_le_sub_left hjk n)
  exact Dvd.dvd.mul_left (hpow.trans (two_pow_dvd_two_sub_X_pow_coeff n j)) _

end DiagonalIntegralLog2
