import Mathlib.Tactic

/-!
# Exponent reduction for Beal's conjecture: prime (and 4) exponents suffice

**The standard first reduction of the Beal problem.** Beal's conjecture asserts
that `A^x + B^y = C^z` has no solution in positive integers with `x, y, z ≥ 3`
and `A, B, C` pairwise coprime. This file mechanizes the elementary observation
that it suffices to prove the conjecture for exponent triples drawn from the
*odd primes together with `4`*.

The mechanism is the substitution identity `A^(d·m) = (A^d)^m`: if `d ∣ x` then a
counterexample at exponent `x` with base `A` is, after replacing `A` by `A^(x/d)`,
a counterexample at exponent `d`. The arithmetic input is that **every `n ≥ 3`
has an odd prime divisor, or else is divisible by `4`** (the only `n ≥ 3` with no
odd prime factor are the powers of two, which are then `≥ 4`). Choosing such a
divisor `p ∣ x`, `q ∣ y`, `r ∣ z` and substituting drops every exponent into the
set `{odd primes} ∪ {4}`, with positivity and coprimality preserved
(`Nat.Coprime.pow`). This is why the literature attacks Beal one prime exponent
at a time.

## Contents
* `exists_prime_or_four_dvd` — every `n ≥ 3` has an odd prime divisor or `4 ∣ n`.
* `beal_reduce_exponent` — the substitution identity `A^x = (A^(x/d))^d` for `d ∣ x`.
* `BealConjecture` / `BealForPrimeExponents` — the two primitive-form statements.
* `beal_of_prime_exponents` — **HEADLINE**: prime-and-4 exponents suffice.
* `beal_iff_prime_exponents` — the equivalence (the reverse direction is trivial).

Dependency policy: mathlib4 permitted. Use `lake env lean BealReduction.lean`
to typecheck. Elementary throughout: `ℕ` with prime/divisibility facts only.
-/

namespace BealReduction

/-- Every `n ≥ 3` has an odd prime divisor, or else `4 ∣ n`.

The only `n ≥ 3` lacking an odd prime factor are the powers of two; such `n` are
`≥ 4` and even, and (being `≥ 4` with no odd part) are divisible by `4`. We argue
on `minFac n`: if it is odd we are done; otherwise it is `2`, and we split on
whether `4 ∣ n`. If not, `n = 2·k` with `k` odd; since `n ≥ 3` is even we have
`n ≥ 4`, so `k ≥ 2`, hence `k` is an odd number `≥ 3` and supplies an odd prime
divisor of `k ∣ n`. -/
theorem exists_prime_or_four_dvd {n : ℕ} (hn : 3 ≤ n) :
    (∃ p, p.Prime ∧ Odd p ∧ p ∣ n) ∨ (4 ∣ n) := by
  have hn0 : n ≠ 0 := by omega
  have hn1 : n ≠ 1 := by omega
  -- minFac is prime and divides n
  have hmf_prime : (n.minFac).Prime := Nat.minFac_prime hn1
  have hmf_dvd : n.minFac ∣ n := Nat.minFac_dvd n
  rcases Nat.even_or_odd n.minFac with hev | hodd
  · -- minFac n is even ⟹ it is 2
    have hmf2 : n.minFac = 2 := (Nat.Prime.even_iff hmf_prime).mp hev
    by_cases h4 : 4 ∣ n
    · exact Or.inr h4
    · -- 2 ∣ n but ¬4 ∣ n ⟹ n = 2*k with k odd
      have h2dvd : 2 ∣ n := hmf2 ▸ hmf_dvd
      obtain ⟨k, hk⟩ := h2dvd
      -- k is odd: else 4 ∣ n
      have hk_odd : Odd k := by
        rcases Nat.even_or_odd k with hke | hko
        · obtain ⟨j, hj⟩ := hke
          exact absurd ⟨j, by omega⟩ h4
        · exact hko
      have hk3 : 3 ≤ k := by
        -- n ≥ 3 even ⟹ n ≥ 4 ⟹ k ≥ 2; k odd ⟹ k ≥ 3
        have : 2 ≤ k := by omega
        rcases hk_odd with ⟨m, hm⟩
        omega
      -- k ≥ 3 has a prime divisor; that prime is odd (k is odd)
      obtain ⟨p, hp_prime, hp_dvd⟩ := Nat.exists_prime_and_dvd (show k ≠ 1 by omega)
      have hp_odd : Odd p := by
        rcases Nat.Prime.eq_two_or_odd' hp_prime with h2 | hodd
        · -- p = 2 would make k even, contradiction
          subst h2
          obtain ⟨j, hj⟩ := hk_odd
          obtain ⟨i, hi⟩ := hp_dvd
          omega
        · exact hodd
      exact Or.inl ⟨p, hp_prime, hp_odd, hp_dvd.trans ⟨2, by omega⟩⟩
  · -- minFac n is odd, and prime, and divides n
    exact Or.inl ⟨n.minFac, hmf_prime, hodd, hmf_dvd⟩

/-- The substitution identity: if `d ∣ x` then `A^x = (A^(x/d))^d`. Substituting a
counterexample at exponent `x` with base `A` by `A^(x/d)` lands it at exponent `d`. -/
theorem beal_reduce_exponent {A : ℕ} {x d : ℕ} (hd : d ∣ x) :
    A ^ x = (A ^ (x / d)) ^ d := by
  rw [← Nat.pow_mul, Nat.div_mul_cancel hd]

/-- Beal's conjecture (primitive form): no positive coprime solution with all
exponents `≥ 3`. Primitivity is encoded by two `Coprime` hypotheses
(`A,B` and `B,C`). -/
def BealConjecture : Prop :=
  ∀ A B C x y z : ℕ, 0 < A → 0 < B → 0 < C →
    3 ≤ x → 3 ≤ y → 3 ≤ z →
    Nat.Coprime A B → Nat.Coprime B C →
    A ^ x + B ^ y = C ^ z → False

/-- Beal's conjecture restricted to exponents that are odd primes or `4`. -/
def BealForPrimeExponents : Prop :=
  ∀ A B C p q r : ℕ, 0 < A → 0 < B → 0 < C →
    (p.Prime ∧ Odd p ∨ p = 4) →
    (q.Prime ∧ Odd q ∨ q = 4) →
    (r.Prime ∧ Odd r ∨ r = 4) →
    Nat.Coprime A B → Nat.Coprime B C →
    A ^ p + B ^ q = C ^ r → False

/-- A prime-or-4 divisor of `n ≥ 3` always exists, packaged for the reduction:
it returns `d ∣ n`, `d ≤ n` (so `n / d ≥ 1`), and the prime-or-4 predicate. -/
private theorem exists_prime_or_four_divisor {n : ℕ} (hn : 3 ≤ n) :
    ∃ d, d ∣ n ∧ 1 ≤ n / d ∧ (d.Prime ∧ Odd d ∨ d = 4) := by
  rcases exists_prime_or_four_dvd hn with ⟨p, hp, hodd, hdvd⟩ | h4
  · refine ⟨p, hdvd, ?_, Or.inl ⟨hp, hodd⟩⟩
    have hple : p ≤ n := Nat.le_of_dvd (by omega) hdvd
    exact Nat.one_le_div_iff (hp.pos) |>.mpr hple
  · refine ⟨4, h4, ?_, Or.inr rfl⟩
    have : (4 : ℕ) ≤ n := Nat.le_of_dvd (by omega) h4
    exact Nat.one_le_div_iff (by norm_num) |>.mpr this

/-- **HEADLINE.** Beal for the odd-prime-and-`4` exponent triples implies the full
Beal conjecture. Given a putative counterexample at `(x, y, z)`, pick prime-or-`4`
divisors `p ∣ x`, `q ∣ y`, `r ∣ z`, and substitute bases `A^(x/p)`, `B^(y/q)`,
`C^(z/r)`. The substitution identity rewrites the equation to one at `(p, q, r)`;
positivity and coprimality of the new bases follow from `Nat.Coprime.pow`. -/
theorem beal_of_prime_exponents (h : BealForPrimeExponents) : BealConjecture := by
  intro A B C x y z hA hB hC hx hy hz hAB hBC heq
  obtain ⟨p, hpx, hpx1, hp⟩ := exists_prime_or_four_divisor hx
  obtain ⟨q, hqy, hqy1, hq⟩ := exists_prime_or_four_divisor hy
  obtain ⟨r, hrz, hrz1, hr⟩ := exists_prime_or_four_divisor hz
  -- substitute the equation
  have heq' : (A ^ (x / p)) ^ p + (B ^ (y / q)) ^ q = (C ^ (z / r)) ^ r := by
    rw [← beal_reduce_exponent hpx, ← beal_reduce_exponent hqy, ← beal_reduce_exponent hrz]
    exact heq
  -- positivity of the new bases
  have hA' : 0 < A ^ (x / p) := pow_pos hA _
  have hB' : 0 < B ^ (y / q) := pow_pos hB _
  have hC' : 0 < C ^ (z / r) := pow_pos hC _
  -- coprimality preserved under taking powers
  have hAB' : Nat.Coprime (A ^ (x / p)) (B ^ (y / q)) := hAB.pow _ _
  have hBC' : Nat.Coprime (B ^ (y / q)) (C ^ (z / r)) := hBC.pow _ _
  exact h (A ^ (x / p)) (B ^ (y / q)) (C ^ (z / r)) p q r
    hA' hB' hC' hp hq hr hAB' hBC' heq'

/-- An odd prime or `4` is `≥ 3`. -/
private theorem three_le_of_prime_or_four {p : ℕ} (h : p.Prime ∧ Odd p ∨ p = 4) :
    3 ≤ p := by
  rcases h with ⟨hp, hodd⟩ | h4
  · -- odd prime ≥ 3 (a prime is ≥ 2, and ≠ 2 since odd)
    have h2 : 2 ≤ p := hp.two_le
    rcases hodd with ⟨m, hm⟩; omega
  · omega

/-- The equivalence: full Beal `↔` Beal for odd-prime-and-`4` exponents. The
reverse direction is immediate since odd primes and `4` are all `≥ 3`. -/
theorem beal_iff_prime_exponents : BealConjecture ↔ BealForPrimeExponents := by
  constructor
  · intro h A B C p q r hA hB hC hp hq hr hAB hBC heq
    exact h A B C p q r hA hB hC
      (three_le_of_prime_or_four hp) (three_le_of_prime_or_four hq)
      (three_le_of_prime_or_four hr) hAB hBC heq
  · exact beal_of_prime_exponents

end BealReduction
