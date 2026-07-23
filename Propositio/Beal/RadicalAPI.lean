import Propositio.Beal.Radical

/-!
# The integer radical: the full natural API (Lean 4)

Mathlib4 carries only a *polynomial* radical (`Polynomial.radical`) and the general
`UniqueFactorizationMonoid.radical`; it has **no dedicated integer radical**. The
companion file `BealRadical.lean` introduces

  `rad(n) = ∏_{p ∣ n, p prime} p`,

the **squarefree kernel** of `n` — the central object of the ABC conjecture — and
proves the headline Beal/ABC facts (`radical_pow`, `radical_coprime_mul`,
`radical_dvd_self`, `radical_le_self`, `radical_pos`). This file rounds out the
standard reusable API one expects of `rad`:

* boundary values `rad 0 = rad 1 = 1`;
* evaluation on primes and prime powers (`rad p = p`, `rad (pᵏ) = p`);
* **squarefreeness** `Squarefree (rad n)` — the radical is a product of distinct
  primes, hence squarefree;
* **idempotence** `rad (rad n) = rad n` — `rad` is a projection onto squarefree
  numbers;
* `rad n = n ↔ Squarefree n` (the fixed points of `rad` are the squarefree
  numbers);
* **divisibility-monotonicity** `m ∣ n → rad m ∣ rad n`;
* **sub-multiplicativity** `rad (m·n) ∣ rad m · rad n` (with equality on coprime
  arguments, already `BealRadical.radical_coprime_mul`);
* lower bounds `1 ≤ rad n` and `2 ≤ rad n` for `n > 1`.

These are the structural lemmas (squarefree, idempotent, divisibility-monotone,
sub-multiplicative) that any ABC development reuses. Foundation for `BealRadical`
and downstream `BealABC*` files.

Key mathlib lemmas relied on:
* `Nat.primeFactors_prod`, `Nat.prod_primeFactors_of_squarefree`.
* `Nat.primeFactors_mono`, `Nat.primeFactors_mul`, `Nat.primeFactors_pow`.
* `Nat.Prime.primeFactors`, `Nat.primeFactors_prime_pow`.
* `Nat.coprime_primes`, `Nat.coprime_iff_isRelPrime`, `Nat.Prime.squarefree`.
* `Finset.squarefree_prod_of_pairwise_isCoprime`, `Finset.prod_dvd_prod_of_subset`.

Dependency policy: mathlib4 permitted (user authorization 2026-05-17). Use
`lake env lean BealRadicalAPI.lean` to typecheck.
-/

namespace BealRadicalAPI

open Finset BealRadical

/-! ## 0. The defining product (bridge lemma) -/

/-- The defining identity, exposed for rewriting: `rad n = ∏_{p ∈ primeFactors n} p`.
Definitional, but handy as a named bridge. -/
theorem prod_primeFactors_eq_radical (n : ℕ) :
    ∏ p ∈ n.primeFactors, p = radical n := rfl

/-! ## 1. Boundary values -/

/-- `rad 0 = 1`: `0` has no prime factors, so the product is empty. -/
@[simp] theorem radical_zero : radical 0 = 1 := by
  unfold radical; rw [Nat.primeFactors_zero, Finset.prod_empty]

/-- `rad 1 = 1`: `1` has no prime factors, so the product is empty. -/
@[simp] theorem radical_one : radical 1 = 1 := by
  unfold radical; rw [Nat.primeFactors_one, Finset.prod_empty]

/-! ## 2. Primes and prime powers -/

/-- The radical of a prime is itself: `rad p = p`. -/
@[simp] theorem radical_prime {p : ℕ} (hp : p.Prime) : radical p = p := by
  unfold radical; rw [hp.primeFactors, Finset.prod_singleton]

/-- The radical of a prime power is the prime: `rad (pᵏ) = p` for `k ≠ 0`. -/
theorem radical_prime_pow {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) :
    radical (p ^ k) = p := by
  rw [radical_pow hk, radical_prime hp]

/-! ## 3. The radical is a product of distinct primes -/

/-- The prime factors of `rad n` are exactly the prime factors of `n`:
`(rad n).primeFactors = n.primeFactors`. (The radical re-collects the same primes,
each to the first power.) -/
@[simp] theorem primeFactors_radical (n : ℕ) :
    (radical n).primeFactors = n.primeFactors := by
  unfold radical
  exact Nat.primeFactors_prod fun p hp => Nat.prime_of_mem_primeFactors hp

/-- **The radical is squarefree:** `Squarefree (rad n)`. The radical is a product
of *distinct* primes (pairwise coprime, each squarefree), hence squarefree. -/
theorem squarefree_radical {n : ℕ} (hn : n ≠ 0) : Squarefree (radical n) := by
  unfold radical
  refine Finset.squarefree_prod_of_pairwise_isCoprime ?_ ?_
  · intro p hp q hq hpq
    rw [Function.onFun, ← Nat.coprime_iff_isRelPrime]
    exact (Nat.coprime_primes (Nat.prime_of_mem_primeFactors hp)
      (Nat.prime_of_mem_primeFactors hq)).2 hpq
  · intro p hp
    exact (Nat.prime_of_mem_primeFactors hp).prime.squarefree

/-! ## 4. Divisibility of the radical -/

/-- The radical divides its argument: `rad n ∣ n` (including `n = 0`, since
`rad 0 = 1 ∣ 0`). -/
theorem radical_dvd_self {n : ℕ} : radical n ∣ n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · exact BealRadical.radical_dvd_self hn

/-! ## 5. Idempotence and the fixed points of `rad` -/

/-- **Idempotence:** `rad (rad n) = rad n`. The radical of a squarefree number is
itself, and `rad n` is squarefree. -/
@[simp] theorem radical_idem (n : ℕ) : radical (radical n) = radical n := by
  conv_lhs => rw [radical, primeFactors_radical]
  rfl

/-- The fixed points of `rad` are exactly the squarefree numbers:
`rad n = n ↔ Squarefree n` (for `n ≠ 0`). -/
theorem radical_eq_self_iff_squarefree {n : ℕ} (hn : n ≠ 0) :
    radical n = n ↔ Squarefree n := by
  constructor
  · intro h; rw [← h]; exact squarefree_radical hn
  · intro h; unfold radical; exact Nat.prod_primeFactors_of_squarefree h

/-! ## 6. Monotonicity under divisibility -/

/-- **Divisibility-monotonicity:** `m ∣ n → rad m ∣ rad n` (for `n ≠ 0`). The
prime-factor sets are monotone under divisibility, so the products divide. -/
theorem radical_dvd_radical_of_dvd {m n : ℕ} (hn : n ≠ 0) (h : m ∣ n) :
    radical m ∣ radical n := by
  unfold radical
  exact Finset.prod_dvd_prod_of_subset _ _ _ (Nat.primeFactors_mono h hn)

/-! ## 7. Sub-multiplicativity -/

/-- **Sub-multiplicativity:** `rad (m·n) ∣ rad m · rad n`. (Equality holds on
coprime arguments — that is `BealRadical.radical_coprime_mul`.) -/
theorem radical_mul_dvd {m n : ℕ} : radical (m * n) ∣ radical m * radical n := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  unfold radical
  rw [Nat.primeFactors_mul hm hn]
  -- `(∏ S)(∏ T) = (∏ S∪T)(∏ S∩T)`, so `∏ S∪T ∣ (∏ S)(∏ T)`.
  exact ⟨_, Finset.prod_union_inter.symm⟩

/-! ## 8. Lower bounds -/

/-- The radical is at least `1`: `1 ≤ rad n`. -/
theorem one_le_radical (n : ℕ) : 1 ≤ radical n := by
  unfold radical
  exact Finset.one_le_prod' fun p hp => (Nat.prime_of_mem_primeFactors hp).one_lt.le

/-- The radical is positive (restated without a positivity hypothesis on `n`):
`0 < rad n`. -/
theorem radical_pos' (n : ℕ) : 0 < radical n := one_le_radical n

/-- For `n > 1` the radical is at least `2`: a number `> 1` has a prime factor, and
every prime is `≥ 2`. -/
theorem two_le_radical_of_one_lt {n : ℕ} (hn : 1 < n) : 2 ≤ radical n := by
  obtain ⟨p, hp⟩ := Nat.nonempty_primeFactors.2 hn
  unfold radical
  have hp2 : 2 ≤ p := (Nat.prime_of_mem_primeFactors hp).two_le
  calc 2 ≤ p := hp2
    _ ≤ ∏ q ∈ n.primeFactors, q :=
        Finset.single_le_prod' (fun q hq => (Nat.prime_of_mem_primeFactors hq).one_lt.le) hp

end BealRadicalAPI
