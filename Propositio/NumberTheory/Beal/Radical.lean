import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic

/-!
# The integer radical and the ABC-backbone of Beal's conjecture (Lean 4)

Mathlib4 carries a *polynomial* radical (`Mathlib/RingTheory/Radical/Basic.lean`,
`Polynomial.radical`) and the general `UniqueFactorizationMonoid.radical`, but it
has **no dedicated integer radical** `rad : ℕ → ℕ` with the squarefree-kernel
identities one wants for ABC. This file builds it and the key identities.

The radical of `n` is the product of its distinct prime factors,
`rad(n) = ∏_{p ∣ n, p prime} p`. Its defining feature is that it is
**exponent-blind**: `rad(aᵏ) = rad(a)` for `k ≠ 0`. Consequently a Beal solution
`Aˣ + Bʸ = Cᶻ` is an *extreme ABC triple*:

  `rad(Aˣ · Bʸ · Cᶻ) = rad(A·B·C) ≤ A·B·C`,

a quantity that is tiny compared to the value `Cᶻ`. This is the formal backbone of
the implication **ABC ⟹ Beal**: under the ABC conjecture, `Cᶻ` is bounded by a
near-linear power of `rad(Aˣ Bʸ Cᶻ) = rad(ABC)`, which forces the exponents down.

## Contents
* `radical` — the integer radical.
* `radical_pow` — exponent-blindness.
* `radical_coprime_mul` — multiplicativity on coprime arguments.
* `radical_dvd_self`, `radical_le_self`, `radical_pos` — basic estimates.
* `primeFactors_beal_eq` / `radical_beal_eq` — the **headline**: the radical of a
  Beal product equals `rad(ABC)`, with no coprimality among `A, B, C` required.
* `radical_beal_le` — the quantitative core `rad(Aˣ Bʸ Cᶻ) ≤ A·B·C`.
* `ABCConjecture` / `beal_abc_bounded` — the ABC conjecture as a `Prop`, and the
  derived statement that primitive Beal solutions are ABC-bounded.

Key mathlib lemmas relied on:
* `Nat.primeFactors_pow`, `Nat.primeFactors_mul`, `Nat.Coprime.primeFactors_mul`.
* `Nat.Coprime.disjoint_primeFactors`, `Finset.prod_union`, `Finset.prod_pos`.
* `Nat.prod_primeFactors_dvd`, `Nat.le_of_dvd`, `Nat.prime_of_mem_primeFactors`.

Dependency policy: mathlib4 permitted (user authorization 2026-05-17). Use
`lake env lean BealRadical.lean` to typecheck.
-/

namespace BealRadical

open Finset

/-! ## 1. The integer radical -/

/-- The **radical** of a natural number `n`: the product of its distinct prime
factors, `rad(n) = ∏_{p ∣ n, p prime} p`. The squarefree kernel of `n`.
(Mathlib has only a polynomial / UFM radical; this is the integer one.) -/
def radical (n : ℕ) : ℕ := ∏ p ∈ n.primeFactors, p

/-! ## 2. Exponent-blindness -/

/-- The radical is **exponent-blind**: `rad(aᵏ) = rad(a)` for any `k ≠ 0`. This is
the property that makes a Beal solution an extreme ABC triple. -/
theorem radical_pow {a k : ℕ} (hk : k ≠ 0) : radical (a ^ k) = radical a := by
  unfold radical
  rw [Nat.primeFactors_pow a hk]

/-! ## 3. Multiplicativity on coprime arguments -/

/-- The radical is **multiplicative on coprime arguments**:
`rad(a·b) = rad(a)·rad(b)` when `gcd(a,b) = 1`. (Coprimality makes the prime-factor
sets disjoint, so the product splits.) -/
theorem radical_coprime_mul {a b : ℕ} (hab : Nat.Coprime a b) :
    radical (a * b) = radical a * radical b := by
  unfold radical
  rw [hab.primeFactors_mul, Finset.prod_union hab.disjoint_primeFactors]

/-! ## 4. Basic estimates -/

/-- The radical divides its argument: `rad(n) ∣ n`. -/
theorem radical_dvd_self {n : ℕ} (hn : n ≠ 0) : radical n ∣ n :=
  Nat.prod_primeFactors_dvd n

/-- The radical is bounded by its argument: `rad(n) ≤ n` for `n > 0`. -/
theorem radical_le_self {n : ℕ} (hn : 0 < n) : radical n ≤ n :=
  Nat.le_of_dvd hn (radical_dvd_self hn.ne')

/-- The radical is positive: `0 < rad(n)` for `n > 0` (a product of primes, each
`> 0`). -/
theorem radical_pos {n : ℕ} (hn : 0 < n) : 0 < radical n := by
  unfold radical
  exact Finset.prod_pos fun p hp => (Nat.prime_of_mem_primeFactors hp).pos

/-! ## 5. The Beal product: the ABC backbone

The crux. The prime-factor set of a Beal product `Aˣ·Bʸ·Cᶻ` (exponents nonzero)
equals that of `A·B·C` — **no coprimality among `A, B, C` is needed**, only that
the bases are nonzero (required for `Nat.primeFactors_mul`). Hence the radicals
coincide. -/

/-- The prime-factor set of a Beal product equals that of `A·B·C`:
`(Aˣ·Bʸ·Cᶻ).primeFactors = (A·B·C).primeFactors`. The exponents drop out by
exponent-blindness of `primeFactors`. -/
theorem primeFactors_beal_eq {A B C x y z : ℕ}
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) :
    (A ^ x * B ^ y * C ^ z).primeFactors = (A * B * C).primeFactors := by
  rw [Nat.primeFactors_mul (mul_ne_zero (pow_ne_zero _ hA) (pow_ne_zero _ hB))
        (pow_ne_zero _ hC),
      Nat.primeFactors_mul (pow_ne_zero _ hA) (pow_ne_zero _ hB),
      Nat.primeFactors_pow A hx, Nat.primeFactors_pow B hy, Nat.primeFactors_pow C hz,
      Nat.primeFactors_mul (mul_ne_zero hA hB) hC, Nat.primeFactors_mul hA hB]

/-- **Headline.** The radical of a Beal product equals `rad(A·B·C)`:
`rad(Aˣ·Bʸ·Cᶻ) = rad(A·B·C)`, for nonzero bases and nonzero exponents — with **no
coprimality among `A, B, C`**. Because `rad` is exponent-blind, a Beal solution
`Aˣ + Bʸ = Cᶻ` has the same radical as the (tiny) product `A·B·C`; this is what
makes it an extreme ABC triple. -/
theorem radical_beal_eq {A B C x y z : ℕ}
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) :
    radical (A ^ x * B ^ y * C ^ z) = radical (A * B * C) := by
  unfold radical
  rw [primeFactors_beal_eq hA hB hC hx hy hz]

/-- **Quantitative core.** The radical of a Beal product is bounded by `A·B·C`:
`rad(Aˣ·Bʸ·Cᶻ) ≤ A·B·C`. The left side is the radical of the (large) Beal values;
the right side is the small product of bases. This `tiny radical / huge value` gap
is exactly the ABC-extremity of Beal solutions. -/
theorem radical_beal_le {A B C x y z : ℕ}
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) :
    radical (A ^ x * B ^ y * C ^ z) ≤ A * B * C := by
  rw [radical_beal_eq hA hB hC hx hy hz]
  exact radical_le_self (by positivity)

/-! ## 6. ABC conjecture and the Beal consequence

We formulate the ABC conjecture over `ℝ` and derive the formal statement that a
primitive Beal solution is ABC-bounded: its value `Cᶻ` is controlled by a
near-linear power of `rad(ABC) ≤ ABC`. -/

/-- The **ABC conjecture**: for every `ε > 0` there is a constant `K > 0` such that
for all coprime positive `a, b` with `a + b = c`,
`c ≤ K · rad(a·b·c)^(1+ε)`. -/
def ABCConjecture : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, 0 < K ∧
    ∀ a b c : ℕ, 0 < a → 0 < b → 0 < c → Nat.Coprime a b → a + b = c →
      (c : ℝ) ≤ K * (radical (a * b * c) : ℝ) ^ (1 + ε)

/-- **Beal solutions are ABC-bounded.** Assume the ABC conjecture. Fix `ε > 0` and
let `K` be the corresponding constant. Then any *primitive* Beal solution
`Aˣ + Bʸ = Cᶻ` (with `Aˣ`, `Bʸ` coprime and all of `A, B, C` and `x, y, z`
nonzero) satisfies

  `(Cᶻ : ℝ) ≤ K · (A·B·C)^(1+ε)`.

The proof applies ABC to `a := Aˣ`, `b := Bʸ`, `c := Cᶻ`, then rewrites
`rad(Aˣ·Bʸ·Cᶻ) = rad(A·B·C) ≤ A·B·C` via `radical_beal_eq` and `radical_le_self`.
This is the formal core of "ABC ⟹ Beal": the right-hand side grows only like a
near-linear power of the small product `A·B·C`, while the left-hand side is the
full value `Cᶻ`. -/
theorem beal_abc_bounded
    (habc : ABCConjecture) {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧
      ∀ A B C x y z : ℕ,
        A ≠ 0 → B ≠ 0 → C ≠ 0 → x ≠ 0 → y ≠ 0 → z ≠ 0 →
        Nat.Coprime (A ^ x) (B ^ y) → A ^ x + B ^ y = C ^ z →
        ((C ^ z : ℕ) : ℝ) ≤ K * (A * B * C : ℝ) ^ (1 + ε) := by
  obtain ⟨K, hK, hbound⟩ := habc ε hε
  refine ⟨K, hK, ?_⟩
  intro A B C x y z hA hB hC hx hy hz hcop hsum
  have hAx : 0 < A ^ x := pow_pos (Nat.pos_of_ne_zero hA) x
  have hBy : 0 < B ^ y := pow_pos (Nat.pos_of_ne_zero hB) y
  have hCz : 0 < C ^ z := pow_pos (Nat.pos_of_ne_zero hC) z
  -- ABC applied to the Beal triple.
  have key := hbound (A ^ x) (B ^ y) (C ^ z) hAx hBy hCz hcop hsum
  -- Rewrite the radical of the Beal product as rad(ABC) ≤ ABC.
  have hrad : radical (A ^ x * B ^ y * C ^ z) ≤ A * B * C :=
    radical_beal_le hA hB hC hx hy hz
  have hABC : (0 : ℝ) < (A * B * C : ℕ) := by
    have : 0 < A * B * C := by positivity
    exact_mod_cast this
  -- Monotonicity of `t ↦ t^(1+ε)` in `t ≥ 0` carries the radical bound through.
  have hmono :
      (radical (A ^ x * B ^ y * C ^ z) : ℝ) ^ (1 + ε)
        ≤ ((A * B * C : ℕ) : ℝ) ^ (1 + ε) := by
    apply Real.rpow_le_rpow (by positivity)
    · exact_mod_cast hrad
    · positivity
  calc ((C ^ z : ℕ) : ℝ)
      ≤ K * (radical (A ^ x * B ^ y * C ^ z) : ℝ) ^ (1 + ε) := key
    _ ≤ K * ((A * B * C : ℕ) : ℝ) ^ (1 + ε) := by
          apply mul_le_mul_of_nonneg_left hmono hK.le
    _ = K * (A * B * C : ℝ) ^ (1 + ε) := by push_cast; ring_nf

end BealRadical
