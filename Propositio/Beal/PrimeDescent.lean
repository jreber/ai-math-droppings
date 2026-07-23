import Mathlib.RingTheory.Coprime.Basic
import Mathlib.RingTheory.Int.Basic
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic
import Propositio.Beal.CubeDescent

/-!
# Prime-exponent sum descent reduction toward Beal-(p, p, z) (case `p ∤ (A + B)`)

**NEW mathematics — no LaTTe sibling.** This file generalizes the Eisenstein
*cube-sum* (`p = 3`) descent of `BealEisenstein.lean` / `BealCubeDescent.lean` to
**all odd primes `p`** — the first descent step of the Beal equation
`A^p + B^p = C^z` toward Beal-`(p, p, z)`.

For an odd prime `p`, the prime-power sum factors as

  `A^p + B^p = (A + B) · Φ`,   `Φ = Σ_{i=0}^{p-1} (−1)^i A^{p−1−i} B^i`,

the "cyclotomic-like" cofactor. For `p = 3`, `Φ = A² − A·B + B²` recovers the
Eisenstein quadratic of `BealEisenstein` (`cube_sum_factor`). The arithmetic
heart is the **gcd dichotomy**: for coprime `A, B`,

  `gcd(A + B, Φ) ∈ {1, p}`.

The reason is the congruence `Φ ≡ p · A^{p−1} (mod A + B)` (each term reduces, via
`B ≡ −A (mod A + B)`, to `A^{p−1}`), so a common divisor of `A + B` and `Φ`
divides `p · A^{p−1}`; coprimality of `A, B` makes it coprime to `A`, hence it
divides `p` (prime). This generalizes
`BealEisenstein.eisenstein_gcd_eq_one_or_three`.

The **descent reduction** (case `p ∤ (A + B)`): when `p ∤ (A + B)` the `p` branch
is excluded, so `A + B` and `Φ` are genuinely coprime, and a coprime factorization
of a perfect `z`-th power forces each factor to be a perfect `z`-th power:

  `A^p + B^p = C^z`, `Nat.Coprime A B`, `p ∤ (A + B)`, `z ≠ 0`  ⟹
  `∃ s t, A + B = sᶻ ∧ Φ = tᶻ ∧ C = s·t`.

This mirrors `BealCubeDescent.cube_sum_descent`, with the role of `3` played by the
general odd prime `p`, reusing `BealCubeDescent.eq_pow_of_coprime_mul` for the
coprime-power extraction.

We work over `ℤ` (the alternating sign in `Φ` is honest only with genuine
subtraction; over `ℕ` truncated subtraction would distort it). The headline
descent is stated over `ℕ`, bridging through the nat-cast of `Φ` (whose value is
nonnegative for the relevant inputs is *not* needed — we keep `Φ` over `ℤ` and
phrase the nat factorization through `Int.toNat` / casts only where required).

Key mathlib lemmas relied on:
* `geom_sum₂_mul` — `(∑ i, x^i y^{n−1−i})·(x − y) = x^n − y^n`, the source of the
  `A^p + B^p = (A + B)·Φ` factorization (`Odd.add_dvd_pow_add_pow` is the
  divisibility-only shadow).
* `Finset.dvd_sum`, `sub_dvd_pow_sub_pow` — the term-by-term congruence
  `Φ ≡ p·A^{p−1} (mod A + B)`.
* `IsCoprime` Bézout closure (`IsCoprime.pow_right`, `.mul_right`) — `d ∣ p` from
  `d ∣ p·A^{p−1}` and `d` coprime to `A`.
* `BealCubeDescent.eq_pow_of_coprime_mul`, `Nat.pow_left_injective` — the descent.

Dependency policy: mathlib4 permitted (user authorization 2026-05-17). Use
`lake env lean BealPrimeDescent.lean` to typecheck.
-/

namespace BealPrimeDescent

open Finset

/-- **The cyclotomic-like cofactor `Φ`.**
`Φ p A B = Σ_{i=0}^{p−1} (−1)^i A^{p−1−i} B^i`. For `p = 3` this is
`A² − A·B + B²`, the Eisenstein quadratic of `BealEisenstein.cube_sum_factor`. -/
def Phi (p : ℕ) (A B : ℤ) : ℤ :=
  ∑ i ∈ Finset.range p, (-1) ^ i * A ^ (p - 1 - i) * B ^ i

/-- `Φ 3 A B = A² − A·B + B²` — the `p = 3` cofactor is the Eisenstein quadratic,
recovering `BealEisenstein` / `BealCubeDescent`. -/
theorem Phi_three (A B : ℤ) : Phi 3 A B = A ^ 2 - A * B + B ^ 2 := by
  simp [Phi, Finset.sum_range_succ]; ring

/-!
## 1. The prime-power sum factorization

`A^p + B^p = (A + B) · Φ` for odd `p`, from mathlib's `geom_sum₂_mul` specialized
to `y := −B`.
-/

/-- **Prime-power sum factorization.**
For odd `p`, `A^p + B^p = (A + B) · Φ p A B`. Generalizes
`BealEisenstein.cube_sum_factor` (`p = 3`).

Proof: `geom_sum₂_mul A (−B) p` gives
`(∑ i, A^i (−B)^{p−1−i})·(A − (−B)) = A^p − (−B)^p`; for odd `p`,
`(−B)^p = −B^p`, turning the right side into `A^p + B^p` and `A − (−B)` into
`A + B`. The geometric sum is `Φ` after the reindex `i ↦ p − 1 − i` and pulling
out the sign `(−B)^j = (−1)^j B^j`. -/
theorem sum_pow_eq (p : ℕ) (hp : Odd p) (A B : ℤ) :
    A ^ p + B ^ p = (A + B) * Phi p A B := by
  -- mathlib geometric factorization with y := -B
  have hg := geom_sum₂_mul A (-B) p
  rw [Odd.neg_pow hp, sub_neg_eq_add, sub_neg_eq_add] at hg
  -- hg : (∑ i ∈ range p, A^i * (-B)^(p-1-i)) * (A + B) = A^p + B^p
  -- Identify the geometric sum with Φ by reindexing i ↦ p - 1 - i.
  have hsum : (∑ i ∈ Finset.range p, A ^ i * (-B) ^ (p - 1 - i)) = Phi p A B := by
    rw [Phi]
    -- reindex via the reflection i ↦ p - 1 - i on range p
    rw [← Finset.sum_range_reflect (fun i => A ^ i * (-B) ^ (p - 1 - i)) p]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    -- after reflect, index becomes p - 1 - i; exponents: A^(p-1-i), (-B)^(p-1-(p-1-i)) = (-B)^i
    have h1 : p - 1 - (p - 1 - i) = i := by omega
    rw [h1]
    rw [show ((-B) ^ i : ℤ) = (-1) ^ i * B ^ i by rw [← neg_one_mul, mul_pow]]
    ring
  rw [← hsum, mul_comm]
  exact hg.symm

/-!
## 2. The congruence `Φ ≡ p · A^{p−1} (mod A + B)`

Each term `(−1)^i A^{p−1−i} B^i` reduces mod `A + B` (where `B ≡ −A`) to
`A^{p−1}`; the `p` terms sum to `p · A^{p−1}`.
-/

/-- **Congruence `Φ ≡ p · A^{p−1} (mod A + B)`.**
`(A + B) ∣ (Φ p A B − p · A^{p−1})`.

Proof: term-by-term, `(−1)^i A^{p−1−i} B^i − A^{p−1}` is divisible by `A + B`,
because `B^i − (−A)^i` is divisible by `B − (−A) = A + B` (`sub_dvd_pow_sub_pow`)
and `(−1)^i A^{p−1−i}·(−A)^i = A^{p−1}`. Summing the `p` term-differences via
`Finset.dvd_sum` gives the result, since `Σ_i A^{p−1} = p·A^{p−1}`. -/
theorem Phi_mod_sum (p : ℕ) (hp : p.Prime) (_hodd : Odd p) (A B : ℤ) :
    (A + B) ∣ (Phi p A B - (p : ℤ) * A ^ (p - 1)) := by
  -- Φ − p·A^{p-1} = Σ_{i<p} [ (-1)^i A^{p-1-i} B^i − A^{p-1} ].
  have hp1 : 1 ≤ p := hp.one_lt.le
  have hrw : Phi p A B - (p : ℤ) * A ^ (p - 1)
      = ∑ i ∈ Finset.range p, ((-1) ^ i * A ^ (p - 1 - i) * B ^ i - A ^ (p - 1)) := by
    rw [Phi, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [hrw]
  apply Finset.dvd_sum
  intro i hi
  rw [Finset.mem_range] at hi
  -- A^{p-1} = (-1)^i A^{p-1-i} · (-A)^i  (since (-1)^i (-A)^i = A^i and (p-1-i)+i = p-1).
  have hexp : (p - 1 - i) + i = p - 1 := by omega
  have hAeq : A ^ (p - 1) = (-1) ^ i * A ^ (p - 1 - i) * (-A) ^ i := by
    rw [show ((-A) ^ i : ℤ) = (-1) ^ i * A ^ i by rw [← neg_one_mul, mul_pow]]
    rw [show ((-1 : ℤ)) ^ i * A ^ (p - 1 - i) * ((-1) ^ i * A ^ i)
        = ((-1) ^ i * (-1) ^ i) * (A ^ (p - 1 - i) * A ^ i) by ring]
    rw [← pow_add A, hexp, ← mul_pow]
    simp
  rw [hAeq]
  -- factor out (-1)^i A^{p-1-i}; remaining factor B^i − (-A)^i divisible by B − (-A) = A + B.
  have hfac : (-1) ^ i * A ^ (p - 1 - i) * B ^ i - (-1) ^ i * A ^ (p - 1 - i) * (-A) ^ i
      = (-1) ^ i * A ^ (p - 1 - i) * (B ^ i - (-A) ^ i) := by ring
  rw [hfac]
  apply Dvd.dvd.mul_left
  have hd := sub_dvd_pow_sub_pow B (-A) i
  -- B - (-A) = A + B
  have : B - (-A) = A + B := by ring
  rwa [this] at hd

/-!
## 3. The gcd dichotomy `gcd(A + B, Φ) ∈ {1, p}`

A common divisor of `A + B` and `Φ` divides `p`, by combining the congruence with
coprimality of `A, B`.
-/

/-- **Common divisor of `A + B`, `Φ` divides `p` (HEADLINE gcd dichotomy core).**
For odd prime `p` and coprime `A, B` (over `ℤ`), any common divisor `d` of
`A + B` and `Φ p A B` divides `p`. Generalizes
`BealEisenstein.eisenstein_gcd_divides_three`.

Proof: from `Phi_mod_sum`, `d ∣ Φ` and `d ∣ (A + B) ∣ (Φ − p·A^{p−1})` give
`d ∣ p·A^{p−1}`. Coprimality `IsCoprime A B` plus `d ∣ A + B` make `d` coprime to
`A` (and to `A^{p−1}`), so `d ∣ p`. -/
theorem dvd_prime_of_dvd_sum_factor (p : ℕ) (hp : p.Prime) (hodd : Odd p)
    (A B d : ℤ) (hcop : IsCoprime A B)
    (hs : d ∣ A + B) (hq : d ∣ Phi p A B) : d ∣ (p : ℤ) := by
  -- d ∣ p·A^{p-1}: from d ∣ Φ and d ∣ (A+B) ∣ (Φ - p·A^{p-1}).
  have hmod : (A + B) ∣ (Phi p A B - (p : ℤ) * A ^ (p - 1)) := Phi_mod_sum p hp hodd A B
  have hdmod : d ∣ (Phi p A B - (p : ℤ) * A ^ (p - 1)) := hs.trans hmod
  have hdpA : d ∣ A ^ (p - 1) * (p : ℤ) := by
    have hsub := dvd_sub hq hdmod
    have : Phi p A B - (Phi p A B - (p : ℤ) * A ^ (p - 1)) = A ^ (p - 1) * (p : ℤ) := by ring
    rwa [this] at hsub
  -- d is coprime to A: d ∣ A+B and IsCoprime A B ⟹ IsCoprime d A.
  -- IsCoprime A B ⟹ IsCoprime (A+B) A (since gcd(A+B,A) | gcd(B,A) essentially).
  have hcopABA : IsCoprime (A + B) A := by
    have : IsCoprime B A := hcop.symm
    simpa [add_comm] using this.add_mul_left_left 1
  have hcopdA : IsCoprime d A := hcopABA.of_isCoprime_of_dvd_left hs
  -- d coprime to A^{p-1}.
  have hcopdApow : IsCoprime d (A ^ (p - 1)) := hcopdA.pow_right
  -- d ∣ A^{p-1}·p and coprime to A^{p-1} ⟹ d ∣ p.
  exact hcopdApow.dvd_of_dvd_mul_left hdpA

/-- **Prime-power gcd dichotomy (HEADLINE), divisor form.**
For odd prime `p` and coprime `A, B`, any **nonnegative** common divisor `d` of
`A + B` and `Φ p A B` is `1` or `p`. Generalizes
`BealEisenstein.eisenstein_gcd_one_or_three`. -/
theorem gcd_one_or_prime (p : ℕ) (hp : p.Prime) (hodd : Odd p)
    (A B d : ℤ) (hd : 0 ≤ d) (hcop : IsCoprime A B)
    (hs : d ∣ A + B) (hq : d ∣ Phi p A B) : d = 1 ∨ d = (p : ℤ) := by
  have hdp : d ∣ (p : ℤ) := dvd_prime_of_dvd_sum_factor p hp hodd A B d hcop hs hq
  -- Convert to ℕ: d.natAbs ∣ p, and Nat.Prime p gives natAbs ∈ {1, p}.
  have hdnat : d.natAbs ∣ p := by
    have : (d.natAbs : ℤ) ∣ (p : ℤ) := by
      rw [Int.natCast_natAbs]; exact (abs_dvd d (p : ℤ)).mpr hdp
    exact_mod_cast this
  -- d.natAbs = d since 0 ≤ d.
  have hcast : (d.natAbs : ℤ) = d := by
    rw [Int.natCast_natAbs, abs_of_nonneg hd]
  rcases (Nat.Prime.eq_one_or_self_of_dvd hp d.natAbs hdnat) with h1 | hp'
  · left; rw [← hcast, h1]; norm_num
  · right; rw [← hcast, hp']

/-- **Prime-power gcd dichotomy (HEADLINE), `gcd` form.**
For odd prime `p` and coprime `A, B`, `Int.gcd (A + B) (Φ p A B) = 1 ∨ = p`.
Generalizes `BealEisenstein.eisenstein_gcd_eq_one_or_three`. -/
theorem gcd_sum_factor_eq_one_or_prime (p : ℕ) (hp : p.Prime) (hodd : Odd p)
    (A B : ℤ) (hcop : IsCoprime A B) :
    Int.gcd (A + B) (Phi p A B) = 1 ∨ Int.gcd (A + B) (Phi p A B) = p := by
  set s := A + B
  set q := Phi p A B
  have hgnn : (0 : ℤ) ≤ (Int.gcd s q : ℤ) := Int.natCast_nonneg _
  have hgs : (Int.gcd s q : ℤ) ∣ s := Int.gcd_dvd_left s q
  have hgq : (Int.gcd s q : ℤ) ∣ q := Int.gcd_dvd_right s q
  rcases gcd_one_or_prime p hp hodd A B (Int.gcd s q : ℤ) hgnn hcop hgs hgq with h | h
  · left; exact_mod_cast h
  · right; exact_mod_cast h

/-!
## 4. The descent reduction `A^p + B^p = C^z` toward Beal-(p, p, z)

The case `p ∤ (A + B)`: the gcd dichotomy excludes the `p` branch, the two factors
`A + B` and `Φ` are coprime, and a coprime factorization of a perfect `z`-th power
splits into perfect `z`-th powers. We package `Φ` over `ℕ` as the cofactor
`(Φ p A B).toNat`.
-/

/-- **`Φ ≥ 0` over `ℕ` inputs (not both zero).**
For naturals `A, B` not both zero (so `A + B ≥ 1`), the integer cofactor
`Φ p (A) (B)` is nonnegative, because `(A + B)·Φ = A^p + B^p ≥ 0` and `A + B > 0`. -/
theorem Phi_nonneg_of_natCast (p : ℕ) (hp : Odd p) (A B : ℕ) (hAB : 0 < A + B) :
    0 ≤ Phi p (A : ℤ) (B : ℤ) := by
  have hfac := sum_pow_eq p hp (A : ℤ) (B : ℤ)
  have hpos : (0 : ℤ) < (A : ℤ) + B := by exact_mod_cast hAB
  -- (A+B)·Φ = A^p + B^p ≥ 0.
  have hge : (0 : ℤ) ≤ ((A : ℤ) + B) * Phi p (A : ℤ) (B : ℤ) := by
    rw [← hfac]; positivity
  by_contra hneg
  rw [not_le] at hneg
  have : ((A : ℤ) + B) * Phi p (A : ℤ) (B : ℤ) < 0 := mul_neg_of_pos_of_neg hpos hneg
  exact absurd hge (not_le.mpr this)

/-- **Prime-power sum descent reduction (HEADLINE, case `p ∤ (A + B)`).**
For an odd prime `p`, coprime naturals `A, B` with `p ∤ (A + B)` and `z ≠ 0`, a
solution `A^p + B^p = C^z` of Beal-`(p, p, z)` forces each factor of the
factorization `(A + B)·Φ = A^p + B^p` to be a perfect `z`-th power, with `C`
their product:

  `∃ s t, A + B = sᶻ ∧ (Φ p A B).toNat = tᶻ ∧ C = s·t`.

Mirrors `BealCubeDescent.cube_sum_descent`, with the role of `3` played by the
general odd prime `p`. The cofactor `Φ` is packaged over `ℕ` as `(Φ p A B).toNat`
(it is nonnegative by `Phi_nonneg_of_natCast`). **NEW — no LaTTe sibling.**

For `p = 3`, `Φ.toNat = A² + B² − A·B`, recovering `BealCubeDescent.cube_sum_descent`. -/
theorem prime_sum_descent {p A B C z : ℕ} (hp : p.Prime) (hodd : Odd p)
    (hAB : Nat.Coprime A B) (hpAB : ¬ (p ∣ (A + B))) (hz : z ≠ 0)
    (h : A ^ p + B ^ p = C ^ z) :
    ∃ s t, A + B = s ^ z ∧ (Phi p (A : ℤ) (B : ℤ)).toNat = t ^ z ∧ C = s * t := by
  -- A, B not both zero (coprime ⟹ gcd 1), so A + B ≥ 1.
  have hABpos : 0 < A + B := by
    rcases Nat.eq_zero_or_pos (A + B) with h0 | hpos
    · exfalso
      have hA0 : A = 0 := by omega
      have hB0 : B = 0 := by omega
      rw [hA0, hB0] at hAB
      simp [Nat.Coprime] at hAB
    · exact hpos
  -- The integer cofactor Φ and its toNat package Q.
  have hPhinn : 0 ≤ Phi p (A : ℤ) (B : ℤ) := Phi_nonneg_of_natCast p hodd A B hABpos
  set Q : ℕ := (Phi p (A : ℤ) (B : ℤ)).toNat with hQ_def
  have hQcast : (Q : ℤ) = Phi p (A : ℤ) (B : ℤ) := Int.toNat_of_nonneg hPhinn
  -- ℤ coprimality of A, B.
  have hcopZ : IsCoprime (A : ℤ) (B : ℤ) :=
    Int.isCoprime_iff_nat_coprime.mpr (by simpa using hAB)
  -- The nat factorization (A+B)·Q = C^z.
  have hfacZ := sum_pow_eq p hodd (A : ℤ) (B : ℤ)
  have hCcast : (A : ℤ) ^ p + (B : ℤ) ^ p = (C : ℤ) ^ z := by exact_mod_cast h
  have hprodZ : ((A : ℤ) + B) * (Q : ℤ) = (C : ℤ) ^ z := by
    rw [hQcast, ← hfacZ, hCcast]
  have hprod : (A + B) * Q = C ^ z := by exact_mod_cast hprodZ
  -- The two factors are coprime: gcd(A+B, Φ) = 1 (the p branch is excluded).
  have hcop : Nat.Coprime (A + B) Q := by
    rcases gcd_sum_factor_eq_one_or_prime p hp hodd (A : ℤ) (B : ℤ) hcopZ with hg | hg
    · -- gcd(A+B, Φ) = 1 over ℤ ⟹ Nat.Coprime (A+B) Q.
      have hseq : ((A : ℤ) + B) = ((A + B : ℕ) : ℤ) := by push_cast; ring
      rw [hseq, ← hQcast, Int.gcd_natCast_natCast] at hg
      exact hg
    · -- gcd = p would give p ∣ (A+B), contradicting hpAB.
      exfalso
      apply hpAB
      have hseq : ((A : ℤ) + B) = ((A + B : ℕ) : ℤ) := by push_cast; ring
      rw [hseq, ← hQcast, Int.gcd_natCast_natCast] at hg
      have : p ∣ Nat.gcd (A + B) Q := by rw [hg]
      exact this.trans (Nat.gcd_dvd_left _ _)
  -- Each factor is a perfect z-th power.
  obtain ⟨s, hs⟩ := BealCubeDescent.eq_pow_of_coprime_mul hcop hprod
  obtain ⟨t, ht⟩ := BealCubeDescent.eq_pow_of_coprime_mul (a := Q) (b := A + B) hcop.symm
    (by rw [Nat.mul_comm]; exact hprod)
  refine ⟨s, t, hs, ht, ?_⟩
  have hCz : C ^ z = (s * t) ^ z := by rw [mul_pow, ← hs, ← ht, hprod]
  exact Nat.pow_left_injective hz hCz

end BealPrimeDescent
