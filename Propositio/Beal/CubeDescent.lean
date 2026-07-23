import Mathlib.RingTheory.Coprime.Basic
import Mathlib.RingTheory.Int.Basic
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Tactic
import Propositio.Beal.Eisenstein

/-!
# Cube-sum descent reduction toward Beal-(3, 3, z) (case `3 ∤ C`)

**NEW mathematics — no LaTTe sibling.** This file extends the Eisenstein gcd
dichotomy of `BealEisenstein.lean` into the *first descent step* of the Beal
cube-sum equation `A³ + B³ = C^z`.

The classical factorization `a³ + b³ = (a + b)·(a² − a·b + b²)` exposes the two
Eisenstein factors `s = a + b` and `q = a² − a·b + b²`. The Eisenstein
dichotomy (`BealEisenstein.eisenstein_gcd_eq_one_or_three`) says that for coprime
`a, b` the gcd of these factors is `1` or `3`. **When `3 ∤ C`** the `3` branch is
excluded (a factor of `3` in the gcd would divide `A + B`, hence `C^z`, hence
`C`), so the two factors are genuinely coprime. A coprime factorization of a
perfect `z`-th power forces **each** factor to be a perfect `z`-th power — this is
the descent reduction:

  `A³ + B³ = C^z`, `gcd(A, B) = 1`, `3 ∤ C`  ⟹
  `∃ s t, A + B = sᶻ ∧ A² + B² − A·B = tᶻ ∧ C = s·t`.

We work over `ℕ`. The Eisenstein quadratic is written `A² + B² − A·B`, which
parses as `(A² + B²) − A·B`; truncated subtraction is honest here because
`A·B ≤ A² + B²` (`ab_le_sq_add_sq`). We bridge to the `ℤ` dichotomy of
`BealEisenstein` through the nat-cast of this honest quadratic.

Key mathlib lemmas relied on:
* `exists_eq_pow_of_mul_eq_pow` — coprime factorization of a perfect power.
* `Int.isCoprime_iff_nat_coprime`, `Int.gcd_eq_natAbs` — `ℤ`/`ℕ` coprimality bridge.
* `Nat.Prime.dvd_of_dvd_pow` — `3 ∣ C^z → 3 ∣ C`.
* `Nat.pow_left_injective` — recover `C = s·t` from `C^z = (s·t)^z`.

Dependency policy: mathlib4 permitted (user authorization 2026-05-17). Use
`lake env lean BealCubeDescent.lean` to typecheck.
-/

namespace BealCubeDescent

/-- **`A·B ≤ A² + B²`.** The Eisenstein quadratic `A² + B² − A·B` is honest over
`ℕ`: truncated subtraction does not distort it. -/
theorem ab_le_sq_add_sq (A B : ℕ) : A * B ≤ A ^ 2 + B ^ 2 := by
  rcases le_total A B with h | h
  · calc A * B ≤ B * B := Nat.mul_le_mul_right B h
      _ = B ^ 2 := by ring
      _ ≤ A ^ 2 + B ^ 2 := Nat.le_add_left _ _
  · calc A * B ≤ A * A := Nat.mul_le_mul_left A h
      _ = A ^ 2 := by ring
      _ ≤ A ^ 2 + B ^ 2 := Nat.le_add_right _ _

/-- **Coprime factor of a perfect power is a perfect power.**
If `a, b` are coprime and `a·b = c^k`, then `a` is itself a `k`-th power.
This is the arithmetic engine of the descent: it splits a coprime factorization
of a perfect power into perfect-power factors. -/
theorem eq_pow_of_coprime_mul {a b c k : ℕ} (hab : Nat.Coprime a b)
    (h : a * b = c ^ k) : ∃ d, a = d ^ k := by
  apply exists_eq_pow_of_mul_eq_pow (a := a) (b := b) (c := c) (k := k) _ h
  rw [gcd_eq_nat_gcd, Nat.isUnit_iff]
  exact hab

/-- **Cube-sum factorization over `ℕ`.**
`(A + B)·(A² + B² − A·B) = A³ + B³`. Mirrors the `ℤ` factorization of
`BealEisenstein.cube_sum_factor`, with the honest truncated quadratic. -/
theorem cube_sum_factor_nat (A B : ℕ) :
    (A + B) * (A ^ 2 + B ^ 2 - A * B) = A ^ 3 + B ^ 3 := by
  zify [ab_le_sq_add_sq A B]; ring

/-- **The Eisenstein factors are coprime when `3 ∤ (A + B)`.**
For coprime `A, B` with `3 ∤ (A + B)`, the factors `A + B` and `A² + B² − A·B`
are coprime. This excludes the `3` branch of the Eisenstein gcd dichotomy: the
gcd is `1` or `3`, but a `3` would divide `A + B`, contradicting `3 ∤ (A + B)`. -/
theorem coprime_factors {A B : ℕ} (hAB : Nat.Coprime A B)
    (h3 : ¬ (3 ∣ (A + B))) : Nat.Coprime (A + B) (A ^ 2 + B ^ 2 - A * B) := by
  -- Bridge coprimality of A, B into ℤ.
  have hcopZ : IsCoprime (A : ℤ) (B : ℤ) :=
    Int.isCoprime_iff_nat_coprime.mpr (by simpa using hAB)
  -- The ℤ Eisenstein dichotomy.
  have hdich := BealEisenstein.eisenstein_gcd_eq_one_or_three (A : ℤ) (B : ℤ) hcopZ
  -- Rewrite the two Int.gcd arguments as nat-casts of the ℕ expressions.
  have hs : ((A : ℤ) + B) = ((A + B : ℕ) : ℤ) := by push_cast; ring
  have hq : ((A : ℤ) ^ 2 - A * B + B ^ 2) = ((A ^ 2 + B ^ 2 - A * B : ℕ) : ℤ) := by
    rw [Nat.cast_sub (ab_le_sq_add_sq A B)]; push_cast; ring
  rw [hs, hq, Int.gcd_natCast_natCast] at hdich
  -- Now hdich : Nat.gcd (A+B) (...) = 1 ∨ = 3.  Rule out 3 via h3.
  rcases hdich with h | h
  · exact h
  · exfalso
    apply h3
    have : (3 : ℕ) ∣ Nat.gcd (A + B) (A ^ 2 + B ^ 2 - A * B) := by rw [h]
    exact dvd_trans this (Nat.gcd_dvd_left _ _)

/-- **Cube-sum descent reduction (HEADLINE, case `3 ∤ C`).**
For coprime `A, B` with `3 ∤ C` and `z ≠ 0`, a solution `A³ + B³ = C^z` of the
Beal cube-sum equation forces **each** Eisenstein factor to be a perfect `z`-th
power, with `C` their product:

  `∃ s t, A + B = sᶻ ∧ A² + B² − A·B = tᶻ ∧ C = s·t`.

This is the first descent step toward Beal-(3, 3, z): the coprime factorization
`(A + B)·(A² + B² − A·B) = A³ + B³ = C^z` of a perfect power splits into
perfect-power factors. The `z ≠ 0` hypothesis is needed only to recover
`C = s·t` from `C^z = (s·t)^z` by injectivity of `· ↦ ·^z`; it is harmless since
`z ≥ 3` in Beal. **NEW — no LaTTe sibling.** -/
theorem cube_sum_descent {A B C z : ℕ} (hAB : Nat.Coprime A B) (hC : ¬ (3 ∣ C))
    (hz : z ≠ 0) (h : A ^ 3 + B ^ 3 = C ^ z) :
    ∃ s t, A + B = s ^ z ∧ A ^ 2 + B ^ 2 - A * B = t ^ z ∧ C = s * t := by
  set q := A ^ 2 + B ^ 2 - A * B with hq_def
  -- (A+B)·q = C^z.
  have hprod : (A + B) * q = C ^ z := by rw [hq_def, cube_sum_factor_nat, h]
  -- 3 ∤ (A + B): else 3 ∣ (A+B)·q = C^z, so 3 ∣ C, contradicting hC.
  have h3 : ¬ (3 ∣ (A + B)) := by
    intro hdvd
    apply hC
    have hdvdCz : (3 : ℕ) ∣ C ^ z := by
      rw [← hprod]; exact Dvd.dvd.mul_right hdvd q
    exact (Nat.prime_three).dvd_of_dvd_pow hdvdCz
  -- The two factors are coprime.
  have hcop : Nat.Coprime (A + B) q := coprime_factors hAB h3
  -- Each factor is a perfect z-th power.
  obtain ⟨s, hs⟩ := eq_pow_of_coprime_mul hcop hprod
  obtain ⟨t, ht⟩ := eq_pow_of_coprime_mul (a := q) (b := A + B) hcop.symm
    (by rw [Nat.mul_comm]; exact hprod)
  refine ⟨s, t, hs, ht, ?_⟩
  -- C^z = s^z·t^z = (s·t)^z, then injectivity of ·^z gives C = s·t.
  have hCz : C ^ z = (s * t) ^ z := by
    rw [mul_pow, ← hs, ← ht, hprod]
  exact Nat.pow_left_injective hz hCz

end BealCubeDescent
