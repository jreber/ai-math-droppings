import Mathlib.Algebra.DualNumber
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# The arithmetic engine of Kummer's lemma for `p = 5`

`BealRealSubfieldDescent` reduced the open `(5,5,z)` input to: a **real** unit `v` of `𝓞(ℚ(√5))`
with `v ≡ rational integer (mod λ²)` must be a `5`-th power. With the real unit group
`= ⟨-1, φ⟩` (`φ` the golden ratio, the fundamental unit), `v = ±φⁿ`, and `±φⁿ` is a `5`-th power
**iff `5 ∣ n`**. So Kummer's lemma at `p = 5` comes down to one arithmetic fact:

> **`φⁿ` is congruent to a rational integer modulo `5` iff `5 ∣ n`.**

This file proves that engine, two equivalent ways, both elementary and self-contained (no
cyclotomic / number-field machinery):

* **Dual-number model.** `ℤ[φ]/(5) = 𝔽₅[X]/(X²-X-1)`, and `X²-X-1 ≡ (X-3)² (mod 5)`, so
  `ℤ[φ]/(5) ≅ 𝔽₅[ε]/(ε²)` (the dual numbers) via `φ ↦ 3 + ε`. There `(3+ε)ⁿ = 3ⁿ + n·3ⁿ⁻¹·ε`,
  whose `ε`-component (`= snd`) vanishes — i.e. `φⁿ` is "rational mod 5" — iff `5 ∣ n`
  (`golden_dual_rational_iff`).
* **Fibonacci model.** `φⁿ = fib(n-1) + fib n · φ`, so `φⁿ` is rational mod `5` iff `5 ∣ fib n`,
  and `5 ∣ fib n ↔ 5 ∣ n` (`five_dvd_fib_iff`, the rank-of-apparition of `5` is `5 = fib 5`).

These agree: `snd((3+ε)ⁿ) = n·3ⁿ⁻¹ ≡ fib n (mod 5)`. This is the non-trivial computational core
of Kummer `p = 5`; the remaining layers (real unit group `= ⟨-1,φ⟩`; `ℚ(ζ₅)⁺ ≅ ℚ(√5)`; the descent
congruence) are the field-theoretic wrappers documented in `BealRealSubfieldDescent` / `NEXT-STEPS`.
-/

open DualNumber TrivSqZeroExt

namespace BealGoldenKummerEngine

/-! ## Dual-number model: `ℤ[φ]/(5) ≅ 𝔽₅[ε]`, `φ ↦ 3 + ε` -/

/-- In `ℤ[φ]/(5) ≅ 𝔽₅[ε]` (with `φ ↦ 3 + ε`), the `ε`-component of `φⁿ` is `n · 3ⁿ⁻¹`. -/
theorem golden_dual_snd_pow (n : ℕ) :
    ((inl (3 : ZMod 5) + ε) ^ n).snd = (n : ZMod 5) * 3 ^ (n - 1) := by
  have hfst : (inl (3 : ZMod 5) + ε).fst = 3 := by
    rw [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, fst_eps, add_zero]
  have hsnd : (inl (3 : ZMod 5) + ε).snd = 1 := by
    rw [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, snd_eps, zero_add]
  rw [TrivSqZeroExt.snd_pow, hfst, hsnd]
  simp [nsmul_eq_mul]

/-- **The engine (dual-number form).** `φⁿ` is congruent to a rational integer modulo `5`
(i.e. its `ε`-component vanishes in `ℤ[φ]/(5) ≅ 𝔽₅[ε]`) **iff** `5 ∣ n`. -/
theorem golden_dual_rational_iff (n : ℕ) :
    ((inl (3 : ZMod 5) + ε) ^ n).snd = 0 ↔ 5 ∣ n := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have h3 : (3 : ZMod 5) ≠ 0 := by
    have h : ((3 : ℕ) : ZMod 5) ≠ 0 := by
      intro hc; rw [ZMod.natCast_eq_zero_iff] at hc; omega
    simpa using h
  rw [golden_dual_snd_pow, mul_eq_zero]
  constructor
  · rintro (h | h)
    · exact (ZMod.natCast_eq_zero_iff n 5).mp h
    · exact absurd h (pow_ne_zero (n - 1) h3)
  · intro h
    exact Or.inl ((ZMod.natCast_eq_zero_iff n 5).mpr h)

/-- **Kummer's lemma `p = 5`, in the model, for powers of `φ`.** If `φⁿ` is congruent to a
rational integer modulo `5` (vanishing `ε`-component), then `φⁿ` is a **`5`-th power** in
`ℤ[φ]/(5)` — explicitly `φⁿ = (φ^{n/5})⁵`. This is the conclusion shape of Kummer's lemma: the
engine (`golden_dual_rational_iff`) forces `5 ∣ n`, after which `pow_mul` exhibits the `5`-th root.
The full lemma additionally needs that every real unit of `𝓞(ℚ(√5))` is `±φⁿ` (the fundamental
unit `φ`) and the field identification `ℚ(ζ₅)⁺ ≅ ℚ(√5)` — the wrappers in `NEXT-STEPS`. -/
theorem golden_dual_kummer (n : ℕ)
    (h : ((inl (3 : ZMod 5) + ε) ^ n).snd = 0) :
    ∃ w : DualNumber (ZMod 5), (inl (3 : ZMod 5) + ε) ^ n = w ^ 5 := by
  obtain ⟨m, rfl⟩ := (golden_dual_rational_iff n).mp h
  exact ⟨(inl (3 : ZMod 5) + ε) ^ m, by rw [← pow_mul, Nat.mul_comm]⟩

/-! ## Fibonacci model: `φⁿ = fib(n-1) + fib n · φ`, rational mod 5 ⟺ `5 ∣ fib n` -/

/-- **`5 ∣ fib n ↔ 5 ∣ n`** — the rank of apparition of `5` is `5` (and `fib 5 = 5`). This is the
Fibonacci form of the Kummer `p = 5` engine: `φⁿ = fib(n-1) + fib n · φ` is rational mod `5` iff
the `φ`-coefficient `fib n` vanishes mod `5`. -/
theorem five_dvd_fib_iff (n : ℕ) : 5 ∣ Nat.fib n ↔ 5 ∣ n := by
  have hfib5 : Nat.fib 5 = 5 := by decide
  constructor
  · intro h
    have hg := Nat.fib_gcd 5 n
    rw [hfib5, Nat.gcd_eq_left h] at hg
    -- hg : Nat.fib (Nat.gcd 5 n) = 5
    have hdvd : Nat.gcd 5 n ∣ 5 := Nat.gcd_dvd_left 5 n
    rcases (Nat.dvd_prime (by norm_num)).mp hdvd with h1 | h5
    · rw [h1] at hg; simp [Nat.fib_one] at hg
    · have : (5 : ℕ) ∣ n := h5 ▸ Nat.gcd_dvd_right 5 n
      exact this
  · intro h
    have := Nat.fib_dvd 5 n h
    rwa [hfib5] at this

end BealGoldenKummerEngine
