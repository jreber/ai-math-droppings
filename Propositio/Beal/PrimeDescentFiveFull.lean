import Mathlib.RingTheory.Coprime.Basic
import Mathlib.RingTheory.Int.Basic
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.RootsOfUnity.CyclotomicUnits
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.NumberTheory.NumberField.Cyclotomic.PID
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.Tactic
import Propositio.Beal.PrimeDescent
import Propositio.Beal.CyclotomicFactor
import Propositio.Beal.PrimeDescentFive

/-!
# Closing the `(5, 5, z)` cyclotomic descent: factor coprimality in `ℤ[ζ₅]` (Lean 4 / mathlib)

**NEW mathematics — no LaTTe sibling.** This file closes the *factor-coprimality
gap* left open by `BealPrimeDescentFive`, so that the `p = 5` cyclotomic descent
matches the `p = 3` descent (`BealEisensteinDescent`). It supplies the `p = 5`
analogue of `BealEisensteinDescent.coprime_conj_of_lambda_not_dvd`, and composes it
with `BealPrimeDescentFive.associated_pow_cyclotomic_five` to discharge the
coprimality hypothesis of the power-extraction step.

## Where this sits in the development

`BealPrimeDescentFive` proved everything for `p = 5` *except* the coprimality of the
cyclotomic factors `A + ζⁱ·B`: the engine `five_power_extraction`, the `ℤ[ζ₅]`
specialization `associated_pow_cyclotomic_five` (PID input discharged by
`IsCyclotomicExtension.Rat.five_pid`), and the primality `lambda_five_prime`
(`Prime (ζ − 1)`). The single gap was the analogue of `p = 3`'s
`coprime_conj_of_lambda_not_dvd`, which for `p = 3` used `λ² ~ −3` from the explicit
relation `η² + η + 1 = 0`.

## The key insight: cyclotomic units replace the explicit discriminant

For `p = 3` the confinement of a common prime factor to `λ` went through the
closed-form `(ω − ω²)² = −3 ~ λ²`. For `p = 5` there is no `Five` discriminant
skeleton in mathlib — **but it is not needed**. The cleaner, fully general input is
already in mathlib:

  `IsPrimitiveRoot.associated_pow_add_sub_sub_one`
    : `Associated (ζ − 1) (ζ^(i+j) − ζ^i)`   for `j` coprime to `n`.

For prime `p` every difference of distinct `p`-th roots of unity `ζⁱ − ζʲ` is
therefore *associated to `λ = ζ − 1`* (a single prime). This replaces the explicit
`(ω − ω²)² = −3` identity entirely: a common divisor `d` of two factors
`A + ζⁱ·B`, `A + ζʲ·B` divides `(ζⁱ − ζʲ)·B` and (after an `ℤ[ζ]`-twist) `(ζⁱ − ζʲ)·A`,
hence (Bézout) divides `ζⁱ − ζʲ ~ λ`; primality of `λ` and `λ ∤ (A + ζ·B)` finish
exactly as for `p = 3`.

## What this file proves (namespace `BealPrimeDescentFiveFull`)

* `zeta_diff_associated_lambda` — for distinct `i, j ∈ range 5`,
  `Associated (ζ − 1) (ζ^j − ζ^i)` in `𝓞 K` (item 1), via
  `associated_pow_add_sub_sub_one`.
* `lambda_dvd_intCast_iff_five` — `λ ∣ (n : 𝓞 K) ↔ 5 ∣ n` for `n : ℤ` (item 2),
  via `Ideal.norm_dvd_iff` and `N(λ) = 5`, mirroring
  `BealCubeSynthesis.lambda_dvd_intCast_iff`.
* **`coprime_conj_five_of_lambda_not_dvd`** — under `IsCoprime A B` and
  `λ ∤ (A + ζ·B)`, the cyclotomic factors `A + ζ·B` and `A + ζ²·B` are coprime in
  `𝓞 K` (item 3, the MAIN deliverable). Mirrors `coprime_conj_of_lambda_not_dvd`.
* **`five_power_extraction_unconditional`** — item 3 composed with
  `associated_pow_cyclotomic_five`, discharging the coprimality hypothesis (item 4):
  given coprime `A, B`, `λ ∤ (A + ζ·B)`, and `(A + ζ·B)·(A + ζ²·B) = tᶻ`,
  `∃ d, Associated (dᶻ) (A + ζ·B)`.

Dependency policy: mathlib4 permitted (user authorization 2026-05-17). Use
`lake env lean BealPrimeDescentFiveFull.lean` to typecheck (cyclotomic imports ⟹
slow, ~90s).
-/

namespace BealPrimeDescentFiveFull

open scoped NumberField
open Finset

/-!
## 1. Differences of `5`-th roots of unity are associated to `λ = ζ − 1`

The `p = 5` replacement for `p = 3`'s explicit `(ω − ω²)² = −3`: every difference
`ζ^j − ζ^i` of distinct powers of a primitive `5`-th root is a *unit multiple of
`λ = ζ − 1`*. This is `IsPrimitiveRoot.associated_pow_add_sub_sub_one`, which gives
`Associated (ζ − 1) (ζ^(i+m) − ζ^i)` for `m` coprime to `5`; since `5` is prime,
every `0 < m < 5` is coprime to `5`.
-/

/-- **Item 1 — difference of distinct `5`-th roots is associated to `λ`.** For a
primitive `5`-th root of unity `η = ζ` in `𝓞 K` and distinct `i, j ∈ range 5`,

  `Associated (η − 1) (η^j − η^i)`.

The difference of any two distinct powers of `η` is a unit multiple of `λ = η − 1`,
the `p = 5` analogue of the closed-form `(ω − ω²) ~ λ` used for `p = 3`. Proof:
write `j = i + m` (wlog `i ≤ j`) with `0 < m < 5`, so `m` is coprime to the prime
`5`, and apply `associated_pow_add_sub_sub_one`. -/
theorem zeta_diff_associated_lambda {K : Type*} [Field K] [NumberField K]
    [IsCyclotomicExtension {5} ℚ K] {ζ : K} (hζ : IsPrimitiveRoot ζ 5)
    {i j : ℕ} (hi : i < 5) (hj : j < 5) (hne : i ≠ j) :
    Associated (hζ.toInteger - 1) (hζ.toInteger ^ j - hζ.toInteger ^ i) := by
  have hη : IsPrimitiveRoot hζ.toInteger 5 := hζ.toInteger_isPrimitiveRoot
  -- WLOG i < j; handle j < i by symmetry (negation).
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · -- i < j: set m = j - i, coprime to 5, and use associated_pow_add_sub_sub_one.
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt hlt
    -- now j = i + m + 1; let mm = m + 1, 0 < mm < 5.
    have hmcop : (m + 1).Coprime 5 :=
      (Nat.coprime_of_lt_prime (by omega) (by omega) (by norm_num)).symm
    have h := hη.associated_pow_add_sub_sub_one (by norm_num) i hmcop
    -- h : Associated (η - 1) (η^(i + (m+1)) - η^i)
    have : i + (m + 1) = i + m + 1 := by ring
    rwa [this] at h
  · -- j < i: symmetric, negate.
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt hgt
    have hmcop : (m + 1).Coprime 5 :=
      (Nat.coprime_of_lt_prime (by omega) (by omega) (by norm_num)).symm
    have h := hη.associated_pow_add_sub_sub_one (by norm_num) j hmcop
    have heq : j + (m + 1) = j + m + 1 := by ring
    rw [heq] at h
    -- h : Associated (η-1) (η^(j+m+1) - η^j); the goal swaps the two terms (negation).
    have hneg : hζ.toInteger ^ j - hζ.toInteger ^ (j + m + 1)
        = -(hζ.toInteger ^ (j + m + 1) - hζ.toInteger ^ j) := by ring
    rw [hneg]
    exact h.neg_right

/-!
## 2. The λ-bridge: `λ ∣ (n : 𝓞 K) ↔ 5 ∣ n`

A verbatim `p = 5` copy of `BealCubeSynthesis.lambda_dvd_intCast_iff` (which is for
`p = 3`): the unique prime `λ = ζ − 1` over `5` detects integer divisibility by `5`,
through the norm `N(λ) = 5` (`norm_toInteger_sub_one_of_prime_ne_two'`, general for
odd primes) and `Ideal.norm_dvd_iff`.
-/

/-- **Item 2 — the λ-bridge (integer cast form), `p = 5`.** In `𝓞 K = ℤ[ζ₅]`, for
`n : ℤ`, `λ = ζ − 1` divides the image of `n` iff `5 ∣ n`. Proof: `N(λ) = 5` is
prime, and `Ideal.norm_dvd_iff` gives `λ ∣ (n : 𝓞 K) ↔ N(λ) ∣ n`. Mirrors
`BealCubeSynthesis.lambda_dvd_intCast_iff`. -/
theorem lambda_dvd_intCast_iff_five {K : Type*} [Field K] [NumberField K]
    [IsCyclotomicExtension {5} ℚ K] {ζ : K} (hζ : IsPrimitiveRoot ζ 5) (n : ℤ) :
    (hζ.toInteger - 1) ∣ ((n : ℤ) : 𝓞 K) ↔ (5 : ℤ) ∣ n := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hprime : Prime (Algebra.norm ℤ (hζ.toInteger - 1)) :=
    hζ.prime_norm_toInteger_sub_one_of_prime_ne_two' (by decide)
  have hnorm : Algebra.norm ℤ (hζ.toInteger - 1) = 5 :=
    hζ.norm_toInteger_sub_one_of_prime_ne_two' (by decide)
  have hiff := Ideal.norm_dvd_iff (S := 𝓞 K) hprime (y := n)
  rw [hnorm] at hiff
  rw [← hiff]

/-!
## 3. Coprimality of the cyclotomic factors (the MAIN deliverable)

The `p = 5` analogue of `BealEisensteinDescent.coprime_conj_of_lambda_not_dvd`. We
first record the divisibility skeleton (a common divisor of two factors divides the
relevant `ζⁱ − ζʲ`), then conclude coprimality via `isCoprime_of_prime_dvd` exactly
as for `p = 3`, with the explicit-discriminant input replaced by
`zeta_diff_associated_lambda`.
-/

/-- **Item 3 skeleton — a common divisor of two factors divides `ζ − ζ²`.** With
`η = ζ` (so `η⁵ = 1`), the difference and `η`-twist of the two cyclotomic factors
`A + η·B` and `A + η²·B` isolate `B·(η − η²)` and `A·(η − η²)`:

  `(A + η·B) − (A + η²·B) = B·(η − η²)`,
  `η²·(A + η·B) − η·(A + η²·B) = A·(η² − η)`   (the `B·η³` terms cancel identically).

So for any Bézout pair `u·A + v·B = 1`, a common divisor `d` divides `η − η²`. -/
theorem dvd_zeta_sub_of_dvd_conj {K : Type*} [Field K] {ζ : K}
    (hζ : IsPrimitiveRoot ζ 5) {A B u v d : 𝓞 K}
    (huv : u * A + v * B = 1)
    (hd₁ : d ∣ A + B * hζ.toInteger)
    (hd₂ : d ∣ A + B * hζ.toInteger ^ 2) :
    d ∣ (hζ.toInteger - hζ.toInteger ^ 2) := by
  set η := hζ.toInteger
  -- d divides the difference B·(η − η²).
  have hdB : d ∣ B * (η - η ^ 2) := by
    have hsub : (A + B * η) - (A + B * η ^ 2) = B * (η - η ^ 2) := by ring
    rw [← hsub]; exact dvd_sub hd₁ hd₂
  -- d divides the η-twist A·(η² − η) = η²·(A+Bη) − η·(A+Bη²).
  have hdA : d ∣ A * (η ^ 2 - η) := by
    have htw : η ^ 2 * (A + B * η) - η * (A + B * η ^ 2) = A * (η ^ 2 - η) := by ring
    rw [← htw]; exact dvd_sub (hd₁.mul_left _) (hd₂.mul_left _)
  have hdA' : d ∣ A * (η - η ^ 2) := by
    have : A * (η - η ^ 2) = -(A * (η ^ 2 - η)) := by ring
    rw [this]; exact hdA.neg_right
  -- Bézout assembly: v·(B·δ) + u·(A·δ) = (u·A + v·B)·δ = δ, δ = η − η².
  have hcomb : v * (B * (η - η ^ 2)) + u * (A * (η - η ^ 2)) = (η - η ^ 2) := by
    linear_combination (η - η ^ 2) * huv
  rw [← hcomb]
  exact dvd_add (hdB.mul_left v) (hdA'.mul_left u)

/-- **Item 3 (the key coprimality lemma).** In `𝓞 K = ℤ[ζ₅]`, the two cyclotomic
factors `A + ζ·B` and `A + ζ²·B` are **coprime** whenever `A, B` are coprime in
`𝓞 K` and `λ = ζ − 1` does *not* divide `A + ζ·B`.

This is the `p = 5` analogue of `BealEisensteinDescent.coprime_conj_of_lambda_not_dvd`,
and the MAIN deliverable: it discharges — unconditionally within the `λ ∤ (A + ζ·B)`
case — the coprimality hypothesis of `BealPrimeDescentFive.associated_pow_cyclotomic_five`.

Proof via `isCoprime_of_prime_dvd`, mirroring `p = 3`: any prime `p` dividing both
factors divides `η − η²` (`dvd_zeta_sub_of_dvd_conj`); but `η − η² ~ λ`
(`zeta_diff_associated_lambda` with `i = 1, j = 2`, up to sign), so `p ∣ λ`, hence
`p ~ λ` (both prime, `Prime.associated_of_dvd`), so `λ ∣ p ∣ (A + ζ·B)` —
contradicting the hypothesis. The explicit-discriminant `(ω − ω²)² = −3` of the
`p = 3` proof is replaced by the cyclotomic-unit fact `η − η² ~ λ`. -/
theorem coprime_conj_five_of_lambda_not_dvd {K : Type*} [Field K] [NumberField K]
    [IsCyclotomicExtension {5} ℚ K] {ζ : K} (hζ : IsPrimitiveRoot ζ 5) {A B : 𝓞 K}
    (hAB : IsCoprime A B)
    (hlam : ¬ (hζ.toInteger - 1) ∣ (A + B * hζ.toInteger)) :
    IsCoprime (A + B * hζ.toInteger) (A + B * hζ.toInteger ^ 2) := by
  haveI : IsPrincipalIdealRing (𝓞 K) := IsCyclotomicExtension.Rat.five_pid K
  set η := hζ.toInteger with hη_def
  -- Bézout coefficients for the coprime A, B.
  obtain ⟨u, v, huv⟩ := hAB
  have huv' : u * A + v * B = 1 := by linear_combination huv
  -- λ = η − 1 is prime in 𝓞 K.
  have hlamPrime : Prime (η - 1) := BealPrimeDescentFive.lambda_five_prime hζ
  -- η − η² is associated to λ (difference of η^1 and η^2, both 5-th roots).
  have hassoc : Associated (η - 1) (η - η ^ 2) := by
    -- zeta_diff_associated_lambda gives Associated (η-1) (η^j - η^i) for distinct i,j.
    have h := zeta_diff_associated_lambda hζ (i := 2) (j := 1)
      (by norm_num) (by norm_num) (by norm_num)
    -- h : Associated (η - 1) (η^1 - η^2)
    simpa [pow_one] using h
  refine isCoprime_of_prime_dvd ?_ ?_
  · -- the factors are not both zero (else λ ∣ 0 = A + B·η, contra)
    rintro ⟨h1, -⟩
    exact hlam (h1 ▸ dvd_zero _)
  · -- no prime divides both factors
    intro p hp p_dvd_1 p_dvd_2
    have hpδ : p ∣ (η - η ^ 2) := dvd_zeta_sub_of_dvd_conj hζ huv' p_dvd_1 p_dvd_2
    -- p ∣ (η − η²) ~ λ, so p ∣ λ.
    have hp_lam : p ∣ (η - 1) := hpδ.trans hassoc.symm.dvd
    -- p, λ both prime ⟹ p ~ λ ⟹ λ ∣ p.
    have hlam_p : (η - 1) ∣ p :=
      (hp.associated_of_dvd hlamPrime hp_lam).symm.dvd
    exact hlam (hlam_p.trans p_dvd_1)

/-!
## 4. Power extraction with the coprimality hypothesis discharged

Composing item 3 with `BealPrimeDescentFive.associated_pow_cyclotomic_five`: the
`p = 5` analogue of `BealEisensteinDescent.eisenstein_power_extraction`. The
coprimality of `A + ζ·B` against `A + ζ²·B` is no longer assumed — it is supplied by
`coprime_conj_five_of_lambda_not_dvd`.
-/

/-- **Item 4 — `five_power_extraction_unconditional`.** For `A, B` coprime in
`𝓞 K = ℤ[ζ₅]`, `λ = ζ − 1 ∤ (A + ζ·B)`, and `(A + ζ·B)·(A + ζ²·B) = tᶻ`, the
cyclotomic factor `A + ζ·B` is a `z`-th power up to a unit of `ℤ[ζ₅]`:

  `∃ d, Associated (dᶻ) (A + ζ·B)`.

The `𝓞 K`-coprimality hypothesis that
`BealPrimeDescentFive.associated_pow_cyclotomic_five` took as input is now
**discharged** by `coprime_conj_five_of_lambda_not_dvd`. The PID structure is, as
before, supplied internally by `IsCyclotomicExtension.Rat.five_pid`. This is the
`p = 5` analogue of `BealEisensteinDescent.eisenstein_power_extraction`, modulo the
factor ordering (`A + ζ·B` vs `B + A·ζ`): we state it with `ζ` on the `B`
coefficient to match `associated_pow_cyclotomic_five`. -/
theorem five_power_extraction_unconditional {K : Type*} [Field K] [NumberField K]
    [IsCyclotomicExtension {5} ℚ K] {ζ : K} (hζ : IsPrimitiveRoot ζ 5) {A B t : 𝓞 K}
    {z : ℕ} (hAB : IsCoprime A B)
    (hlam : ¬ (hζ.toInteger - 1) ∣ (A + B * hζ.toInteger))
    (h : (A + B * hζ.toInteger) * (A + B * hζ.toInteger ^ 2) = t ^ z) :
    ∃ d : 𝓞 K, Associated (d ^ z) (A + B * hζ.toInteger) := by
  have hcop : IsCoprime (A + B * hζ.toInteger) (A + B * hζ.toInteger ^ 2) :=
    coprime_conj_five_of_lambda_not_dvd hζ hAB hlam
  -- `associated_pow_cyclotomic_five` is phrased with `ζ * B`; commute B * η = η * B.
  have hcomm : A + B * hζ.toInteger = A + hζ.toInteger * B := by rw [mul_comm]
  have hcop' : IsCoprime (A + hζ.toInteger * B) (A + B * hζ.toInteger ^ 2) := by
    rwa [hcomm] at hcop
  have h' : (A + hζ.toInteger * B) * (A + B * hζ.toInteger ^ 2) = t ^ z := by
    rwa [hcomm] at h
  have hres := BealPrimeDescentFive.associated_pow_cyclotomic_five
    hζ.toInteger_isPrimitiveRoot
    (A := A) (B := B) (γ := A + B * hζ.toInteger ^ 2) (t := t) (z := z) hcop' h'
  -- hres : ∃ d, Associated (d ^ z) (A + η * B); rewrite back to A + B * η.
  rwa [← hcomm] at hres

end BealPrimeDescentFiveFull

/-!
## REMAINING PLAN

This file closes, with no `sorry`, the **factor-coprimality gap** of the `p = 5`
cyclotomic descent, bringing it level with `p = 3`:

* **Item 1** `zeta_diff_associated_lambda` — every difference `ζ^j − ζ^i` of distinct
  `5`-th roots is associated to `λ = ζ − 1`, via mathlib's cyclotomic-units lemma
  `IsPrimitiveRoot.associated_pow_add_sub_sub_one`. This is the `p = 5` replacement
  for the explicit discriminant `(ω − ω²)² = −3` used at `p = 3`.

* **Item 2** `lambda_dvd_intCast_iff_five` — `λ ∣ (n : 𝓞 K) ↔ 5 ∣ n`, a verbatim
  `p = 5` copy of `BealCubeSynthesis.lambda_dvd_intCast_iff` (`N(λ) = 5` +
  `Ideal.norm_dvd_iff`). The bridge from the integer side-condition `5 ∤ (A + B)` to
  the cyclotomic `λ ∤ (A + ζ·B)`.

* **Item 3 (MAIN)** `coprime_conj_five_of_lambda_not_dvd` — `A + ζ·B` and `A + ζ²·B`
  are coprime in `ℤ[ζ₅]` whenever `A, B` are coprime and `λ ∤ (A + ζ·B)`.
  **Discharged**, exactly mirroring `coprime_conj_of_lambda_not_dvd`, using
  primality of `λ` (`lambda_five_prime`/`zeta_sub_one_prime'`), the PID structure
  (`five_pid`, `isCoprime_of_prime_dvd`), and item 1 in place of the explicit
  discriminant.

* **Item 4** `five_power_extraction_unconditional` — item 3 composed with
  `associated_pow_cyclotomic_five`: for coprime `A, B`, `λ ∤ (A + ζ·B)`, and
  `(A + ζ·B)·(A + ζ²·B) = tᶻ`, one gets `∃ d, Associated (dᶻ) (A + ζ·B)` **with no
  coprimality hypothesis assumed** — the `p = 5` analogue of
  `BealEisensteinDescent.eisenstein_power_extraction`.

### What remains open at `p = 5` (the genuine obstruction beyond `p = 3`)

The remaining gap is the **unit / Kummer step**, and it is *substantively harder*
than at `p = 3`:

1. **Coprimality across the full factor set, not just the displayed pair.** Item 3 is
   stated and proved for the pair `(A + ζ·B, A + ζ²·B)`, which is what the
   power-extraction engine consumes (the complementary cofactor `γ` collects the
   other three factors; `isCoprime_of_prime_dvd` + item 1 generalize verbatim to any
   distinct pair `(A + ζⁱ·B, A + ζʲ·B)`, since `zeta_diff_associated_lambda` is
   uniform in `i, j`). Packaging the *whole* product `∏_{i=1}^{4}(A + ζⁱ·B)` as a
   single coprime cofactor is routine `IsCoprime`-of-a-product bookkeeping
   (`IsCoprime.prod_right`), not a new mathematical input, but is not done here.

2. **The unit group of `ℤ[ζ₅]` is infinite.** Unlike `ℤ[ζ₃]` (units `{±1, ±η, ±η²}`,
   a finite group), `ℤ[ζ₅]` has unit rank `1` (a real fundamental unit of Pell type),
   so absorbing the residual unit `u` in `A + ζ·B = u·dᶻ` into a `z`-th power is **not**
   a finite case-check. mathlib has **no `Five` Kummer lemma**
   (`Mathlib/NumberTheory/NumberField/Cyclotomic/Three.lean`'s
   `eq_one_or_neg_one_of_unit_of_congruent` has no `Five` analogue), and the
   real-unit obstruction is the honest endpoint of the `p = 5` rung. This is the
   genuine number-theoretic content that the PID (class number `1`) does **not**
   resolve.

In short: the **factor coprimality is now closed** (item 3) and the up-to-a-unit
power extraction is **unconditional** in both the PID and the coprimality inputs
(item 4); the residual unit/Kummer step is the real open problem at `p = 5`, beyond
what mathlib currently carries.
-/
