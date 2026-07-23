import Mathlib.RingTheory.Coprime.Basic
import Mathlib.RingTheory.Int.Basic
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.NumberTheory.NumberField.Cyclotomic.Three
import Mathlib.NumberTheory.NumberField.Cyclotomic.PID
import Mathlib.Tactic
import Propositio.Beal.Eisenstein
import Propositio.Beal.CubeDescent

/-!
# ℤ[ζ₃] Eisenstein descent for the Beal cube-sum equation (Lean 4 / mathlib)

**NEW mathematics — no LaTTe sibling.** This file begins the genuine,
*unconditional* ℤ[ζ₃] **Eisenstein descent** — the algebraic core of the
Kraus/classical attack on Beal-`(3, 3, z)` — building directly on the reduction
already mechanized in `BealCubeDescent.lean`.

## Where this sits in the development

`BealCubeDescent.cube_sum_descent` reduces the equation `A³ + B³ = C^z`
(case `3 ∤ C`, coprime `A, B`) to a pair of perfect-power statements

  `A + B = sᶻ`,    `A² − A·B + B² = tᶻ`.

The second equation is the one this file attacks. The Eisenstein norm form
factors as

  `A² − A·B + B² = (A + B·ω)(A + B·ω²) = N(A + B·ω)`   in `ℤ[ω]`,

where `ω` is a primitive cube root of unity (`ω² + ω + 1 = 0`). The classical
descent then runs:

1. **M1 — Norm identity.** `(A + B·ω)(A + B·ω²) = A² − A·B + B²`. (proved, two
   forms: a generic commutative-ring identity and the `𝓞 K`/cyclotomic phrasing.)
2. **M2 — Coprimality of the conjugate factors.** For coprime `A, B` with the
   `3 ∤ ·` condition, `A + B·ω` and `A + B·ω²` are coprime in `ℤ[ω]` (their gcd is
   a unit). The algebraic skeleton — the difference/sum identities and
   `(ω − ω²)² = −3` — is proved here; the `𝓞 K` coprimality is staged in the plan.
3. **M3 — Power extraction.** In the PID `𝓞 K` (`three_pid`), a coprime
   factorization `(A + B·ω)(A + B·ω²) = tᶻ` forces each factor to be a `z`-th
   power *up to a unit*: `∃ d, Associated (dᶻ) (A + B·ω)`. (proved as a clean
   conditional lemma over any Bézout domain.)
4. **M4 — Unit constraint** (Kummer's lemma, `eq_one_or_neg_one_of_unit_of_congruent`,
   units `{±1, ±η, ±η²}`): staged in the plan.

## Mathlib machinery used

* `IsCyclotomicExtension.Rat.Three.eta_sq_add_eta_add_one : η² + η + 1 = 0` — the
  cyclotomic relation in `𝓞 K`, used for the `𝓞 K` norm phrasing.
* `IsCyclotomicExtension.Rat.three_pid : IsPrincipalIdealRing (𝓞 K)` — `ℤ[ζ₃]`
  is a PID, hence a Bézout domain, hence `GCDMonoid`/UFD.
* `exists_associated_pow_of_mul_eq_pow'` (PrincipalIdealDomain.lean): in a Bézout
  domain, `IsCoprime a b → a*b = cᵏ → ∃ d, Associated (dᵏ) a`. This is the power
  extraction engine.

Dependency policy: mathlib4 permitted (user authorization 2026-05-17). Use
`lake env lean BealEisensteinDescent.lean` to typecheck.
-/

namespace BealEisensteinDescent

open scoped NumberField

/-!
## M1 — The Eisenstein norm identity

Two fully-rigorous forms.

The first is a pure commutative-ring identity: in any commutative ring `R`, for
any element `ω` satisfying `ω² + ω + 1 = 0` and any `A B : R`,

  `(A + B·ω)(A + B·ω²) = A² − A·B + B²`.

Expanding, `(A + Bω)(A + Bω²) = A² + AB(ω + ω²) + B²ω³`. Using `ω³ = 1` (a
consequence of `ω² + ω + 1 = 0`, since `ω³ − 1 = (ω − 1)(ω² + ω + 1)`) and
`ω + ω² = −1`, this collapses to `A² − AB + B²`. The whole thing is a
`linear_combination` in the single hypothesis `ω² + ω + 1 = 0`.
-/

/-- **M1 (generic norm identity).** In any commutative ring `R`, if `ω` is a root
of `X² + X + 1` (a primitive cube root of unity relation), then the Eisenstein
factorization holds:

  `(A + B·ω)(A + B·ω²) = A² − A·B + B²`.

This is the algebraic heart of the Eisenstein norm form `N(A + B·ω)`. Fully
elementary: a `linear_combination` in `hω : ω² + ω + 1 = 0`. -/
theorem norm_identity {R : Type*} [CommRing R] (ω A B : R)
    (hω : ω ^ 2 + ω + 1 = 0) :
    (A + B * ω) * (A + B * ω ^ 2) = A ^ 2 - A * B + B ^ 2 := by
  linear_combination (A * B + B ^ 2 * (ω - 1)) * hω

/-- **M1 (integer specialization).** The same identity with `A, B : ℤ` cast into
`R`, the form used when descending from the integer equation
`A² − A·B + B² = tᶻ`. -/
theorem norm_identity_intCast {R : Type*} [CommRing R] (ω : R) (A B : ℤ)
    (hω : ω ^ 2 + ω + 1 = 0) :
    ((A : R) + (B : R) * ω) * ((A : R) + (B : R) * ω ^ 2)
      = (A : R) ^ 2 - (A : R) * (B : R) + (B : R) ^ 2 :=
  norm_identity ω (A : R) (B : R) hω

/-!
### M1 in the cyclotomic ring `𝓞 K` (`ℤ[ζ₃]`)

`Mathlib/NumberTheory/NumberField/Cyclotomic/Three.lean` provides, for a
primitive cube root `ζ` with `hζ : IsPrimitiveRoot ζ 3`, the integer `η := ζ`'s
`toInteger` (as a unit), satisfying `η² + η + 1 = 0`
(`eta_sq_add_eta_add_one`). Feeding that relation into `norm_identity` gives the
Eisenstein factorization in the genuine ring of integers `𝓞 K`. -/

/-- **M1 (`𝓞 K` / cyclotomic phrasing).** In the ring of integers of a cyclotomic
field `K = ℚ(ζ₃)`, with `η = ζ` the primitive cube root, the Eisenstein norm
form factors:

  `(A + B·η)(A + B·η²) = A² − A·B + B²`   in `𝓞 K`.

This is the genuine `ℤ[ζ₃]` factorization (not the `ℤ[√−3]` suborder model). It
specializes `norm_identity` to `ω = η`, using mathlib's `eta_sq_add_eta_add_one`. -/
theorem norm_identity_cyclotomic {K : Type*} [Field K] {ζ : K}
    (hζ : IsPrimitiveRoot ζ 3) (A B : 𝓞 K) :
    (A + B * hζ.toInteger) * (A + B * hζ.toInteger ^ 2)
      = A ^ 2 - A * B + B ^ 2 := by
  have hη : hζ.toInteger ^ 2 + hζ.toInteger + 1 = 0 :=
    IsCyclotomicExtension.Rat.Three.eta_sq_add_eta_add_one hζ
  linear_combination (A * B + B ^ 2 * (hζ.toInteger - 1)) * hη

/-!
## M2 — Coprimality of the conjugate factors (algebraic skeleton)

The two conjugate factors are `α = A + B·ω` and `ᾱ = A + B·ω²`. A common divisor
`d` of `α, ᾱ` divides every `ℤ[ω]`-linear combination of them. The two basic
combinations are:

* the **difference** `α − ᾱ = B·(ω − ω²)`, and
* the **`ω`-twisted difference** `ω²·α − ω·ᾱ`, which produces `A·(ω² − ω)`,

so `d` divides both `B·(ω − ω²)` and `A·(ω² − ω) = −A·(ω − ω²)`. Since
`(ω − ω²)² = −3` (`= λ²`-type element, the different), `d` divides
`gcd(A, B)·(ω − ω²)`, and squaring, `d²` divides `3·gcd(A,B)²`. With `A, B`
coprime and the `3 ∤ ·` condition this forces `d` to be a unit.

We prove the *ring-identity skeleton* of this argument fully; the passage to
`IsCoprime` in `𝓞 K` (which needs the `λ`-adic valuation bookkeeping) is staged
in the plan. -/

/-- **M2.a — the discriminant element.** `(ω − ω²)² = −3` whenever
`ω² + ω + 1 = 0`. This is the value `λ² = −3η` (up to a unit) appearing in the
cyclotomic file; here it is the elementary identity that makes `3` the only
possible common factor of the conjugates. -/
theorem omega_sub_omega_sq_sq {R : Type*} [CommRing R] (ω : R)
    (hω : ω ^ 2 + ω + 1 = 0) :
    (ω - ω ^ 2) ^ 2 = -3 := by
  linear_combination (ω ^ 2 - 3 * ω + 3) * hω

/-- **M2.b — difference of the conjugates.** `(A + B·ω) − (A + B·ω²) = B·(ω − ω²)`.
A common divisor of the two conjugates divides this; it is one of the two
combinations pinning the gcd to `gcd(A,B)·(ω − ω²)`. -/
theorem conj_sub {R : Type*} [CommRing R] (ω A B : R) :
    (A + B * ω) - (A + B * ω ^ 2) = B * (ω - ω ^ 2) := by ring

/-- **M2.c — `ω`-twisted combination isolating `A`.** With `ω² + ω + 1 = 0`,

  `ω² · (A + B·ω) − ω · (A + B·ω²) = A · (ω² − ω)`.

(The `B` terms cancel: `B·ω³ − B·ω³ = 0` after `ω³ = 1`.) Together with `conj_sub`
this shows a common divisor of the conjugates divides both `A·(ω − ω²)` and
`B·(ω − ω²)`, hence `gcd(A,B)·(ω − ω²)`. The `B·ω³` terms cancel identically, so
this needs no cyclotomic relation — it is a pure `ring` identity. -/
theorem conj_twist {R : Type*} [CommRing R] (ω A B : R) :
    ω ^ 2 * (A + B * ω) - ω * (A + B * ω ^ 2) = A * (ω ^ 2 - ω) := by
  ring

/-- **M2.d — a common divisor divides `(ω − ω²)`.** This is the operational
output of M2's skeleton, packaged divisibility-theoretically and proved in full.

Let `d` be any element of a commutative ring dividing both conjugates,
`d ∣ A + B·ω` and `d ∣ A + B·ω²`. Then for *every* Bézout-style pair `u, v` with
`u·A + v·B = 1`, the element `d` divides `(ω − ω²)`.

Reason: `d ∣ B·(ω − ω²)` (from `conj_sub`) and `d ∣ A·(ω − ω²)` (from
`conj_twist`, since `A·(ω² − ω) = −A·(ω − ω²)`). Hence `d` divides
`v·(B·(ω − ω²)) + u·(A·(ω − ω²)) = (u·A + v·B)·(ω − ω²) = (ω − ω²)`.

Squaring then gives `d² ∣ (ω − ω²)² = −3` (via `omega_sub_omega_sq_sq`), the step
that confines a non-unit common factor to lie over the prime `3`. -/
theorem dvd_omega_sub_of_dvd_conj {R : Type*} [CommRing R] {ω A B u v d : R}
    (huv : u * A + v * B = 1)
    (hd₁ : d ∣ A + B * ω) (hd₂ : d ∣ A + B * ω ^ 2) :
    d ∣ (ω - ω ^ 2) := by
  -- d divides the difference B·(ω − ω²).
  have hdB : d ∣ B * (ω - ω ^ 2) := by
    rw [← conj_sub ω A B]; exact dvd_sub hd₁ hd₂
  -- d divides the ω-twist A·(ω² − ω) = ω²·(A+Bω) − ω·(A+Bω²).
  have hdA : d ∣ A * (ω ^ 2 - ω) := by
    rw [← conj_twist ω A B]
    exact dvd_sub (hd₁.mul_left _) (hd₂.mul_left _)
  -- Rewrite A·(ω² − ω) = (−A)·(ω − ω²) and assemble the Bézout combination.
  have hdA' : d ∣ A * (ω - ω ^ 2) := by
    have : A * (ω - ω ^ 2) = -(A * (ω ^ 2 - ω)) := by ring
    rw [this]; exact hdA.neg_right
  have hcomb : v * (B * (ω - ω ^ 2)) + u * (A * (ω - ω ^ 2)) = (ω - ω ^ 2) := by
    linear_combination (ω - ω ^ 2) * huv
  rw [← hcomb]
  exact dvd_add (hdB.mul_left v) (hdA'.mul_left u)

/-- **M2.e — squared common divisor divides `−3`.** Immediate from
`dvd_omega_sub_of_dvd_conj` and `omega_sub_omega_sq_sq`: a common divisor `d` of
the two conjugates satisfies `d² ∣ −3`. This is the precise sense in which "the
only possible non-trivial common factor lies over `3`": in the PID `𝓞 K`, `−3` is
`−η⁻¹·λ²` with `λ` the unique prime over `3`, so `d² ∣ −3` forces `d` to be a
unit unless `λ ∣ d`. -/
theorem common_divisor_sq_dvd_neg_three {R : Type*} [CommRing R] {ω A B u v d : R}
    (hω : ω ^ 2 + ω + 1 = 0) (huv : u * A + v * B = 1)
    (hd₁ : d ∣ A + B * ω) (hd₂ : d ∣ A + B * ω ^ 2) :
    d ^ 2 ∣ (-3 : R) := by
  have hd : d ∣ (ω - ω ^ 2) := dvd_omega_sub_of_dvd_conj huv hd₁ hd₂
  have : d ^ 2 ∣ (ω - ω ^ 2) ^ 2 := pow_dvd_pow_of_dvd hd 2
  rwa [omega_sub_omega_sq_sq ω hω] at this

/-!
## M3 — Power extraction in the PID `𝓞 K`

In a Bézout domain (in particular the PID `𝓞 K = ℤ[ζ₃]` via `three_pid`), a
coprime factorization of a perfect power splits into perfect powers *up to a
unit*. We state this as a clean, fully-proved conditional lemma: it takes the
coprimality `IsCoprime α ᾱ` as a hypothesis (its discharge in `𝓞 K` is the
content of M2, staged in the plan) and the product equation
`α · ᾱ = tᶻ`, and returns `∃ d, Associated (dᶻ) α`.

The engine is `exists_associated_pow_of_mul_eq_pow'`. -/

/-- **M3 (power extraction, conditional).** In any commutative Bézout domain `R`,
if `α, β` are coprime and `α · β = c ^ z`, then `α` is a `z`-th power up to a
unit: `∃ d, Associated (dᶻ) α`.

Applied with `R = 𝓞 K`, `α = A + B·η`, `β = A + B·η²`, `c = t`: a coprime
Eisenstein factorization of `tᶻ` forces `A + B·η` to be, up to a unit of `ℤ[ζ₃]`,
a perfect `z`-th power. This is the crux of the classical descent; combined with
the unit structure (M4) it drives the contradiction. -/
theorem associated_pow_of_coprime_mul {R : Type*} [CommRing R] [IsDomain R]
    [IsBezout R] {α β c : R} {z : ℕ} (hcop : IsCoprime α β)
    (h : α * β = c ^ z) : ∃ d : R, Associated (d ^ z) α :=
  exists_associated_pow_of_mul_eq_pow' hcop h

/-- **M3 (both factors).** The symmetric statement: under the same hypotheses,
*both* `α` and `β` are `z`-th powers up to a unit. This is the form fed into the
descent, where one tracks `A + B·η = u₁·d₁ᶻ` and `A + B·η² = u₂·d₂ᶻ`
simultaneously. -/
theorem associated_pow_of_coprime_mul_both {R : Type*} [CommRing R] [IsDomain R]
    [IsBezout R] {α β c : R} {z : ℕ} (hcop : IsCoprime α β)
    (h : α * β = c ^ z) :
    (∃ d : R, Associated (d ^ z) α) ∧ (∃ e : R, Associated (e ^ z) β) :=
  ⟨exists_associated_pow_of_mul_eq_pow' hcop h,
   exists_associated_pow_of_mul_eq_pow' hcop.symm (by rw [mul_comm]; exact h)⟩

/-!
## M3 specialized to the genuine ring `ℤ[ζ₃] = 𝓞 K`

`three_pid` gives `IsPrincipalIdealRing (𝓞 K)`, whence `IsBezout (𝓞 K)`, so the
generic M3 applies verbatim. We record the specialization with the Eisenstein
factors substituted via `norm_identity_cyclotomic`, so that a future session
need only supply the `𝓞 K`-coprimality `IsCoprime (A + B·η) (A + B·η²)` to obtain
the descent's power-extraction conclusion. -/

/-- **M3 (`𝓞 K` specialization).** In the ring of integers `𝓞 K = ℤ[ζ₃]` of the
cyclotomic field `K = ℚ(ζ₃)`, given the `𝓞 K`-coprimality of the two Eisenstein
conjugates and the equation `A² − A·B + B² = tᶻ`, the factor `A + B·η` is a
`z`-th power up to a unit of `ℤ[ζ₃]`. -/
theorem associated_pow_cyclotomic {K : Type*} [Field K] [NumberField K]
    [IsCyclotomicExtension {3} ℚ K] {ζ : K} (hζ : IsPrimitiveRoot ζ 3)
    {A B t : 𝓞 K} {z : ℕ}
    (hcop : IsCoprime (A + B * hζ.toInteger) (A + B * hζ.toInteger ^ 2))
    (h : A ^ 2 - A * B + B ^ 2 = t ^ z) :
    ∃ d : 𝓞 K, Associated (d ^ z) (A + B * hζ.toInteger) := by
  haveI : IsPrincipalIdealRing (𝓞 K) := IsCyclotomicExtension.Rat.three_pid K
  haveI : IsBezout (𝓞 K) := inferInstance
  apply associated_pow_of_coprime_mul hcop (c := t) (z := z)
  rw [norm_identity_cyclotomic hζ A B, h]

/-!
## M2 proper — `𝓞 K`-coprimality of the conjugate factors

This section discharges the coprimality hypothesis of `associated_pow_cyclotomic`
in the case `λ ∤ (A + B·η)`, i.e. away from the prime over `3`.

The mathlib input is the *primality of `λ = η − 1`* in `𝓞 K`
(`IsPrimitiveRoot.zeta_sub_one_prime'`) and the PID structure (`three_pid`), which
makes the M2 skeleton (`common_divisor_sq_dvd_neg_three`: any common divisor `d`
of the conjugates has `d² ∣ −3`) into a genuine coprimality statement: combine
`d² ∣ −3` with the factorization `−3 ~ λ²` (from `λ² = −3·η`, `η` a unit) and
`λ ∤ (A + B·η)`.

The argument: a prime `p` dividing both conjugates has `p² ∣ −3 ~ λ²`, so
`p ∣ λ²`; as `p` is prime, `p ∣ λ`; as both `p, λ` are prime, `p ~ λ`, whence
`λ ∣ p ∣ (A + B·η)` — contradicting `λ ∤ (A + B·η)`. So no prime divides both
conjugates: they are coprime (`isCoprime_of_prime_dvd`).
-/

/-- **M2.f — the cyclotomic discriminant `λ² = −3·η`.** Derived purely from the
cyclotomic relation `η² + η + 1 = 0` (`eta_sq_add_eta_add_one`): with `λ = η − 1`,

  `(η − 1)² = −3·η`   in `𝓞 K`.

This is the `𝓞 K` incarnation of `omega_sub_omega_sq_sq` (`(ω − ω²)² = −3`); it
is the precise factorization that confines a common prime factor of the
conjugates to lie over `3`, i.e. to be associated to `λ`. (Mathlib's namesake
`lambda_sq` is `private`, so this re-derives it from the public relation.) -/
theorem lambda_sq_eq {K : Type*} [Field K] {ζ : K} (hζ : IsPrimitiveRoot ζ 3) :
    (hζ.toInteger - 1) ^ 2 = -3 * hζ.toInteger := by
  have hη : hζ.toInteger ^ 2 + hζ.toInteger + 1 = 0 :=
    IsCyclotomicExtension.Rat.Three.eta_sq_add_eta_add_one hζ
  linear_combination hη

/-- **M2.g — `−3` is associated to `λ²`.** Since `λ² = −3·η` (`lambda_sq_eq`) and
`η = ζ` is a unit (a root of unity), `−3` and `λ²` differ by the unit `η`, hence
are associated in `𝓞 K`. This is what turns the generic `d² ∣ −3` into the
`λ`-adic statement `d² ∣ λ²` used to pin a common factor to `λ`. -/
theorem neg_three_associated_lambda_sq {K : Type*} [Field K] [NumberField K]
    [IsCyclotomicExtension {3} ℚ K] {ζ : K} (hζ : IsPrimitiveRoot ζ 3) :
    Associated ((-3 : 𝓞 K)) ((hζ.toInteger - 1) ^ 2) := by
  have hunit : IsUnit hζ.toInteger :=
    hζ.toInteger_isPrimitiveRoot.isUnit (by norm_num)
  obtain ⟨u, hu⟩ := hunit
  refine ⟨u, ?_⟩
  rw [lambda_sq_eq hζ, hu]

/-- **M2 proper (the key coprimality lemma).** In `𝓞 K = ℤ[ζ₃]`, the two
Eisenstein conjugates `A + B·η` and `A + B·η²` are **coprime** whenever `A, B` are
coprime in `𝓞 K` and `λ = η − 1` does *not* divide `A + B·η`.

This discharges — unconditionally within the `λ ∤ (A + B·η)` case — the hypothesis
that `associated_pow_cyclotomic` (M3) previously took as input. Proof via
`isCoprime_of_prime_dvd`: any prime `p` dividing both conjugates satisfies
`p² ∣ −3` (`common_divisor_sq_dvd_neg_three`), hence `p² ∣ λ²` (since `−3 ~ λ²`),
hence `p ∣ λ` (`p` prime, `Prime.dvd_of_dvd_pow`), hence `p ~ λ`
(`Prime.associated_of_dvd`, both prime), so `λ ∣ p ∣ (A + B·η)` — contradicting
the hypothesis. -/
theorem coprime_conj_of_lambda_not_dvd {K : Type*} [Field K] [NumberField K]
    [IsCyclotomicExtension {3} ℚ K] {ζ : K} (hζ : IsPrimitiveRoot ζ 3) {A B : 𝓞 K}
    (hAB : IsCoprime A B)
    (hlam : ¬ (hζ.toInteger - 1) ∣ (A + B * hζ.toInteger)) :
    IsCoprime (A + B * hζ.toInteger) (A + B * hζ.toInteger ^ 2) := by
  haveI : IsPrincipalIdealRing (𝓞 K) := IsCyclotomicExtension.Rat.three_pid K
  -- η satisfies the cyclotomic relation η² + η + 1 = 0.
  have hη : hζ.toInteger ^ 2 + hζ.toInteger + 1 = 0 :=
    IsCyclotomicExtension.Rat.Three.eta_sq_add_eta_add_one hζ
  -- Bézout coefficients for the coprime A, B.
  obtain ⟨u, v, huv⟩ := hAB
  have huv' : u * A + v * B = 1 := by linear_combination huv
  -- λ = η − 1 is prime in 𝓞 K.
  have hlamPrime : Prime (hζ.toInteger - 1) := hζ.zeta_sub_one_prime'
  -- −3 is associated to λ².
  have hassoc : Associated ((-3 : 𝓞 K)) ((hζ.toInteger - 1) ^ 2) :=
    neg_three_associated_lambda_sq hζ
  refine isCoprime_of_prime_dvd ?_ ?_
  · -- the conjugates are not both zero (else λ ∣ 0 = A + B·η, contra)
    rintro ⟨h1, -⟩
    exact hlam (h1 ▸ dvd_zero _)
  · -- no prime divides both conjugates
    intro p hp p_dvd_1 p_dvd_2
    have hp2 : p ^ 2 ∣ (-3 : 𝓞 K) :=
      common_divisor_sq_dvd_neg_three hη huv' p_dvd_1 p_dvd_2
    have hp2' : p ^ 2 ∣ (hζ.toInteger - 1) ^ 2 := hp2.trans hassoc.dvd
    have hplam2 : p ∣ (hζ.toInteger - 1) ^ 2 :=
      (dvd_pow_self p (n := 2) (by norm_num)).trans hp2'
    have hplam : p ∣ (hζ.toInteger - 1) := hp.dvd_of_dvd_pow hplam2
    have hlamp : (hζ.toInteger - 1) ∣ p :=
      (hp.associated_of_dvd hlamPrime hplam).symm.dvd
    exact hlam (hlamp.trans p_dvd_1)

/-- **M3 unconditional (within the `λ ∤ conj` case).** Combining M2 proper with
the M3 specialization `associated_pow_cyclotomic`: for `A, B` coprime in `𝓞 K`,
`λ ∤ (A + B·η)`, and `A² − A·B + B² = tᶻ`, the factor `A + B·η` is a `z`-th power
up to a unit of `ℤ[ζ₃]`. The `𝓞 K`-coprimality hypothesis is no longer assumed —
it is supplied internally by `coprime_conj_of_lambda_not_dvd`. -/
theorem eisenstein_power_extraction {K : Type*} [Field K] [NumberField K]
    [IsCyclotomicExtension {3} ℚ K] {ζ : K} (hζ : IsPrimitiveRoot ζ 3) {A B t : 𝓞 K}
    {z : ℕ} (hAB : IsCoprime A B)
    (hlam : ¬ (hζ.toInteger - 1) ∣ (A + B * hζ.toInteger))
    (h : A ^ 2 - A * B + B ^ 2 = t ^ z) :
    ∃ d : 𝓞 K, Associated (d ^ z) (A + B * hζ.toInteger) :=
  associated_pow_cyclotomic hζ (coprime_conj_of_lambda_not_dvd hζ hAB hlam) h

/-!
## M2 entry condition — lifting `λ ∤ (A + B)` to `λ ∤ (A + B·η)`

The hypothesis `λ ∤ (A + B·η)` of M2 proper is supplied, in the descent, by the
arithmetic side-condition on the integers. Since `λ = η − 1`, one has
`η ≡ 1 (mod λ)`, so `A + B·η ≡ A + B (mod λ)`. Concretely
`(A + B·η) − (A + B) = B·λ`, giving the divisibility equivalence below; the
side-condition `λ ∤ (A + B)` (e.g. lifted from `3 ∤ (A + B)` in the `3 ∤ C` Beal
branch) then yields the M2-proper hypothesis directly. -/

/-- **Congruence mod `λ`.** `λ ∣ (A + B·η) ↔ λ ∣ (A + B)`, because
`(A + B·η) − (A + B) = B·(η − 1) = B·λ`. -/
theorem lambda_dvd_conj_iff {K : Type*} [Field K] {ζ : K} (hζ : IsPrimitiveRoot ζ 3)
    (A B : 𝓞 K) :
    (hζ.toInteger - 1) ∣ (A + B * hζ.toInteger) ↔ (hζ.toInteger - 1) ∣ (A + B) := by
  have hdvd : (hζ.toInteger - 1) ∣ ((A + B * hζ.toInteger) - (A + B)) :=
    ⟨B, by ring⟩
  constructor
  · intro h
    have h2 := dvd_sub h hdvd
    rwa [sub_sub_cancel] at h2
  · intro h
    have h2 := dvd_add h hdvd
    rwa [add_sub_cancel] at h2

/-- **M2 entry condition.** If `λ ∤ (A + B)` then `λ ∤ (A + B·η)`. This delivers
the hypothesis of `coprime_conj_of_lambda_not_dvd` (hence of
`eisenstein_power_extraction`) from a condition on `A + B` alone — the bridge to
the integer side-condition `3 ∤ (A + B)` of the Beal cube-sum reduction. -/
theorem lambda_not_dvd_conj {K : Type*} [Field K] {ζ : K} (hζ : IsPrimitiveRoot ζ 3)
    {A B : 𝓞 K} (hlam : ¬ (hζ.toInteger - 1) ∣ (A + B)) :
    ¬ (hζ.toInteger - 1) ∣ (A + B * hζ.toInteger) :=
  fun h => hlam ((lambda_dvd_conj_iff hζ A B).mp h)

end BealEisensteinDescent

/-!
## REMAINING PLAN

This file now fully proves the algebraic core **and** M2-proper of the Eisenstein
descent (all axiom-clean: `[propext, Classical.choice, Quot.sound]`):

  * **M1** `norm_identity` / `norm_identity_intCast` / `norm_identity_cyclotomic`
    — the factorization `(A + B·ω)(A + B·ω²) = A² − A·B + B²`, in a generic ring,
    with integer casts, and in the genuine ring `𝓞 K = ℤ[ζ₃]`.
  * **M2 skeleton** `omega_sub_omega_sq_sq`, `conj_sub`, `conj_twist`,
    `dvd_omega_sub_of_dvd_conj`, `common_divisor_sq_dvd_neg_three`
    — any common divisor `d` of the conjugates has `d ∣ (ω − ω²)` and `d² ∣ −3`.
  * **M2 proper** `lambda_sq_eq` (`λ² = −3·η`), `neg_three_associated_lambda_sq`
    (`−3 ~ λ²`), and the key lemma `coprime_conj_of_lambda_not_dvd` —
    `IsCoprime (A + B·η) (A + B·η²)` holds whenever `A, B` are coprime in `𝓞 K`
    and `λ ∤ (A + B·η)`. **Discharged**, using primality of `λ`
    (`zeta_sub_one_prime'`) and the PID structure (`three_pid`,
    `isCoprime_of_prime_dvd`).
  * **M2 entry condition** `lambda_dvd_conj_iff` (`λ ∣ (A+B·η) ↔ λ ∣ (A+B)`) and
    `lambda_not_dvd_conj` — lifts the side-condition from `A + B` to the conjugate,
    bridging to the integer condition `3 ∤ (A + B)`.
  * **M3** `associated_pow_of_coprime_mul(_both)` and the `𝓞 K` specialization
    `associated_pow_cyclotomic` — coprime factorization ⇒ each factor is a
    `z`-th power up to a unit (the engine: `exists_associated_pow_of_mul_eq_pow'`).
  * **M3 unconditional** `eisenstein_power_extraction` — M2-proper composed with
    M3: for coprime `A, B`, `λ ∤ (A + B·η)`, and `A² − A·B + B² = tᶻ`, one gets
    `∃ d, Associated (dᶻ) (A + B·η)` **with no coprimality hypothesis assumed**.

What remains is the unit/Kummer step (M4) and the descent assembly. A precise,
lemma-by-lemma continuation:

### Obstruction now hit (M4 — the unit constraint)

`eisenstein_power_extraction` gives `Associated (dᶻ) (A + B·η)`, i.e.
`A + B·η = u·dᶻ` for some unit `u : (𝓞 K)ˣ`. The next obstruction is purely the
**unit bookkeeping**:

  (a) `Units.mem` constrains `u ∈ {±1, ±η, ±η²}`; one must absorb the `η^k`
      factor into `dᶻ`. This needs `z` coprime to `3` so that `η^k` is itself a
      `z`-th power of a unit (`η` has order `3`), reducing `u` to `{±1}`. The
      coprimality `gcd(z,3)=1` is an *arithmetic hypothesis* to thread through
      from the Beal reduction (the `3 ∣ z` subcase is the FLT-3 branch handled in
      `BealCubeDescentThree`); until it is wired in, `eisenstein_descent_unit`
      below must **take `IsCoprime z 3` (or the explicit `η^k` absorption) as a
      hypothesis** rather than assert it.

  (b) With `u ∈ {±1}`, `A + B·η = ±dᶻ` and `A + B = sᶻ` (from
      `BealCubeDescent.cube_sum_descent`) must be compared. Extracting integer
      relations requires taking the `ℤ`-coordinates of `A + B·η` in the basis
      `{1, η}` (or trace/norm to `ℤ`) — `𝓞 K`-basis/coordinate API not yet wired.

### Next concrete lemmas (continuation)

3. `eisenstein_descent_unit` — feed `eisenstein_power_extraction` through the
   `Associated`-unwrap to get `A + B·η = u · dᶻ` with `u : (𝓞 K)ˣ`. Then
   `Units.mem` constrains `u ∈ {±1, ±η, ±η²}`. With `z` coprime to `3` (an added
   hypothesis until threaded from the Beal reduction), absorb `η^k` into `dᶻ` by
   adjusting `d` by a `z`-th-power preimage of `η^k`, reducing to `u ∈ {1, −1}`.

4. `kummer_reduction` — apply Kummer's lemma
   `IsCyclotomicExtension.Rat.Three.eq_one_or_neg_one_of_unit_of_congruent`
   to pin the residual unit, then take real/imaginary parts (or the trace/norm to
   `ℤ`) of `A + B·η = ±dᶻ`. Compare with `A + B = sᶻ` from
   `BealCubeDescent.cube_sum_descent` to extract integer relations between
   `s, t, d` — the descent equations.

5. `beal_33z_descent_step` — assemble (1)–(4) into the headline: under the Beal
   cube-sum hypotheses (coprime `A, B`, `3 ∤ C`, `z` with the appropriate
   coprimality to `3`), the solution descends to a strictly smaller Eisenstein
   solution, contradicting minimality (use the `Solution'`/`Solution` minimal-
   descent framework of `Mathlib/NumberTheory/FLT/Three.lean` as the template,
   adapting `FermatLastTheoremForThreeGen` to the exponent-`z` norm form).

### Mathlib declarations to use for the continuation

* `IsCyclotomicExtension.Rat.Three.eta_sq : η² = −η − 1` — reduce `η`-powers.
* `IsCyclotomicExtension.Rat.Three.Units.mem` — `u ∈ {±1, ±η, ±η²}` (M4 step (a)).
* `IsCyclotomicExtension.Rat.Three.eq_one_or_neg_one_of_unit_of_congruent` — Kummer.
* `IsCyclotomicExtension.Rat.three_pid` (used) — PID ⇒ UFD ⇒ `Prime λ`.
* `IsPrimitiveRoot.zeta_sub_one_prime'` (used) — `Prime (η − 1)`, the engine of
  M2-proper via `isCoprime_of_prime_dvd`.
* `Mathlib/NumberTheory/FLT/Three.lean`: `Solution'`, `Solution`,
  `FermatLastTheoremForThreeGen`, and the model lemma `isCoprime_helper` — the
  minimal-descent scaffolding to imitate.

Note: mathlib's `IsCyclotomicExtension.Rat.Three.lambda_sq : λ² = −3·η` is
`private`, so this file re-derives it as the public `lambda_sq_eq` from
`eta_sq_add_eta_add_one`.
-/
