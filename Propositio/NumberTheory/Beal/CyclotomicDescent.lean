import Mathlib.RingTheory.Coprime.Basic
import Mathlib.RingTheory.Int.Basic
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.RootsOfUnity.CyclotomicUnits
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.NumberTheory.NumberField.Cyclotomic.PID
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.Tactic
import Propositio.NumberTheory.Beal.PrimeDescent
import Propositio.NumberTheory.Beal.CyclotomicFactor
import Propositio.NumberTheory.Beal.EisensteinDescent
import Propositio.NumberTheory.Beal.PrimeDescentFiveFull

/-!
# The GENERAL `(p, p, z)` cyclotomic descent structure theorem (Lean 4 / mathlib)

**NEW mathematics — no LaTTe sibling.** This file abstracts the two completed
cyclotomic descents — `p = 3` (`BealEisensteinDescent` / `BealCubeSynthesis`) and
`p = 5` (`BealPrimeDescentFiveFull` / `BealFiveStructure`) — into a **single
theorem over a general prime `p`**, parametrized only by the structural inputs that
both share. The `p = 3` and `p = 5` results then become **one-line instances**
(`beal_33z_structure_inst`, `beal_55z_structure_inst`) of the general engine, and
any future prime `p` whose cyclotomic ring `𝓞 (ℚ(ζ_p))` is a PID is also a one-line
instance.

## The abstraction

Reading the `p = 5` file `BealPrimeDescentFiveFull` shows that *every* ingredient of
its descent is already **`p`-uniform** — `5` is only ever used through general
mathlib lemmas:

* `λ = ζ − 1` is prime: `IsPrimitiveRoot.zeta_sub_one_prime'` (general odd prime,
  via `Fact (Nat.Prime p)`).
* differences of distinct `p`-th roots are associates of `λ`:
  `IsPrimitiveRoot.associated_pow_add_sub_sub_one` (general `n`).
* `λ ∣ (n : 𝓞 K) ↔ p ∣ n` for `n : ℤ`: `norm_toInteger_sub_one_of_prime_ne_two'`
  (`N(λ) = p`) + `Ideal.norm_dvd_iff` (general odd prime).
* factor coprimality: `isCoprime_of_prime_dvd` (general).
* power extraction: `exists_associated_pow_of_mul_eq_pow'` via the PID → `IsBezout`
  (general).

So the only genuinely per-prime input is **`IsPrincipalIdealRing (𝓞 K)`** — class
number `1`. We **take it as a typeclass hypothesis** `[IsPrincipalIdealRing (𝓞 K)]`,
and mathlib's `IsCyclotomicExtension.Rat.three_pid` / `five_pid` discharge it for
`p = 3, 5`.

## What this file proves (namespace `BealCyclotomicDescent`)

All over a general prime `p` with `[Fact p.Prime]`, `p ≠ 2`, a cyclotomic field `K`
with `[IsCyclotomicExtension {p} ℚ K]`, and `[IsPrincipalIdealRing (𝓞 K)]`:

* **Item 1** `lambda_dvd_intCast_iff_gen` — `λ ∣ (n : 𝓞 K) ↔ p ∣ n` (general odd
  prime), generalizing `lambda_dvd_intCast_iff_five` / `lambda_dvd_intCast_iff`.
* **Item 2** `zeta_diff_dvd_lambda_gen` (= `zeta_diff_associated_lambda_gen`) and
  `coprime_conj_gen` — the general factor-coprimality
  `IsCoprime (A + ζⁱ·B) (A + ζʲ·B)` for distinct `i, j` mod `p`, under
  `IsCoprime A B` and `λ ∤ (A + B)`.
* **Item 3 (HEADLINE)** `cyclotomic_power_extraction_gen` — the general cyclotomic
  power-extraction: given `IsCoprime A B`, `λ ∤ (A + B)`, and the perfect-power
  product `(A + ζ·B)·∏_{other conjugates} = tᶻ`, conclude
  `∃ d, Associated (dᶻ) (A + ζ·B)`.
* **Item 4 (HEADLINE)** `beal_ppz_structure_gen` — the structure theorem assembled:
  for `Nat.Coprime A B`, `¬ p ∣ (A + B)`, `z ≠ 0`, `Aᵖ + Bᵖ = Cᶻ`,
  `(∃ s, A + B = sᶻ) ∧ (∃ d, Associated (dᶻ) (A + B·ζ))`.
* **Item 5** `beal_33z_structure_inst`, `beal_55z_structure_inst` — the `p = 3` and
  `p = 5` instances, recovering `BealCubeSynthesis.beal_cube_structure_three_ndvd_C`
  / `BealFiveStructure.beal_55z_structure` from the general engine in one line each.

The remaining gap — uniform over `p` — is the **unit / Kummer step**: pinning the
residual unit `u` in `A + ζ·B = u·dᶻ`. For `p = 3` the unit group is finite; for
`p ≥ 5` it has positive rank, and mathlib carries no general Kummer lemma. This is
the honest, `p`-uniform endpoint of the cyclotomic rung, *beyond* what the PID
(class number `1`) resolves.

Dependency policy: mathlib4 permitted (user authorization 2026-05-17). Use
`lake env lean BealCyclotomicDescent.lean` to typecheck (cyclotomic imports ⟹ slow,
~90s).
-/

namespace BealCyclotomicDescent

open scoped NumberField
open Finset

/-!
## 0. `Odd p` from a prime `p ≠ 2`

The whole development needs the odd-prime hypothesis. We package it once: a prime
`p ≠ 2` is odd.
-/

/-- A prime `p ≠ 2` is odd. -/
theorem odd_of_prime_ne_two {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) : Odd p :=
  hp.odd_of_ne_two h2

/-!
## 1. The λ-bridge: `λ ∣ (n : 𝓞 K) ↔ p ∣ n` (general odd prime)

The unique prime `λ = ζ − 1` over `p` detects integer divisibility by `p`, through
the norm `N(λ) = p` (`norm_toInteger_sub_one_of_prime_ne_two'`, general for odd
primes) and `Ideal.norm_dvd_iff`. This is the general form of
`BealCubeSynthesis.lambda_dvd_intCast_iff` (`p = 3`) and
`BealPrimeDescentFiveFull.lambda_dvd_intCast_iff_five` (`p = 5`).
-/

/-- **Item 1 — the λ-bridge (integer cast form), general odd prime.** In
`𝓞 K = ℤ[ζ_p]`, for `n : ℤ`, `λ = ζ − 1` divides the image of `n` iff `p ∣ n`.
Proof: `N(λ) = p` is prime (`prime_norm_toInteger_sub_one_of_prime_ne_two'`,
`norm_toInteger_sub_one_of_prime_ne_two'`), and `Ideal.norm_dvd_iff` gives
`λ ∣ (n : 𝓞 K) ↔ N(λ) ∣ n`. Generalizes `lambda_dvd_intCast_iff`(_five) over the
prime `p`. -/
theorem lambda_dvd_intCast_iff_gen {p : ℕ} [Fact p.Prime] [NeZero p] (hp2 : p ≠ 2)
    {K : Type*} [Field K] [NumberField K]
    [IsCyclotomicExtension {p} ℚ K] {ζ : K} (hζ : IsPrimitiveRoot ζ p) (n : ℤ) :
    (hζ.toInteger - 1) ∣ ((n : ℤ) : 𝓞 K) ↔ (p : ℤ) ∣ n := by
  have hprime : Prime (Algebra.norm ℤ (hζ.toInteger - 1)) :=
    hζ.prime_norm_toInteger_sub_one_of_prime_ne_two' hp2
  have hnorm : Algebra.norm ℤ (hζ.toInteger - 1) = (p : ℤ) :=
    hζ.norm_toInteger_sub_one_of_prime_ne_two' hp2
  have hiff := Ideal.norm_dvd_iff (S := 𝓞 K) hprime (y := n)
  rw [hnorm] at hiff
  rw [← hiff]

/-!
## 2. Differences of `p`-th roots are associated to `λ`, and factor coprimality

The general replacement for the explicit `p = 3` discriminant `(ω − ω²)² = −3`:
every difference `ζ^j − ζ^i` of distinct powers of a primitive `p`-th root is a unit
multiple of `λ = ζ − 1`. This is `IsPrimitiveRoot.associated_pow_add_sub_sub_one`,
which gives `Associated (ζ − 1) (ζ^(i+m) − ζ^i)` for `m` coprime to `p`; since `p`
is prime, every `0 < m < p` is coprime to `p`.
-/

/-- **Difference of distinct `p`-th roots is associated to `λ` (general).** For a
primitive `p`-th root of unity `η = ζ` in `𝓞 K` and distinct `i, j ∈ range p`,
`Associated (η − 1) (η^j − η^i)`. The general-`p` analogue of
`BealPrimeDescentFiveFull.zeta_diff_associated_lambda`. Proof: write `j = i + m`
(wlog `i ≤ j`) with `0 < m < p`, so `m` is coprime to the prime `p`, and apply
`associated_pow_add_sub_sub_one`; the `j < i` case follows by negation. -/
theorem zeta_diff_associated_lambda_gen {p : ℕ} (hp : p.Prime) [NeZero p]
    {K : Type*} [Field K] [NumberField K]
    [IsCyclotomicExtension {p} ℚ K] {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    {i j : ℕ} (hi : i < p) (hj : j < p) (hne : i ≠ j) :
    Associated (hζ.toInteger - 1) (hζ.toInteger ^ j - hζ.toInteger ^ i) := by
  have hη : IsPrimitiveRoot hζ.toInteger p := hζ.toInteger_isPrimitiveRoot
  have h2p : 2 ≤ p := hp.two_le
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · -- i < j: set m = j - i, with 0 < m < p, coprime to p.
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt hlt
    -- now j = i + m + 1; mm = m + 1, 0 < mm < p.
    have hmcop : (m + 1).Coprime p :=
      (Nat.coprime_of_lt_prime (by omega) (by omega) hp).symm
    have h := hη.associated_pow_add_sub_sub_one h2p i hmcop
    have heq : i + (m + 1) = i + m + 1 := by ring
    rwa [heq] at h
  · -- j < i: symmetric, negate.
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt hgt
    have hmcop : (m + 1).Coprime p :=
      (Nat.coprime_of_lt_prime (by omega) (by omega) hp).symm
    have h := hη.associated_pow_add_sub_sub_one h2p j hmcop
    have heq : j + (m + 1) = j + m + 1 := by ring
    rw [heq] at h
    have hneg : hζ.toInteger ^ j - hζ.toInteger ^ (j + m + 1)
        = -(hζ.toInteger ^ (j + m + 1) - hζ.toInteger ^ j) := by ring
    rw [hneg]
    exact h.neg_right

/-- **The λ-bridge for conjugate factors (general).** `λ ∣ (A + B·ζⁱ) ↔ λ ∣ (A + B)`
in `𝓞 K`, because `(A + B·ζⁱ) − (A + B) = B·(ζⁱ − 1)` and `λ = ζ − 1 ∣ ζⁱ − 1`
(`sub_dvd_pow_sub_pow`). The general-`p` analogue of
`BealEisensteinDescent.lambda_dvd_conj_iff` /
`BealFiveStructure.lambda_dvd_conj_five_iff`. -/
theorem lambda_dvd_conj_iff_gen {K : Type*} [Field K] {p : ℕ} [NeZero p]
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) (A B : 𝓞 K) (i : ℕ) :
    (hζ.toInteger - 1) ∣ (A + B * hζ.toInteger ^ i) ↔ (hζ.toInteger - 1) ∣ (A + B) := by
  have hpow : (hζ.toInteger - 1) ∣ (hζ.toInteger ^ i - 1) := by
    have := sub_dvd_pow_sub_pow (hζ.toInteger) 1 i
    simpa using this
  have hdvd : (hζ.toInteger - 1) ∣ ((A + B * hζ.toInteger ^ i) - (A + B)) := by
    have hfac : (A + B * hζ.toInteger ^ i) - (A + B) = B * (hζ.toInteger ^ i - 1) := by ring
    rw [hfac]; exact hpow.mul_left B
  constructor
  · intro h
    have h2 := dvd_sub h hdvd
    rwa [sub_sub_cancel] at h2
  · intro h
    have h2 := dvd_add h hdvd
    rwa [add_sub_cancel] at h2

/-- **The divisibility skeleton (general `i, j`).** With `η = ζ`, for any Bézout
pair `u·A + v·B = 1`, a common divisor `d` of `A + B·η^i` and `A + B·η^j` divides
`η^i − η^j`. The general analogue of
`BealFiveStructure.dvd_zeta_pow_sub_of_dvd_conj`. -/
theorem dvd_zeta_pow_sub_of_dvd_conj_gen {K : Type*} [Field K] {p : ℕ} [NeZero p] {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) {A B u v d : 𝓞 K} {i j : ℕ}
    (huv : u * A + v * B = 1)
    (hd₁ : d ∣ A + B * hζ.toInteger ^ i)
    (hd₂ : d ∣ A + B * hζ.toInteger ^ j) :
    d ∣ (hζ.toInteger ^ i - hζ.toInteger ^ j) := by
  set η := hζ.toInteger
  have hdB : d ∣ B * (η ^ i - η ^ j) := by
    have hsub : (A + B * η ^ i) - (A + B * η ^ j) = B * (η ^ i - η ^ j) := by ring
    rw [← hsub]; exact dvd_sub hd₁ hd₂
  have hdA : d ∣ A * (η ^ j - η ^ i) := by
    have htw : η ^ j * (A + B * η ^ i) - η ^ i * (A + B * η ^ j) = A * (η ^ j - η ^ i) := by
      ring
    rw [← htw]; exact dvd_sub (hd₁.mul_left _) (hd₂.mul_left _)
  have hdA' : d ∣ A * (η ^ i - η ^ j) := by
    have : A * (η ^ i - η ^ j) = -(A * (η ^ j - η ^ i)) := by ring
    rw [this]; exact hdA.neg_right
  have hcomb : v * (B * (η ^ i - η ^ j)) + u * (A * (η ^ i - η ^ j)) = (η ^ i - η ^ j) := by
    linear_combination (η ^ i - η ^ j) * huv
  rw [← hcomb]
  exact dvd_add (hdB.mul_left v) (hdA'.mul_left u)

/-- **Item 2 — general factor coprimality `coprime_conj_gen`.** For distinct
`i, j ∈ {0, …, p−1}`, the cyclotomic factors `A + ζⁱ·B` and `A + ζʲ·B` are coprime
in `𝓞 K = ℤ[ζ_p]`, whenever `A, B` are coprime and `λ = ζ − 1 ∤ (A + B)`.

This is the general `i, j` version of
`BealPrimeDescentFiveFull.coprime_conj_five_of_lambda_not_dvd` /
`BealFiveStructure.coprime_conj_five_ij`. Proof via `isCoprime_of_prime_dvd`: a
common prime divides `ζⁱ − ζʲ ~ λ` (`zeta_diff_associated_lambda_gen`,
`dvd_zeta_pow_sub_of_dvd_conj_gen`), hence `~ λ` (both prime,
`Prime.associated_of_dvd`), hence `λ ∣ (A + ζⁱ·B)`, contradicting `λ ∤ (A + B)` via
`lambda_dvd_conj_iff_gen`. The PID hypothesis supplies `IsBezout` so that
`isCoprime_of_prime_dvd` applies. -/
theorem coprime_conj_gen {p : ℕ} [Fact p.Prime] [NeZero p] (_hp2 : p ≠ 2)
    {K : Type*} [Field K] [NumberField K]
    [IsCyclotomicExtension {p} ℚ K] [IsPrincipalIdealRing (𝓞 K)]
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) {A B : 𝓞 K}
    (hAB : IsCoprime A B)
    (hlam : ¬ (hζ.toInteger - 1) ∣ (A + B))
    {i j : ℕ} (hi : i < p) (hj : j < p) (hne : i ≠ j) :
    IsCoprime (A + B * hζ.toInteger ^ i) (A + B * hζ.toInteger ^ j) := by
  have hp : p.Prime := (inferInstance : Fact p.Prime).out
  set η := hζ.toInteger with hη_def
  obtain ⟨u, v, huv⟩ := hAB
  have huv' : u * A + v * B = 1 := by linear_combination huv
  -- λ = η − 1 is prime in 𝓞 K (general odd prime).
  have hlamPrime : Prime (η - 1) := hζ.zeta_sub_one_prime'
  -- ηⁱ − ηʲ is associated to λ (difference of distinct p-th roots).
  have hassoc : Associated (η - 1) (η ^ i - η ^ j) :=
    zeta_diff_associated_lambda_gen hp hζ hj hi hne.symm
  -- The λ-non-divisibility transports to A + B·ηⁱ.
  have hlami : ¬ (η - 1) ∣ (A + B * η ^ i) := by
    rw [lambda_dvd_conj_iff_gen hζ A B i]; exact hlam
  refine isCoprime_of_prime_dvd ?_ ?_
  · rintro ⟨h1, -⟩
    exact hlami (h1 ▸ dvd_zero _)
  · intro q hq q_dvd_1 q_dvd_2
    have hqδ : q ∣ (η ^ i - η ^ j) := dvd_zeta_pow_sub_of_dvd_conj_gen hζ huv' q_dvd_1 q_dvd_2
    have hq_lam : q ∣ (η - 1) := hqδ.trans hassoc.symm.dvd
    have hlam_q : (η - 1) ∣ q :=
      (hq.associated_of_dvd hlamPrime hq_lam).symm.dvd
    exact hlami (hlam_q.trans q_dvd_1)

/-- **Item 2 (alias) — `zeta_diff_dvd_lambda_gen`.** A common divisor of two distinct
cyclotomic factors divides `λ = ζ − 1` (up to associates): from a Bézout pair it
divides `ζⁱ − ζʲ ~ λ`. Records the divisibility-into-`λ` content used by
`coprime_conj_gen` in standalone form. -/
theorem zeta_diff_dvd_lambda_gen {p : ℕ} (hp : p.Prime) [NeZero p]
    {K : Type*} [Field K] [NumberField K]
    [IsCyclotomicExtension {p} ℚ K] {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    {A B u v d : 𝓞 K} {i j : ℕ}
    (hi : i < p) (hj : j < p) (hne : i ≠ j)
    (huv : u * A + v * B = 1)
    (hd₁ : d ∣ A + B * hζ.toInteger ^ i)
    (hd₂ : d ∣ A + B * hζ.toInteger ^ j) :
    d ∣ (hζ.toInteger - 1) := by
  have hassoc : Associated (hζ.toInteger - 1) (hζ.toInteger ^ i - hζ.toInteger ^ j) :=
    zeta_diff_associated_lambda_gen hp hζ hj hi hne.symm
  have hδ : d ∣ (hζ.toInteger ^ i - hζ.toInteger ^ j) :=
    dvd_zeta_pow_sub_of_dvd_conj_gen hζ huv hd₁ hd₂
  exact hδ.trans hassoc.symm.dvd

/-!
## 3. The general cyclotomic power extraction (HEADLINE)

Composing item 2 with the PID power-extraction engine
`exists_associated_pow_of_mul_eq_pow'` (PID ⟹ `IsBezout`). The product coprimality
of `A + ζ·B` against the complementary cofactor `γ = ∏_{i ∈ Ico 2 p}(A + ζⁱ·B)`
comes from `IsCoprime.prod_right` over the uniform pairwise lemma `coprime_conj_gen`.
-/

/-- **Product coprimality (general).** The cyclotomic factor `A + ζ·B` is coprime to
the full complementary product `γ = ∏_{i ∈ Ico 2 p}(A + ζⁱ·B)` in `𝓞 K = ℤ[ζ_p]`,
whenever `A, B` are coprime and `λ = ζ − 1 ∤ (A + B)`. General analogue of
`BealFiveStructure.prod_cofactor_coprime_five`, via `IsCoprime.prod_right` over
`coprime_conj_gen` (`i = 1` vs each `j ∈ {2, …, p−1}`). -/
theorem prod_cofactor_coprime_gen {p : ℕ} [Fact p.Prime] [NeZero p] (hp2 : p ≠ 2)
    {K : Type*} [Field K] [NumberField K]
    [IsCyclotomicExtension {p} ℚ K] [IsPrincipalIdealRing (𝓞 K)]
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) {A B : 𝓞 K}
    (hAB : IsCoprime A B)
    (hlam : ¬ (hζ.toInteger - 1) ∣ (A + B)) :
    IsCoprime (A + B * hζ.toInteger ^ 1)
      (∏ j ∈ Finset.Ico 2 p, (A + B * hζ.toInteger ^ j)) := by
  have hp : p.Prime := (inferInstance : Fact p.Prime).out
  have hp1 : 1 < p := hp.one_lt
  apply IsCoprime.prod_right
  intro j hj
  rw [Finset.mem_Ico] at hj
  exact coprime_conj_gen hp2 hζ hAB hlam (by omega) (by omega) (by omega)

/-- **Item 3 (HEADLINE) — `cyclotomic_power_extraction_gen`.** Over a general prime
`p` (odd, with `𝓞 K = ℤ[ζ_p]` a PID), given coprime `A, B`, `λ = ζ − 1 ∤ (A + B)`,
and the perfect-power product of the cyclotomic factor with its complementary
cofactor,

  `(A + ζ·B) · ∏_{i ∈ Ico 2 p}(A + ζⁱ·B) = tᶻ`,

the displayed factor `A + ζ·B` is a `z`-th power up to a unit of `ℤ[ζ_p]`:

  `∃ d, Associated (dᶻ) (A + ζ·B)`.

The general cyclotomic power-extraction. The coprimality input that the per-prime
engines (`associated_pow_cyclotomic_five`) took as a hypothesis is **discharged**
here by `prod_cofactor_coprime_gen` (item 2 + `IsCoprime.prod_right`), and the PID
power-extraction is `exists_associated_pow_of_mul_eq_pow'` (PID ⟹ `IsBezout`).
Generalizes both `BealPrimeDescentFiveFull.five_power_extraction_unconditional`
(`p = 5`) and `BealEisensteinDescent.eisenstein_power_extraction` (`p = 3`). -/
theorem cyclotomic_power_extraction_gen {p : ℕ} [Fact p.Prime] [NeZero p] (hp2 : p ≠ 2)
    {K : Type*} [Field K] [NumberField K]
    [IsCyclotomicExtension {p} ℚ K] [IsPrincipalIdealRing (𝓞 K)]
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) {A B t : 𝓞 K} {z : ℕ}
    (hAB : IsCoprime A B)
    (hlam : ¬ (hζ.toInteger - 1) ∣ (A + B))
    (h : (A + B * hζ.toInteger ^ 1)
        * (∏ i ∈ Finset.Ico 2 p, (A + B * hζ.toInteger ^ i)) = t ^ z) :
    ∃ d : 𝓞 K, Associated (d ^ z) (A + B * hζ.toInteger) := by
  haveI : IsBezout (𝓞 K) := inferInstance
  have hcop : IsCoprime (A + B * hζ.toInteger ^ 1)
      (∏ i ∈ Finset.Ico 2 p, (A + B * hζ.toInteger ^ i)) :=
    prod_cofactor_coprime_gen hp2 hζ hAB hlam
  have hres := exists_associated_pow_of_mul_eq_pow' hcop h
  -- hres : ∃ d, Associated (d^z) (A + B * η^1); rewrite η^1 = η.
  rwa [pow_one] at hres

/-!
## 4. The general `(p, p, z)` structure theorem (HEADLINE)

Assembling the integer descent (`BealPrimeDescent.prime_sum_descent`) with the
cyclotomic power-extraction (item 3) via the λ-bridge. We build the perfect-power
product `(A + ζ·B)·∏ = tᶻ` from the cyclotomic factorization
`BealCyclotomicFactor.prod_add_eq_pow_add` and the integer descent's `A + B = sᶻ`,
`Aᵖ + Bᵖ = Cᶻ`, `C = s·t`.
-/

/-- **Item 4 (HEADLINE) — `beal_ppz_structure_gen`.** The GENERAL `(p, p, z)`
cyclotomic descent structure theorem. For a general prime `p` (odd, `𝓞 K = ℤ[ζ_p]`
a PID), a primitive `(p, p, z)` Beal solution with `p ∤ (A + B)` makes `A + B` a
perfect `z`-th power *in `ℤ`* **and** `A + B·ζ` a `z`-th power up to a unit *in
`ℤ[ζ_p]`*, simultaneously:

  `(∃ s, A + B = sᶻ) ∧ (∃ d : 𝓞 K, Associated (dᶻ) ((A : 𝓞 K) + B·ζ))`.

The integer conjunct is `BealPrimeDescent.prime_sum_descent`. The cyclotomic
conjunct composes: the λ-bridge `p ∤ (A+B) ⟹ λ ∤ (A + B)` in `𝓞 K`
(`lambda_dvd_intCast_iff_gen`), coprimality lifted to `𝓞 K`, the perfect-power
product `(A + ζ·B)·γ = tᶻ` built from `prod_add_eq_pow_add` (cancelling
`A + B ≠ 0`), fed into `cyclotomic_power_extraction_gen` (item 3). **No λ-hypothesis
assumed:** the λ-bridge is a theorem. The general-`p` analogue of
`BealCubeSynthesis.beal_cube_structure_three_ndvd_C` and
`BealFiveStructure.beal_55z_structure`. **NEW.** -/
theorem beal_ppz_structure_gen {p : ℕ} [Fact p.Prime] [NeZero p] (hp2 : p ≠ 2)
    {K : Type*} [Field K] [NumberField K]
    [IsCyclotomicExtension {p} ℚ K] [IsPrincipalIdealRing (𝓞 K)]
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    {A B C z : ℕ} (hAB : Nat.Coprime A B) (hpAB : ¬ p ∣ (A + B)) (hz : z ≠ 0)
    (h : A ^ p + B ^ p = C ^ z) :
    (∃ s : ℕ, A + B = s ^ z) ∧
    (∃ d : 𝓞 K, Associated (d ^ z) ((A : 𝓞 K) + (B : 𝓞 K) * hζ.toInteger)) := by
  classical
  have hp : p.Prime := (inferInstance : Fact p.Prime).out
  have hodd : Odd p := odd_of_prime_ne_two hp hp2
  set η := hζ.toInteger with hη_def
  have hηprim : IsPrimitiveRoot η p := hζ.toInteger_isPrimitiveRoot
  -- Integer descent: A + B = sᶻ, (Φ).toNat = tᶻ, C = s·t.
  obtain ⟨s, t, hs, _ht, hC⟩ := BealPrimeDescent.prime_sum_descent hp hodd hAB hpAB hz h
  refine ⟨⟨s, hs⟩, ?_⟩
  -- Coprimality of A, B lifted to 𝓞 K (via ℤ).
  have hcopZ : IsCoprime (A : ℤ) (B : ℤ) :=
    Int.isCoprime_iff_nat_coprime.mpr (by simpa using hAB)
  have hcopOK : IsCoprime ((A : 𝓞 K)) ((B : 𝓞 K)) := by
    have := hcopZ.map (algebraMap ℤ (𝓞 K))
    simpa using this
  -- λ ∤ (A + B) in 𝓞 K, from p ∤ (A + B) in ℕ.
  have hlamAB : ¬ (η - 1) ∣ ((A : 𝓞 K) + (B : 𝓞 K)) := by
    have hcast : ((A : 𝓞 K) + (B : 𝓞 K)) = (((A + B : ℕ) : ℤ) : 𝓞 K) := by push_cast; ring
    rw [hcast, lambda_dvd_intCast_iff_gen hp2 hζ]
    intro hdvd
    exact hpAB (by exact_mod_cast hdvd)
  -- The cyclotomic factorization over 𝓞 K: ∏_{range p}(A + ηⁱB) = A^p + B^p.
  have hfull : ∏ i ∈ Finset.range p, ((A : 𝓞 K) + η ^ i * (B : 𝓞 K))
      = (A : 𝓞 K) ^ p + (B : 𝓞 K) ^ p :=
    BealCyclotomicFactor.prod_add_eq_pow_add hodd hηprim (A : 𝓞 K) (B : 𝓞 K)
  -- Split off i = 0: ∏_{range p} = (A + B) · ∏_{Ico 1 p}.
  have h0 : (0 : ℕ) ∈ Finset.range p := Finset.mem_range.mpr hp.pos
  have hsplit0 := Finset.prod_eq_prod_diff_singleton_mul h0
    (fun i => (A : 𝓞 K) + η ^ i * (B : 𝓞 K))
  have hset0 : Finset.range p \ {0} = Finset.Ico 1 p := by
    ext x; simp only [Finset.mem_sdiff, Finset.mem_range, Finset.mem_singleton,
      Finset.mem_Ico]; omega
  rw [hset0, pow_zero, one_mul] at hsplit0
  -- hsplit0 : ∏_{range p} = (∏_{Ico 1 p}) * (A + B)
  have hfact : ((A : 𝓞 K) + (B : 𝓞 K))
      * ∏ i ∈ Finset.Ico 1 p, ((A : 𝓞 K) + η ^ i * (B : 𝓞 K))
      = (A : 𝓞 K) ^ p + (B : 𝓞 K) ^ p := by
    rw [← hfull, hsplit0]; ring
  -- A^p + B^p = Cᶻ in 𝓞 K.
  have hCz : (A : 𝓞 K) ^ p + (B : 𝓞 K) ^ p = (C : 𝓞 K) ^ z := by exact_mod_cast h
  -- A + B = sᶻ and C = s·t in 𝓞 K.
  have hsOK : (A : 𝓞 K) + (B : 𝓞 K) = (s : 𝓞 K) ^ z := by exact_mod_cast hs
  have hCOK : (C : 𝓞 K) = (s : 𝓞 K) * (t : 𝓞 K) := by exact_mod_cast hC
  -- A + B ≠ 0 (p ∤ (A + B) forces A + B ≥ 1).
  have hABpos : (A : 𝓞 K) + (B : 𝓞 K) ≠ 0 := by
    have hnat : A + B ≠ 0 := by
      intro h0; exact hpAB (h0 ▸ dvd_zero p)
    have hcast : ((A + B : ℕ) : 𝓞 K) ≠ 0 := by
      rw [Nat.cast_ne_zero]; exact hnat
    have hpc : ((A + B : ℕ) : 𝓞 K) = (A : 𝓞 K) + (B : 𝓞 K) := by push_cast; ring
    rwa [hpc] at hcast
  -- Cancel A + B from (A+B)·∏ = Cᶻ = sᶻ·tᶻ = (A+B)·tᶻ to get ∏ = tᶻ.
  have hprodEq : (∏ i ∈ Finset.Ico 1 p, ((A : 𝓞 K) + η ^ i * (B : 𝓞 K))) = (t : 𝓞 K) ^ z := by
    apply mul_left_cancel₀ hABpos
    rw [hfact, hCz, hCOK, mul_pow, ← hsOK]
  -- Split off i = 1: ∏_{Ico 1 p} = (A + η·B) · ∏_{Ico 2 p}.
  have h1mem : (1 : ℕ) ∈ Finset.Ico 1 p := by
    rw [Finset.mem_Ico]; exact ⟨le_refl 1, hp.one_lt⟩
  have hsplit1 := Finset.prod_eq_prod_diff_singleton_mul h1mem
    (fun i => (A : 𝓞 K) + η ^ i * (B : 𝓞 K))
  have hset1 : Finset.Ico 1 p \ {1} = Finset.Ico 2 p := by
    ext x; simp only [Finset.mem_sdiff, Finset.mem_Ico, Finset.mem_singleton]; omega
  rw [hset1, pow_one] at hsplit1
  -- Convert factors to the `A + B * η^i` orientation used by item 3.
  set γ : 𝓞 K := ∏ i ∈ Finset.Ico 2 p, ((A : 𝓞 K) + (B : 𝓞 K) * η ^ i) with hγ_def
  have hγeq : (∏ i ∈ Finset.Ico 2 p, ((A : 𝓞 K) + η ^ i * (B : 𝓞 K))) = γ := by
    rw [hγ_def]; apply Finset.prod_congr rfl; intro i _; ring
  -- The perfect-power product (A + B·η)·γ = tᶻ in the item-3 orientation.
  have hprodFactor : ((A : 𝓞 K) + (B : 𝓞 K) * η ^ 1) * γ = (t : 𝓞 K) ^ z := by
    rw [pow_one, ← hγeq, ← hprodEq, hsplit1]; ring
  -- Apply the general cyclotomic power extraction (item 3).
  exact cyclotomic_power_extraction_gen hp2 hζ hcopOK hlamAB hprodFactor

/-!
## 5. The `p = 3` and `p = 5` instances (one-liners)

The general engine subsumes both completed rungs. We instantiate `p = 3` (PID via
`three_pid`) and `p = 5` (PID via `five_pid`), recovering the per-prime structure
theorems `BealCubeSynthesis.beal_cube_structure_three_ndvd_C` /
`BealFiveStructure.beal_55z_structure` as one-line corollaries. Adding any future
PID prime `p` is the same one-line pattern.
-/

/-- **Item 5 — the `p = 3` instance.** The cube-sum structure theorem recovered from
the general engine `beal_ppz_structure_gen`, with the PID hypothesis discharged by
`IsCyclotomicExtension.Rat.three_pid`. One line. Subsumes
`BealCubeSynthesis.beal_cube_structure_three_ndvd_C` (case `3 ∤ (A + B)`). -/
theorem beal_33z_structure_inst
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {3} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ 3)
    {A B C z : ℕ} (hAB : Nat.Coprime A B) (h3 : ¬ 3 ∣ (A + B)) (hz : z ≠ 0)
    (h : A ^ 3 + B ^ 3 = C ^ z) :
    (∃ s : ℕ, A + B = s ^ z) ∧
    (∃ d : 𝓞 K, Associated (d ^ z) ((A : 𝓞 K) + (B : 𝓞 K) * hζ.toInteger)) := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  haveI : IsPrincipalIdealRing (𝓞 K) := IsCyclotomicExtension.Rat.three_pid K
  exact beal_ppz_structure_gen (by decide) hζ hAB h3 hz h

/-- **Item 5 — the `p = 5` instance.** The `(5, 5, z)` structure theorem recovered
from the general engine `beal_ppz_structure_gen`, with the PID hypothesis discharged
by `IsCyclotomicExtension.Rat.five_pid`. One line. Subsumes
`BealFiveStructure.beal_55z_structure`. -/
theorem beal_55z_structure_inst
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {5} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ 5)
    {A B C z : ℕ} (hAB : Nat.Coprime A B) (h5 : ¬ 5 ∣ (A + B)) (hz : z ≠ 0)
    (h : A ^ 5 + B ^ 5 = C ^ z) :
    (∃ s : ℕ, A + B = s ^ z) ∧
    (∃ d : 𝓞 K, Associated (d ^ z) ((A : 𝓞 K) + (B : 𝓞 K) * hζ.toInteger)) := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  haveI : IsPrincipalIdealRing (𝓞 K) := IsCyclotomicExtension.Rat.five_pid K
  exact beal_ppz_structure_gen (by decide) hζ hAB h5 hz h

end BealCyclotomicDescent

/-!
## REMAINING PLAN

This file abstracts the `p = 3` and `p = 5` cyclotomic descents into **one
general theorem over a prime `p`**, with the per-prime PID input taken as a
typeclass `[IsPrincipalIdealRing (𝓞 K)]` and discharged for `p = 3, 5` by mathlib's
`three_pid` / `five_pid`. All declarations are axiom-clean
(`[propext, Classical.choice, Quot.sound]`).

**The GENERAL `(p, p, z)` cyclotomic descent structure theorem.** Abstracted over
any prime `p` (odd, `p ≠ 2`) with a cyclotomic field `K = ℚ(ζ_p)` and
`IsPrincipalIdealRing (𝓞 K)` (class number `1`):

* **Item 1** `lambda_dvd_intCast_iff_gen` — `λ ∣ (n : 𝓞 K) ↔ p ∣ n` (general odd
  prime), via `N(λ) = p` and `Ideal.norm_dvd_iff`.
* **Item 2** `zeta_diff_associated_lambda_gen` (every `ζⁱ − ζʲ ~ λ`),
  `zeta_diff_dvd_lambda_gen`, and the factor coprimality `coprime_conj_gen`
  (`IsCoprime (A + ζⁱ·B) (A + ζʲ·B)` for distinct `i, j`, under `IsCoprime A B` and
  `λ ∤ (A + B)`), with the product form `prod_cofactor_coprime_gen`.
* **Item 3 (HEADLINE)** `cyclotomic_power_extraction_gen` — the general cyclotomic
  power-extraction: coprime `A, B`, `λ ∤ (A + B)`, and
  `(A + ζ·B)·∏_{i ∈ Ico 2 p}(A + ζⁱ·B) = tᶻ` ⟹ `∃ d, Associated (dᶻ) (A + ζ·B)`.
  Coprimality and PID inputs both discharged internally.
* **Item 4 (HEADLINE)** `beal_ppz_structure_gen` — the structure theorem: `p ∤ (A+B)`
  primitive `(p,p,z)` solution ⟹ `A + B = sᶻ` in `ℤ` **and**
  `Associated (dᶻ) (A + B·ζ)` in `ℤ[ζ_p]`. No λ-hypothesis assumed.
* **Item 5** `beal_33z_structure_inst`, `beal_55z_structure_inst` — the `p = 3`
  (`three_pid`) and `p = 5` (`five_pid`) instances, each a one-line corollary
  recovering `BealCubeSynthesis`/`BealFiveStructure`. **Any future PID prime is the
  same one-line instance.**

### Per-prime facts kept as hypotheses

Only **one**: `[IsPrincipalIdealRing (𝓞 K)]` (class number `1`). Every other
ingredient is genuinely `p`-uniform (general mathlib lemmas
`zeta_sub_one_prime'`, `associated_pow_add_sub_sub_one`,
`norm_toInteger_sub_one_of_prime_ne_two'`, `isCoprime_of_prime_dvd`,
`exists_associated_pow_of_mul_eq_pow'`). mathlib supplies the PID instance for
`p ≤ 19` (`three_pid`, `five_pid`, …); larger primes are class-number-`1` only up to
`p = 19`, after which the descent genuinely changes (irregular primes).

### The remaining gap (uniform over `p`): the unit / Kummer step

`beal_ppz_structure_gen` outputs `Associated (dᶻ) (A + B·ζ)`, i.e.
`A + B·ζ = u·dᶻ` for a unit `u : (𝓞 K)ˣ`. Absorbing `u` into a `z`-th power (the
Kummer step) is the honest, `p`-uniform endpoint:

* For `p = 3` the unit group is **finite** (`{±1, ±η, ±η²}`); absorbing the
  `η`-power part is a finite case-check (`BealCubeSynthesis.kummer_absorb_eta_pow`),
  leaving only a `±1` sign pinned by mathlib's `Three.eq_one_or_neg_one_of_unit_of_congruent`.
* For `p ≥ 5` the unit group has **positive rank** (a real fundamental unit of Pell
  type at `p = 5`); the absorption is not a finite case-check, and mathlib has no
  general `Five`/`p` Kummer lemma. This is the genuine number-theoretic content that
  the PID (class number `1`) does **not** resolve — the uniform-over-`p` frontier.

In short: the GENERAL up-to-a-unit cyclotomic descent (items 1–4) is **closed and
abstracted over any PID prime `p`**; the `p = 3, 5` instances (item 5) confirm the
abstraction subsumes both per-prime developments; the residual unit/Kummer step is
the real open problem, uniform over `p` and beyond what mathlib currently carries.
-/
