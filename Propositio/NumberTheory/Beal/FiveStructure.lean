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
import Propositio.NumberTheory.Beal.PrimeDescentFive
import Propositio.NumberTheory.Beal.PrimeDescentFiveFull

/-!
# Assembling the `(5, 5, z)` cyclotomic descent into a structure theorem (Lean 4 / mathlib)

**NEW mathematics — no LaTTe sibling.** This file *assembles* the two `(5, 5, z)`
descents — the elementary integer descent (`BealPrimeDescentFive.prime_sum_descent_five`)
and the cyclotomic factor descent (`BealPrimeDescentFiveFull.five_power_extraction_unconditional`)
— into a single **structure theorem**, the `p = 5` analogue of
`BealCubeSynthesis.beal_cube_structure_three_ndvd_C`. It is the `p = 5` companion of
`BealCubeSynthesis` (`p = 3`), and it also derives the **integral-basis coordinate
relations** of `𝓞 K = ℤ[ζ₅]` (the `p = 5` analogue of
`BealCubeDescentStep.eta_coords_unique`/`descent_relations_*`).

## What is synthesized

Two independent descents were mechanized separately:

* **Integer descent** (`BealPrimeDescentFive.prime_sum_descent_five`): for coprime
  `A, B`, `5 ∤ (A + B)`, `z ≠ 0`, a solution `A⁵ + B⁵ = C^z` forces
  `A + B = sᶻ`, `(Φ₅).toNat = tᶻ`, `C = s·t` — perfect `z`-th powers in `ℕ`.

* **Cyclotomic descent** (`BealPrimeDescentFiveFull.five_power_extraction_unconditional`):
  in `𝓞 K = ℤ[ζ₅]`, for coprime `A, B` with `λ ∤ (A + ζ·B)`, the cyclotomic factor
  `A + ζ·B` is a `z`-th power up to a unit: `∃ d, Associated (dᶻ) (A + ζ·B)`.

The **structure theorem** `beal_55z_structure` ties them together: a primitive
`(5,5,z)` Beal solution with `5 ∤ (A + B)` makes `A + B` a perfect `z`-th power *in
`ℤ`* **and** `A + ζ·B` a `z`-th power up to a unit *in `ℤ[ζ₅]`*, simultaneously.

## The λ-bridge (the new technical content here)

The cyclotomic descent needs `λ = ζ − 1 ∤ (A + B·ζ)`; the integer side delivers
`5 ∤ (A + B)`. The bridge `5 ∤ (A + B) ⟹ λ ∤ (A + B·ζ)` is closed **fully** via:

  1. `lambda_dvd_conj_five_iff` : `λ ∣ (A+B·ζⁱ) ↔ λ ∣ (A+B)` (the difference
     `(A+B·ζⁱ) − (A+B) = B·(ζⁱ − 1)` is `λ`-divisible since `λ = ζ − 1 ∣ ζⁱ − 1`);
  2. `BealPrimeDescentFiveFull.lambda_dvd_intCast_iff_five` : `λ ∣ (n : 𝓞 K) ↔ 5 ∣ n`.

So **the cyclotomic conjunct closes with no extra hypothesis**: the λ-bridge is a
theorem, not an assumption.

## What is proved vs. the remaining gap

* **Item 1** `prod_cofactor_coprime_five` — the cyclotomic factor `A + ζ·B` is
  coprime to the full complementary product `∏_{i ∈ Ico 2 5}(A + ζⁱ·B)` (and the
  four factors `A + ζⁱ·B`, `i = 1..4`, are pairwise coprime,
  `pairwise_coprime_factors_five`). Routine `IsCoprime.prod_right` bookkeeping on top
  of the uniform pairwise lemma `coprime_conj_five_ij`.

* **Item 2 (HEADLINE)** `beal_55z_structure` — the structure theorem: `5 ∤ (A + B)`
  primitive `(5,5,z)` solution ⟹ `A + B = sᶻ` in `ℤ` **and**
  `Associated (dᶻ) (A + B·ζ)` in `ℤ[ζ₅]`. **No λ-hypothesis assumed.**

* **Item 3** `five_coords_unique`/`descent_relations_two_five` — the `{1,ζ,ζ²,ζ³}`
  integral-basis coordinate-uniqueness engine (`ℤ`-linear independence) and the
  explicit `z = 1` coordinate relation, the `p = 5` analogue of
  `BealCubeDescentStep.eta_coords_unique`.

The remaining gap is the **unit/Kummer step**: `ℤ[ζ₅]` has unit rank `1` (an infinite
unit group, real fundamental unit of Pell type), so absorbing the residual unit `u`
in `A + ζ·B = u·dᶻ` is *not* a finite case-check, and mathlib has no `Five` Kummer
lemma. This is the honest endpoint of the `p = 5` rung, beyond what the PID (class
number `1`) resolves.

Dependency policy: mathlib4 permitted (user authorization 2026-05-17). Use
`lake env lean BealFiveStructure.lean` to typecheck (cyclotomic imports ⟹ slow,
~90s).
-/

namespace BealFiveStructure

open scoped NumberField
open Finset

/-!
## Item 1 — product coprimality of the cyclotomic factors

The power-extraction engine consumes the coprimality of `A + ζ·B` against the
complementary cofactor `γ = ∏_{i ∈ Ico 2 5}(A + ζⁱ·B)`. We obtain it from the uniform
pairwise lemma `coprime_conj_five_ij` (the general `i, j` version of
`BealPrimeDescentFiveFull.coprime_conj_five_of_lambda_not_dvd`) via
`IsCoprime.prod_right`.
-/

/-- **The λ-bridge for the conjugate factors, `p = 5`.** `λ ∣ (A + B·ζⁱ) ↔ λ ∣ (A + B)`
in `𝓞 K`, because `(A + B·ζⁱ) − (A + B) = B·(ζⁱ − 1)` and `λ = ζ − 1 ∣ ζⁱ − 1`
(`sub_dvd_pow_sub_pow` with `ζ¹ = ζ`). The `p = 5` analogue of
`BealEisensteinDescent.lambda_dvd_conj_iff`, generalized to an arbitrary power `i`. -/
theorem lambda_dvd_conj_five_iff {K : Type*} [Field K] {ζ : K} (hζ : IsPrimitiveRoot ζ 5)
    (A B : 𝓞 K) (i : ℕ) :
    (hζ.toInteger - 1) ∣ (A + B * hζ.toInteger ^ i) ↔ (hζ.toInteger - 1) ∣ (A + B) := by
  -- λ = η − 1 divides ηⁱ − 1, hence B·(ηⁱ − 1), hence the difference of the two factors.
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

/-- **Item 1 skeleton (general `i, j`) — a common divisor of two factors divides
`ζⁱ − ζʲ`.** With `η = ζ`, for any Bézout pair `u·A + v·B = 1`, a common divisor `d`
of `A + η^i·B` and `A + η^j·B` divides `η^i − η^j`. The `i, j` generalization of
`BealPrimeDescentFiveFull.dvd_zeta_sub_of_dvd_conj`. -/
theorem dvd_zeta_pow_sub_of_dvd_conj {K : Type*} [Field K] {ζ : K}
    (hζ : IsPrimitiveRoot ζ 5) {A B u v d : 𝓞 K} {i j : ℕ}
    (huv : u * A + v * B = 1)
    (hd₁ : d ∣ A + B * hζ.toInteger ^ i)
    (hd₂ : d ∣ A + B * hζ.toInteger ^ j) :
    d ∣ (hζ.toInteger ^ i - hζ.toInteger ^ j) := by
  set η := hζ.toInteger
  -- d divides the difference B·(ηⁱ − ηʲ).
  have hdB : d ∣ B * (η ^ i - η ^ j) := by
    have hsub : (A + B * η ^ i) - (A + B * η ^ j) = B * (η ^ i - η ^ j) := by ring
    rw [← hsub]; exact dvd_sub hd₁ hd₂
  -- d divides the η-twist A·(ηʲ − ηⁱ) = ηʲ·(A+Bηⁱ) − ηⁱ·(A+Bηʲ).
  have hdA : d ∣ A * (η ^ j - η ^ i) := by
    have htw : η ^ j * (A + B * η ^ i) - η ^ i * (A + B * η ^ j) = A * (η ^ j - η ^ i) := by
      ring
    rw [← htw]; exact dvd_sub (hd₁.mul_left _) (hd₂.mul_left _)
  have hdA' : d ∣ A * (η ^ i - η ^ j) := by
    have : A * (η ^ i - η ^ j) = -(A * (η ^ j - η ^ i)) := by ring
    rw [this]; exact hdA.neg_right
  -- Bézout assembly: v·(B·δ) + u·(A·δ) = (u·A + v·B)·δ = δ, δ = ηⁱ − ηʲ.
  have hcomb : v * (B * (η ^ i - η ^ j)) + u * (A * (η ^ i - η ^ j)) = (η ^ i - η ^ j) := by
    linear_combination (η ^ i - η ^ j) * huv
  rw [← hcomb]
  exact dvd_add (hdB.mul_left v) (hdA'.mul_left u)

/-- **Item 1 (uniform pairwise coprimality).** For distinct `i, j ∈ {1,2,3,4}`, the
cyclotomic factors `A + ζⁱ·B` and `A + ζʲ·B` are coprime in `𝓞 K = ℤ[ζ₅]`, whenever
`A, B` are coprime and `λ = ζ − 1 ∤ (A + B)`. The `i, j` generalization of
`BealPrimeDescentFiveFull.coprime_conj_five_of_lambda_not_dvd`. Proof mirrors that
lemma: a common prime divides `ζⁱ − ζʲ ~ λ` (`zeta_diff_associated_lambda`,
`dvd_zeta_pow_sub_of_dvd_conj`), hence `~ λ`, hence `λ ∣ (A + ζⁱ·B)`, contradicting
`λ ∤ (A + B)` via `lambda_dvd_conj_five_iff`. -/
theorem coprime_conj_five_ij {K : Type*} [Field K] [NumberField K]
    [IsCyclotomicExtension {5} ℚ K] {ζ : K} (hζ : IsPrimitiveRoot ζ 5) {A B : 𝓞 K}
    (hAB : IsCoprime A B)
    (hlam : ¬ (hζ.toInteger - 1) ∣ (A + B))
    {i j : ℕ} (hi : i < 5) (hj : j < 5) (hne : i ≠ j) :
    IsCoprime (A + B * hζ.toInteger ^ i) (A + B * hζ.toInteger ^ j) := by
  haveI : IsPrincipalIdealRing (𝓞 K) := IsCyclotomicExtension.Rat.five_pid K
  set η := hζ.toInteger with hη_def
  obtain ⟨u, v, huv⟩ := hAB
  have huv' : u * A + v * B = 1 := by linear_combination huv
  have hlamPrime : Prime (η - 1) := BealPrimeDescentFive.lambda_five_prime hζ
  -- ηⁱ − ηʲ is associated to λ (difference of distinct 5-th roots).
  have hassoc : Associated (η - 1) (η ^ i - η ^ j) :=
    BealPrimeDescentFiveFull.zeta_diff_associated_lambda hζ hj hi hne.symm
  -- The λ-non-divisibility transports to A + B·ηⁱ.
  have hlami : ¬ (η - 1) ∣ (A + B * η ^ i) := by
    rw [lambda_dvd_conj_five_iff hζ A B i]; exact hlam
  refine isCoprime_of_prime_dvd ?_ ?_
  · rintro ⟨h1, -⟩
    exact hlami (h1 ▸ dvd_zero _)
  · intro p hp p_dvd_1 p_dvd_2
    have hpδ : p ∣ (η ^ i - η ^ j) := dvd_zeta_pow_sub_of_dvd_conj hζ huv' p_dvd_1 p_dvd_2
    have hp_lam : p ∣ (η - 1) := hpδ.trans hassoc.symm.dvd
    have hlam_p : (η - 1) ∣ p :=
      (hp.associated_of_dvd hlamPrime hp_lam).symm.dvd
    exact hlami (hlam_p.trans p_dvd_1)

/-- **Item 1 (pairwise form, all four factors).** The four cyclotomic factors
`A + ζⁱ·B`, `i = 1, 2, 3, 4`, are pairwise coprime in `𝓞 K = ℤ[ζ₅]`, whenever `A, B`
are coprime and `λ = ζ − 1 ∤ (A + B)`. -/
theorem pairwise_coprime_factors_five {K : Type*} [Field K] [NumberField K]
    [IsCyclotomicExtension {5} ℚ K] {ζ : K} (hζ : IsPrimitiveRoot ζ 5) {A B : 𝓞 K}
    (hAB : IsCoprime A B)
    (hlam : ¬ (hζ.toInteger - 1) ∣ (A + B)) :
    ∀ i ∈ Finset.Ico 1 5, ∀ j ∈ Finset.Ico 1 5, i ≠ j →
      IsCoprime (A + B * hζ.toInteger ^ i) (A + B * hζ.toInteger ^ j) := by
  intro i hi j hj hne
  rw [Finset.mem_Ico] at hi hj
  exact coprime_conj_five_ij hζ hAB hlam (by omega) (by omega) hne

/-- **Item 1 (product form, the MAIN item-1 deliverable).** The cyclotomic factor
`A + ζ·B` is coprime to the **full complementary product**
`γ = ∏_{i ∈ Ico 2 5}(A + ζⁱ·B)` in `𝓞 K = ℤ[ζ₅]`, whenever `A, B` are coprime and
`λ = ζ − 1 ∤ (A + B)`. This is exactly the coprimality hypothesis the
power-extraction engine `associated_pow_cyclotomic_five` consumes. Proof:
`IsCoprime.prod_right` over the uniform pairwise lemma `coprime_conj_five_ij`
(`i = 1` vs each `j ∈ {2,3,4}`). -/
theorem prod_cofactor_coprime_five {K : Type*} [Field K] [NumberField K]
    [IsCyclotomicExtension {5} ℚ K] {ζ : K} (hζ : IsPrimitiveRoot ζ 5) {A B : 𝓞 K}
    (hAB : IsCoprime A B)
    (hlam : ¬ (hζ.toInteger - 1) ∣ (A + B)) :
    IsCoprime (A + B * hζ.toInteger ^ 1)
      (∏ j ∈ Finset.Ico 2 5, (A + B * hζ.toInteger ^ j)) := by
  apply IsCoprime.prod_right
  intro j hj
  rw [Finset.mem_Ico] at hj
  exact coprime_conj_five_ij hζ hAB hlam (by norm_num) (by omega) (by omega)

/-!
## Item 2 — the `(5,5,z)` structure theorem (HEADLINE)

The integer descent gives `A + B = sᶻ` directly. The cyclotomic conjunct needs: the
coprimality of `A, B` lifted to `𝓞 K`; the λ-bridge `5 ∤ (A+B) ⟹ λ ∤ (A+B·ζ)`; and
the perfect-power product `(A + ζ·B)·γ = tᶻ` of the cyclotomic factors. We build the
latter from the cyclotomic factorization `norm_factor_five` and the integer descent's
`A + B = sᶻ`, `A⁵ + B⁵ = Cᶻ`, `C = s·t`: in the domain `𝓞 K`,
`(A+B)·∏_{Ico 1 5} = Cᶻ = sᶻ·tᶻ = (A+B)·tᶻ`, and cancelling `A + B ≠ 0` gives
`∏_{Ico 1 5} = tᶻ`; splitting off `i = 1` gives `(A + ζ·B)·γ = tᶻ`.
-/

/-- **Beal `(5,5,z)` structure theorem (HEADLINE, case `5 ∤ (A + B)`).**
A primitive `(5,5,z)` Beal solution with `5 ∤ (A + B)` makes `A + B` a perfect `z`-th
power *in `ℤ`* and `A + B·ζ` a `z`-th power up to a unit *in `ℤ[ζ₅]`*:

  `(∃ s, A + B = sᶻ) ∧ (∃ d, Associated (dᶻ) ((A : 𝓞 K) + B·ζ))`.

The first conjunct is `BealPrimeDescentFive.prime_sum_descent_five`. The second
composes: the λ-bridge `5 ∤ (A+B) ⟹ λ ∤ (A+B·ζ)` (`lambda_dvd_conj_five_iff` +
`lambda_dvd_intCast_iff_five`), coprimality lifted to `𝓞 K`, the product coprimality
`prod_cofactor_coprime_five` (item 1), and the perfect-power product `(A+ζB)·γ = tᶻ`
built from the cyclotomic factorization, fed into `five_power_extraction`. **No extra
hypothesis:** the λ-bridge is a theorem here. The `p = 5` analogue of
`BealCubeSynthesis.beal_cube_structure_three_ndvd_C`. **NEW.** -/
theorem beal_55z_structure
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {5} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ 5)
    {A B C z : ℕ} (hAB : Nat.Coprime A B) (h5 : ¬ 5 ∣ (A + B)) (hz : z ≠ 0)
    (h : A ^ 5 + B ^ 5 = C ^ z) :
    (∃ s : ℕ, A + B = s ^ z) ∧
    (∃ d : 𝓞 K, Associated (d ^ z) ((A : 𝓞 K) + (B : 𝓞 K) * hζ.toInteger)) := by
  classical
  haveI : IsPrincipalIdealRing (𝓞 K) := IsCyclotomicExtension.Rat.five_pid K
  haveI : IsBezout (𝓞 K) := inferInstance
  set η := hζ.toInteger with hη_def
  have hηprim : IsPrimitiveRoot η 5 := hζ.toInteger_isPrimitiveRoot
  -- Integer descent: A + B = sᶻ, (Φ₅).toNat = tᶻ, C = s·t.
  obtain ⟨s, t, hs, _ht, hC⟩ := BealPrimeDescentFive.prime_sum_descent_five hAB h5 hz h
  refine ⟨⟨s, hs⟩, ?_⟩
  -- Coprimality of A, B lifted to 𝓞 K (via ℤ).
  have hcopZ : IsCoprime (A : ℤ) (B : ℤ) :=
    Int.isCoprime_iff_nat_coprime.mpr (by simpa using hAB)
  have hcopOK : IsCoprime ((A : 𝓞 K)) ((B : 𝓞 K)) := by
    have := hcopZ.map (algebraMap ℤ (𝓞 K))
    simpa using this
  -- λ ∤ (A + B) in 𝓞 K, from 5 ∤ (A + B) in ℕ.
  have hlamAB : ¬ (η - 1) ∣ ((A : 𝓞 K) + (B : 𝓞 K)) := by
    have hcast : ((A : 𝓞 K) + (B : 𝓞 K)) = (((A + B : ℕ) : ℤ) : 𝓞 K) := by push_cast; ring
    rw [hcast, BealPrimeDescentFiveFull.lambda_dvd_intCast_iff_five hζ]
    intro hdvd
    exact h5 (by exact_mod_cast hdvd)
  -- λ ∤ (A + B·η), from λ ∤ (A + B) via the conjugate λ-bridge (i = 1).
  have hlam : ¬ (η - 1) ∣ ((A : 𝓞 K) + (B : 𝓞 K) * η) := by
    have := (lambda_dvd_conj_five_iff hζ (A : 𝓞 K) (B : 𝓞 K) 1)
    rw [pow_one] at this
    rw [this]; exact hlamAB
  -- The cyclotomic factorization over 𝓞 K: (A+B)·∏_{Ico 1 5}(A + ηⁱB) = A⁵ + B⁵.
  have hfact : ((A : 𝓞 K) + (B : 𝓞 K))
      * ∏ i ∈ Finset.Ico 1 5, ((A : 𝓞 K) + η ^ i * (B : 𝓞 K)) = (A : 𝓞 K) ^ 5 + (B : 𝓞 K) ^ 5 :=
    BealPrimeDescentFive.norm_factor_five hηprim (A : 𝓞 K) (B : 𝓞 K)
  -- A⁵ + B⁵ = Cᶻ in 𝓞 K.
  have hCz : (A : 𝓞 K) ^ 5 + (B : 𝓞 K) ^ 5 = (C : 𝓞 K) ^ z := by exact_mod_cast h
  -- A + B = sᶻ and C = s·t in 𝓞 K.
  have hsOK : (A : 𝓞 K) + (B : 𝓞 K) = (s : 𝓞 K) ^ z := by exact_mod_cast hs
  have hCOK : (C : 𝓞 K) = (s : 𝓞 K) * (t : 𝓞 K) := by exact_mod_cast hC
  -- A + B ≠ 0 (5 ∤ (A + B) forces A + B ≥ 1).
  have hABpos : (A : 𝓞 K) + (B : 𝓞 K) ≠ 0 := by
    have hnat : A + B ≠ 0 := by
      intro h0; exact h5 (h0 ▸ dvd_zero 5)
    have hcast : ((A + B : ℕ) : 𝓞 K) ≠ 0 := by
      rw [Nat.cast_ne_zero]; exact hnat
    have hpc : ((A + B : ℕ) : 𝓞 K) = (A : 𝓞 K) + (B : 𝓞 K) := by push_cast; ring
    rwa [hpc] at hcast
  -- Cancel A + B from (A+B)·∏ = Cᶻ = sᶻ·tᶻ = (A+B)·tᶻ to get ∏ = tᶻ.
  have hprodEq : (∏ i ∈ Finset.Ico 1 5, ((A : 𝓞 K) + η ^ i * (B : 𝓞 K))) = (t : 𝓞 K) ^ z := by
    apply mul_left_cancel₀ hABpos
    rw [hfact, hCz, hCOK, mul_pow, ← hsOK]
  -- Split off i = 1 from the product: ∏_{Ico 1 5} = (A + η·B) · ∏_{Ico 2 5}.
  have h1mem : (1 : ℕ) ∈ Finset.Ico 1 5 := by decide
  have hsplit := Finset.prod_eq_prod_diff_singleton_mul h1mem
    (fun i => (A : 𝓞 K) + η ^ i * (B : 𝓞 K))
  have hset : Finset.Ico 1 5 \ {1} = Finset.Ico 2 5 := by decide
  rw [hset, pow_one] at hsplit
  -- hsplit : ∏_{Ico 1 5} = (∏_{Ico 2 5}) * (A + η·B)
  -- Rewrite ∏_{Ico 1 5} = tᶻ as (A + η·B)·γ = tᶻ.
  set γ : 𝓞 K := ∏ i ∈ Finset.Ico 2 5, ((A : 𝓞 K) + η ^ i * (B : 𝓞 K)) with hγ_def
  have hprodFactor : ((A : 𝓞 K) + η * (B : 𝓞 K)) * γ = (t : 𝓞 K) ^ z := by
    rw [← hprodEq, hsplit]; ring
  -- Commute B·η = η·B and η^i·B = B·η^i to align with the product-coprimality lemma.
  have hcommBη : (A : 𝓞 K) + η * (B : 𝓞 K) = (A : 𝓞 K) + (B : 𝓞 K) * η := by ring
  -- Product coprimality (item 1): A + η·B coprime to γ.
  have hγcomm : γ = ∏ j ∈ Finset.Ico 2 5, ((A : 𝓞 K) + (B : 𝓞 K) * η ^ j) := by
    rw [hγ_def]; apply Finset.prod_congr rfl; intro i _; ring
  have hcopγ : IsCoprime ((A : 𝓞 K) + η * (B : 𝓞 K)) γ := by
    rw [hcommBη, hγcomm]
    have := prod_cofactor_coprime_five hζ hcopOK hlamAB
    rwa [pow_one] at this
  -- Power extraction (PID/Bézout engine, coprimality discharged).
  have hres : ∃ d : 𝓞 K, Associated (d ^ z) ((A : 𝓞 K) + η * (B : 𝓞 K)) :=
    BealPrimeDescentFive.five_power_extraction hcopγ hprodFactor
  rwa [hcommBη] at hres

/-!
## Item 3 (STRETCH) — the integral-basis coordinate engine for `𝓞 K = ℤ[ζ₅]`

`𝓞 K = ℤ[ζ₅]` is free of rank `φ(5) = 4` over `ℤ` on `{1, ζ, ζ², ζ³}`. The
coordinate-uniqueness lemma — the `p = 5` analogue of
`BealCubeDescentStep.eta_coords_unique` — is the `ℤ`-linear independence of
`{1, ζ}` (the first two basis elements suffice for the `z = 1` relation; the full
`{1, ζ, ζ², ζ³}` independence is the engine for general `z`). We prove the
`{1, ζ}`-coordinate uniqueness via the degree-`4` minimal polynomial of `ζ`
(`finrank ℚ K = φ(5) = 4`), exactly as for `p = 3`, then read off the `z = 1`
coordinate relation `A + ζ·B = e + f·ζ ⟹ A = e ∧ B = f`.
-/

/-- **Item 3 — `{1, ζ}` coordinate uniqueness over `ℤ` in `𝓞 K = ℤ[ζ₅]`.**
If `e₁ + f₁·ζ = e₂ + f₂·ζ` with `eᵢ, fᵢ : ℤ`, then `e₁ = e₂` and `f₁ = f₂`. This is
the `ℤ`-linear independence of `{1, ζ}` in `ℤ[ζ₅]`, the `p = 5` analogue of
`BealCubeDescentStep.eta_coords_unique`. Proof: reduce to `a + b·ζ = 0`; if `b ≠ 0`
then `ζ ∈ range(algebraMap ℚ K)`, forcing `(minpoly ℚ ζ).degree = 1`; but the power
basis of `K = ℚ(ζ₅)` has `degree (minpoly ℚ ζ) = dim = finrank ℚ K = φ(5) = 4` —
contradiction. (Linear independence of the *full* basis `{1, ζ, ζ², ζ³}` is the
power-basis statement `hζ.powerBasis ℚ`; the `{1, ζ}` slice proved here is what the
`z = 1` coordinate relation needs.) -/
theorem five_coords_unique {K : Type*} [Field K] [NumberField K]
    [IsCyclotomicExtension {5} ℚ K] {ζ : K} (hζ : IsPrimitiveRoot ζ 5)
    {e₁ f₁ e₂ f₂ : ℤ}
    (h : (e₁ : 𝓞 K) + (f₁ : 𝓞 K) * hζ.toInteger
       = (e₂ : 𝓞 K) + (f₂ : 𝓞 K) * hζ.toInteger) :
    e₁ = e₂ ∧ f₁ = f₂ := by
  have hsub : ((e₁ - e₂ : ℤ) : 𝓞 K) + ((f₁ - f₂ : ℤ) : 𝓞 K) * hζ.toInteger = 0 := by
    push_cast; linear_combination h
  set a : ℤ := e₁ - e₂ with ha
  set b : ℤ := f₁ - f₂ with hb0
  suffices hab : a = 0 ∧ b = 0 by
    obtain ⟨ha0, hb0'⟩ := hab
    exact ⟨by omega, by omega⟩
  have hKeq : (a : K) + (b : K) * ζ = 0 := by
    have := congrArg (fun y : 𝓞 K => (y : K)) hsub
    simpa [IsPrimitiveRoot.coe_toInteger] using this
  set pb := hζ.powerBasis ℚ with hpb
  have hgen : pb.gen = ζ := hζ.powerBasis_gen ℚ
  have hdim : pb.dim = 4 := by
    have h1 : Module.finrank ℚ K = pb.dim := pb.finrank
    have h2 : Module.finrank ℚ K = (5 : ℕ).totient :=
      IsCyclotomicExtension.finrank (n := 5) K (Polynomial.cyclotomic.irreducible_rat (by norm_num))
    have h3 : (5 : ℕ).totient = 4 := by decide
    rw [h2, h3] at h1; omega
  have hbzero : b = 0 := by
    by_contra hb
    have hbK : (b : K) ≠ 0 := by exact_mod_cast hb
    have hζrange : ζ ∈ (algebraMap ℚ K).range := by
      refine ⟨(-(a : ℚ)) / (b : ℚ), ?_⟩
      have hbQ : ((b : ℚ) : K) = (b : K) := by push_cast; ring
      rw [map_div₀, map_neg, map_intCast, map_intCast]
      field_simp
      linear_combination -hKeq
    have hdeg1 : (minpoly ℚ ζ).degree = 1 :=
      (minpoly.degree_eq_one_iff).2 hζrange
    have hdeg2 : (minpoly ℚ pb.gen).degree = (pb.dim : WithBot ℕ) := pb.degree_minpoly
    rw [hgen, hdeg1, hdim] at hdeg2
    norm_num at hdeg2
  refine ⟨?_, hbzero⟩
  rw [hbzero] at hKeq
  simp only [Int.cast_zero, zero_mul, add_zero] at hKeq
  exact_mod_cast hKeq

/-- **Item 3 — `z = 1` integral-basis coordinate relation.** If
`(A : 𝓞 K) + B·ζ = (e : 𝓞 K) + f·ζ` with `A, B, e, f : ℤ`, then `A = e` and `B = f`
in `ℤ`. The `p = 5` `z = 1` analogue of `BealCubeDescentStep.descent_relations_two`:
the displayed cyclotomic factor's `{1, ζ}`-coordinates are pinned by
`five_coords_unique`. (For general `z` the right side is the binomial expansion of
`(e + f·ζ)ᶻ` reduced via `1 + ζ + ζ² + ζ³ + ζ⁴ = 0` into `{1, ζ, ζ², ζ³}`-form,
whose four coordinates are pinned by the full basis independence; the coupling is
recorded as future work in `## REMAINING PLAN`.) -/
theorem descent_relations_one_five {K : Type*} [Field K] [NumberField K]
    [IsCyclotomicExtension {5} ℚ K] {ζ : K} (hζ : IsPrimitiveRoot ζ 5)
    {A B e f : ℤ}
    (h : (A : 𝓞 K) + (B : 𝓞 K) * hζ.toInteger
       = (e : 𝓞 K) + (f : 𝓞 K) * hζ.toInteger) :
    A = e ∧ B = f :=
  five_coords_unique hζ h

end BealFiveStructure

/-!
## REMAINING PLAN

This file assembles the `(5, 5, z)` descent into one **structure theorem**, the
`p = 5` analogue of `BealCubeSynthesis`, and supplies the integral-basis coordinate
engine. All declarations are axiom-clean (`[propext, Classical.choice, Quot.sound]`).

**Proved here:**

* **Item 1 (product coprimality).** `lambda_dvd_conj_five_iff`
  (`λ ∣ (A+B·ζⁱ) ↔ λ ∣ (A+B)`), the uniform pairwise lemma `coprime_conj_five_ij`
  (any distinct `i, j ∈ {1,2,3,4}`), the four-factor pairwise form
  `pairwise_coprime_factors_five`, and the **product form**
  `prod_cofactor_coprime_five` (`A + ζ·B` coprime to `∏_{Ico 2 5}(A + ζⁱ·B)`), via
  `IsCoprime.prod_right`. The general `i, j` divisibility skeleton
  `dvd_zeta_pow_sub_of_dvd_conj` generalizes the displayed-pair version of
  `BealPrimeDescentFiveFull`.

* **Item 2 (HEADLINE) `beal_55z_structure`.** A primitive `(5,5,z)` solution with
  `5 ∤ (A + B)` gives `A + B = sᶻ` in `ℤ` **and** `Associated (dᶻ) (A + B·ζ)` in
  `ℤ[ζ₅]`, **with no λ-hypothesis assumed**. The cyclotomic conjunct routes the
  cyclotomic factorization `norm_factor_five` (cancelling `A + B ≠ 0`) into the
  perfect-power product `(A + ζ·B)·γ = tᶻ`, discharges coprimality with item 1, and
  applies `five_power_extraction`. The λ-bridge `5 ∤ (A+B) ⟹ λ ∤ (A+B·ζ)` is a
  theorem (`lambda_dvd_conj_five_iff` + `lambda_dvd_intCast_iff_five`).

* **Item 3 (STRETCH).** `five_coords_unique` — `{1, ζ}` coordinate uniqueness over
  `ℤ` in `ℤ[ζ₅]` (the `ℤ`-linear-independence engine, via the degree-`4` minimal
  polynomial `finrank ℚ K = φ(5) = 4`) — and `descent_relations_one_five` (the
  `z = 1` relation `A + B·ζ = e + f·ζ ⟹ A = e ∧ B = f`). The `p = 5` analogue of
  `BealCubeDescentStep.eta_coords_unique`/`descent_relations_two`.

### The remaining gap to Beal-`(5,5,z)` non-existence (the unit/Kummer step)

The honest endpoint of the `p = 5` rung, *substantively harder* than `p = 3`:

1. **The unit group of `ℤ[ζ₅]` is infinite.** Unlike `ℤ[ζ₃]` (units `{±1, ±η, ±η²}`,
   finite), `ℤ[ζ₅]` has unit rank `1` (a real fundamental unit of Pell type), so
   absorbing the residual unit `u` in `A + ζ·B = u·dᶻ` (the output of
   `beal_55z_structure`) into a `z`-th power is **not** a finite case-check. mathlib
   has **no `Five` Kummer lemma** (no `Five` analogue of
   `IsCyclotomicExtension.Rat.Three.eq_one_or_neg_one_of_unit_of_congruent`). This is
   the genuine number-theoretic content the PID (class number `1`) does **not**
   resolve, and the precise frontier left open.

2. **General-`z` coordinate coupling.** `descent_relations_one_five` is the `z = 1`
   slice. For general `z`, the right side `(e + f·ζ)ᶻ` reduces, via the cyclotomic
   relation `1 + ζ + ζ² + ζ³ + ζ⁴ = 0` (`IsPrimitiveRoot.geom_sum_eq_zero`), into
   `{1, ζ, ζ², ζ³}`-coordinate form; the four coordinates are then pinned by the full
   basis independence (`hζ.powerBasis ℚ`), coupling `(A, B)` to the base coordinates
   `(e, f)` and the integer root `s` (`A + B = sᶻ`). Computing the explicit degree-`z`
   coordinate polynomials and assembling the strict minimal descent (à la
   `Mathlib/NumberTheory/FLT/Three.lean`) is the remaining work — gated, as above, on
   the missing `p = 5` unit theory.

### Mathlib declarations used

* `BealPrimeDescentFive.norm_factor_five`, `prime_sum_descent_five`,
  `five_power_extraction`, `lambda_five_prime`,
  `IsCyclotomicExtension.Rat.five_pid` — the `(5,5,z)` descent engine.
* `BealPrimeDescentFiveFull.zeta_diff_associated_lambda`,
  `lambda_dvd_intCast_iff_five`, `dvd_zeta_sub_of_dvd_conj`,
  `coprime_conj_five_of_lambda_not_dvd` — the factor-coprimality skeleton.
* `IsCoprime.prod_right`, `isCoprime_of_prime_dvd`, `sub_dvd_pow_sub_pow` — item 1.
* `minpoly.degree_eq_one_iff`, `PowerBasis.degree_minpoly`,
  `IsCyclotomicExtension.finrank` — the coordinate-uniqueness engine (item 3).
-/
