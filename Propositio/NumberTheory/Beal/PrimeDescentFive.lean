import Mathlib.RingTheory.Coprime.Basic
import Mathlib.RingTheory.Int.Basic
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.NumberTheory.NumberField.Cyclotomic.PID
import Mathlib.Tactic
import Propositio.NumberTheory.Beal.PrimeDescent
import Propositio.NumberTheory.Beal.CyclotomicFactor

/-!
# The `(5, 5, z)` cyclotomic descent for the Beal prime-sum equation (Lean 4 / mathlib)

**NEW mathematics — no LaTTe sibling.** This file extends the `(p, p, z)`
cyclotomic descent to the next unconditional rung beyond `p = 3`: the prime
`p = 5`. It builds on the elementary prime-sum reduction `BealPrimeDescent`
(`prime_sum_descent`, valid for all odd primes) and the cyclotomic factorization
`BealCyclotomicFactor`, and uses mathlib's `IsCyclotomicExtension.Rat.five_pid`
(ℤ[ζ₅] is a principal ideal domain — class number `1`) for the power-extraction
crux, exactly as `BealEisensteinDescent` used `three_pid` for `p = 3`.

## Where this sits in the development

For the odd prime `5`, the prime-power sum factors (over any commutative ring) as

  `A⁵ + B⁵ = (A + B) · Φ₅`,   `Φ₅ = A⁴ − A³B + A²B² − AB³ + B⁴`,

the degree-`4` cyclotomic cofactor (`BealPrimeDescent.Phi 5`, here made explicit).
Cyclotomically, with `ζ` a primitive `5`-th root of unity,

  `A⁵ + B⁵ = ∏_{i=0}^{4} (A + ζⁱ·B) = (A + B) · ∏_{i=1}^{4} (A + ζⁱ·B)`,

and the residual product `∏_{i=1}^{4}(A + ζⁱ·B)` equals `Φ₅`
(`BealCyclotomicFactor.cyclotomic_cofactor_eq_Phi`).

## What this file proves

* **Unconditional, elementary (items 1–3).** The `p = 5` specialization of the
  whole `BealPrimeDescent` reduction:
  - `norm_factor_five` — the cyclotomic factorization `(A + B)·∏ = A⁵ + B⁵` and
    `Phi_five_eq` — the explicit degree-`4` cofactor.
  - `prime_sum_descent_five` — for coprime `A, B` with `5 ∤ (A + B)` and `z ≠ 0`,
    `A⁵ + B⁵ = Cᶻ` forces `A + B = sᶻ`, `(Φ₅).toNat = tᶻ`, `C = s·t`.

* **Cyclotomic power-extraction (item 4), unconditional in the PID input.** Using
  `five_pid` (so `𝓞 K = ℤ[ζ₅]` is a Bézout domain), a coprime cyclotomic
  factorization of a perfect `z`-th power splits into perfect `z`-th powers up to a
  unit. The generic engine (`five_power_extraction`) and the `𝓞 K`-specialization
  (`associated_pow_cyclotomic_five`) are fully proved; the PID hypothesis is
  *discharged* by `five_pid`, not assumed.

  The one input the `𝓞 K`-specialization takes is the **coprimality of the
  cyclotomic factor `A + ζ·B` against the complementary cofactor** — see the
  `## REMAINING PLAN` for why this is exactly the missing ingredient for `p = 5`
  (mathlib has no `Five` analogue of the explicit `Three` discriminant skeleton
  `eta_sq_add_eta_add_one` / Kummer's lemma).

## INVESTIGATION finding (mathlib ring-theory for ℤ[ζ₅])

`IsCyclotomicExtension.Rat.five_pid` **exists** in this mathlib
(`Mathlib/NumberTheory/NumberField/Cyclotomic/PID.lean`):

  `theorem five_pid [IsCyclotomicExtension {5} ℚ K] : IsPrincipalIdealRing (𝓞 K)`

so ℤ[ζ₅] is a PID (class number `1`), hence a Bézout domain, hence the
power-extraction engine `exists_associated_pow_of_mul_eq_pow'` applies verbatim —
the descent's power-extraction works for `p = 5` exactly as for `p = 3`. mathlib
also has `IsPrimitiveRoot.zeta_sub_one_prime'` for general prime `p` (the prime
`λ = ζ − 1`), and `NumberField.classNumber_eq_one_iff`. What mathlib does **not**
provide for `p = 5` is the explicit cyclotomic-relation / discriminant skeleton and
Kummer's-lemma file that `Mathlib/NumberTheory/NumberField/Cyclotomic/Three.lean`
supplies for `p = 3` (no `Five` namespace with `eta_sq_add_eta_add_one`-analogues).

Dependency policy: mathlib4 permitted (user authorization 2026-05-17). Use
`lake env lean BealPrimeDescentFive.lean` to typecheck (cyclotomic imports ⟹ slow).
-/

namespace BealPrimeDescentFive

open scoped NumberField
open Finset

/-!
## 1. The `p = 5` cyclotomic factorization and explicit cofactor

`norm_factor_five` specializes `BealCyclotomicFactor.prod_add_eq_pow_add` (or
`pow_add_eq_sum_mul_cofactor`) to `p = 5`; `Phi_five_eq` expands
`BealPrimeDescent.Phi 5` into the explicit degree-`4` polynomial.
-/

/-- **The `p = 5` cyclotomic factorization.** For a primitive `5`-th root of unity
`ζ` over a commutative integral domain `R`,

  `(A + B) · ∏_{i ∈ Ico 1 5} (A + ζⁱ·B) = A⁵ + B⁵`.

The full product `∏_{i=0}^{4}(A + ζⁱ·B)` is `A⁵ + B⁵`
(`BealCyclotomicFactor.prod_add_eq_pow_add`); splitting off the `i = 0` factor
`A + ζ⁰·B = A + B` leaves the residual cyclotomic cofactor over `Ico 1 5`. -/
theorem norm_factor_five {R : Type*} [CommRing R] [IsDomain R] {ζ : R}
    (hζ : IsPrimitiveRoot ζ 5) (A B : R) :
    (A + B) * ∏ i ∈ Finset.Ico 1 5, (A + ζ ^ i * B) = A ^ 5 + B ^ 5 := by
  -- The full product over range 5 is A⁵ + B⁵.
  have hfull := BealCyclotomicFactor.prod_add_eq_pow_add (p := 5) (by decide) hζ A B
  -- Split the i = 0 factor (= A + B) out of the range-5 product.
  have h0 : (0 : ℕ) ∈ Finset.range 5 := by decide
  have hsplit := Finset.prod_eq_prod_diff_singleton_mul h0 (fun i => A + ζ ^ i * B)
  rw [pow_zero, one_mul] at hsplit
  -- range 5 \ {0} = Ico 1 5.
  have hset : Finset.range 5 \ {0} = Finset.Ico 1 5 := by decide
  rw [hset] at hsplit
  rw [mul_comm, ← hsplit, hfull]

/-- **The explicit `p = 5` cofactor.**
`BealPrimeDescent.Phi 5 A B = A⁴ − A³B + A²B² − AB³ + B⁴` over `ℤ`. -/
theorem Phi_five_eq (A B : ℤ) :
    BealPrimeDescent.Phi 5 A B = A ^ 4 - A ^ 3 * B + A ^ 2 * B ^ 2 - A * B ^ 3 + B ^ 4 := by
  simp [BealPrimeDescent.Phi, Finset.sum_range_succ]; ring

/-!
## 2. The elementary `(5, 5, z)` descent reduction (case `5 ∤ (A + B)`)

A direct specialization of `BealPrimeDescent.prime_sum_descent` at `p = 5`, with
`Nat.Prime 5` by `norm_num` and `Odd 5` by `decide`.
-/

/-- **`(5, 5, z)` prime-sum descent (HEADLINE elementary reduction, case
`5 ∤ (A + B)`).** For coprime naturals `A, B` with `5 ∤ (A + B)` and `z ≠ 0`, a
solution `A⁵ + B⁵ = Cᶻ` forces both factors of `(A + B)·Φ₅ = A⁵ + B⁵` to be
perfect `z`-th powers, with `C` their product:

  `∃ s t, A + B = sᶻ ∧ (Φ₅ A B).toNat = tᶻ ∧ C = s·t`.

This is `BealPrimeDescent.prime_sum_descent` at `p = 5`. Unconditional and
elementary. -/
theorem prime_sum_descent_five {A B C z : ℕ}
    (hAB : Nat.Coprime A B) (h5 : ¬ (5 ∣ (A + B))) (hz : z ≠ 0)
    (h : A ^ 5 + B ^ 5 = C ^ z) :
    ∃ s t, A + B = s ^ z ∧ (BealPrimeDescent.Phi 5 (A : ℤ) (B : ℤ)).toNat = t ^ z
      ∧ C = s * t :=
  BealPrimeDescent.prime_sum_descent (by norm_num) (by decide) hAB h5 hz h

/-!
## 3. Cyclotomic power-extraction in the PID `𝓞 K = ℤ[ζ₅]`

`five_pid` makes `𝓞 K` a Bézout domain, so the generic power-extraction lemma
(`exists_associated_pow_of_mul_eq_pow'`, reused as in `BealEisensteinDescent`'s M3)
applies: a coprime factorization of a perfect `z`-th power splits into perfect
`z`-th powers up to a unit. We record the generic Bézout-domain engine and then
the `𝓞 K = ℤ[ζ₅]` specialization with the cyclotomic factor `A + ζ·B` substituted.

Unlike the `p = 3` file, the PID input here is **not** a hypothesis — it is
discharged inside `associated_pow_cyclotomic_five` by `five_pid`.
-/

/-- **Power extraction (generic Bézout domain).** In any commutative Bézout domain
`R`, if `α, β` are coprime and `α · β = c ^ z`, then `α` is a `z`-th power up to a
unit: `∃ d, Associated (dᶻ) α`. The engine is `exists_associated_pow_of_mul_eq_pow'`
(identical to `BealEisensteinDescent.associated_pow_of_coprime_mul`, repeated here
so this file is self-contained for `p = 5`). -/
theorem five_power_extraction {R : Type*} [CommRing R] [IsDomain R] [IsBezout R]
    {α β c : R} {z : ℕ} (hcop : IsCoprime α β) (h : α * β = c ^ z) :
    ∃ d : R, Associated (d ^ z) α :=
  exists_associated_pow_of_mul_eq_pow' hcop h

/-- **Power extraction (`𝓞 K = ℤ[ζ₅]` specialization), PID input discharged.**
In the ring of integers `𝓞 K` of the cyclotomic field `K = ℚ(ζ₅)`, given the
`𝓞 K`-coprimality of the cyclotomic factor `A + ζ·B` and its complementary cofactor
`γ`, and the factorization `(A + ζ·B) · γ = tᶻ`, the factor `A + ζ·B` is a `z`-th
power up to a unit of `ℤ[ζ₅]`:

  `∃ d, Associated (dᶻ) (A + ζ·B)`.

The PID structure `IsPrincipalIdealRing (𝓞 K)` is supplied internally by
`IsCyclotomicExtension.Rat.five_pid` (class number `1`), so — exactly as for `p = 3`
via `three_pid` — the extraction is *unconditional in the PID*. The only remaining
input is the coprimality of `A + ζ·B` against `γ`; see `## REMAINING PLAN`. -/
theorem associated_pow_cyclotomic_five {K : Type*} [Field K] [NumberField K]
    [IsCyclotomicExtension {5} ℚ K] {ζ : 𝓞 K} (_hζ : IsPrimitiveRoot ζ 5)
    {A B γ t : 𝓞 K} {z : ℕ}
    (hcop : IsCoprime (A + ζ * B) γ)
    (h : (A + ζ * B) * γ = t ^ z) :
    ∃ d : 𝓞 K, Associated (d ^ z) (A + ζ * B) := by
  haveI : IsPrincipalIdealRing (𝓞 K) := IsCyclotomicExtension.Rat.five_pid K
  haveI : IsBezout (𝓞 K) := inferInstance
  exact five_power_extraction hcop h

/-- **`λ = ζ − 1` is prime in `ℤ[ζ₅]`.** The general-prime mathlib input
`IsPrimitiveRoot.zeta_sub_one_prime'` (`[Fact (Nat.Prime 5)]` supplied by
`Nat.prime_five`), the `p = 5` analogue of the `λ`-primality that drives the
coprimality step in the `p = 3` descent (`BealEisensteinDescent.coprime_conj_*`). It
is the prime over `5` that any common factor of the cyclotomic factors must lie
over. Recorded here as the available hook for the remaining coprimality work. -/
theorem lambda_five_prime {K : Type*} [Field K] [NumberField K]
    [IsCyclotomicExtension {5} ℚ K] {ζ : K} (hζ : IsPrimitiveRoot ζ 5) :
    Prime (hζ.toInteger - 1) := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  exact hζ.zeta_sub_one_prime'

end BealPrimeDescentFive

/-!
## REMAINING PLAN

This file closes, with no `sorry`:

* **Items 1–3 (unconditional, elementary).** `norm_factor_five` (the `p = 5`
  cyclotomic factorization), `Phi_five_eq` (the explicit cofactor
  `A⁴ − A³B + A²B² − AB³ + B⁴`), and `prime_sum_descent_five` (the full
  `(5, 5, z)` reduction `A⁵ + B⁵ = Cᶻ ⟹ A + B = sᶻ ∧ (Φ₅).toNat = tᶻ ∧ C = s·t`,
  case `5 ∤ (A + B)`). These specialize `BealPrimeDescent` / `BealCyclotomicFactor`
  at `p = 5` and depend on nothing beyond them.

* **Item 4 (cyclotomic power-extraction), PID input discharged.**
  `five_power_extraction` (generic Bézout-domain engine) and
  `associated_pow_cyclotomic_five` (`ℤ[ζ₅]` specialization). The PID/UFD obstacle
  that blocks the descent for irregular primes is **NOT** a gap here: mathlib's
  `IsCyclotomicExtension.Rat.five_pid` discharges it, exactly as `three_pid` does
  for `p = 3`. `lambda_five_prime` records the prime `λ = ζ − 1` over `5`.

### The one remaining input for `p = 5` (and why it is not `five_pid`)

`associated_pow_cyclotomic_five` takes as a hypothesis the **coprimality of the
cyclotomic factor `A + ζ·B` against its complementary cofactor `γ`** in `ℤ[ζ₅]`.
For `p = 3` this exact coprimality was discharged unconditionally
(`BealEisensteinDescent.coprime_conj_of_lambda_not_dvd`) using two ingredients:

  1. `IsCyclotomicExtension.Rat.Three.eta_sq_add_eta_add_one` — the *explicit*
     cyclotomic relation `η² + η + 1 = 0` in `𝓞 K`, giving the closed-form
     discriminant identity `(ω − ω²)² = −3` / `λ² = −3·η`; and
  2. `λ`-primality (`zeta_sub_one_prime'`, available for `p = 5` as
     `lambda_five_prime`) + `isCoprime_of_prime_dvd`.

Ingredient (2) is in mathlib for `p = 5`. Ingredient (1) is **NOT**: mathlib's
`Mathlib/NumberTheory/NumberField/Cyclotomic/Three.lean` provides the explicit
`Three`-relation skeleton (and Kummer's lemma
`eq_one_or_neg_one_of_unit_of_congruent`), but there is **no `Five` namespace**
with the analogous `eta⁴ + η³ + η² + η + 1 = 0`-driven discriminant computation and
unit theory. So the `p = 5` coprimality of the cyclotomic factors — which for `p = 3`
reduced to the closed-form `λ² ~ −3` confinement — is the precise missing input.

What mathlib *does* give for `p = 5` to close this in a future session:

  * `lambda_five_prime` (proved above) — `Prime (ζ − 1)`.
  * `IsPrimitiveRoot.geom_sum_eq_zero` — the cyclotomic relation
    `1 + ζ + ζ² + ζ³ + ζ⁴ = 0` in `𝓞 K`, the `p = 5` analogue of
    `eta_sq_add_eta_add_one`, from which the degree-`4` discriminant element and the
    confinement `d ∣ (ζ − 1)` (the multi-factor analogue of
    `BealEisensteinDescent.dvd_omega_sub_of_dvd_conj`) can be re-derived elementarily.
  * `IsCyclotomicExtension.Rat.five_pid` (used) — PID ⇒ UFD ⇒ the `isCoprime_of_prime_dvd`
    argument and `exists_associated_pow_of_mul_eq_pow'` both apply.

### Continuation (lemma-by-lemma, the `p = 5` analogue of `BealEisensteinDescent`)

1. `geom_sum_five` — `1 + ζ + ζ² + ζ³ + ζ⁴ = 0` in `𝓞 K` (from `geom_sum_eq_zero`).
2. `coprime_cyc_factors_five` — for coprime `A, B` with `λ ∤ (A + ζ·B)`, the
   cyclotomic factor `A + ζ·B` is coprime to the complementary cofactor `γ`
   (the multi-factor generalization of `coprime_conj_of_lambda_not_dvd`; needs the
   degree-`4` discriminant confinement, re-derived from `geom_sum_five` and the
   resultant/different of `ζ⁵ = 1`, plus `lambda_five_prime`).
3. `five_power_extraction_unconditional` — `coprime_cyc_factors_five` composed with
   `associated_pow_cyclotomic_five`: the analogue of
   `BealEisensteinDescent.eisenstein_power_extraction`, with the coprimality
   hypothesis discharged.
4. `kummer_reduction_five` / unit constraint — the `p = 5` unit group of `ℤ[ζ₅]` is
   infinite (rank `1` real, Pell-type fundamental unit), so this is genuinely harder
   than `p = 3`; mathlib has no `Five` Kummer lemma. This is the substantive
   number-theoretic obstruction *beyond* the PID, and the honest endpoint of the
   `p = 5` rung: the PID (and hence the up-to-a-unit power extraction) is
   unconditional, but pinning the residual unit needs unit-group theory mathlib does
   not yet carry for `p = 5`.

In short: the **PID is available** (so item 4's power-extraction is unconditional in
that input), and the elementary reduction (items 1–3) is fully unconditional; the
two remaining mechanizable inputs are the explicit degree-`4` discriminant
coprimality (re-derivable from `geom_sum_eq_zero`) and the `p = 5` unit/Kummer
theory (a real gap in this mathlib).
-/
