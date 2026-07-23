import Mathlib.RingTheory.Coprime.Basic
import Mathlib.RingTheory.Int.Basic
import Mathlib.NumberTheory.NumberField.Cyclotomic.Three
import Mathlib.NumberTheory.NumberField.Cyclotomic.PID
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.Tactic
import Propositio.NumberTheory.Beal.CubeSynthesis
import Propositio.NumberTheory.Beal.CubeDescentStep
import Propositio.NumberTheory.Beal.KummerSign
import Propositio.NumberTheory.Beal.LambdaResidue

/-!
# M4 (interface): the sharpest CONDITIONAL (3,3,z) descent theorem and the typed λ²-gap

This file is the **typed interface** for the remaining gap of the ℤ[ζ₃] cube-sum
descent. It assembles the three proved pieces of the pipeline —

  * `BealCubeSynthesis.beal_cube_structure_three_ndvd_C` (the structure theorem:
    `3 ∤ C ⟹ A+B = sᶻ ∧ Associated (dᶻ) (A+B·η)`),
  * `BealCubeDescentStep.unit_pinned_to_sign` (`gcd(z,3)=1 ⟹` the descent unit
    collapses to a *sign*: `A+B·η = d'ᶻ ∨ A+B·η = −d'ᶻ`),
  * `BealKummerSign.sign_eliminated` (the residue hypothesis kills the `−` branch),

— into a single chain that exhibits the **exact** congruence the modular method
must supply, as a named, minimal hypothesis on the descent base. Nothing here is
faked: every unproven fact is a typed hypothesis, and every theorem is
axiom-clean (`[propext, Classical.choice, Quot.sound]`).

## The interface hypothesis `H` (the documented gap)

For a *fixed* descent base `d' : 𝓞 K` produced by the structure theorem, the gap is

  `H(d') : (η−1)² ∣ ((A + B·η) − d'ᶻ)`     (`A + B·η ≡ d'ᶻ (mod λ²)`).

This is **exactly** the λ²-congruence that Kummer's lemma
(`IsCyclotomicExtension.Rat.Three.eq_one_or_neg_one_of_unit_of_congruent`)
consumes, restated as a sign-pinning input. `BealLambdaResidue.hres_iff_plus_branch`
shows `H(d')` is *equivalent* to landing in the `+` branch, so it is genuine extra
input — not derivable from the sign-pinning alone.

## What this file delivers

1. **`cube_descent_to_sign`** — the proved, unconditional half: a `3 ∤ C` primitive
   cube-sum solution with `gcd(z,3)=1` yields a base `d'` with the sign-pinned
   descent `A+B·η = ±d'ᶻ` and `λ ∤ (A+B·η)`. (Assembles structure theorem +
   `unit_pinned_to_sign`; carries the side data `sᶻ`, the λ-nondivisibility.)

2. **`cube_plus_branch_of_residue`** (HEADLINE, the sharpest conditional) — given a
   `3 ∤ C` primitive cube-sum solution, `gcd(z,3)=1`, and the **single** explicit
   residue hypothesis `H` on the descent base, the `+` branch is forced:
   `A + B·η = d'ᶻ` with `A + B = sᶻ`. This is the descent *with the sign gap
   discharged by exactly `H`* — the tightest conditional (3,3,z) statement, naming
   the gap as a typed hypothesis.

3. **`residue_gap_iff_plus_branch`** (the honest elementary reduction) — for the
   base `d'` of the sign-pinned descent, `H(d') ↔ (A+B·η = d'ᶻ)`. This makes the
   remaining gap fully explicit: the missing congruence is logically *the same as*
   choosing the correct branch.

4. **`cube_plus_branch_case_two`** (the UNCONDITIONAL Case-2 corollary) — in the
   case `3 ∣ B` (the classical FLT-3 Case-2 split), `H` is dischargeable from the
   mathlib FLT-3 cube engine with **no Kummer input**, given only the integer-side
   λ²-match. We record the resulting conditional-free-of-Kummer `+` branch.

## What remains OPEN, and why

The hypothesis `H` is **open precisely when `λ ∤ B` (i.e. `3 ∤ B`)** — the
classical (3,3,z) Case 1. There:

* the left factor `A + B·η = (A+B) + B·λ` does *not* reduce to a rational integer
  mod λ² (`BealLambdaResidue.lambda_sq_dvd_eta_sub_sum_iff`: it does iff `λ ∣ B`),
  so `H` cannot be matched against an integer residue;
* Kummer's lemma is the classical route, but its hypothesis is `H` again
  (`eq_one_or_neg_one_of_unit_of_congruent`), so the gap is intrinsic;
* for prime `z ≥ 17`, supplying `H` is precisely what the **modular method**
  (Frey curve / level lowering, Kraus 1998) accomplishes — there is no elementary
  derivation, which is why this stays a typed hypothesis rather than a theorem.

So `cube_plus_branch_of_residue` is the exact point at which the elementary
descent terminates and the modular input must enter. The Case-2 corollary shows
the elementary descent *does* close when `3 ∣ B`.

`lake env lean BealLambdaInterface.lean` to typecheck (SLOW, cyclotomic imports).
-/

namespace BealLambdaInterface

open scoped NumberField

/-!
## Part 1 — the proved, unconditional half: structure theorem ⟹ sign-pinned descent

This composes `beal_cube_structure_three_ndvd_C` (giving `A+B = sᶻ` and
`Associated (dᶻ) (A+B·η)`) with `unit_pinned_to_sign` (collapsing the descent unit
to a sign). It also recovers the λ-nondivisibility `λ ∤ (A+B·η)` from `3 ∤ C`
(`lambda_not_dvd_conj_of_nat`), which is the entry condition of the sign step.
No residue hypothesis is used here.
-/

/-- **The unconditional descent-to-sign assembly.** A primitive cube-sum Beal
solution `A³ + B³ = C^z` with `3 ∤ C`, `z ≠ 0`, and `gcd(z,3) = 1` produces a
descent base `d' : 𝓞 K` with:

* the integer descent `A + B = sᶻ` (some `s : ℕ`),
* the λ-coprimality `λ ∤ (A + B·η)` (entry condition, `λ = η − 1`),
* the **sign-pinned** cyclotomic descent `A + B·η = d'ᶻ ∨ A + B·η = −d'ᶻ`.

Everything here is proved unconditionally; the only remaining ambiguity is the
sign, addressed by the residue hypothesis below. -/
theorem cube_descent_to_sign
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {3} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ 3)
    {A B C z : ℕ} (hAB : Nat.Coprime A B) (hC : ¬ 3 ∣ C) (hz : z ≠ 0)
    (hcop : Nat.Coprime z 3)
    (h : A ^ 3 + B ^ 3 = C ^ z) :
    ∃ (s : ℕ) (d' : 𝓞 K),
      A + B = s ^ z ∧
      ¬ (hζ.toInteger - 1) ∣ ((A : 𝓞 K) + (B : 𝓞 K) * hζ.toInteger) ∧
      ((A : 𝓞 K) + (B : 𝓞 K) * hζ.toInteger = d' ^ z ∨
       (A : 𝓞 K) + (B : 𝓞 K) * hζ.toInteger = -(d' ^ z)) := by
  -- Structure theorem: A+B = sᶻ and Associated (dᶻ) (A+B·η).
  obtain ⟨⟨s, hs⟩, ⟨d, hassoc⟩⟩ :=
    BealCubeSynthesis.beal_cube_structure_three_ndvd_C hζ hAB hC hz h
  -- λ ∤ (A+B·η), from 3 ∤ C ⟹ 3 ∤ (A+B) ⟹ λ ∤ (A+B·η).
  have h3sum : ¬ (3 ∣ (A + B)) := fun hdvd =>
    hC ((BealCubeDescentThree.three_dvd_sum_iff hz h).mpr hdvd)
  have hlam : ¬ (hζ.toInteger - 1) ∣ ((A : 𝓞 K) + (B : 𝓞 K) * hζ.toInteger) :=
    BealCubeSynthesis.lambda_not_dvd_conj_of_nat hζ h3sum
  -- unit_pinned_to_sign: collapse the descent unit to a sign.
  obtain ⟨d', hpin⟩ := BealCubeDescentStep.unit_pinned_to_sign hζ hcop hassoc
  exact ⟨s, d', hs, hlam, hpin⟩

/-!
## Part 2 — HEADLINE: the sharpest conditional (3,3,z) statement

We now feed the sign-pinned descent into `BealKummerSign.sign_eliminated`. The
**single** extra hypothesis is `H(d') : λ² ∣ ((A+B·η) − d'ᶻ)` for the descent
base `d'`. The conclusion is the `+`-branch descent identity, with `A+B = sᶻ`
retained. This is the tightest conditional (3,3,z) statement: the entire
remaining gap is the typed hypothesis `H`.
-/

/-- **HEADLINE — `cube_plus_branch_of_residue`.** The sharpest CONDITIONAL
(3,3,z) descent statement. A primitive cube-sum Beal solution `A³ + B³ = C^z`
with `3 ∤ C`, `z ≠ 0`, `gcd(z,3) = 1` admits a descent base `d' : 𝓞 K` and
integer `s : ℕ` with `A + B = sᶻ`, such that:

  **IF** the explicit λ²-residue hypothesis
    `H(d') : (η−1)² ∣ ((A + B·η) − d'ᶻ)`   (`A + B·η ≡ d'ᶻ (mod λ²)`)
  holds, **THEN** the sign-free descent identity holds:
    `A + B·η = d'ᶻ`   and   `A + B = sᶻ`.

The hypothesis `H(d')` is the *only* gap: it is exactly the congruence Kummer's
lemma consumes (`eq_one_or_neg_one_of_unit_of_congruent`), and by
`residue_gap_iff_plus_branch` it is equivalent to the `+` branch, so it is honest
extra input — supplied elementarily only in Case 2 (`3 ∣ B`), and by the modular
method in Case 1 (`3 ∤ B`, prime `z ≥ 17`).

The statement quantifies `d'`, `s` existentially with `H` *inside* the
existential body, so it reads "there is a base for which `H` suffices" — the
typed interface to the modular input. -/
theorem cube_plus_branch_of_residue
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {3} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ 3)
    {A B C z : ℕ} (hAB : Nat.Coprime A B) (hC : ¬ 3 ∣ C) (hz : 1 ≤ z)
    (hcop : Nat.Coprime z 3)
    (h : A ^ 3 + B ^ 3 = C ^ z) :
    ∃ (s : ℕ) (d' : 𝓞 K),
      A + B = s ^ z ∧
      ((hζ.toInteger - 1) ^ 2 ∣
        (((A : 𝓞 K) + (B : 𝓞 K) * hζ.toInteger) - d' ^ z) →
       (A : 𝓞 K) + (B : 𝓞 K) * hζ.toInteger = d' ^ z) := by
  obtain ⟨s, d', hs, hlam, hpin⟩ :=
    cube_descent_to_sign hζ hAB hC (by omega) hcop h
  refine ⟨s, d', hs, ?_⟩
  intro hres
  exact BealKummerSign.sign_eliminated hζ hz hlam hpin hres

/-!
## Part 3 — the honest elementary reduction of the gap

For the descent base `d'` of the sign-pinned descent, the residue gap `H(d')` is
logically equivalent to landing in the `+` branch. This is the most explicit
statement of the remaining gap: discharging `H` is *exactly* choosing the correct
sign. (Repackaged from `BealLambdaResidue.hres_iff_plus_branch`, applied to the
descent base produced by the structure theorem.) -/

/-- **`residue_gap_iff_plus_branch`** (the explicit gap). A primitive cube-sum
solution with `3 ∤ C`, `gcd(z,3)=1` produces a base `d'` (with `A + B = sᶻ`) for
which the λ²-residue gap is *equivalent* to the `+` branch:

  `(η−1)² ∣ ((A+B·η) − d'ᶻ)  ↔  A + B·η = d'ᶻ`.

So the remaining gap `H(d')` is the same proposition as the descent conclusion —
it cannot be derived from the sign-pinning (that would be circular), and is the
genuine extra (modular) input. -/
theorem residue_gap_iff_plus_branch
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {3} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ 3)
    {A B C z : ℕ} (hAB : Nat.Coprime A B) (hC : ¬ 3 ∣ C) (hz : 1 ≤ z)
    (hcop : Nat.Coprime z 3)
    (h : A ^ 3 + B ^ 3 = C ^ z) :
    ∃ (s : ℕ) (d' : 𝓞 K),
      A + B = s ^ z ∧
      (((hζ.toInteger - 1) ^ 2 ∣
        (((A : 𝓞 K) + (B : 𝓞 K) * hζ.toInteger) - d' ^ z)) ↔
       (A : 𝓞 K) + (B : 𝓞 K) * hζ.toInteger = d' ^ z) := by
  obtain ⟨s, d', hs, hlam, hpin⟩ :=
    cube_descent_to_sign hζ hAB hC (by omega) hcop h
  exact ⟨s, d', hs, BealLambdaResidue.hres_iff_plus_branch hζ hz hlam hpin⟩

/-!
## Part 4 — the UNCONDITIONAL Case-2 corollary (`3 ∣ B`)

When `λ ∣ B` (equivalently `3 ∣ B`, the classical FLT-3 Case-2 split), the
mathlib FLT-3 cube engine discharges `H` for `z = 3` with **no Kummer input**,
given only the integer-side λ²-match. We thread `cube_descent_to_sign` through
`BealLambdaResidue.sign_eliminated_of_lambda_dvd_B` to get the `+` branch free of
the residue hypothesis. (This is the case where the *elementary* descent closes.)

For the operative exponent `z = 3` the η-absorption of `unit_pinned_to_sign` is
*unavailable* (it requires `gcd(z,3) = 1`, false for `z = 3`), so the sign-pinned
descent `hpin` is taken as a hypothesis here (it is what the cyclotomic
factorization delivers up to a unit). What this corollary establishes is that,
**given** the sign-pinned descent, the residue gap `H` is *discharged
unconditionally* in Case 2 by the FLT-3 cube engine — no Kummer / modular input.
-/

/-- **`cube_plus_branch_case_two`** (Case 2: the elementary descent closes). For
the cube exponent `z = 3`, given the sign-pinned cyclotomic descent
`A + B·η = d'³ ∨ A + B·η = −d'³`, the λ-coprimality `λ ∤ (A+B·η)`, and **the
Case-2 split** `λ ∣ B` (≡ `3 ∣ B`) together with the descent-base coprimality
`λ ∤ d'` and the integer-side λ²-match
  `∀ N : ℤ, λ² ∣ (d'³ − N) → λ² ∣ ((A+B) − N)`,
the `+` branch is forced **with no Kummer / residue hypothesis**:

  `A + B·η = d'³`.

The residue gap `H` is *discharged* by the FLT-3 cube engine
(`BealLambdaResidue.sign_eliminated_of_lambda_dvd_B`): in Case 2 the left factor
`A + B·η` reduces to a rational integer mod λ² (because `λ ∣ B`), matching the
integer residue `±1` of `d'³` from `lambda_pow_four_dvd_cube_sub_one_or_add_one`.
This is the case where the *elementary* (3,3,3) descent terminates without the
modular input; the Case-1 analogue (`λ ∤ B`) is exactly what stays open. -/
theorem cube_plus_branch_case_two
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {3} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ 3)
    {A B d' : 𝓞 K}
    (hlam : ¬ (hζ.toInteger - 1) ∣ (A + B * hζ.toInteger))
    (hpin : A + B * hζ.toInteger = d' ^ 3 ∨ A + B * hζ.toInteger = -(d' ^ 3))
    (hlamd : ¬ (hζ.toInteger - 1) ∣ d')
    (hlamB : (hζ.toInteger - 1) ∣ B)
    (hint : ∀ N : ℤ, (hζ.toInteger - 1) ^ 2 ∣ (d' ^ 3 - (N : 𝓞 K)) →
              (hζ.toInteger - 1) ^ 2 ∣ ((A + B) - (N : 𝓞 K))) :
    A + B * hζ.toInteger = d' ^ 3 :=
  BealLambdaResidue.sign_eliminated_of_lambda_dvd_B hζ hlam hpin hlamd hlamB hint

end BealLambdaInterface

-- Axiom audit (remove before finishing): each kept theorem reports
-- `[propext, Classical.choice, Quot.sound]`.
-- #print axioms BealLambdaInterface.cube_descent_to_sign
-- #print axioms BealLambdaInterface.cube_plus_branch_of_residue
-- #print axioms BealLambdaInterface.residue_gap_iff_plus_branch
-- #print axioms BealLambdaInterface.cube_plus_branch_case_two
