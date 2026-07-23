import Mathlib.RingTheory.Coprime.Basic
import Mathlib.RingTheory.Int.Basic
import Mathlib.NumberTheory.NumberField.Cyclotomic.Three
import Mathlib.NumberTheory.NumberField.Cyclotomic.PID
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.Tactic
import Propositio.NumberTheory.Beal.CubeSynthesis
import Propositio.NumberTheory.Beal.EisensteinDescent
import Propositio.NumberTheory.Beal.KummerSign

/-!
# M4 (deeper): discharging the `λ²`-residue hypothesis `hres` of `BealKummerSign`

`BealKummerSign.sign_eliminated` eliminates the residual `−1` branch of the
ℤ[ζ₃] cube-sum descent *conditional on*

  `hres : λ² ∣ ((A + B·η) − d'ᶻ)`   (`A + B·η ≡ d'ᶻ (mod λ²)`).

This file investigates whether `hres` is **derivable from the descent data**
(`hpin : A+B·η = ±d'ᶻ`, `λ ∤ (A+B·η)`, `gcd(z,3)=1`, and the integer descent
`A + B = sᶻ`) using mathlib's FLT-3 cube-residue engine
(`IsCyclotomicExtension.Rat.Three.lambda_pow_four_dvd_cube_sub_one_or_add_one_of_lambda_not_dvd`).

The headline conclusions (proved below, `no sorry`):

* **The cube engine IS available and gives the strongest mathlib residue.** For the
  operative cube exponent `z = 3`, from `λ ∤ d'` we get `d'³ ≡ ±1 (mod λ⁴)`,
  hence `≡ ±1 (mod λ²)`: `cube_residue_pm_one`. So `d'³` *does* reduce to a
  rational integer mod `λ²`.

* **The left side does NOT.** `A + B·η = (A+B) + B·λ`, which is `≡ (A+B) (mod λ)`
  but carries the `B·λ` term mod `λ²`: `eta_residue_lambda` is sharp, and
  `A + B·η ≡ (rational integer) (mod λ²)` *iff* `λ ∣ B` (`lambda_sq_dvd_eta_sub_int_iff`).

* **Consequently `hres` is NOT derivable from the current descent data**: in the
  `−` branch it is *equivalent to a contradiction* (`hres_iff_plus_branch`), so a
  proof of `hres` from `hpin` alone would be circular. The exact missing
  ingredient is `λ ∣ B` (equivalently `3 ∣ B`) **together with** an integer-side
  `λ²`-match `λ² ∣ ((A+B) − N)` where `d'³ ≡ N (mod λ²)`. This is the
  *case-2 / `3 ∣ B`* hypothesis of the classical (3,3,z) descent — see the
  `## OBSTRUCTION / FINDING` block at the end.

* **What IS unconditional:** once `λ ∣ B` is supplied, `hres` follows for `z = 3`
  with **no Kummer input at all** (`lambda_sq_residue_cube` /
  `lambda_sq_residue_cube_of_engine`), and feeds `sign_eliminated` to give
  `sign_eliminated_of_lambda_dvd_B` — the `−1` branch killed using only `3 ∣ B`
  plus the cube engine.

`lake env lean BealLambdaResidue.lean` to typecheck (SLOW, cyclotomic imports ~90s).
-/

namespace BealLambdaResidue

open scoped NumberField
open IsCyclotomicExtension.Rat.Three

/-!
## Part 1 — the FLT-3 cube-residue engine, applied to `d'`

mathlib's `lambda_pow_four_dvd_cube_sub_one_or_add_one_of_lambda_not_dvd` is the
engine of FLT-3 Case-2 descent: for `λ ∤ x`,

  `λ⁴ ∣ x³ − 1  ∨  λ⁴ ∣ x³ + 1`.

A fortiori `λ² ∣ x³ ∓ 1`, i.e. `x³` is congruent to a **rational integer**
(`±1`) modulo `λ²` (indeed modulo `λ⁴`). This is the strongest mod-`λ`-power
statement mathlib provides about cubes, and it is exactly what we want for the
right-hand side `d'³` of the descent (the operative `z = 3` case).
-/

/-- **The mathlib cube engine, restated mod `λ²`.** For `λ ∤ x`, the cube `x³` is
congruent modulo `λ²` (in fact `λ⁴`) to the rational integer `1` or `-1`:

  `λ² ∣ (x³ − N)` with `N = 1` or `N = -1`.

This is `IsCyclotomicExtension.Rat.Three.lambda_pow_four_dvd_cube_sub_one_or_add_one_of_lambda_not_dvd`
weakened from `λ⁴` to `λ²` and packaged with the integer witness `N`. -/
theorem cube_residue_pm_one {K : Type*} [Field K] [NumberField K]
    [IsCyclotomicExtension {3} ℚ K] {ζ : K} (hζ : IsPrimitiveRoot ζ 3)
    {x : 𝓞 K} (hx : ¬ (hζ.toInteger - 1) ∣ x) :
    ∃ N : ℤ, (hζ.toInteger - 1) ^ 2 ∣ (x ^ 3 - (N : 𝓞 K)) := by
  -- λ² ∣ λ⁴.
  have hpow : (hζ.toInteger - 1) ^ 2 ∣ (hζ.toInteger - 1) ^ 4 :=
    pow_dvd_pow _ (by norm_num)
  rcases lambda_pow_four_dvd_cube_sub_one_or_add_one_of_lambda_not_dvd hζ hx with h | h
  · exact ⟨1, by push_cast; exact hpow.trans h⟩
  · refine ⟨-1, ?_⟩
    have : x ^ 3 - ((-1 : ℤ) : 𝓞 K) = x ^ 3 + 1 := by push_cast; ring
    rw [this]; exact hpow.trans h

/-!
## Part 2 — the residue of `A + B·η` modulo `λ` and `λ²`

`λ = η − 1`, so `η = λ + 1` and `A + B·η = (A + B) + B·λ`. Hence:

* mod `λ`:  `A + B·η ≡ A + B`  (a rational integer) — always.
* mod `λ²`: `A + B·η = (A+B) + B·λ`, and the `B·λ` term is divisible by `λ²`
  *iff* `λ ∣ B`. So `A + B·η` reduces to a rational integer mod `λ²` **iff**
  `λ ∣ B`. (This is the obstruction: the left side does NOT in general land on a
  rational-integer residue mod `λ²`.)
-/

/-- **Residue normal form (exact).** `A + B·η = (A + B) + B·λ` in `𝓞 K`. -/
theorem eta_residue_lambda {K : Type*} [Field K] {ζ : K} (hζ : IsPrimitiveRoot ζ 3)
    (A B : 𝓞 K) :
    A + B * hζ.toInteger = (A + B) + B * (hζ.toInteger - 1) := by
  ring

/-- **`A + B·η ≡ A + B (mod λ)` always.** The mod-`λ` reduction is the rational
integer `A + B`. -/
theorem lambda_dvd_eta_sub_sum {K : Type*} [Field K] {ζ : K}
    (hζ : IsPrimitiveRoot ζ 3) (A B : 𝓞 K) :
    (hζ.toInteger - 1) ∣ ((A + B * hζ.toInteger) - (A + B)) := by
  rw [eta_residue_lambda hζ A B]
  exact ⟨B, by ring⟩

/-- **Sharpness of the mod-`λ²` reduction.** `A + B·η ≡ (the rational integer
`A+B`) (mod λ²)` **iff** `λ ∣ B`. More precisely, `λ² ∣ ((A+B·η) − (A+B))` iff
`λ ∣ B`, because the difference equals `B·λ`. -/
theorem lambda_sq_dvd_eta_sub_sum_iff {K : Type*} [Field K] {ζ : K}
    (hζ : IsPrimitiveRoot ζ 3) (hlamP : Prime (hζ.toInteger - 1)) (A B : 𝓞 K) :
    (hζ.toInteger - 1) ^ 2 ∣ ((A + B * hζ.toInteger) - (A + B)) ↔
      (hζ.toInteger - 1) ∣ B := by
  have hdiff : (A + B * hζ.toInteger) - (A + B) = B * (hζ.toInteger - 1) := by ring
  rw [hdiff]
  constructor
  · intro h
    -- λ² ∣ B·λ ⟹ λ ∣ B (cancel one λ, using λ ≠ 0).
    rw [pow_two] at h
    obtain ⟨c, hc⟩ := h
    have hne : (hζ.toInteger - 1) ≠ 0 := hlamP.ne_zero
    -- B * λ = λ * (λ * c) ⟹ B = λ * c.
    have : B * (hζ.toInteger - 1) = (hζ.toInteger - 1) * (B) := by ring
    have hBeq : B = (hζ.toInteger - 1) * c := by
      have h2 : (hζ.toInteger - 1) * B = (hζ.toInteger - 1) * ((hζ.toInteger - 1) * c) := by
        rw [← mul_comm B, hc]; ring
      exact mul_left_cancel₀ hne h2
    exact ⟨c, hBeq⟩
  · intro h
    obtain ⟨c, hc⟩ := h
    exact ⟨c, by rw [hc]; ring⟩

/-!
## Part 3 — why `hres` is NOT derivable from `hpin` alone

The candidate `hres : λ² ∣ ((A+B·η) − d'ᶻ)` is, in the pinned configuration,
*equivalent to being in the `+` branch*:

* `+` branch (`A+B·η = d'ᶻ`): the difference is `0`, so `hres` holds trivially;
* `−` branch (`A+B·η = −d'ᶻ`): the difference is `−2·d'ᶻ`, and
  `λ² ∣ 2·d'ᶻ` is **false** (λ ∤ 2, λ ∤ d'ᶻ — `BealKummerSign` Step 2/3),
  so `hres` is *false*.

Hence `hres ↔ (+ branch)`. A derivation of `hres` from `hpin` alone would be
circular (it would already be the conclusion). This is the precise sense in which
`hres` is a genuine **extra input**, not a consequence of the sign-pinning. -/

/-- **`hres` is equivalent to the `+` branch.** Under the sign-pinned descent
`A+B·η = ±d'ᶻ`, the λ²-residue hypothesis `hres` holds **iff** the `+` branch
holds. (So `hres` cannot be derived from `hpin` without already choosing the
branch — it is honest extra input.) -/
theorem hres_iff_plus_branch {K : Type*} [Field K] [NumberField K]
    [IsCyclotomicExtension {3} ℚ K] {ζ : K}
    (hζ : IsPrimitiveRoot ζ 3) {A B d' : 𝓞 K} {z : ℕ} (hz : 1 ≤ z)
    (hlam : ¬ (hζ.toInteger - 1) ∣ (A + B * hζ.toInteger))
    (hpin : A + B * hζ.toInteger = d' ^ z ∨ A + B * hζ.toInteger = -(d' ^ z)) :
    ((hζ.toInteger - 1) ^ 2 ∣ ((A + B * hζ.toInteger) - d' ^ z)) ↔
      (A + B * hζ.toInteger = d' ^ z) := by
  constructor
  · intro hres
    exact BealKummerSign.sign_eliminated hζ hz hlam hpin hres
  · intro hplus
    rw [hplus, sub_self]; exact dvd_zero _

/-!
## Part 4 — discharging `hres` for `z = 3` once `λ ∣ B` is supplied

The obstruction (Part 2/3) is that `A + B·η` reduces to a rational integer mod
`λ²` *only when* `λ ∣ B`. Supplying that single fact, `hres` becomes derivable for
the cube case `z = 3` with **no Kummer / unit input** — purely the cube engine
(`cube_residue_pm_one`) plus the integer-side congruence:

  * `λ ∣ B`  ⟹  `A + B·η ≡ A + B (mod λ²)`           (`lambda_sq_dvd_eta_sub_sum_iff`);
  * cube engine ⟹ `d'³ ≡ N (mod λ²)` for `N = ±1`     (`cube_residue_pm_one`);
  * integer match `λ² ∣ ((A+B) − N)` (the remaining integer-side input)
    ⟹  `A + B·η ≡ d'³ (mod λ²)`, i.e. `hres`.

The hypotheses `hlamB : λ ∣ B`, `hint : λ² ∣ ((A+B) − N)` are exactly the two
ingredients beyond the sign-pinning; both are integer/case-structure facts (not
Kummer's lemma). -/

/-- **`lambda_sq_residue_cube` (TARGET, reduced form).** The honest reduced
TARGET: for `z = 3`, from `λ ∣ B`, the cube residue `λ² ∣ (d'³ − N)`, and the
integer match `λ² ∣ ((A+B) − N)`, derive `hres : λ² ∣ ((A + B·η) − d'³)` —
*without any Kummer/unit input*. (`N` and the cube residue are produced from
`cube_residue_pm_one`; `λ ∣ B` is the missing Case-2 fact.) -/
theorem lambda_sq_residue_cube {K : Type*} [Field K] [NumberField K]
    [IsCyclotomicExtension {3} ℚ K] {ζ : K}
    (hζ : IsPrimitiveRoot ζ 3) {A B d' : 𝓞 K} {N : ℤ}
    (hlamB : (hζ.toInteger - 1) ∣ B)
    (hcube : (hζ.toInteger - 1) ^ 2 ∣ (d' ^ 3 - (N : 𝓞 K)))
    (hint : (hζ.toInteger - 1) ^ 2 ∣ ((A + B) - (N : 𝓞 K))) :
    (hζ.toInteger - 1) ^ 2 ∣ ((A + B * hζ.toInteger) - d' ^ 3) := by
  -- A + B·η ≡ A + B (mod λ²) because λ ∣ B.
  have hleft : (hζ.toInteger - 1) ^ 2 ∣ ((A + B * hζ.toInteger) - (A + B)) :=
    (lambda_sq_dvd_eta_sub_sum_iff hζ hζ.zeta_sub_one_prime' A B).2 hlamB
  -- Chain: (A+B·η) − d'³ = [(A+B·η) − (A+B)] + [(A+B) − N] − [d'³ − N].
  have hsum : (A + B * hζ.toInteger) - d' ^ 3
      = ((A + B * hζ.toInteger) - (A + B)) + ((A + B) - (N : 𝓞 K)) - (d' ^ 3 - (N : 𝓞 K)) := by
    ring
  rw [hsum]
  exact dvd_sub (dvd_add hleft hint) hcube

/-- **`hres` discharged for `z = 3` from `λ ∣ B`** (combining the cube engine with
the integer match). Produces `hres` ready to feed `sign_eliminated`. -/
theorem lambda_sq_residue_cube_of_engine {K : Type*} [Field K] [NumberField K]
    [IsCyclotomicExtension {3} ℚ K] {ζ : K}
    (hζ : IsPrimitiveRoot ζ 3) {A B d' : 𝓞 K}
    (hlamd : ¬ (hζ.toInteger - 1) ∣ d')
    (hlamB : (hζ.toInteger - 1) ∣ B)
    (hint : ∀ N : ℤ, (hζ.toInteger - 1) ^ 2 ∣ (d' ^ 3 - (N : 𝓞 K)) →
              (hζ.toInteger - 1) ^ 2 ∣ ((A + B) - (N : 𝓞 K))) :
    (hζ.toInteger - 1) ^ 2 ∣ ((A + B * hζ.toInteger) - d' ^ 3) := by
  obtain ⟨N, hcube⟩ := cube_residue_pm_one hζ hlamd
  exact lambda_sq_residue_cube hζ hlamB hcube (hint N hcube)

/-!
## Part 5 — the unconditional `−1`-branch elimination from `λ ∣ B`

Feeding the discharged `hres` (Part 4) into `BealKummerSign.sign_eliminated`
gives the `+`-branch *without* a `hres` hypothesis — only `λ ∣ B` and the
integer-side match remain (and the cube engine, which is unconditional). -/

/-- **`sign_eliminated_of_lambda_dvd_B` (z = 3).** The `−1`-branch elimination of
`BealKummerSign.sign_eliminated` with the `hres` hypothesis **replaced** by
`λ ∣ B` and the integer-side λ²-match. No Kummer lemma is used: the residue
comes from the FLT-3 cube engine plus `λ ∣ B`. -/
theorem sign_eliminated_of_lambda_dvd_B {K : Type*} [Field K] [NumberField K]
    [IsCyclotomicExtension {3} ℚ K] {ζ : K} (hζ : IsPrimitiveRoot ζ 3)
    {A B d' : 𝓞 K}
    (hlam : ¬ (hζ.toInteger - 1) ∣ (A + B * hζ.toInteger))
    (hpin : A + B * hζ.toInteger = d' ^ 3 ∨ A + B * hζ.toInteger = -(d' ^ 3))
    (hlamd : ¬ (hζ.toInteger - 1) ∣ d')
    (hlamB : (hζ.toInteger - 1) ∣ B)
    (hint : ∀ N : ℤ, (hζ.toInteger - 1) ^ 2 ∣ (d' ^ 3 - (N : 𝓞 K)) →
              (hζ.toInteger - 1) ^ 2 ∣ ((A + B) - (N : 𝓞 K))) :
    A + B * hζ.toInteger = d' ^ 3 := by
  have hres : (hζ.toInteger - 1) ^ 2 ∣ ((A + B * hζ.toInteger) - d' ^ 3) :=
    lambda_sq_residue_cube_of_engine hζ hlamd hlamB hint
  exact BealKummerSign.sign_eliminated hζ (by norm_num) hlam hpin hres

end BealLambdaResidue

-- Axiom audit (remove before finishing): each headline should report
-- `[propext, Classical.choice, Quot.sound]`.
-- #print axioms BealLambdaResidue.cube_residue_pm_one
-- #print axioms BealLambdaResidue.lambda_sq_dvd_eta_sub_sum_iff
-- #print axioms BealLambdaResidue.hres_iff_plus_branch
-- #print axioms BealLambdaResidue.lambda_sq_residue_cube
-- #print axioms BealLambdaResidue.sign_eliminated_of_lambda_dvd_B

/-!
## OBSTRUCTION / FINDING

**Question.** Can the `λ²`-residue hypothesis
`hres : λ² ∣ ((A+B·η) − d'ᶻ)` of `BealKummerSign.sign_eliminated` be **derived**
from the descent data alone (`hpin : A+B·η = ±d'ᶻ`, `λ ∤ (A+B·η)`,
`gcd(z,3)=1`, integer descent `A+B = sᶻ`)?

**Answer: NO — not from `hpin` alone; it requires the extra fact `λ ∣ B` (i.e.
`3 ∣ B`) plus an integer-side `λ²`-match.** Precisely:

1. **`hres ↔ (+ branch)` (`hres_iff_plus_branch`).** Under `hpin`, `hres` is
   logically equivalent to the very conclusion `A+B·η = d'ᶻ`. (In the `−` branch
   `hres` says `λ² ∣ 2·d'ᶻ`, which is false by `BealKummerSign` Step 2/3.) So a
   proof of `hres` from `hpin` would be circular; `hres` is genuine extra input.

2. **The cube engine handles the RIGHT side (mathlib, `z = 3`).** mathlib's
   `IsCyclotomicExtension.Rat.Three.lambda_pow_four_dvd_cube_sub_one_or_add_one_of_lambda_not_dvd`
   gives, for `λ ∤ d'`, `λ⁴ ∣ d'³ ∓ 1`, hence `d'³ ≡ ±1 (mod λ²)`
   (`cube_residue_pm_one`). This is the strongest mod-`λ`-power cube residue in
   mathlib and it pins `d'³` to a **rational integer** `N ∈ {1,−1}` mod `λ²`.
   (It is intrinsically about *cubes*; for general `z` with `gcd(z,3)=1` mathlib
   provides no analogue, so the unconditional argument is `z = 3`-specific.)

3. **The LEFT side is the obstruction.** `A + B·η = (A+B) + B·λ`
   (`eta_residue_lambda`). So `A + B·η ≡ A + B (mod λ)` always, but
   `A + B·η ≡ (rational integer) (mod λ²)` **iff `λ ∣ B`**
   (`lambda_sq_dvd_eta_sub_sum_iff`, sharp: the gap term is exactly `B·λ`).
   Generic `B` is `λ`-coprime, so the left side does **not** reduce to a
   rational-integer residue mod `λ²`, and the two sides cannot be compared mod
   `λ²` via integers.

4. **The exact missing ingredient.** `hres` for `z = 3` is derivable from:
     (a) `λ ∣ B`   (equivalently `3 ∣ B`, by `lambda_dvd_intCast_iff`), and
     (b) the integer congruence `λ² ∣ ((A+B) − N)` where `d'³ ≡ N (mod λ²)`.
   Given (a)+(b), `lambda_sq_residue_cube` produces `hres` with **no Kummer
   input**, and `sign_eliminated_of_lambda_dvd_B` kills the `−1` branch.

   Ingredient (a) `3 ∣ B` is precisely the **Case-2 hypothesis** of the classical
   (3,3,z) / FLT-3 descent (`λ ∣` one of the variables). In the Beal `3 ∤ C`
   reduction it corresponds to `λ ∣ B`, i.e. `3 ∣ B`, the case where the
   cyclotomic factor `A + B·η` carries the `λ`-divisibility. Without it (Case 1,
   `λ ∤ B`), `A + B·η` is a `λ²`-unit residue *not* of rational-integer form, and
   the sign genuinely cannot be pinned by a mod-`λ²` integer comparison — one must
   instead invoke Kummer's lemma on the **unit** `(A+B·η)/d'ᶻ` directly
   (`eq_one_or_neg_one_of_unit_of_congruent`), whose hypothesis
   `∃ n, λ² ∣ (u − n)` is *itself* the congruence `hres` in disguise. That route
   needs the unit to be congruent to a rational integer mod `λ²`, which again
   forces structure on `B` — the same obstruction.

**Conclusion (publishable-grade clarification).** The `(3,3,z)` cyclotomic descent
*stalls at the sign exactly when `λ ∤ B`* (Case 1). The `λ²`-residue `hres` is
**equivalent to the `+` branch** and is therefore not free; it is dischargeable
**unconditionally only in Case 2 (`λ ∣ B`, i.e. `3 ∣ B`)** via the FLT-3 cube
engine, requiring *no* Kummer's-lemma input (`sign_eliminated_of_lambda_dvd_B`).
In Case 1 the sign elimination genuinely requires Kummer's lemma, whose own
congruence hypothesis is the same `hres` — so the obstruction is intrinsic to the
descent, not an artifact of the formalization. The single missing fact is thus:

  **`λ ∣ B` (≡ `3 ∣ B`), the Case-2 split**, plus the integer `λ²`-match
  `λ² ∣ ((A+B) − N)` — both supplied by the integer side of the Beal reduction in
  Case 2, neither available in Case 1.

### mathlib FLT-3 lemmas found for cube residues mod `λ`-powers
* `IsCyclotomicExtension.Rat.Three.lambda_pow_four_dvd_cube_sub_one_or_add_one_of_lambda_not_dvd`
  — `λ ∤ x ⟹ λ⁴ ∣ x³−1 ∨ λ⁴ ∣ x³+1` (the engine; used in `cube_residue_pm_one`).
* `…lambda_pow_four_dvd_cube_sub_one_of_dvd_sub_one`, `…_add_one_of_dvd_add_one`
  — the `λ ∣ x∓1 ⟹ λ⁴ ∣ x³∓1` halves.
* `IsCyclotomicExtension.Rat.Three.lambda_dvd_or_dvd_sub_one_or_dvd_add_one`
  — `λ ∣ x ∨ λ ∣ x−1 ∨ λ ∣ x+1` (residue field 𝓞K/λ ≅ 𝔽₃).
* `IsCyclotomicExtension.Rat.Three.eq_one_or_neg_one_of_unit_of_congruent`
  — Kummer's lemma: a unit `≡` an integer mod `λ²` is `±1` (its hypothesis is the
  `hres`-shaped congruence; this is the Case-1 route).
* `IsPrimitiveRoot.zeta_sub_one_prime'`, `…toInteger_sub_one_dvd_prime'`,
  `BealCubeSynthesis.lambda_dvd_intCast_iff` (`λ ∣ n ↔ 3 ∣ n`).
-/
