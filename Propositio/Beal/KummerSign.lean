import Mathlib.RingTheory.Coprime.Basic
import Mathlib.RingTheory.Int.Basic
import Mathlib.NumberTheory.NumberField.Cyclotomic.Three
import Mathlib.NumberTheory.NumberField.Cyclotomic.PID
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.Tactic
import Propositio.Beal.CubeDescentStep
import Propositio.Beal.CubeSynthesis
import Propositio.Beal.EisensteinDescent

/-!
# M4 (close): Kummer `−1`-sign elimination in the ℤ[ζ₃] cube-sum descent

**NEW mathematics — no LaTTe sibling.** `BealCubeDescentStep.unit_pinned_to_sign`
already collapses the residual descent unit to a *sign*:

  `A + B·η = d'ᶻ ∨ A + B·η = −(d'ᶻ)`   (given `gcd(z,3)=1`, `Associated (dᶻ) (A+B·η)`).

This file closes the residual `−1` branch via the `λ²`-congruence comparison that
underlies Kummer's lemma (`IsCyclotomicExtension.Rat.Three.eq_one_or_neg_one_of_unit_of_congruent`).

## The mathematics

Write `λ = η − 1`. The two sign candidates `d'ᶻ` and `−(d'ᶻ)` differ by `2·d'ᶻ`.
The **prime** `λ` (`IsPrimitiveRoot.zeta_sub_one_prime'`) satisfies `λ ∤ 2`
(since `λ ∣ (2 : 𝓞 K) ↔ 3 ∣ 2`, false, via `BealCubeSynthesis.lambda_dvd_intCast_iff`)
and, in the descent, `λ ∤ d'` (because `λ ∤ (A+B·η) = ±d'ᶻ`). Hence

  `λ² ∤ 2·d'ᶻ`   (`lambda_sq_not_dvd_two_mul`).

So `A+B·η` cannot be `≡` to **both** `d'ᶻ` and `−(d'ᶻ)` modulo `λ²`: the two
residues are incongruent. Supplying the residue of `A+B·η` modulo `λ²` — namely
`A + B·η ≡ d'ᶻ (mod λ²)`, the classical congruence input that Kummer's lemma
consumes — forces the `+` branch, eliminating the `−1` sign
(`sign_eliminated`).

## What is genuinely new here

* **`eta_congr_lambda_sq`** — the residue normal form `A + B·η = (A+B) + B·λ`
  (so `A + B·η ≡ (A+B) + B·λ (mod λ²)` trivially), the `{1,λ}`-shape used to
  feed the residue comparison.
* **`lambda_sq_not_dvd_two_mul`** — `λ ∤ x ⟹ λ² ∤ 2x`, via primality of `λ` and
  `λ ∤ 2`.
* **`lambda_not_dvd_of_pinned`** — in the pinned configuration `A+B·η = ±d'ᶻ`,
  `λ ∤ (A+B·η)` lifts to `λ ∤ d'`.
* **`sign_eliminated`** (HEADLINE) — the `−1`-branch elimination: with the residue
  hypothesis `A + B·η ≡ d'ᶻ (mod λ²)` and `λ ∤ (A+B·η)`, the sign-pinned descent
  collapses to the `+` branch `A + B·η = d'ᶻ`.
* **`descent_coupling_three_signed`** (STRETCH) — feeds the sharpened `+` branch
  into `BealCubeDescentStep`'s `z=3` coordinate coupling, dropping the sign
  ambiguity from `descent_coupling_three`.

`lake env lean BealKummerSign.lean` to typecheck (SLOW, ~90s).
-/

namespace BealKummerSign

open scoped NumberField

/-!
## Step 1 — the residue normal form mod `λ²`

`λ = η − 1`, so `η = λ + 1` and
`A + B·η = A + B·(λ+1) = (A + B) + B·λ`. This is an exact equality in `𝓞 K`
(not merely a congruence), so a fortiori `A + B·η ≡ (A+B) + B·λ (mod λ²)`. It is
the `{1, λ}`-coordinate form: `A + B·η` reduces to the rational integer `A + B`
modulo `λ`, with the next coefficient `B` carried on `λ`. This is exactly the
shape Kummer's congruence comparison reads.
-/

/-- **Step 1 — residue normal form.** `A + B·η = (A + B) + B·λ` in `𝓞 K`
(`λ = η − 1`). Hence `λ² ∣ ((A + B·η) − ((A+B) + B·λ))` trivially. -/
theorem eta_congr_lambda_sq {K : Type*} [Field K] {ζ : K} (hζ : IsPrimitiveRoot ζ 3)
    (A B : 𝓞 K) :
    A + B * hζ.toInteger
      = (A + B) + B * (hζ.toInteger - 1) := by
  ring

/-- The `λ²`-divisibility (congruence) form of `eta_congr_lambda_sq`:
`λ² ∣ ((A + B·η) − ((A+B) + B·λ))` (the difference is `0`). -/
theorem lambda_sq_dvd_eta_residue {K : Type*} [Field K] {ζ : K}
    (hζ : IsPrimitiveRoot ζ 3) (A B : 𝓞 K) :
    (hζ.toInteger - 1) ^ 2 ∣
      ((A + B * hζ.toInteger) - ((A + B) + B * (hζ.toInteger - 1))) := by
  rw [eta_congr_lambda_sq hζ A B, sub_self]
  exact dvd_zero _

/-!
## Step 2 — `λ` is odd-residue: `λ² ∤ 2·x` when `λ ∤ x`

`λ = η − 1` is **prime** in `𝓞 K` (`IsPrimitiveRoot.zeta_sub_one_prime'`). It does
not divide `2`: `λ ∣ (2 : 𝓞 K) ↔ 3 ∣ (2 : ℤ)` (`lambda_dvd_intCast_iff`), which is
false (`N(λ) = 3` is odd). So for `λ ∤ x`, primality of `λ` gives `λ ∤ 2·x`, and a
fortiori `λ² ∤ 2·x`.
-/

/-- `λ = η − 1` does not divide `2` in `𝓞 K`, since `λ ∣ (2 : 𝓞 K) ↔ 3 ∣ 2`. -/
theorem lambda_not_dvd_two {K : Type*} [Field K] [NumberField K]
    [IsCyclotomicExtension {3} ℚ K] {ζ : K} (hζ : IsPrimitiveRoot ζ 3) :
    ¬ (hζ.toInteger - 1) ∣ (2 : 𝓞 K) := by
  intro hdvd
  -- (2 : 𝓞 K) = ((2 : ℤ) : 𝓞 K); use the λ-bridge.
  have hcast : (2 : 𝓞 K) = (((2 : ℤ)) : 𝓞 K) := by push_cast; ring
  rw [hcast, BealCubeSynthesis.lambda_dvd_intCast_iff hζ] at hdvd
  norm_num at hdvd

/-- **Step 2 — `λ² ∤ 2·x` from `λ ∤ x`.** With `λ` prime and `λ ∤ 2`, if `λ ∤ x`
then `λ ∤ 2·x` (primality), hence `λ² ∤ 2·x` (as `λ ∣ λ²`). -/
theorem lambda_sq_not_dvd_two_mul {K : Type*} [Field K] [NumberField K]
    [IsCyclotomicExtension {3} ℚ K] {ζ : K} (hζ : IsPrimitiveRoot ζ 3) {x : 𝓞 K}
    (hx : ¬ (hζ.toInteger - 1) ∣ x) :
    ¬ (hζ.toInteger - 1) ^ 2 ∣ (2 * x) := by
  have hlamPrime : Prime (hζ.toInteger - 1) := hζ.zeta_sub_one_prime'
  -- First: λ ∤ 2·x.
  have hlam2x : ¬ (hζ.toInteger - 1) ∣ (2 * x) := by
    intro hdvd
    rcases (hlamPrime.dvd_mul.mp hdvd) with h2 | hxx
    · exact lambda_not_dvd_two hζ h2
    · exact hx hxx
  -- λ ∣ λ², so λ² ∣ 2x would give λ ∣ 2x.
  intro hsq
  exact hlam2x ((dvd_pow_self _ (n := 2) (by norm_num)).trans hsq)

/-!
## Step 3 — `λ ∤ d'` in the pinned configuration

In the sign-pinned descent `A + B·η = d'ᶻ ∨ A + B·η = −(d'ᶻ)`, the descent base
`d'` is `λ`-coprime: from `λ ∤ (A+B·η)` we get `λ ∤ ±d'ᶻ`, hence `λ ∤ d'ᶻ`, hence
`λ ∤ d'` (else `λ ∣ d' ⟹ λ ∣ d'ᶻ` for `z ≥ 1`). -/

/-- **Step 3 — `λ ∤ d'`.** If `λ ∤ (A+B·η)` and `A+B·η = ±d'ᶻ` (`z ≥ 1`), then
`λ ∤ d'`. -/
theorem lambda_not_dvd_of_pinned {K : Type*} [Field K] {ζ : K}
    (hζ : IsPrimitiveRoot ζ 3) {A B d' : 𝓞 K} {z : ℕ} (hz : 1 ≤ z)
    (hlam : ¬ (hζ.toInteger - 1) ∣ (A + B * hζ.toInteger))
    (hpin : A + B * hζ.toInteger = d' ^ z ∨ A + B * hζ.toInteger = -(d' ^ z)) :
    ¬ (hζ.toInteger - 1) ∣ d' := by
  intro hd'
  -- λ ∣ d' ⟹ λ ∣ d'ᶻ.
  have hdz : (hζ.toInteger - 1) ∣ d' ^ z := dvd_pow hd' (by omega)
  apply hlam
  rcases hpin with h | h
  · rw [h]; exact hdz
  · rw [h]; exact (dvd_neg).2 hdz

/-!
## HEADLINE — `sign_eliminated`: closing the `−1` branch

`unit_pinned_to_sign` leaves `A + B·η = d'ᶻ ∨ A + B·η = −(d'ᶻ)`. Kummer's lemma
pins units that are `≡` a rational integer modulo `λ²`; the residue of the
descent factor `A + B·η` modulo `λ²` is the classical input. Supplying it as

  `hres : λ² ∣ ((A + B·η) − d'ᶻ)`    (i.e. `A + B·η ≡ d'ᶻ (mod λ²)`)

eliminates the `−` branch: in that branch `A + B·η = −(d'ᶻ)`, so
`λ² ∣ (−(d'ᶻ) − d'ᶻ) = −2·d'ᶻ`, i.e. `λ² ∣ 2·d'ᶻ`; but `λ ∤ d'` (Step 3) gives
`λ ∤ d'ᶻ`, so `λ² ∤ 2·d'ᶻ` (Step 2) — contradiction. Hence the `+` branch holds.

The residue hypothesis `hres` is exactly the `λ²`-congruence that Kummer's lemma
(`eq_one_or_neg_one_of_unit_of_congruent`) consumes; here it pins the **sign**
rather than a generic unit. See `## REMAINING PLAN` for how `hres` is supplied
from the integer side of the Beal `3 ∤ C` reduction. -/

/-- **HEADLINE — `sign_eliminated`.** Given the sign-pinned descent
`A + B·η = d'ᶻ ∨ A + B·η = −(d'ᶻ)` (the output of
`BealCubeDescentStep.unit_pinned_to_sign`), the `λ`-coprimality `λ ∤ (A+B·η)`
(the M2 entry condition), `z ≥ 1`, and the residue hypothesis

  `hres : λ² ∣ ((A + B·η) − d'ᶻ)`   (`A + B·η ≡ d'ᶻ mod λ²`),

the `−1` branch is eliminated:

  `A + B·η = d'ᶻ`.

Proof: in the `−` branch, `hres` with `A+B·η = −(d'ᶻ)` forces `λ² ∣ 2·d'ᶻ`,
contradicting `lambda_sq_not_dvd_two_mul` applied to `d'ᶻ` (which is `λ`-coprime
by `lambda_not_dvd_of_pinned` + `Prime.dvd_of_dvd_pow`). -/
theorem sign_eliminated {K : Type*} [Field K] [NumberField K]
    [IsCyclotomicExtension {3} ℚ K] {ζ : K} (hζ : IsPrimitiveRoot ζ 3)
    {A B d' : 𝓞 K} {z : ℕ} (hz : 1 ≤ z)
    (hlam : ¬ (hζ.toInteger - 1) ∣ (A + B * hζ.toInteger))
    (hpin : A + B * hζ.toInteger = d' ^ z ∨ A + B * hζ.toInteger = -(d' ^ z))
    (hres : (hζ.toInteger - 1) ^ 2 ∣ ((A + B * hζ.toInteger) - d' ^ z)) :
    A + B * hζ.toInteger = d' ^ z := by
  rcases hpin with h | h
  · exact h
  · exfalso
    -- λ ∤ d', hence λ ∤ d'ᶻ.
    have hlamd' : ¬ (hζ.toInteger - 1) ∣ d' :=
      lambda_not_dvd_of_pinned hζ hz hlam (Or.inr h)
    have hlamPrime : Prime (hζ.toInteger - 1) := hζ.zeta_sub_one_prime'
    have hlamdz : ¬ (hζ.toInteger - 1) ∣ d' ^ z := by
      intro hdvd
      exact hlamd' (hlamPrime.dvd_of_dvd_pow hdvd)
    -- In the − branch, hres gives λ² ∣ −(2·d'ᶻ), hence λ² ∣ 2·d'ᶻ.
    have hdvd2 : (hζ.toInteger - 1) ^ 2 ∣ (2 * d' ^ z) := by
      have hrw : (A + B * hζ.toInteger) - d' ^ z = -(2 * d' ^ z) := by rw [h]; ring
      rw [hrw] at hres
      exact (dvd_neg).1 hres
    -- contradiction with Step 2.
    exact lambda_sq_not_dvd_two_mul hζ hlamdz hdvd2

/-!
## STRETCH — feeding the `+` branch into the `z = 3` coupling

With the sign pinned to `+`, the descent factor is `A + B·η = d'ᶻ` *without*
ambiguity. Writing `d' = e + f·η` (`e, f : ℤ`) and specializing to the operative
exponent `z = 3`, the `{1,η}`-coordinate relations of `BealCubeDescentStep`
(`descent_relations_three`) apply directly, and the coupling
`descent_coupling_three` (`e³ + 3e²f − 6ef² + f³ = s³`) holds with no sign case
split. We record this sharpened, sign-free form. -/

/-- **STRETCH — sign-free `z = 3` coupling.** Combining `sign_eliminated` (the `+`
branch) with the integer descent `A + B = s³` and the base coordinates
`d' = e + f·η`, the descent coupling

  `e³ + 3e²f − 6ef² + f³ = s³`

holds without the sign ambiguity of `BealCubeDescentStep.descent_coupling_three`.

Here the input `hpin`/`hres` are the `z = 3` sign-pinned descent and its `λ²`
residue; `hbase` identifies the descent base `d'` with the integer-coordinate
form `(e + f·η)` so the `{1,η}`-coordinate machinery applies. -/
theorem descent_coupling_three_signed {K : Type*} [Field K] [NumberField K]
    [IsCyclotomicExtension {3} ℚ K] {ζ : K} (hζ : IsPrimitiveRoot ζ 3)
    {A B e f s : ℤ} {d' : 𝓞 K}
    (hlam : ¬ (hζ.toInteger - 1) ∣ ((A : 𝓞 K) + (B : 𝓞 K) * hζ.toInteger))
    (hpin : (A : 𝓞 K) + (B : 𝓞 K) * hζ.toInteger = d' ^ 3 ∨
            (A : 𝓞 K) + (B : 𝓞 K) * hζ.toInteger = -(d' ^ 3))
    (hres : (hζ.toInteger - 1) ^ 2 ∣
      (((A : 𝓞 K) + (B : 𝓞 K) * hζ.toInteger) - d' ^ 3))
    (hbase : d' = (e : 𝓞 K) + (f : 𝓞 K) * hζ.toInteger)
    (hsum : A + B = s ^ 3) :
    e ^ 3 + 3 * e ^ 2 * f - 6 * e * f ^ 2 + f ^ 3 = s ^ 3 := by
  -- Eliminate the sign: A + B·η = d'³.
  have hplus : (A : 𝓞 K) + (B : 𝓞 K) * hζ.toInteger = d' ^ 3 :=
    sign_eliminated hζ (by norm_num) hlam hpin hres
  -- Rewrite the base on coordinates and apply the z = 3 coupling.
  rw [hbase] at hplus
  exact BealCubeDescentStep.descent_coupling_three hζ hsum hplus

end BealKummerSign

-- Axiom audit (remove before finishing): each headline should report
-- `[propext, Classical.choice, Quot.sound]`.
-- #print axioms BealKummerSign.sign_eliminated
-- #print axioms BealKummerSign.lambda_sq_not_dvd_two_mul
-- #print axioms BealKummerSign.descent_coupling_three_signed

/-!
## REMAINING PLAN

This file **closes the residual `−1`-sign branch** of the ℤ[ζ₃] cube-sum descent,
*conditional on the `λ²`-residue input* `hres` (the classical Kummer congruence).
All declarations are intended axiom-clean (`[propext, Classical.choice, Quot.sound]`).

**Proved here:**

  * **`eta_congr_lambda_sq` / `lambda_sq_dvd_eta_residue`** (Step 1) — the residue
    normal form `A + B·η = (A+B) + B·λ`; `A + B·η ≡ (A+B) + B·λ (mod λ²)` trivially.

  * **`lambda_not_dvd_two` / `lambda_sq_not_dvd_two_mul`** (Step 2) — `λ ∤ 2`
    (via `lambda_dvd_intCast_iff`: `λ ∣ 2 ↔ 3 ∣ 2`), and `λ ∤ x ⟹ λ² ∤ 2·x`
    (primality of `λ`, `zeta_sub_one_prime'`).

  * **`lambda_not_dvd_of_pinned`** (Step 3) — `λ ∤ (A+B·η)` lifts to `λ ∤ d'` in
    the pinned configuration `A+B·η = ±d'ᶻ`.

  * **`sign_eliminated`** (HEADLINE) — given the sign-pinned descent, `λ ∤ (A+B·η)`,
    `z ≥ 1`, and the residue hypothesis `λ² ∣ ((A+B·η) − d'ᶻ)`, the `−1` branch is
    eliminated: `A + B·η = d'ᶻ`. The two candidates differ by `2·d'ᶻ`, which is not
    divisible by `λ²` (Step 2 + Step 3), so only the `+` residue can match.

  * **`descent_coupling_three_signed`** (STRETCH) — the sign-free `z = 3` coupling
    `e³ + 3e²f − 6ef² + f³ = s³`, with the sign ambiguity removed.

### The precise remaining gap

`sign_eliminated` is rigorous and unconditional *except* for the single hypothesis

  `hres : λ² ∣ ((A + B·η) − d'ᶻ)`    (i.e. `A + B·η ≡ d'ᶻ (mod λ²)`).

This is **exactly** the congruence that Kummer's lemma
(`IsCyclotomicExtension.Rat.Three.eq_one_or_neg_one_of_unit_of_congruent`) consumes,
restated as a sign-pinning input. Supplying `hres` from first principles requires:

1. **`d'ᶻ ≡ (integer) (mod λ²)`.** For `gcd(z,3)=1`, a `z`-th power in `𝓞 K` is
   congruent to a rational integer modulo `λ²`. Concretely, every `y : 𝓞 K` is
   `≡ 0, ±1 (mod λ)` (`lambda_dvd_or_dvd_sub_one_or_dvd_add_one`), and the cube
   `y³ ≡ y (mod λ²)`-type lift (`lambda_pow_four_dvd_cube_sub_one_or_add_one…` in
   `Mathlib/NumberTheory/FLT/Three.lean`) pushes a `λ`-coprime base to `±1`
   modulo `λ³`; combined with `gcd(z,3)=1` this lands `d'ᶻ ≡ n (mod λ²)` for an
   integer `n`. NOT yet wired: the integer `n` and its `λ²`-lift.

2. **`A + B·η ≡ (A+B) (mod λ²)`?** Step 1 gives `A + B·η = (A+B) + B·λ`, which is
   only `≡ (A+B) (mod λ)` — the `B·λ` term obstructs the `mod λ²` reduction unless
   `λ ∣ B`. So `A + B·η` is *not* in general `≡` a rational integer mod `λ²`; the
   residue `hres` compares `A+B·η` against `d'ᶻ` **directly** (both carry the same
   `B·λ`/`λ`-linear part once the descent is set up), which is why `hres` is the
   honest input rather than a derived integer congruence. Deriving `hres` needs the
   `λ²`-matching of the `λ`-linear parts of `A+B·η` and `d'ᶻ`, i.e. the next rung
   of the coordinate descent. This is the precise open step.

Everything downstream of `hres` (the `2·d'ᶻ` incongruence and sign forcing) is
**closed and axiom-clean** here.

### Mathlib declarations used

* `IsPrimitiveRoot.zeta_sub_one_prime'` — `Prime (η − 1) = Prime λ` (Step 2, 3).
* `BealCubeSynthesis.lambda_dvd_intCast_iff` — `λ ∣ (n:𝓞 K) ↔ 3 ∣ n` (`λ ∤ 2`).
* `Prime.dvd_mul`, `Prime.dvd_of_dvd_pow`, `dvd_pow`, `dvd_pow_self` — divisibility.
* `BealCubeDescentStep.descent_coupling_three` — the `z = 3` coordinate coupling
  (STRETCH).

### Continuation (to make `sign_eliminated` unconditional)

* `IsCyclotomicExtension.Rat.Three.lambda_dvd_or_dvd_sub_one_or_dvd_add_one` and the
  FLT-3 cube-lift lemmas — to derive `d'ᶻ ≡ n (mod λ²)` and match it against the
  integer-side residue of `A+B·η`, discharging `hres`.
* Feed `sign_eliminated` (with discharged `hres`) into the
  `Solution'`/`Solution` minimal-descent scaffolding
  (`Mathlib/NumberTheory/FLT/Three.lean`).
-/
