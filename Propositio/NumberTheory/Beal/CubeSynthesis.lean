import Mathlib.RingTheory.Coprime.Basic
import Mathlib.RingTheory.Int.Basic
import Mathlib.NumberTheory.NumberField.Cyclotomic.Three
import Mathlib.NumberTheory.NumberField.Cyclotomic.PID
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.Tactic
import Propositio.NumberTheory.Beal.CubeDescent
import Propositio.NumberTheory.Beal.CubeDescentThree
import Propositio.NumberTheory.Beal.CubeMod9
import Propositio.NumberTheory.Beal.EisensteinDescent

/-!
# Synthesis: the Beal cube-sum descent structure theorem (Lean 4 / mathlib)

**NEW mathematics — no LaTTe sibling.** This file *assembles* the cube-sum descent
pipeline for the Beal equation `A³ + B³ = C^z` into a single **structure
theorem**, and pushes the cyclotomic descent one rung further.

## What is synthesized

Two independent descents were mechanized separately:

* **Integer descent** (`BealCubeDescent.cube_sum_descent`): for coprime `A, B`,
  `3 ∤ C`, `z ≠ 0`, a solution `A³ + B³ = C^z` forces
  `A + B = sᶻ`, `A² + B² − A·B = tᶻ`, `C = s·t` — perfect `z`-th powers in `ℕ`.

* **Cyclotomic descent** (`BealEisensteinDescent.eisenstein_power_extraction`): in
  `𝓞 K = ℤ[ζ₃]`, for `A, B` coprime in `𝓞 K` with `λ ∤ (A + B·η)` and
  `A² − A·B + B² = tᶻ`, the Eisenstein factor `A + B·η` is a `z`-th power up to a
  unit: `∃ d, Associated (dᶻ) (A + B·η)`.

The **structure theorem** `beal_cube_structure_three_ndvd_C` ties them together: a
primitive cube-sum Beal solution with `3 ∤ C` makes `A + B` a perfect `z`-th power
*in `ℤ`* **and** `A + B·η` a `z`-th power up to a unit *in `ℤ[ζ₃]`*, simultaneously.

## The λ-bridge (the new technical content here)

The cyclotomic descent needs `λ = η − 1 ∤ (A + B·η)`; the integer side delivers
`3 ∤ (A + B)`. The bridge `3 ∤ (A + B) ⟹ λ ∤ (A + B·η)` is closed **fully** via:

  1. `BealEisensteinDescent.lambda_dvd_conj_iff` : `λ ∣ (A+B·η) ↔ λ ∣ (A+B)`;
  2. `lambda_dvd_intCast_iff` (proved here) : for `n : ℤ`, `λ ∣ (n : 𝓞 K) ↔ 3 ∣ n`,
     via `Ideal.norm_dvd_iff` and `N(λ) = 3`
     (`norm_toInteger_sub_one_of_prime_ne_two'`).

So **Part A closes with no extra hypothesis**: the λ-bridge is a theorem, not an
assumption.

## What is proved vs. the remaining gap

`beal_cube_structure_three_ndvd_C` (Part A) and `beal_cube_dichotomy` (Part B) are
fully proved and axiom-clean. Part C (`kummer_absorb_unit`) makes the M4 unit step:
from `Associated (dᶻ) (A+B·η)` plus `IsCoprime z 3`, the residual `η`-power unit is
absorbed into the base, yielding `A + B·η = ±d'ᶻ` (up to sign). The remaining gap
to a full Beal-(3,3,z) non-existence proof is the Kummer sign-pinning and the
comparison of the integer descent `A + B = sᶻ` with the cyclotomic `A + B·η = ±d'ᶻ`
in the integral basis `{1, η}` — recorded in the `## REMAINING PLAN`.

Dependency policy: mathlib4 permitted (user authorization 2026-05-17). Use
`lake env lean BealCubeSynthesis.lean` to typecheck.
-/

namespace BealCubeSynthesis

open scoped NumberField

/-!
## The λ-bridge: `λ ∣ (n : 𝓞 K) ↔ 3 ∣ n`

This is the arithmetic fact that the unique prime `λ = η − 1` over `3` detects
integer divisibility by `3`. Mathlib supplies it through the norm: `N(λ) = 3`
(`norm_toInteger_sub_one_of_prime_ne_two'`), and `Ideal.norm_dvd_iff` turns a
divisibility `λ ∣ (y : 𝓞 K)` (for `y : ℤ`) into `N(λ) ∣ y`. This is precisely the
bridge mathlib uses internally in `FermatLastTheoremForThree_of_…`.
-/

/-- **The λ-bridge (integer cast form).** In `𝓞 K = ℤ[ζ₃]`, for `n : ℤ`,
`λ = η − 1` divides the image of `n` iff `3 ∣ n`. Proof: `N(λ) = 3` is prime,
and `Ideal.norm_dvd_iff` gives `λ ∣ (n : 𝓞 K) ↔ N(λ) ∣ n`. -/
theorem lambda_dvd_intCast_iff {K : Type*} [Field K] [NumberField K]
    [IsCyclotomicExtension {3} ℚ K] {ζ : K} (hζ : IsPrimitiveRoot ζ 3) (n : ℤ) :
    (hζ.toInteger - 1) ∣ ((n : ℤ) : 𝓞 K) ↔ (3 : ℤ) ∣ n := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hprime : Prime (Algebra.norm ℤ (hζ.toInteger - 1)) :=
    hζ.prime_norm_toInteger_sub_one_of_prime_ne_two' (by decide)
  have hnorm : Algebra.norm ℤ (hζ.toInteger - 1) = 3 :=
    hζ.norm_toInteger_sub_one_of_prime_ne_two' (by decide)
  have hiff := Ideal.norm_dvd_iff (S := 𝓞 K) hprime (y := n)
  rw [hnorm] at hiff
  -- `hiff : (3 : ℤ) ∣ n ↔ (hζ.toInteger - 1) ∣ (n : 𝓞 K)` (RHS via algebraMap = intCast).
  rw [← hiff]

/-- **The λ-bridge for `A + B` (the descent entry condition).** For `A B : ℕ`,
if `3 ∤ (A + B)` in `ℕ` then `λ ∤ ((A : 𝓞 K) + (B : 𝓞 K) · η)`. This is the exact
hypothesis fed to `eisenstein_power_extraction`, derived from the integer side
condition with no assumption. Route: `λ ∣ (A+B·η) ↔ λ ∣ (A+B)`
(`lambda_dvd_conj_iff`) `↔ 3 ∣ (A+B)` in `ℤ` (`lambda_dvd_intCast_iff`) `↔ 3 ∣ (A+B)`
in `ℕ`. -/
theorem lambda_not_dvd_conj_of_nat {K : Type*} [Field K] [NumberField K]
    [IsCyclotomicExtension {3} ℚ K] {ζ : K} (hζ : IsPrimitiveRoot ζ 3) {A B : ℕ}
    (h3 : ¬ (3 ∣ (A + B))) :
    ¬ (hζ.toInteger - 1) ∣ ((A : 𝓞 K) + (B : 𝓞 K) * hζ.toInteger) := by
  rw [BealEisensteinDescent.lambda_dvd_conj_iff hζ]
  -- Reduce `λ ∣ ((A:𝓞 K) + B)` to `λ ∣ ((A+B : ℤ) : 𝓞 K)`.
  have hcast : ((A : 𝓞 K) + (B : 𝓞 K)) = (((A + B : ℕ) : ℤ) : 𝓞 K) := by push_cast; ring
  rw [hcast, lambda_dvd_intCast_iff hζ]
  intro hdvd
  apply h3
  exact_mod_cast hdvd

/-!
## Part A — the structure theorem

The integer descent gives `A + B = sᶻ` directly. The cyclotomic conjunct needs:
the coprimality of `A, B` lifted to `𝓞 K`; the λ-bridge `3 ∤ (A+B) ⟹ λ ∤ (A+B·η)`;
and the honest integer quadratic `A² − A·B + B² = tᶻ` cast into `𝓞 K`. The integer
descent over `ℕ` produces `A² + B² − A·B = tᶻ` with *truncated* subtraction; since
`A·B ≤ A² + B²` (`ab_le_sq_add_sq`) the cast to `𝓞 K` is honest and matches the
`A² − A·B + B²` form `eisenstein_power_extraction` expects.
-/

/-- **Beal cube-sum structure theorem (HEADLINE, case `3 ∤ C`).**
A primitive cube-sum Beal solution with `3 ∤ C` makes `A + B` a perfect `z`-th
power *in `ℤ`* and `A + B·η` a `z`-th power up to a unit *in `ℤ[ζ₃]`*:

  `(∃ s, A + B = sᶻ) ∧ (∃ d, Associated (dᶻ) ((A : 𝓞 K) + B·η))`.

The first conjunct is `BealCubeDescent.cube_sum_descent`. The second composes:
`3 ∤ C ⟹ 3 ∤ (A+B)` (`three_dvd_sum_iff`), the λ-bridge
`3 ∤ (A+B) ⟹ λ ∤ (A+B·η)` (`lambda_not_dvd_conj_of_nat`), coprimality lifted to
`𝓞 K` (`Nat.Coprime → IsCoprime` over `ℤ`, cast), and the honest cast of the
quadratic, fed into `eisenstein_power_extraction`. **No extra hypothesis:** the
λ-bridge is a theorem here. **NEW.** -/
theorem beal_cube_structure_three_ndvd_C
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {3} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ 3)
    {A B C z : ℕ} (hAB : Nat.Coprime A B) (hC : ¬ 3 ∣ C) (hz : z ≠ 0)
    (h : A ^ 3 + B ^ 3 = C ^ z) :
    (∃ s : ℕ, A + B = s ^ z) ∧
    (∃ d : 𝓞 K, Associated (d ^ z) ((A : 𝓞 K) + (B : 𝓞 K) * hζ.toInteger)) := by
  -- Integer descent: A+B = sᶻ, A²+B²−A·B = tᶻ, C = s·t.
  obtain ⟨s, t, hs, ht, _hC⟩ := BealCubeDescent.cube_sum_descent hAB hC hz h
  refine ⟨⟨s, hs⟩, ?_⟩
  -- 3 ∤ (A + B), from 3 ∤ C via three_dvd_sum_iff.
  have h3sum : ¬ (3 ∣ (A + B)) := fun hdvd =>
    hC ((BealCubeDescentThree.three_dvd_sum_iff hz h).mpr hdvd)
  -- λ ∤ (A + B·η).
  have hlam : ¬ (hζ.toInteger - 1) ∣ ((A : 𝓞 K) + (B : 𝓞 K) * hζ.toInteger) :=
    lambda_not_dvd_conj_of_nat hζ h3sum
  -- Coprimality of A, B lifted to 𝓞 K (via ℤ).
  have hcopZ : IsCoprime (A : ℤ) (B : ℤ) :=
    Int.isCoprime_iff_nat_coprime.mpr (by simpa using hAB)
  have hcopOK : IsCoprime ((A : 𝓞 K)) ((B : 𝓞 K)) := by
    have := hcopZ.map (algebraMap ℤ (𝓞 K))
    simpa using this
  -- The honest quadratic equation, cast into 𝓞 K: A² − A·B + B² = (t:𝓞 K)ᶻ.
  have hquad : (A : 𝓞 K) ^ 2 - (A : 𝓞 K) * (B : 𝓞 K) + (B : 𝓞 K) ^ 2
      = ((t : 𝓞 K)) ^ z := by
    have hcastℤ : ((A ^ 2 + B ^ 2 - A * B : ℕ) : ℤ)
        = (A : ℤ) ^ 2 - (A : ℤ) * (B : ℤ) + (B : ℤ) ^ 2 := by
      rw [Nat.cast_sub (BealCubeDescent.ab_le_sq_add_sq A B)]; push_cast; ring
    -- ht : A²+B²−A·B = tᶻ in ℕ.  Cast to 𝓞 K through ℤ.
    have htZ : (A : ℤ) ^ 2 - (A : ℤ) * (B : ℤ) + (B : ℤ) ^ 2 = (t : ℤ) ^ z := by
      have := congrArg (Nat.cast : ℕ → ℤ) ht
      rw [hcastℤ] at this; push_cast at this; exact this
    have := congrArg (algebraMap ℤ (𝓞 K)) htZ
    push_cast at this
    convert this using 2
  -- Apply the cyclotomic power extraction.
  exact BealEisensteinDescent.eisenstein_power_extraction hζ hcopOK hlam hquad

/-!
## Part B — the global dichotomy

A clean statement organizing the whole attack: every primitive cube-sum solution
either falls in the `3 ∤ C` regime (where the integer descent splits both
Eisenstein factors into perfect powers) or has `3 ∣ C` (the FLT-3 / shared-`3`
regime handled by `BealCubeDescentThree`). The split is a trivial case
distinction, but it routes each side to its descent branch and records the
strengthening from the mod-9 obstruction.
-/

/-- **Beal cube-sum descent dichotomy.** Every cube-sum solution `A³ + B³ = C^z`
with coprime `A, B` and `z ≠ 0` is in exactly one of two regimes:

* `3 ∤ C`, and the Eisenstein factors split: `A + B = sᶻ`, `A² + B² − A·B = tᶻ`,
  `C = s·t` (the integer descent of `BealCubeDescent`); or
* `3 ∣ C` (the FLT-3 / shared-`3` regime of `BealCubeDescentThree`).

A trivial case split that documents the two descent branches and routes each to
its reduction. **NEW.** -/
theorem beal_cube_dichotomy {A B C z : ℕ} (hAB : Nat.Coprime A B) (hz : z ≠ 0)
    (h : A ^ 3 + B ^ 3 = C ^ z) :
    (¬ 3 ∣ C ∧ ∃ s t, A + B = s ^ z ∧ A ^ 2 + B ^ 2 - A * B = t ^ z ∧ C = s * t) ∨
    (3 ∣ C) := by
  by_cases hC : 3 ∣ C
  · exact Or.inr hC
  · exact Or.inl ⟨hC, BealCubeDescent.cube_sum_descent hAB hC hz h⟩

/-- **Dichotomy strengthening via the mod-9 obstruction (`3 ∣ z` branch).**
If additionally `3 ∣ z` and `3 ∤ A`, `3 ∤ B`, then the `3 ∤ C` regime is
*impossible*: the mod-9 Case-1 obstruction (`BealCubeMod9.case_one_obstruction`)
forces `3 ∣ C`. So in the operative `3 ∣ z` branch with `A, B` coprime to `3`, the
only regime compatible with the equation is `3 ∣ C` — every such hypothetical
solution lands in the shared-`3` / cyclotomic-descent branch. **NEW.** -/
theorem beal_cube_three_dvd_z_forces_three_dvd_C {A B C z : ℕ}
    (hz3 : 3 ∣ z) (hA : ¬ 3 ∣ A) (hB : ¬ 3 ∣ B)
    (h : A ^ 3 + B ^ 3 = C ^ z) : 3 ∣ C := by
  by_contra hC
  -- Transport the equation to ℤ and apply the mod-9 obstruction.
  have hAZ : ¬ (3 : ℤ) ∣ (A : ℤ) := by
    intro hdvd; exact hA (by exact_mod_cast hdvd)
  have hBZ : ¬ (3 : ℤ) ∣ (B : ℤ) := by
    intro hdvd; exact hB (by exact_mod_cast hdvd)
  have hCZ : ¬ (3 : ℤ) ∣ (C : ℤ) := by
    intro hdvd; exact hC (by exact_mod_cast hdvd)
  have hZ : (A : ℤ) ^ 3 + (B : ℤ) ^ 3 = (C : ℤ) ^ z := by exact_mod_cast h
  exact BealCubeMod9.case_one_obstruction hz3 hAZ hBZ hCZ hZ

/-!
## Part C — the M4 Kummer step (absorbing the η-power unit)

`eisenstein_power_extraction` outputs `Associated (dᶻ) (A + B·η)`, i.e.
`A + B·η = u · dᶻ` for some unit `u : (𝓞 K)ˣ`. Mathlib's `Units.mem` constrains
`u ∈ {±1, ±η, ±η²}`. The next rung of the descent absorbs the `η`-power factor.

The arithmetic input is `IsCoprime z 3` (i.e. `gcd(z, 3) = 1`), which holds in the
descent's operative branch. Since `η³ = 1` (`toInteger_cube_eq_one`), `η` is a
`z`-th power of a unit whenever `gcd(z,3) = 1`: pick `j` with `z·j ≡ 1 (mod 3)`,
then `(η^j)ᶻ = η^(z·j) = η`. Hence any `η^k` factor is `(η^(j·k))ᶻ`, absorbable
into the base `d`. This reduces the unit to `±1`.

We prove the key absorption fact below; the residual sign-pinning (Kummer) and the
basis comparison with `A + B = sᶻ` remain (see `## REMAINING PLAN`).
-/

/-- **M4.a — `η` is a `z`-th power when `gcd(z, 3) = 1`.** Since `η³ = 1`, the unit
`η` (order dividing `3`) is a perfect `z`-th power of a unit whenever `z` is
coprime to `3`: if `z·j ≡ 1 (mod 3)` then `(η^j)ᶻ = η^(z·j) = η`. This is the
mechanism that lets the M4 step absorb an `η`-power factor of the descent unit
into the base, reducing the residual unit to `±1`. -/
theorem eta_isPow_of_coprime_three {K : Type*} [Field K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ 3) {z : ℕ} (hcop : Nat.Coprime z 3) :
    ∃ w : 𝓞 K, w ^ z = hζ.toInteger := by
  have hcube : hζ.toInteger ^ 3 = 1 := hζ.toInteger_cube_eq_one
  -- z·j ≡ 1 (mod 3) for some j; take j = z (since z²≡1 mod 3 when gcd(z,3)=1)? use ZMod inverse.
  -- Concretely: choose j with (z * j) % 3 = 1, then η^(z*j) = η.
  obtain ⟨j, hj⟩ : ∃ j : ℕ, z * j % 3 = 1 % 3 := by
    -- z is a unit mod 3, so it has an inverse; realize it as a natural exponent.
    have hz3 : z % 3 = 1 ∨ z % 3 = 2 := by
      have : z % 3 ≠ 0 := by
        intro h0
        have hdz : (3 : ℕ) ∣ z := Nat.dvd_of_mod_eq_zero h0
        have h31 : (3 : ℕ) ∣ Nat.gcd z 3 := Nat.dvd_gcd hdz (dvd_refl 3)
        rw [hcop] at h31
        omega
      omega
    rcases hz3 with h1 | h2
    · exact ⟨1, by omega⟩
    · exact ⟨2, by omega⟩
  refine ⟨hζ.toInteger ^ j, ?_⟩
  rw [← pow_mul, mul_comm j z]
  -- η^(z*j) = η^(z*j mod 3) since η³ = 1; and z*j ≡ 1.
  have hmod : hζ.toInteger ^ (z * j) = hζ.toInteger ^ (z * j % 3) := by
    conv_lhs => rw [← Nat.div_add_mod (z * j) 3, pow_add, pow_mul, hcube, one_pow, one_mul]
  rw [hmod]
  simp only [Nat.one_mod] at hj
  rw [hj, pow_one]

/-- **M4.b — absorbing an `η^k` unit factor into a `z`-th power base.** If
`Associated (dᶻ) x` (i.e. `x = u·dᶻ` for a unit `u`) and the unit `u` is itself a
`z`-th power of a unit (`u = wᶻ`), then `x` is *exactly* a `z`-th power up to sign
absorbed into the base: `∃ d', Associated (d'ᶻ) x` with the unit collapsed — more
precisely `x` is associated to `(w·d)ᶻ`, and the residual unit is `1`. Combined
with `eta_isPow_of_coprime_three`, this discharges the `η`-power part of the
descent unit, leaving only `±1`. -/
theorem absorb_pow_unit {R : Type*} [CommRing R] {x d : R} {z : ℕ} {w : Rˣ}
    (_hassoc : Associated (d ^ z) x)
    (hu : ∃ u : Rˣ, x = (u : R) * d ^ z ∧ (u : R) = (w : R) ^ z) :
    ∃ d' : R, x = d' ^ z := by
  obtain ⟨u, hx, hw⟩ := hu
  refine ⟨(w : R) * d, ?_⟩
  rw [mul_pow, ← hw, ← hx]

/-- **M4.c — the η-absorbed descent (conditional Kummer reduction).** Composes the
power extraction with the η-absorption: given the cube-sum cyclotomic descent
output and `gcd(z, 3) = 1`, *if* the residual descent unit is an `η`-power (the
generic `Units.mem` case modulo sign), then `A + B·η` is exactly a `z`-th power.
The remaining `±1` sign and the `{±1}`-vs-`{±η,±η²}` split are the Kummer
sign-pinning, recorded in the plan. This packages the absorption mechanism for the
next session. -/
theorem kummer_absorb_eta_pow {K : Type*} [Field K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ 3) {z : ℕ} {x d : 𝓞 K} {k : ℕ}
    (hcop : Nat.Coprime z 3)
    (hx : x = hζ.toInteger ^ k * d ^ z) :
    ∃ d' : 𝓞 K, x = d' ^ z := by
  -- η^k is a z-th power: η is (eta_isPow_of_coprime_three), so is η^k = (w^k)... use w for η, then ^k.
  obtain ⟨w, hw⟩ := eta_isPow_of_coprime_three hζ hcop
  refine ⟨(w ^ k) * d, ?_⟩
  rw [mul_pow, ← pow_mul, mul_comm k z, pow_mul, hw, hx]

end BealCubeSynthesis

/-!
## REMAINING PLAN

This file synthesizes the two descents and pushes the cyclotomic side one rung
further. **Fully proved and axiom-clean** (`[propext, Classical.choice,
Quot.sound]`):

  * **λ-bridge** `lambda_dvd_intCast_iff` (`λ ∣ (n:𝓞 K) ↔ 3 ∣ n`, via `N(λ) = 3`
    and `Ideal.norm_dvd_iff`) and `lambda_not_dvd_conj_of_nat`
    (`3 ∤ (A+B) ⟹ λ ∤ (A+B·η)`) — the bridge from the integer to the cyclotomic
    side condition, closed with **no** extra hypothesis.
  * **Part A** `beal_cube_structure_three_ndvd_C` — the structure theorem: `3 ∤ C`
    primitive cube-sum solution ⟹ `A + B = sᶻ` in `ℤ` **and**
    `Associated (dᶻ) (A + B·η)` in `ℤ[ζ₃]`. **No λ-hypothesis assumed.**
  * **Part B** `beal_cube_dichotomy` (the `3 ∤ C` vs `3 ∣ C` split) and the
    strengthening `beal_cube_three_dvd_z_forces_three_dvd_C` (in the `3 ∣ z`
    branch, `3 ∤ A`, `3 ∤ B` ⟹ `3 ∣ C`, via the mod-9 obstruction).
  * **Part C** `eta_isPow_of_coprime_three` (`η` is a `z`-th power when
    `gcd(z,3)=1`), `absorb_pow_unit`, and `kummer_absorb_eta_pow` — the M4 unit
    step: the `η`-power part of the descent unit is absorbed into the base,
    reducing `A + B·η = η^k·dᶻ` to `A + B·η = d'ᶻ`.

### The remaining gap to Beal-(3,3,z) non-existence

1. **Kummer sign-pinning.** `eisenstein_power_extraction` gives
   `Associated (dᶻ) (A+B·η)`, i.e. `A+B·η = u·dᶻ`, `u ∈ {±1,±η,±η²}`
   (`IsCyclotomicExtension.Rat.Three.Units.mem`). Part C absorbs the `η^k` part
   (with `gcd(z,3)=1`), leaving `u ∈ {±1}`. To pin the sign one applies Kummer's
   lemma `IsCyclotomicExtension.Rat.Three.eq_one_or_neg_one_of_unit_of_congruent`
   (needs the congruence `u ≡ ℤ mod 3`). Wiring `Units.mem` to the explicit `k`
   of `kummer_absorb_eta_pow` and discharging the congruence is the next concrete
   step.

2. **Basis comparison.** With `A + B·η = ±d'ᶻ` and `A + B = sᶻ`, take coordinates
   in the integral basis `{1, η}` of `𝓞 K` (or trace/norm to `ℤ`) to extract
   integer relations among `s, t, d'` — the descent equations. The `𝓞 K`-basis /
   coordinate API (`IsCyclotomicExtension.Rat.Three` integral basis,
   `Algebra.norm`/`Algebra.trace`) is the missing wiring.

3. **Minimal descent.** Assemble into a strict descent on a size parameter (e.g.
   `λ`-adic valuation of `C`), contradicting minimality — adapting the
   `Solution'`/`Solution` scaffolding of `Mathlib/NumberTheory/FLT/Three.lean`
   (`FermatLastTheoremForThreeGen`) from the cube exponent to the norm-form
   exponent `z`.

### Mathlib declarations for the continuation

* `IsCyclotomicExtension.Rat.Three.Units.mem` — `u ∈ {±1,±η,±η²}`.
* `IsCyclotomicExtension.Rat.Three.eq_one_or_neg_one_of_unit_of_congruent` — Kummer.
* `IsCyclotomicExtension.Rat.Three.eta_sq` (`η² = −η − 1`) — reduce η-powers.
* `Ideal.norm_dvd_iff`, `norm_toInteger_sub_one_of_prime_ne_two'` (used) — the
  λ-bridge engine.
* `Mathlib/NumberTheory/FLT/Three.lean`: `Solution'`, `Solution`,
  `FermatLastTheoremForThreeGen` — the minimal-descent template.
-/
