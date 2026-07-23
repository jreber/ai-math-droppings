import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Propositio.NumberTheory.Beal.LambdaCongruence

/-!
# The λ⁴ Kummer congruence for ℚ(ζ₅): the *conditional* truth, and the converse core

This file settles what is actually true about the "λ⁴ Kummer congruence" underlying the
Beal `(5,5,z)` descent, correcting a mis-statement in the research feed
(`conj-2026-06-29-005`) and supplying the genuinely new *converse* content.

## The plain-language target and what is actually true

The conjecture card reads: *"every unit of ℤ[ζ₅] is ≡ a rational integer mod λ⁴,
λ = 1−ζ₅."*  **As literally stated this is FALSE.**  Two explicit counterexamples,
both units of `𝓞(ℚ(ζ₅))`:

* `ζ₅` itself: `ζ₅ = 1 − λ`, so `ζ₅ − m` has λ-valuation `1` for every rational integer
  `m` (valuation `0` if `5 ∤ m`, valuation `1` from the `λ`-term if `5 ∣ m`) — never `≥ 4`.
* the golden unit `φ = 1 + ζ₅ + ζ₅⁴ = −ζ₅² − ζ₅³` (fundamental unit of the real subfield
  ℤ[ζ₅]⁺): `φ − 3 = λ²·ζ₅⁴` has λ-valuation exactly `2`, so `φ ≢ (integer) (mod λ⁴)`.

(The second computation is `BealLambdaCongruence.phi_mod_lambda_sq`; the ideal `(λ⁴) = (5)`
since `5` is totally ramified with `e = 4`, `N(λ) = 5`.)

So the "mod λ⁴" congruence is **selective**, not universal.  The correct statement, for the
real-unit powers `φⁿ` that actually arise in the descent, is the equivalence

  **`φⁿ ≡ (rational integer) (mod λ⁴)   ⟺   5 ∣ n`.**

The `⟸` direction is `BealLambdaCongruence.phi_pow_cong_mod_lambda4_of_five_dvd`
(and its ring form).  This file supplies the structural reduction and the arithmetic heart
of the `⟹` direction.

## Why this is *not* Baker-class (the breaking-monoculture finding)

Prior attempts flagged the "λ-adic valuation" route as "Baker-class."  That is a
mis-diagnosis.  The exact expansion `BealLambdaCongruence.phi_pow_mod_lambda4_ring`,

  `φⁿ − 3ⁿ = λ²·(n·3ⁿ⁻¹·ζ₅⁴) + λ⁴·c`,

pins the entire obstruction into the single λ²-coefficient `n·3ⁿ⁻¹·ζ₅⁴`.  Reducing to the
**finite** local ring `𝓞K/(λ⁴) ≅ 𝔽₅[s]/(s⁴)` (625 elements, `s = λ`), the golden unit
becomes `φ̄ = 3 + s² + s³`, and a direct finite computation gives
`φ̄ⁿ = 3ⁿ + 3ⁿ·2n·(s² + s³)`, which is a constant (i.e. `≡ rational integer`) iff
`3ⁿ·2n ≡ 0 (mod 5)` iff `5 ∣ n`.  This is a *decidable finite-ring* fact, not an infinite
descent.  The only genuinely non-elementary ingredient in transferring it back to `𝓞K` is

  **for a rational integer `m`, `λ² ∣ m ⟹ 5 ∣ m`,**

which is *elementary via norms*: `N(λ) = Φ₅(1) = 5`, so `λ² ∣ m` in `𝓞K` gives
`25 = N(λ²) ∣ N(m) = m⁴`, hence `5 ∣ m`.  No Baker theory, no Thaine annihilator — that
wall lives one level up, in extracting `z ∣ n` (which the λ-congruence does **not** force).

## What this file proves (all axiom-clean, `[propext, Classical.choice, Quot.sound]`)

1. `obstruction_zmod5` — the arithmetic heart of the converse: for `n : ℕ`,
   `(n : ZMod 5) · 3ⁿ⁻¹ = 0 ↔ 5 ∣ n`.  (`3ⁿ⁻¹` is a unit mod 5, so the product vanishes
   iff `n ≡ 0`.)  This is the `𝔽₅[s]/(s⁴)`-level obstruction made precise.

2. `golden_pow_cong_lambda4_iff_coeff` — the structural reduction, in any `CommRing`:
   `φⁿ ≡ 3ⁿ (mod λ⁴) ↔ the λ²-coefficient `λ²·(n·3ⁿ⁻¹·ζ⁴)` is itself divisible by λ⁴`.
   This isolates the obstruction elementarily (no valuation, no field, no norms), and is the
   honest half of the `⟺` that stays inside identity-level algebra.

3. `golden_pow_cong_lambda4_of_five_dvd` — a direct one-line restatement of the pre-existing
   `BealLambdaCongruence.phi_pow_cong_mod_lambda4_five_dvd_ring` under this file's naming.
   Does NOT itself go through reduction (2) — no new content, kept only so theorem 4 below
   has a same-file name to compose with.

4. `coeff_lambda4_dvd_of_five_dvd` — composes (2) and (3) via `.mp`; THIS is where the
   reduction (2) actually gets used to reach the coefficient-divisibility form.
-/

namespace BealKummerLambda4Congruence

/-! ## 1. The arithmetic heart of the converse (finite quotient `𝔽₅[s]/(s⁴)` level) -/

/-- **`(n : ZMod 5)·3ⁿ⁻¹ = 0 ↔ 5 ∣ n`.**

This is the exact obstruction controlling `φⁿ ≡ (rational integer) (mod λ⁴)`.  In the finite
local ring `𝓞K/(λ⁴) ≅ 𝔽₅[s]/(s⁴)` the golden power is `φ̄ⁿ = 3ⁿ + 3ⁿ·2n·(s²+s³)`; it is a
constant (a rational integer residue) precisely when the `s²`-coefficient `3ⁿ·2n` vanishes
in `𝔽₅`.  Since `3` is a unit mod `5`, that coefficient — equivalently `n·3ⁿ⁻¹` — vanishes
iff `5 ∣ n`. -/
theorem obstruction_zmod5 (n : ℕ) :
    ((n : ZMod 5) * (3 : ZMod 5) ^ (n - 1) = 0) ↔ 5 ∣ n := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have h3 : IsUnit (3 : ZMod 5) := by
    have h : (3 : ZMod 5) = ((3 : ℕ) : ZMod 5) := by norm_num
    rw [h, ZMod.isUnit_iff_coprime]; decide
  have hu : IsUnit ((3 : ZMod 5) ^ (n - 1)) := h3.pow _
  rw [mul_comm, hu.mul_right_eq_zero]
  exact ZMod.natCast_eq_zero_iff n 5

/-! ## 2. The structural reduction: ring congruence ⟺ coefficient divisibility -/

/-- **`φⁿ ≡ 3ⁿ (mod λ⁴) ↔ λ⁴ ∣ λ²·(n·3ⁿ⁻¹·η⁴)`**, in any `CommRing`.

Starting from the *exact* expansion
`φⁿ − 3ⁿ = λ²·(n·3ⁿ⁻¹·η⁴) + λ⁴·c₀` (`BealLambdaCongruence.phi_pow_mod_lambda4_ring`),
the mod-`λ⁴` congruence of `φⁿ` to the rational integer `3ⁿ` is *logically equivalent* to
the λ²-coefficient being absorbed into `λ⁴`.  This is a pure identity-level reduction — no
valuation, no field, no norm — that isolates the entire obstruction into the single
coefficient `n·3ⁿ⁻¹·η⁴`.  Combined with `obstruction_zmod5` (which shows that coefficient
vanishes in the residue field iff `5 ∣ n`) it exhibits the true `⟺ 5 ∣ n` characterisation. -/
theorem golden_pow_cong_lambda4_iff_coeff {R : Type*} [CommRing R] [IsDomain R] {η : R}
    (h5 : η ^ 5 = 1) (hne1 : η ≠ 1) (n : ℕ) :
    (∃ c : R, (1 + η + η ^ 4) ^ n - (3 : R) ^ n = (1 - η) ^ 4 * c) ↔
    (∃ c : R, (1 - η) ^ 2 * ((n : R) * (3 : R) ^ (n - 1) * η ^ 4) = (1 - η) ^ 4 * c) := by
  obtain ⟨c0, hc0⟩ := BealLambdaCongruence.phi_pow_mod_lambda4_ring h5 hne1 n
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c - c0, ?_⟩
    have hco : (1 - η) ^ 2 * ((n : R) * (3 : R) ^ (n - 1) * η ^ 4)
        = ((1 + η + η ^ 4) ^ n - (3 : R) ^ n) - (1 - η) ^ 4 * c0 := by
      linear_combination -hc0
    rw [hco, hc]; ring
  · rintro ⟨c, hc⟩
    refine ⟨c + c0, ?_⟩
    rw [hc0, hc]; ring

/-! ## 3. The `⟸` direction, restated (a direct alias, NOT routed through the reduction) -/

/-- **`5 ∣ n ⟹ φⁿ ≡ 3ⁿ (mod λ⁴)`.**

This is a direct one-line restatement of the already-proved
`BealLambdaCongruence.phi_pow_cong_mod_lambda4_five_dvd_ring` under this file's naming — it
does NOT go through `golden_pow_cong_lambda4_iff_coeff` (that composition happens in
`coeff_lambda4_dvd_of_five_dvd` below, via `.mp`). No new mathematical content; kept here
only so `coeff_lambda4_dvd_of_five_dvd` has a same-file name to compose with. -/
theorem golden_pow_cong_lambda4_of_five_dvd {R : Type*} [CommRing R] [IsDomain R] {η : R}
    (h5 : η ^ 5 = 1) (hne1 : η ≠ 1) (n : ℕ) (hdvd : 5 ∣ n) :
    ∃ c : R, (1 + η + η ^ 4) ^ n - (3 : R) ^ n = (1 - η) ^ 4 * c :=
  BealLambdaCongruence.phi_pow_cong_mod_lambda4_five_dvd_ring h5 hne1 n hdvd

/-! ## 4. The coefficient is λ⁴-divisible exactly when `5 ∣ n` (both directions bundled)

The forward half is elementary (via `5 = λ⁴·(−1−η+η³)`); the reverse half is the norm fact
`N(λ) = 5` transferred to the coefficient, and is *not* expressible at the bare-`CommRing`
identity level — it requires the finite quotient / norm structure documented above.  We
record the forward half, which is what the descent's `⟸` direction consumes. -/

/-- **`5 ∣ n ⟹ λ⁴ ∣ λ²·(n·3ⁿ⁻¹·η⁴)`** (the coefficient absorbs into `λ⁴`). -/
theorem coeff_lambda4_dvd_of_five_dvd {R : Type*} [CommRing R] [IsDomain R] {η : R}
    (h5 : η ^ 5 = 1) (hne1 : η ≠ 1) (n : ℕ) (hdvd : 5 ∣ n) :
    ∃ c : R, (1 - η) ^ 2 * ((n : R) * (3 : R) ^ (n - 1) * η ^ 4) = (1 - η) ^ 4 * c :=
  (golden_pow_cong_lambda4_iff_coeff h5 hne1 n).mp
    (golden_pow_cong_lambda4_of_five_dvd h5 hne1 n hdvd)

#print axioms obstruction_zmod5
#print axioms golden_pow_cong_lambda4_iff_coeff
#print axioms golden_pow_cong_lambda4_of_five_dvd
#print axioms coeff_lambda4_dvd_of_five_dvd

end BealKummerLambda4Congruence
