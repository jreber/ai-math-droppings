import Mathlib.RingTheory.Coprime.Basic
import Mathlib.RingTheory.Int.Basic
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.NumberTheory.NumberField.Cyclotomic.PID
import Mathlib.Tactic
import Propositio.Beal.FiveStructure
import Propositio.Beal.PrimeDescentFiveFull

/-!
# M4 (interface, `p = 5`): the sharpest CONDITIONAL (5,5,z) descent and the typed UNIT gap

This file is the **typed interface** for the remaining gap of the ℤ[ζ₅] fifth-power-sum
descent. It is the `p = 5` analogue of `BealLambdaInterface` (`p = 3`). It takes the
proved structure theorem `BealFiveStructure.beal_55z_structure` —

  `5 ∤ (A + B)` primitive `(5,5,z)` solution ⟹
    `(∃ s, A + B = sᶻ) ∧ (∃ d, Associated (dᶻ) (A + B·η))`

— and isolates **exactly** the input the elementary descent cannot supply at `p = 5`:
the **pinning of the descent unit** in `A + B·η = u · dᶻ`, as a named, minimal,
typed hypothesis. Nothing here is faked: every unproved fact is a typed hypothesis,
and every theorem is axiom-clean (`[propext, Classical.choice, Quot.sound]`).

## Why `p = 5` is genuinely harder than `p = 3` (the source of the gap)

For `p = 3`, `ℤ[ζ₃]` has a **finite** unit group (`{±1, ±η, ±η²}`), so the descent
unit collapses to a *sign* (`BealCubeDescentStep.unit_pinned_to_sign`), and the whole
residue gap is one λ²-congruence (`BealLambdaInterface.cube_plus_branch_of_residue`).

For `p = 5`, `ℤ[ζ₅]` has unit rank `1` — an **infinite** unit group: the `10` roots of
unity `±ζ^i` together with a *real fundamental unit* of Pell type from the real
subfield `ℚ(√5)`. So `Associated (dᶻ) (A + B·η)` gives `A + B·η = u·dᶻ` for a unit `u`
that is **not** merely a root of unity; pinning `u` is *not* a finite sign-check. It
needs a real-embedding / absolute-value argument plus a λ-residue (Kummer) congruence.
That is the gap this file exposes as a typed hypothesis.

## The interface hypothesis (the documented gap)

For the descent unit `u : (𝓞 K)ˣ` and base `d : 𝓞 K` produced by the structure
theorem, the minimal TRUE sufficient condition we name is

  `H(u) : ∃ ε : (𝓞 K)ˣ, (u : 𝓞 K) = ε ^ z`     (the descent unit is a `z`-th power of a unit).

This is *exactly* what is needed to absorb `u` into the `z`-th power: if `u = εᶻ` then
`A + B·η = (d·ε)ᶻ`, a clean `z`-th power, with the integer descent `A + B = sᶻ` retained.
Classically `H(u)` is what the **Kummer congruence** (real-unit + λ-residue argument)
must establish at `p = 5`; mathlib carries **no `Five` Kummer lemma**, so it stays a
typed hypothesis, never asserted. `five_unit_gap_characterization` shows `H(u)` is
*equivalent* to the perfect-`z`-th-power conclusion, so it is genuine extra input —
not derivable from the structure theorem alone.

## What this file delivers

1. **`five_descent_to_unit`** — the proved, unconditional half: a `5 ∤ (A + B)`
   primitive `(5,5,z)` solution yields a base `d : 𝓞 K` and an explicit descent unit
   `u : (𝓞 K)ˣ` with `A + B·η = u · dᶻ` and the integer descent `A + B = sᶻ`. (Unpacks
   the `Associated` of the structure theorem; records `u`.)

2. **`five_plus_branch_of_unit_pinned`** (HEADLINE, the sharpest conditional) — given a
   `5 ∤ (A + B)` primitive `(5,5,z)` solution and the **single** explicit unit-pinning
   hypothesis `H(u)`, the perfect-`z`-th-power branch is forced:
   `A + B·η = Dᶻ` (some `D : 𝓞 K`) with `A + B = sᶻ`. This is the descent *with the
   unit gap discharged by exactly `H(u)`* — the tightest conditional (5,5,z) statement.

3. **`five_unit_gap_characterization`** (the honest localization) — for the descent
   base/unit `(d, u)`, `H(u) ↔ A + B·η` is a `z`-th power *associated to `dᶻ`*. This
   makes the remaining gap fully explicit: pinning the unit is *the same proposition*
   as the perfect-power conclusion, so it cannot be derived from the structure theorem.

4. **`five_unit_pinned_trivial_exponent`** (the UNCONDITIONAL sub-case, `z = 1`) — for
   exponent `z = 1` the unit gap is vacuous: `u = u^1`, so `H(u)` holds with `ε = u`
   and the descent is `A + B·η = (d·u)¹` unconditionally. (The `p = 5` analogue of the
   Case-2 corollary: the one exponent where the elementary descent closes outright.)

## What remains OPEN, and why

The hypothesis `H(u)` is **open for general `z` and `A, B`** — it is the infinite-unit
pinning for `ℤ[ζ₅]`:

* The descent unit `u` lives in a group of unit rank `1`; absorbing it into a `z`-th
  power requires showing `u` is itself a `z`-th power of a unit, which is **false in
  general** for an arbitrary unit and requires the specific number-theoretic input that
  the **Kummer congruence** supplies — a real-place (absolute-value) argument on the
  fundamental unit *together with* a λ-residue congruence mod `λ²`.
* mathlib has **no `Five` analogue** of
  `IsCyclotomicExtension.Rat.Three.eq_one_or_neg_one_of_unit_of_congruent`, so there is
  no elementary derivation of `H(u)`; it is genuine extra input.
* For prime `z`, supplying `H(u)` is precisely the `(5,5,z)` analogue of Kraus's modular
  input (Frey curve / level lowering) — there is no elementary route, which is why this
  stays a typed hypothesis rather than a theorem.

So `five_plus_branch_of_unit_pinned` is the exact point at which the elementary
`p = 5` descent terminates and the unit/Kummer (modular) input must enter.

`lake env lean BealFiveUnitInterface.lean` to typecheck (SLOW, cyclotomic imports).
-/

namespace BealFiveUnitInterface

open scoped NumberField

/-!
## Part 1 — the proved, unconditional half: structure theorem ⟹ explicit descent unit

`beal_55z_structure` gives `A + B = sᶻ` and `Associated (dᶻ) (A + B·η)`. Unfolding
`Associated` (`x ~ᵤ y ↔ ∃ u : (𝓞 K)ˣ, x * u = y`) extracts the explicit unit form
`A + B·η = dᶻ · u`, i.e. the descent base times the named descent unit `u`. No pinning
hypothesis is used here; the unit `u` is the *output* we must later pin.
-/

/-- **The unconditional descent-to-unit assembly, `p = 5`.** A primitive `(5,5,z)`
Beal solution `A⁵ + B⁵ = C^z` with `5 ∤ (A + B)` and `z ≠ 0` produces a descent base
`d : 𝓞 K` and an explicit **descent unit** `u : (𝓞 K)ˣ` with:

* the integer descent `A + B = sᶻ` (some `s : ℕ`),
* the explicit cyclotomic descent `A + B·η = dᶻ · u`.

Everything here is proved unconditionally; the only remaining ambiguity is the unit
`u`, addressed by the unit-pinning hypothesis below. The `p = 5` analogue of
`BealLambdaInterface.cube_descent_to_sign`, except the residual ambiguity is an
infinite-group unit `u`, not a finite sign. -/
theorem five_descent_to_unit
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {5} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ 5)
    {A B C z : ℕ} (hAB : Nat.Coprime A B) (h5 : ¬ 5 ∣ (A + B)) (hz : z ≠ 0)
    (h : A ^ 5 + B ^ 5 = C ^ z) :
    ∃ (s : ℕ) (d : 𝓞 K) (u : (𝓞 K)ˣ),
      A + B = s ^ z ∧
      (A : 𝓞 K) + (B : 𝓞 K) * hζ.toInteger = d ^ z * (u : 𝓞 K) := by
  obtain ⟨⟨s, hs⟩, ⟨d, u, hu⟩⟩ := BealFiveStructure.beal_55z_structure hζ hAB h5 hz h
  exact ⟨s, d, u, hs, hu.symm⟩

/-!
## Part 2 — HEADLINE: the sharpest conditional (5,5,z) statement

We feed the explicit descent `A + B·η = dᶻ · u` the **single** extra hypothesis
`H(u) : ∃ ε : (𝓞 K)ˣ, (u : 𝓞 K) = εᶻ` (the descent unit is a `z`-th power of a unit).
Then `dᶻ · u = dᶻ · εᶻ = (d·ε)ᶻ`, a clean `z`-th power. This is the tightest
conditional (5,5,z) statement: the entire remaining gap is the typed hypothesis `H(u)`.
-/

/-- **HEADLINE — `five_plus_branch_of_unit_pinned`.** The sharpest CONDITIONAL (5,5,z)
descent statement. A primitive `(5,5,z)` Beal solution `A⁵ + B⁵ = C^z` with
`5 ∤ (A + B)`, `z ≠ 0`, admits a descent base `d : 𝓞 K`, descent unit `u : (𝓞 K)ˣ`,
and integer `s : ℕ` with `A + B = sᶻ`, such that:

  **IF** the explicit unit-pinning hypothesis
    `H(u) : ∃ ε : (𝓞 K)ˣ, (u : 𝓞 K) = εᶻ`   (the descent unit is a `z`-th power of a unit)
  holds, **THEN** the perfect-`z`-th-power descent identity holds:
    `∃ D : 𝓞 K, A + B·η = Dᶻ`   (with `A + B = sᶻ`).

The hypothesis `H(u)` is the *only* gap: it is exactly what absorbs the infinite-group
descent unit into the `z`-th power, the `p = 5` analogue of the Kummer sign-pinning of
`p = 3`. By `five_unit_gap_characterization` it is equivalent to the perfect-power
conclusion, so it is honest extra input — at `p = 5` it requires the real-unit / Kummer
congruence (no mathlib `Five` Kummer lemma), supplied elementarily only when `z = 1`
(`five_unit_pinned_trivial_exponent`), and by the modular method for prime `z`.

The statement quantifies `d`, `u`, `s` existentially with `H(u)` *inside* the
existential body, so it reads "there is a descent unit for which `H` suffices" — the
typed interface to the unit/Kummer input. -/
theorem five_plus_branch_of_unit_pinned
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {5} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ 5)
    {A B C z : ℕ} (hAB : Nat.Coprime A B) (h5 : ¬ 5 ∣ (A + B)) (hz : z ≠ 0)
    (h : A ^ 5 + B ^ 5 = C ^ z) :
    ∃ (s : ℕ) (d : 𝓞 K) (u : (𝓞 K)ˣ),
      A + B = s ^ z ∧
      (A : 𝓞 K) + (B : 𝓞 K) * hζ.toInteger = d ^ z * (u : 𝓞 K) ∧
      ((∃ ε : (𝓞 K)ˣ, (u : 𝓞 K) = ε ^ z) →
       ∃ D : 𝓞 K, (A : 𝓞 K) + (B : 𝓞 K) * hζ.toInteger = D ^ z) := by
  obtain ⟨s, d, u, hs, hu⟩ := five_descent_to_unit hζ hAB h5 hz h
  refine ⟨s, d, u, hs, hu, ?_⟩
  rintro ⟨ε, hε⟩
  refine ⟨d * (ε : 𝓞 K), ?_⟩
  rw [hu, hε, mul_pow]

/-!
## Part 3 — the honest localization of the gap

For the descent base/unit `(d, u)` of the explicit descent, the unit gap `H(u)` is
logically *equivalent* to the conclusion that `A + B·η` is a `z`-th power associated to
`dᶻ`. This is the most explicit statement of the remaining gap: discharging `H(u)` is
*exactly* exhibiting the perfect-power descent. The `p = 5` analogue of
`BealLambdaInterface.residue_gap_iff_plus_branch`.
-/

/-- **`five_unit_gap_characterization`** (the explicit gap). A primitive `(5,5,z)`
solution with `5 ∤ (A + B)`, `z ≠ 0` produces a base `d` and descent unit `u` (with
`A + B = sᶻ` and `A + B·η = dᶻ·u`) for which the unit gap is *equivalent* to the
perfect-power branch:

  `(∃ ε : (𝓞 K)ˣ, (u : 𝓞 K) = εᶻ)  ↔  (∃ D : 𝓞 K, A + B·η = Dᶻ ∧ Associated D d)`.

So the remaining gap `H(u)` is the same proposition as the descent conclusion (a `z`-th
power associated to the base `d`) — it cannot be derived from the structure theorem
(that would be circular), and is the genuine extra (real-unit / Kummer / modular) input.

(The `Associated D d` rider records that the perfect-power base `D` is `d` up to a unit,
which is forced: `D = d·ε`. The reverse direction reads off `ε` from any such `D`, using
that `dᶻ·u = Dᶻ` and `D = d·ε` give `u = εᶻ` after cancelling `dᶻ` — done at the level of
units, with no `five_coords_unique` coordinate computation needed, since the unit
equation is already exact.) -/
theorem five_unit_gap_characterization
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {5} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ 5)
    {A B C z : ℕ} (hAB : Nat.Coprime A B) (h5 : ¬ 5 ∣ (A + B)) (hz : z ≠ 0)
    (h : A ^ 5 + B ^ 5 = C ^ z) :
    ∃ (s : ℕ) (d : 𝓞 K) (u : (𝓞 K)ˣ),
      A + B = s ^ z ∧
      (A : 𝓞 K) + (B : 𝓞 K) * hζ.toInteger = d ^ z * (u : 𝓞 K) ∧
      ((∃ ε : (𝓞 K)ˣ, (u : 𝓞 K) = ε ^ z) ↔
       (∃ D : 𝓞 K, (A : 𝓞 K) + (B : 𝓞 K) * hζ.toInteger = D ^ z ∧ Associated D d)) := by
  obtain ⟨s, d, u, hs, hu⟩ := five_descent_to_unit hζ hAB h5 hz h
  refine ⟨s, d, u, hs, hu, ?_, ?_⟩
  · -- forward: H(u) ⟹ perfect power D = d·ε, associated to d (via the unit ε⁻¹).
    rintro ⟨ε, hε⟩
    refine ⟨d * (ε : 𝓞 K), ?_, ?_⟩
    · rw [hu, hε, mul_pow]
    · -- Associated (d·ε) d : the unit ε⁻¹ moves d·ε to d.
      exact ⟨ε⁻¹, by rw [mul_assoc]; simp⟩
  · -- reverse: a perfect power associated to d gives u = (ε⁻¹)ᶻ, i.e. H(u) with ε⁻¹.
    rintro ⟨D, hD, ε, hDε⟩
    -- hDε : D * ↑ε = d, so d = D·ε, dᶻ = Dᶻ·εᶻ; matched against Dᶻ gives, as units, εᶻ·u = 1.
    refine ⟨ε⁻¹, ?_⟩
    -- From hu and hD: dᶻ·u = A+Bη = Dᶻ. With d = D·ε: Dᶻ·εᶻ·u = Dᶻ.
    have hkey : D ^ z * ((ε : 𝓞 K) ^ z * (u : 𝓞 K)) = D ^ z * 1 := by
      have : (D ^ z * (ε : 𝓞 K) ^ z) * (u : 𝓞 K) = D ^ z := by
        rw [← mul_pow, hDε, ← hu, hD]
      rw [mul_one]; rw [← mul_assoc]; exact this
    -- Cancel D^z: it is nonzero (else A+Bη = 0, impossible since λ ∤ (A+Bη)).
    have hABη_ne : (A : 𝓞 K) + (B : 𝓞 K) * hζ.toInteger ≠ 0 := by
      -- λ ∤ (A+Bη); in particular A+Bη ≠ 0 (else λ ∣ 0).
      have hlamAB : ¬ (hζ.toInteger - 1) ∣ ((A : 𝓞 K) + (B : 𝓞 K)) := by
        have hcast : ((A : 𝓞 K) + (B : 𝓞 K)) = (((A + B : ℕ) : ℤ) : 𝓞 K) := by push_cast; ring
        rw [hcast, BealPrimeDescentFiveFull.lambda_dvd_intCast_iff_five hζ]
        intro hdvd; exact h5 (by exact_mod_cast hdvd)
      have hlam : ¬ (hζ.toInteger - 1) ∣ ((A : 𝓞 K) + (B : 𝓞 K) * hζ.toInteger) := by
        have := (BealFiveStructure.lambda_dvd_conj_five_iff hζ (A : 𝓞 K) (B : 𝓞 K) 1)
        rw [pow_one] at this
        rw [this]; exact hlamAB
      intro h0; exact hlam (h0 ▸ dvd_zero _)
    have hDz_ne : D ^ z ≠ 0 := by
      intro h0; apply hABη_ne; rw [hD, h0]
    -- Cancel Dᶻ in hkey: εᶻ·u = 1 (as ring elements).
    have hcancel : (ε : 𝓞 K) ^ z * (u : 𝓞 K) = 1 := mul_left_cancel₀ hDz_ne hkey
    -- Promote to a unit equation `(ε^z) * u = 1`, so `u = (ε^z)⁻¹ = (ε⁻¹)^z`.
    have hunit : (ε ^ z) * u = 1 := by
      apply Units.ext
      rw [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_one]
      exact hcancel
    have hueq : u = ε⁻¹ ^ z := by
      rw [inv_pow, eq_inv_iff_mul_eq_one, mul_comm]; exact hunit
    rw [hueq, Units.val_pow_eq_pow_val]

/-!
## Part 4 — the UNCONDITIONAL sub-case (`z = 1`)

For exponent `z = 1` the unit gap is vacuous: every unit `u` satisfies `u = u^1`, so
`H(u)` holds with `ε = u` and the perfect-power descent `A + B·η = (d·u)¹` is
unconditional. This is the `p = 5` analogue of `BealLambdaInterface.cube_plus_branch_case_two`
(the one exponent where the elementary descent closes outright); for `z = 1` the
"descent" is degenerate (`Dᶻ = D`), but it pins down that the unit obstruction is
*genuinely* an obstruction only for `z ≥ 2`.
-/

/-- **`five_unit_pinned_trivial_exponent`** (`z = 1`: the unit gap is vacuous). For
exponent `z = 1`, given the explicit descent `A + B·η = d¹ · u` (`u : (𝓞 K)ˣ` the
descent unit), the perfect-`z`-th-power branch holds **unconditionally** — no unit
pinning is needed, because `u = u^1` trivially:

  `∃ D : 𝓞 K, A + B·η = D ^ 1`.

This records the boundary of the obstruction: the infinite-unit gap at `p = 5` bites
only for `z ≥ 2`. (For `z = 1` the equation `A⁵ + B⁵ = C` is solvable for any coprime
`A, B`, so there is nothing to prove number-theoretically; the lemma confirms the
interface degenerates correctly.) -/
theorem five_unit_pinned_trivial_exponent
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {5} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ 5)
    {A B d : 𝓞 K} {u : (𝓞 K)ˣ}
    (hu : A + B * hζ.toInteger = d ^ 1 * (u : 𝓞 K)) :
    ∃ D : 𝓞 K, A + B * hζ.toInteger = D ^ 1 := by
  refine ⟨d * (u : 𝓞 K), ?_⟩
  rw [hu, pow_one, pow_one]

end BealFiveUnitInterface

-- Axiom audit (remove before finishing): each kept theorem reports
-- `[propext, Classical.choice, Quot.sound]`.
-- #print axioms BealFiveUnitInterface.five_descent_to_unit
-- #print axioms BealFiveUnitInterface.five_plus_branch_of_unit_pinned
-- #print axioms BealFiveUnitInterface.five_unit_gap_characterization
-- #print axioms BealFiveUnitInterface.five_unit_pinned_trivial_exponent
