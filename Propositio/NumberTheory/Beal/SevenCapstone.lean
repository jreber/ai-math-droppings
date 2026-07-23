import Mathlib.Tactic
import Propositio.NumberTheory.Beal.CyclotomicDescent
import Propositio.NumberTheory.Beal.PPZCapstone
import Propositio.NumberTheory.Beal.SevenPID

/-!
# The `p = 7` capstone and the unified `{3, 5, 7}` three-prime statement

**NEW.** With `IsCyclotomicExtension.Rat.Seven.seven_pid` proving `𝓞 ℚ(ζ₇)` is a
PID (class number 1), the general `(p, p, z)` cyclotomic descent engine
`BealCyclotomicDescent.beal_ppz_structure_gen` now covers `p = 7` exactly as it
covers `p = 3` (via `three_pid`) and `p = 5` (via `five_pid`). This file:

1. **`beal_77z_counterexample_constraints`** — the `p = 7` instance of the
   `p`-uniform capstone headline `BealPPZCapstone.beal_ppz_counterexample_constraints`,
   parallel in form to `beal_33z_counterexample_constraints` /
   `beal_55z_counterexample_constraints`. The PID input is discharged by
   `seven_pid` (one line, mirroring the `p = 3, 5` instances).

2. **`beal_357_constraints`** — the UNIFIED three-prime statement: a single
   machine-checked theorem bundling the `p ∈ {3, 5, 7}` instances of the
   unconditional `(p, p, z)` descent, witnessing that the structural descent holds
   for all three primes with known class number 1. (A genuinely uniform
   `∀ p ∈ {3,5,7}` quantification is awkward here because the cyclotomic field
   `K = K p` and its `IsPrimitiveRoot`/`IsCyclotomicExtension` instances are
   per-prime; the conjunction is the cleanest formulation that type-checks while
   keeping every instance axiom-clean.)

## What a primitive `(p, p, z)` Beal counterexample must satisfy, for `p ∈ {3,5,7}`

For each `p ∈ {3, 5, 7}`, with `ζ` a primitive `p`-th root of unity in
`K = ℚ(ζ_p)`, `Nat.Coprime A B`, `p ∤ (A + B)`, `z ≠ 0`, and `A^p + B^p = C^z`:

* **(integer descent)** `A + B` is a perfect `z`-th power, `∃ s, A + B = sᶻ`;
* **(cyclotomic descent)** `A + B·ζ` is a `z`-th power up to a unit in `𝓞 K`,
  `∃ d, Associated (dᶻ) (A + B·ζ)`.

The three primes are exactly the cyclotomic primes for which the prime-power
descent is unconditional *because* `ℚ(ζ_p)` has class number 1 — `p = 3, 5` from
mathlib's `three_pid` / `five_pid`, and `p = 7` from this development's
`seven_pid`.

## The stretch goal (unconditional sub-case closure for `p = 5, 7`)

`BealLambdaInterface.cube_plus_branch_case_two` closes the `p = 3`, `z = 3`,
`3 ∣ B` sub-case with **no Kummer input**, by reducing the `λ²`-residue gap to the
mathlib FLT-3 cube engine (`lambda_pow_four_dvd_cube_sub_one_or_add_one`,
`sign_eliminated_of_lambda_dvd_B`). That closure is *intrinsically `p = 3`*: it
consumes (a) Kummer's lemma for `ℚ(ζ₃)`
(`IsCyclotomicExtension.Rat.Three.eq_one_or_neg_one_of_unit_of_congruent`) and
(b) the explicit `ℤ[ζ₃]` cube-residue fact `λ⁴ ∣ x³ ∓ 1`, **neither of which has
a `p = 5` or `p = 7` analogue in this corpus** (no `Rat.Five.*` / `Rat.Seven.*`
Kummer lemma, no `λ⁴ ∣ x⁵ ∓ 1` residue computation). So the elementary sub-case
closure does *not* transfer to `p = 5, 7` here; this is the documented obstruction.
What *does* transfer uniformly is the structural descent — exactly items 1–2 above.

All kept theorems are axiom-clean: `[propext, Classical.choice, Quot.sound]`.

`lake env lean BealSevenCapstone.lean` to typecheck (SLOW, cyclotomic imports).
-/

namespace BealSevenCapstone

open scoped NumberField

/-! ## Item 1 — the `p = 7` instance of the capstone headline -/

/-- **The `p = 7` instance of the capstone.** The `(7, 7, z)` structural
constraints from the `p`-uniform capstone
`BealPPZCapstone.beal_ppz_counterexample_constraints`, with the PID hypothesis
discharged by `IsCyclotomicExtension.Rat.Seven.seven_pid` (class number 1 of
`ℚ(ζ₇)`). One line — parallel in form to `beal_33z_counterexample_constraints`
(via `three_pid`) and `beal_55z_counterexample_constraints` (via `five_pid`).

If `A^7 + B^7 = C^z` with `A, B` coprime, `7 ∤ (A + B)`, and `z ≠ 0`, then:

* **(integer descent)** `A + B` is a perfect `z`-th power: `∃ s : ℕ, A + B = sᶻ`;
* **(cyclotomic descent)** `A + B·ζ₇` is a `z`-th power up to a unit in `𝓞 ℚ(ζ₇)`:
  `∃ d : 𝓞 K, Associated (dᶻ) ((A : 𝓞 K) + B·ζ₇)`. **NEW.** -/
theorem beal_77z_counterexample_constraints
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {7} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ 7)
    {A B C z : ℕ} (hAB : Nat.Coprime A B) (h7 : ¬ 7 ∣ (A + B)) (hz : z ≠ 0)
    (h : A ^ 7 + B ^ 7 = C ^ z) :
    (∃ s : ℕ, A + B = s ^ z) ∧
    (∃ d : 𝓞 K, Associated (d ^ z) ((A : 𝓞 K) + (B : 𝓞 K) * hζ.toInteger)) := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  haveI : IsPrincipalIdealRing (𝓞 K) := IsCyclotomicExtension.Rat.Seven.seven_pid K
  exact BealPPZCapstone.beal_ppz_counterexample_constraints (by decide) hζ hAB h7 hz h

/-! ## Item 2 — the unified `{3, 5, 7}` three-prime statement

The conjunction bundling the three completed rungs of the unconditional
`(p, p, z)` descent. Each conjunct is the per-prime structural-constraint instance;
together they form a single machine-checked theorem witnessing that the descent
closes for every cyclotomic prime `p ∈ {3, 5, 7}` of class number 1.

We take three independent cyclotomic fields `K₃, K₅, K₇` (one per prime), because
the `IsCyclotomicExtension {p} ℚ K` instance is per-prime; a uniform `∀ p ∈ {3,5,7}`
quantifier would have to carry a prime-dependent field, which Lean's typeclass
resolution cannot supply uniformly. The conjunction is the faithful, axiom-clean
formulation.
-/

/-- **The unified `{3, 5, 7}` three-prime constraint theorem (UNIFIED).** A single
statement bundling the structural-descent constraints for *all three* cyclotomic
primes of class number 1.

For independent cyclotomic fields `K₃ = ℚ(ζ₃)`, `K₅ = ℚ(ζ₅)`, `K₇ = ℚ(ζ₇)` with
primitive roots `ζ₃, ζ₅, ζ₇`, and for any primitive `(p, p, z)` data
`A^p + B^p = C^z` (`Nat.Coprime A B`, `p ∤ (A + B)`, `z ≠ 0`) at the respective
prime, the structural descent holds:

* `p = 3`: `A + B = sᶻ` ∧ `A + B·ζ₃` is a `z`-th power up to a unit;
* `p = 5`: `A + B = sᶻ` ∧ `A + B·ζ₅` is a `z`-th power up to a unit;
* `p = 7`: `A + B = sᶻ` ∧ `A + B·ζ₇` is a `z`-th power up to a unit.

This is the consolidated three-prime coverage: the PID input is `three_pid`,
`five_pid`, `seven_pid` respectively, all discharged automatically by the three
per-prime instances. Adding any future class-number-1 prime is one more conjunct
of the same form. **NEW.** -/
theorem beal_357_constraints
    {K₃ : Type*} [Field K₃] [NumberField K₃] [IsCyclotomicExtension {3} ℚ K₃]
    {ζ₃ : K₃} (hζ₃ : IsPrimitiveRoot ζ₃ 3)
    {K₅ : Type*} [Field K₅] [NumberField K₅] [IsCyclotomicExtension {5} ℚ K₅]
    {ζ₅ : K₅} (hζ₅ : IsPrimitiveRoot ζ₅ 5)
    {K₇ : Type*} [Field K₇] [NumberField K₇] [IsCyclotomicExtension {7} ℚ K₇]
    {ζ₇ : K₇} (hζ₇ : IsPrimitiveRoot ζ₇ 7) :
    -- p = 3
    (∀ {A B C z : ℕ}, Nat.Coprime A B → ¬ 3 ∣ (A + B) → z ≠ 0 →
        A ^ 3 + B ^ 3 = C ^ z →
        (∃ s : ℕ, A + B = s ^ z) ∧
        (∃ d : 𝓞 K₃, Associated (d ^ z)
          ((A : 𝓞 K₃) + (B : 𝓞 K₃) * hζ₃.toInteger))) ∧
    -- p = 5
    (∀ {A B C z : ℕ}, Nat.Coprime A B → ¬ 5 ∣ (A + B) → z ≠ 0 →
        A ^ 5 + B ^ 5 = C ^ z →
        (∃ s : ℕ, A + B = s ^ z) ∧
        (∃ d : 𝓞 K₅, Associated (d ^ z)
          ((A : 𝓞 K₅) + (B : 𝓞 K₅) * hζ₅.toInteger))) ∧
    -- p = 7
    (∀ {A B C z : ℕ}, Nat.Coprime A B → ¬ 7 ∣ (A + B) → z ≠ 0 →
        A ^ 7 + B ^ 7 = C ^ z →
        (∃ s : ℕ, A + B = s ^ z) ∧
        (∃ d : 𝓞 K₇, Associated (d ^ z)
          ((A : 𝓞 K₇) + (B : 𝓞 K₇) * hζ₇.toInteger))) :=
  ⟨fun hAB h3 hz h =>
      BealPPZCapstone.beal_33z_counterexample_constraints hζ₃ hAB h3 hz h,
   fun hAB h5 hz h =>
      BealPPZCapstone.beal_55z_counterexample_constraints hζ₅ hAB h5 hz h,
   fun hAB h7 hz h =>
      beal_77z_counterexample_constraints hζ₇ hAB h7 hz h⟩

end BealSevenCapstone
