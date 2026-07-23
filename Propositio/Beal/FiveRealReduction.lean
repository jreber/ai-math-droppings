import Propositio.Beal.HasseIndex
import Propositio.Beal.FiveUnitInterface
import Mathlib.Tactic

/-!
# (5,5,z) descent reduced to the real subfield `ℚ(√5)` — the payoff of `Q = 1`

`BealFiveUnitInterface.five_plus_branch_of_unit_pinned` reduces a primitive `(5,5,z)` Beal
solution to the single gap `H(u) : ∃ ε, u = εᶻ` (the rank-`1` descent unit is a `z`-th power).
`BealHasseIndex` proved the Hasse unit index `Q = 1`, hence
`BealHasseIndex.unit_eq_torsion_mul_real` factors every unit as `u = ζ · v` with `ζ` a root of
unity and `v` a **real** unit (of `𝓞(ℚ(√5))`).

This file combines the two: the `(5,5,z)` descent yields a perfect `z`-th power **as soon as the
two factors of the descent unit are individually `z`-th powers** — the torsion factor `ζ`
(a *finite*, `gcd(z, 10)` computation in `μ₁₀`) and the real factor `v` (the genuine *Kummer*
content, now an honest statement about the fundamental unit of `ℚ(√5)`, not the full ℤ[ζ₅]ˣ).

So the remaining gap for Beal `(5,5,z)` is now localized to the **real quadratic subfield**:
- `pow_of_factor_pows` — the unit-level reduction `H(u) ⟸ (ζ a zᵗʰ power) ∧ (v a zᵗʰ power)`.
- `five_descent_reduced_to_real` — the Beal corollary: `A + B·η = Dᶻ` follows from those two
  factor-conditions. This is the sharpest current statement of the `(5,5,z)` descent.

`lake env lean BealFiveRealReduction.lean` to typecheck (SLOW — cyclotomic + CM imports).
-/

open NumberField NumberField.Units NumberField.IsCMField

namespace BealFiveRealReduction

variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {5} ℚ K]

/-- **Unit-level reduction.** A unit `u = ζ · v` (root-of-unity `ζ` times real unit `v`) is a
`z`-th power as soon as `ζ` and `v` are each `z`-th powers: then `u = (ξ · w)ᶻ`. This is exactly
the gap `H(u)` of `BealFiveUnitInterface`, split along the `Q = 1` decomposition. -/
theorem pow_of_factor_pows {z : ℕ} {u : (𝓞 K)ˣ}
    (t : torsion K) (v : (𝓞 K)ˣ)
    (hu : u = (t : (𝓞 K)ˣ) * v)
    (htor : ∃ ξ : torsion K, ((t : (𝓞 K)ˣ)) = (ξ : (𝓞 K)ˣ) ^ z)
    (hreal : ∃ w : (𝓞 K)ˣ, v = w ^ z) :
    ∃ ε : (𝓞 K)ˣ, (u : 𝓞 K) = (ε : 𝓞 K) ^ z := by
  obtain ⟨ξ, hξ⟩ := htor
  obtain ⟨w, hw⟩ := hreal
  refine ⟨(ξ : (𝓞 K)ˣ) * w, ?_⟩
  have huw : ((ξ : (𝓞 K)ˣ) * w) ^ z = u := by
    rw [mul_pow, ← hξ, ← hw, ← hu]
  rw [← huw, Units.val_pow_eq_pow_val]

/-- **HEADLINE — `(5,5,z)` descent localized to `ℚ(√5)`.** A primitive `(5,5,z)` Beal solution
`A⁵ + B⁵ = C^z` with `5 ∤ (A + B)`, `z ≠ 0`, admits a descent base `d`, a root of unity `t`, and
a **real** unit `v` (with the integer descent `A + B = sᶻ`) such that:

  **IF** the torsion factor `t` is a `z`-th power of a root of unity, **AND** the real factor `v`
  is a `z`-th power, **THEN** `A + B·η = Dᶻ` is a perfect `z`-th power.

The torsion condition is a finite `gcd(z, 10)` computation in `μ₁₀`; the real condition is the
genuine Kummer input, now confined to the **real quadratic field `ℚ(√5)`** — the structural
simplification delivered by the Hasse index `Q = 1` (`BealHasseIndex.indexRealUnits_eq_one`). -/
theorem five_descent_reduced_to_real {ζ : K} (hζ : IsPrimitiveRoot ζ 5)
    {A B C z : ℕ} (hAB : Nat.Coprime A B) (h5 : ¬ 5 ∣ (A + B)) (hz : z ≠ 0)
    (h : A ^ 5 + B ^ 5 = C ^ z) :
    haveI := BealHasseIndex.isCMField_five (K := K)
    ∃ (s : ℕ) (d : 𝓞 K) (t : torsion K) (v : (𝓞 K)ˣ),
      A + B = s ^ z ∧ v ∈ realUnits K ∧
      ((∃ ξ : torsion K, ((t : (𝓞 K)ˣ)) = (ξ : (𝓞 K)ˣ) ^ z) →
       (∃ w : (𝓞 K)ˣ, v = w ^ z) →
       ∃ D : 𝓞 K, (A : 𝓞 K) + (B : 𝓞 K) * hζ.toInteger = D ^ z) := by
  haveI := BealHasseIndex.isCMField_five (K := K)
  obtain ⟨s, d, u, hs, hu⟩ := BealFiveUnitInterface.five_descent_to_unit hζ hAB h5 hz h
  obtain ⟨t, v, hv, hdecomp⟩ := BealHasseIndex.unit_eq_torsion_mul_real hζ u
  refine ⟨s, d, t, v, hs, hv, ?_⟩
  intro htor hreal
  obtain ⟨ε, hε⟩ := pow_of_factor_pows t v hdecomp htor hreal
  refine ⟨d * (ε : 𝓞 K), ?_⟩
  rw [hu, hε, mul_pow]

end BealFiveRealReduction
