import Propositio.NumberTheory.Beal.CyclotomicDescent
import Propositio.NumberTheory.Beal.CyclotomicUnitIndex
import Mathlib.Tactic

/-!
# Uniform `(p,p,z)` descent reduced to the real subfield `ℚ(ζ_p)⁺`, every odd prime `p`

The common generalization of `BealFiveRealReduction` (`p = 5 → ℚ(√5)`) and
`BealSevenRealReduction` (`p = 7 → ℚ(ζ₇)⁺`). It combines two uniform ingredients:

* `BealCyclotomicDescent.beal_ppz_structure_gen` — the `(p,p,z)` cyclotomic descent for any odd
  prime `p` with `𝓞K` a PID, giving `A + B = sᶻ` and `A + B·η = dᶻ · u`.
* `BealCyclotomicUnitIndex.unit_eq_torsion_mul_real` — the Hasse index `Q = 1` (every odd prime),
  factoring the descent unit `u = ζ · v` (root of unity × real unit).

Result (`beal_ppz_reduced_to_real`): for **every** odd prime `p` with `𝓞(ℚ(ζ_p))` a PID, a
primitive `(p,p,z)` solution forces `A + B·η = Dᶻ` **once** the torsion factor and the real factor
of the descent unit are each `z`-th powers. So the remaining input for the whole `(p,p,z)` family
is localized to the **maximal totally real subfield `ℚ(ζ_p)⁺`** (degree `(p−1)/2`) — uniformly.

Instantiating needs the PID input `[IsPrincipalIdealRing (𝓞 K)]`, available in this pin for
`p = 5` (`five_pid`) and `p = 7` (`seven_pid`); supplying it for `p = 11, 13, …` is the only extra
hypothesis (the genuine class-number/Minkowski wall, tracked in `BEAL-README`).

`lake env lean BealPrimeRealReduction.lean` to typecheck (SLOW — cyclotomic + CM imports).
-/

open NumberField NumberField.Units NumberField.IsCMField

namespace BealPrimeRealReduction

variable {p : ℕ} [hpp : Fact p.Prime] [NeZero p] {K : Type*} [Field K] [NumberField K]
  [IsCyclotomicExtension {p} ℚ K] [IsPrincipalIdealRing (𝓞 K)]

/-- **Uniform `(p,p,z)` descent to an explicit unit** (odd prime `p`, `𝓞K` a PID). -/
theorem beal_ppz_descent_to_unit (hp2 : p ≠ 2) {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    {A B C z : ℕ} (hAB : Nat.Coprime A B) (hpAB : ¬ p ∣ (A + B)) (hz : z ≠ 0)
    (h : A ^ p + B ^ p = C ^ z) :
    ∃ (s : ℕ) (d : 𝓞 K) (u : (𝓞 K)ˣ),
      A + B = s ^ z ∧
      (A : 𝓞 K) + (B : 𝓞 K) * hζ.toInteger = d ^ z * (u : 𝓞 K) := by
  obtain ⟨⟨s, hs⟩, ⟨d, u, hu⟩⟩ :=
    BealCyclotomicDescent.beal_ppz_structure_gen hp2 hζ hAB hpAB hz h
  exact ⟨s, d, u, hs, hu.symm⟩

/-- **HEADLINE — uniform `(p,p,z)` descent localized to `ℚ(ζ_p)⁺`.** For every odd prime `p`
with `𝓞(ℚ(ζ_p))` a PID, a primitive `(p,p,z)` solution gives `A + B = sᶻ`, a root of unity `t`,
and a **real** unit `v` such that: if `t` and `v` are each `z`-th powers, then `A + B·η = Dᶻ`.
The open input is confined to the totally real subfield `ℚ(ζ_p)⁺`. -/
theorem beal_ppz_reduced_to_real (hp2 : p ≠ 2) {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    {A B C z : ℕ} (hAB : Nat.Coprime A B) (hpAB : ¬ p ∣ (A + B)) (hz : z ≠ 0)
    (h : A ^ p + B ^ p = C ^ z) :
    haveI := BealCyclotomicUnitIndex.isCMField_cyclotomic (K := K) hp2
    ∃ (s : ℕ) (d : 𝓞 K) (t : torsion K) (v : (𝓞 K)ˣ),
      A + B = s ^ z ∧ v ∈ realUnits K ∧
      ((∃ ξ : torsion K, ((t : (𝓞 K)ˣ)) = (ξ : (𝓞 K)ˣ) ^ z) →
       (∃ w : (𝓞 K)ˣ, v = w ^ z) →
       ∃ D : 𝓞 K, (A : 𝓞 K) + (B : 𝓞 K) * hζ.toInteger = D ^ z) := by
  haveI := BealCyclotomicUnitIndex.isCMField_cyclotomic (K := K) hp2
  obtain ⟨s, d, u, hs, hu⟩ := beal_ppz_descent_to_unit hp2 hζ hAB hpAB hz h
  obtain ⟨t, v, hv, hdecomp⟩ := BealCyclotomicUnitIndex.unit_eq_torsion_mul_real hζ hp2 u
  refine ⟨s, d, t, v, hs, hv, ?_⟩
  intro htor hreal
  obtain ⟨ξ, hξ⟩ := htor
  obtain ⟨w, hw⟩ := hreal
  have huw : ((ξ : (𝓞 K)ˣ) * w) ^ z = u := by rw [mul_pow, ← hξ, ← hw, ← hdecomp]
  refine ⟨d * (((ξ : (𝓞 K)ˣ) * w : (𝓞 K)ˣ) : 𝓞 K), ?_⟩
  rw [hu, ← huw, Units.val_pow_eq_pow_val, mul_pow]

end BealPrimeRealReduction
