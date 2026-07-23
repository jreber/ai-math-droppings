import Propositio.NumberTheory.Beal.CyclotomicUnitIndex
import Propositio.NumberTheory.Beal.SevenUnitIndex
import Propositio.NumberTheory.Beal.SevenPID
import Mathlib.Tactic

/-!
# (7,7,z) descent reduced to the real subfield `ℚ(ζ₇)⁺` — via the Hasse index `Q = 1`

The `p = 7` mirror of `BealFiveRealReduction`. `IsCyclotomicExtension.Rat.Seven.beal_77z_structure`
(which uses `seven_pid`) is the unconditional `(7,7,z)` descent up to one gap: pinning the descent
unit. `BealSevenUnitIndex` proved `Q = 1` for `ℚ(ζ₇)`, hence every unit is
`(root of unity) · (real unit)`. Combining them localizes the remaining `(7,7,z)` gap onto the
**maximal totally real subfield `ℚ(ζ₇)⁺`** (degree `3`, the cubic field `ℚ(cos 2π/7)`):

- `seven_descent_to_unit` — the unconditional descent to an explicit unit.
- `seven_descent_reduced_to_real` — `A + B·η = Dᶻ` follows once the torsion factor and the real
  factor of the descent unit are each `z`-th powers.

The generic factor-splitting lemma `BealFiveRealReduction.pow_of_factor_pows` is reused verbatim
(it is `p`-independent). This puts `(7,7,z)` at exactly the stage `(5,5,z)` reached, with the open
input now an honest statement about units of the cubic field `ℚ(ζ₇)⁺`.

`lake env lean BealSevenRealReduction.lean` to typecheck (SLOW — cyclotomic + CM imports).
-/

open NumberField NumberField.Units NumberField.IsCMField

namespace BealSevenRealReduction

variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {7} ℚ K]

/-- **Unconditional `(7,7,z)` descent to an explicit unit.** A primitive `(7,7,z)` solution
`A⁷ + B⁷ = C^z` with `7 ∤ (A + B)`, `z ≠ 0` gives `A + B = sᶻ` and an explicit descent unit
`u` with `A + B·η = dᶻ · u`. (Unpacks `beal_77z_structure`'s `Associated`.) -/
theorem seven_descent_to_unit {ζ : K} (hζ : IsPrimitiveRoot ζ 7)
    {A B C z : ℕ} (hAB : Nat.Coprime A B) (h7 : ¬ 7 ∣ (A + B)) (hz : z ≠ 0)
    (h : A ^ 7 + B ^ 7 = C ^ z) :
    ∃ (s : ℕ) (d : 𝓞 K) (u : (𝓞 K)ˣ),
      A + B = s ^ z ∧
      (A : 𝓞 K) + (B : 𝓞 K) * hζ.toInteger = d ^ z * (u : 𝓞 K) := by
  obtain ⟨⟨s, hs⟩, ⟨d, u, hu⟩⟩ :=
    IsCyclotomicExtension.Rat.Seven.beal_77z_structure (K := K) hζ hAB h7 hz h
  exact ⟨s, d, u, hs, hu.symm⟩

/-- **HEADLINE — `(7,7,z)` descent localized to `ℚ(ζ₇)⁺`.** A primitive `(7,7,z)` solution gives
a descent base `d`, a root of unity `t`, and a **real** unit `v` (with `A + B = sᶻ`) such that:
if the torsion factor `t` is a `z`-th power of a root of unity AND the real factor `v` is a `z`-th
power, then `A + B·η = Dᶻ`. The remaining input is now confined to the totally real cubic field
`ℚ(ζ₇)⁺` — the structural payoff of `Q = 1` (`BealSevenUnitIndex.indexRealUnits_eq_one_seven`). -/
theorem seven_descent_reduced_to_real {ζ : K} (hζ : IsPrimitiveRoot ζ 7)
    {A B C z : ℕ} (hAB : Nat.Coprime A B) (h7 : ¬ 7 ∣ (A + B)) (hz : z ≠ 0)
    (h : A ^ 7 + B ^ 7 = C ^ z) :
    haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    haveI := BealCyclotomicUnitIndex.isCMField_cyclotomic (K := K) (p := 7) (by norm_num)
    ∃ (s : ℕ) (d : 𝓞 K) (t : torsion K) (v : (𝓞 K)ˣ),
      A + B = s ^ z ∧ v ∈ realUnits K ∧
      ((∃ ξ : torsion K, ((t : (𝓞 K)ˣ)) = (ξ : (𝓞 K)ˣ) ^ z) →
       (∃ w : (𝓞 K)ˣ, v = w ^ z) →
       ∃ D : 𝓞 K, (A : 𝓞 K) + (B : 𝓞 K) * hζ.toInteger = D ^ z) := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  haveI := BealCyclotomicUnitIndex.isCMField_cyclotomic (K := K) (p := 7) (by norm_num)
  obtain ⟨s, d, u, hs, hu⟩ := seven_descent_to_unit hζ hAB h7 hz h
  obtain ⟨t, v, hv, hdecomp⟩ := BealSevenUnitIndex.unit_eq_torsion_mul_real_seven hζ u
  refine ⟨s, d, t, v, hs, hv, ?_⟩
  intro htor hreal
  obtain ⟨ξ, hξ⟩ := htor
  obtain ⟨w, hw⟩ := hreal
  have huw : ((ξ : (𝓞 K)ˣ) * w) ^ z = u := by rw [mul_pow, ← hξ, ← hw, ← hdecomp]
  refine ⟨d * (((ξ : (𝓞 K)ˣ) * w : (𝓞 K)ˣ) : 𝓞 K), ?_⟩
  rw [hu, ← huw, Units.val_pow_eq_pow_val, mul_pow]

end BealSevenRealReduction
