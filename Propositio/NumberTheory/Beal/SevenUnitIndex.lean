import Propositio.NumberTheory.Beal.CyclotomicUnitIndex

/-!
# The Hasse unit index `Q = 1` for `ℚ(ζ₅)` and `ℚ(ζ₇)` — instances of the odd-prime family

`BealCyclotomicUnitIndex` proves `Q = 1` uniformly for every odd prime conductor. This file
records the two cases of interest for the live `(p,p,z)` Beal descent — `p = 5` and `p = 7`,
the regular primes with a known PID `𝓞K` (`five_pid`, `seven_pid`) — as direct corollaries.

Note `Q = 1` needs **no** PID input: it follows purely from the CM structure and `N(λ) = p` odd.
So the `p = 7` unit index is settled here even though the `(7,7,z)` *descent* additionally needs
`seven_pid` (in `BealSevenPID`). This sets up `(7,7,z)` exactly as `BealFiveRealReduction` set up
`(5,5,z)`: the descent-unit gap reduces to the maximal real subfield `ℚ(ζ₇)⁺` (totally real,
degree 3).
-/

open NumberField NumberField.IsCMField

namespace BealSevenUnitIndex

/-- **`Q = 1` for `ℚ(ζ₇)`.** Instance of the odd-prime family at `p = 7`. -/
theorem indexRealUnits_eq_one_seven {K : Type*} [Field K] [NumberField K]
    [IsCyclotomicExtension {7} ℚ K] {ζ : K} (hζ : IsPrimitiveRoot ζ 7) :
    haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    haveI := BealCyclotomicUnitIndex.isCMField_cyclotomic (K := K) (p := 7) (by norm_num)
    NumberField.IsCMField.indexRealUnits K = 1 := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  haveI := BealCyclotomicUnitIndex.isCMField_cyclotomic (K := K) (p := 7) (by norm_num)
  exact BealCyclotomicUnitIndex.indexRealUnits_eq_one hζ (by norm_num)

/-- **Every unit of `𝓞(ℚ(ζ₇))` is a root of unity times a real unit.** -/
theorem unit_eq_torsion_mul_real_seven {K : Type*} [Field K] [NumberField K]
    [IsCyclotomicExtension {7} ℚ K] {ζ : K} (hζ : IsPrimitiveRoot ζ 7) (u : (𝓞 K)ˣ) :
    haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    haveI := BealCyclotomicUnitIndex.isCMField_cyclotomic (K := K) (p := 7) (by norm_num)
    ∃ (t : NumberField.Units.torsion K) (v : (𝓞 K)ˣ),
      v ∈ realUnits K ∧ u = (t : (𝓞 K)ˣ) * v := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  haveI := BealCyclotomicUnitIndex.isCMField_cyclotomic (K := K) (p := 7) (by norm_num)
  exact BealCyclotomicUnitIndex.unit_eq_torsion_mul_real hζ (by norm_num) u

/-- **`Q = 1` for `ℚ(ζ₅)`** via the uniform family (matches `BealHasseIndex.indexRealUnits_eq_one`). -/
theorem indexRealUnits_eq_one_five {K : Type*} [Field K] [NumberField K]
    [IsCyclotomicExtension {5} ℚ K] {ζ : K} (hζ : IsPrimitiveRoot ζ 5) :
    haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    haveI := BealCyclotomicUnitIndex.isCMField_cyclotomic (K := K) (p := 5) (by norm_num)
    NumberField.IsCMField.indexRealUnits K = 1 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  haveI := BealCyclotomicUnitIndex.isCMField_cyclotomic (K := K) (p := 5) (by norm_num)
  exact BealCyclotomicUnitIndex.indexRealUnits_eq_one hζ (by norm_num)

end BealSevenUnitIndex
