import Propositio.Beal.PrimeRealReductionSharp
import Propositio.Beal.SevenPID
import Mathlib.Tactic

/-!
# Concrete `(5,5,z)` and `(7,7,z)` reductions to the real subfield

Specializes `BealPrimeRealReductionSharp.beal_ppz_reduced_to_real_unit` to `p = 5` and `p = 7`,
using `|μ_K| = 2p` (`cyclotomic_torsion_card`) to turn the abstract coprimality hypothesis
`gcd(z, |μ_K|) = 1` into the concrete `gcd(z, 10) = 1` / `gcd(z, 14) = 1`. These are the headline
usable statements:

> **Beal `(5,5,z)` with `gcd(z,10)=1`** reduces to: *the real unit factor of the descent unit is
> a `z`-th power* — an honest question about the fundamental unit of `ℚ(√5)`.

> **Beal `(7,7,z)` with `gcd(z,14)=1`** reduces likewise to the cubic real field `ℚ(ζ₇)⁺`.

`lake env lean BealRealReductionConcrete.lean` to typecheck (SLOW — cyclotomic + CM imports).
-/

open NumberField NumberField.Units NumberField.IsCMField

namespace BealRealReductionConcrete

/-- `|μ_K| = 2p` for `K = ℚ(ζ_p)`, `p` an odd prime. -/
theorem cyclotomic_torsion_card {p : ℕ} [hpp : Fact p.Prime] (hp2 : p ≠ 2)
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K] :
    Nat.card (torsion K) = 2 * p := by
  haveI : NeZero p := ⟨hpp.out.ne_zero⟩
  have hodd : ¬ Even p := Nat.not_even_iff_odd.mpr (hpp.out.odd_of_ne_two hp2)
  have h := IsCyclotomicExtension.Rat.torsionOrder_eq (n := p) (K := K)
  rw [if_neg hodd] at h
  rw [Nat.card_eq_fintype_card]
  exact h

/-- **Beal `(5,5,z)` with `gcd(z,10)=1` reduced to `ℚ(√5)`.** -/
theorem beal_55z_reduced_to_real_unit {K : Type*} [Field K] [NumberField K]
    [IsCyclotomicExtension {5} ℚ K] {ζ : K} (hζ : IsPrimitiveRoot ζ 5)
    {A B C z : ℕ} (hAB : Nat.Coprime A B) (h5 : ¬ 5 ∣ (A + B)) (hz : z ≠ 0)
    (h : A ^ 5 + B ^ 5 = C ^ z) (hzcop : Nat.Coprime z 10) :
    haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    haveI := BealCyclotomicUnitIndex.isCMField_cyclotomic (K := K) (p := 5) (by norm_num)
    ∃ (s : ℕ) (d : 𝓞 K) (v : (𝓞 K)ˣ),
      A + B = s ^ z ∧ v ∈ realUnits K ∧
      ((∃ w : (𝓞 K)ˣ, v = w ^ z) →
       ∃ D : 𝓞 K, (A : 𝓞 K) + (B : 𝓞 K) * hζ.toInteger = D ^ z) := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  haveI : IsPrincipalIdealRing (𝓞 K) := IsCyclotomicExtension.Rat.five_pid K
  have hcard : Nat.card (torsion K) = 10 := by
    have hc := cyclotomic_torsion_card (p := 5) (by norm_num) (K := K); omega
  exact BealPrimeRealReductionSharp.beal_ppz_reduced_to_real_unit (by norm_num) hζ hAB h5 hz h
    (hcard ▸ hzcop)

/-- **Beal `(7,7,z)` with `gcd(z,14)=1` reduced to `ℚ(ζ₇)⁺`.** -/
theorem beal_77z_reduced_to_real_unit {K : Type*} [Field K] [NumberField K]
    [IsCyclotomicExtension {7} ℚ K] {ζ : K} (hζ : IsPrimitiveRoot ζ 7)
    {A B C z : ℕ} (hAB : Nat.Coprime A B) (h7 : ¬ 7 ∣ (A + B)) (hz : z ≠ 0)
    (h : A ^ 7 + B ^ 7 = C ^ z) (hzcop : Nat.Coprime z 14) :
    haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    haveI := BealCyclotomicUnitIndex.isCMField_cyclotomic (K := K) (p := 7) (by norm_num)
    ∃ (s : ℕ) (d : 𝓞 K) (v : (𝓞 K)ˣ),
      A + B = s ^ z ∧ v ∈ realUnits K ∧
      ((∃ w : (𝓞 K)ˣ, v = w ^ z) →
       ∃ D : 𝓞 K, (A : 𝓞 K) + (B : 𝓞 K) * hζ.toInteger = D ^ z) := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  haveI : IsPrincipalIdealRing (𝓞 K) := IsCyclotomicExtension.Rat.Seven.seven_pid K
  have hcard : Nat.card (torsion K) = 14 := by
    have hc := cyclotomic_torsion_card (p := 7) (by norm_num) (K := K); omega
  exact BealPrimeRealReductionSharp.beal_ppz_reduced_to_real_unit (by norm_num) hζ hAB h7 hz h
    (hcard ▸ hzcop)

end BealRealReductionConcrete
