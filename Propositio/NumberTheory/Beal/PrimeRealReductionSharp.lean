import Propositio.NumberTheory.Beal.PrimeRealReduction
import Mathlib.Tactic

/-!
# Sharper `(p,p,z)` reduction: torsion factor discharged, only the real factor remains

`BealPrimeRealReduction.beal_ppz_reduced_to_real` left two conditions on the descent unit's
factors: the torsion factor and the real factor are each `z`-th powers. The torsion factor lives
in the **finite** group `μ_K = torsion K`, so when `z` is coprime to `|μ_K|` it is *automatically*
a `z`-th power (the `z`-power map is a bijection of a finite group of coprime order).

This file discharges that condition (`torsion_eq_pow_of_coprime`) and records the resulting
sharper capstone (`beal_ppz_reduced_to_real_unit`): for every odd prime `p` with `𝓞K` a PID and
`gcd(z, |μ_K|) = 1`, the `(p,p,z)` descent reduces to the **single** statement that the *real*
unit factor is a `z`-th power — an honest question about the totally real subfield `ℚ(ζ_p)⁺` alone.

(For `ℚ(ζ_p)`, `|μ_K| = 2p`, so the hypothesis is `gcd(z, 2p) = 1`.)

`lake env lean BealPrimeRealReductionSharp.lean` to typecheck (SLOW — cyclotomic + CM imports).
-/

open NumberField NumberField.Units NumberField.IsCMField

namespace BealPrimeRealReductionSharp

variable {p : ℕ} [hpp : Fact p.Prime] [NeZero p] {K : Type*} [Field K] [NumberField K]
  [IsCyclotomicExtension {p} ℚ K] [IsPrincipalIdealRing (𝓞 K)]

/-- **Torsion `z`-th-power lemma.** In the finite group `μ_K = torsion K`, if `z` is coprime to
`|μ_K|` then every root of unity is a `z`-th power (the `z`-power map is bijective). -/
theorem torsion_eq_pow_of_coprime {z : ℕ} (x : torsion K)
    (hcop : Nat.Coprime z (Nat.card (torsion K))) : ∃ ξ : torsion K, ξ ^ z = x := by
  have hox : Nat.Coprime z (orderOf x) := hcop.coprime_dvd_right (orderOf_dvd_natCard x)
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hox
  exact ⟨x ^ m, by rw [← pow_mul, Nat.mul_comm, pow_mul]; exact hm⟩

/-- **HEADLINE — sharper `(p,p,z)` reduction.** For every odd prime `p` with `𝓞K` a PID and
`gcd(z, |μ_K|) = 1`, a primitive `(p,p,z)` solution gives `A + B = sᶻ` and a **real** unit `v`
such that: if `v` is a `z`-th power, then `A + B·η = Dᶻ`. The torsion obstruction is gone; the
only remaining input is about the real subfield `ℚ(ζ_p)⁺`. -/
theorem beal_ppz_reduced_to_real_unit (hp2 : p ≠ 2) {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    {A B C z : ℕ} (hAB : Nat.Coprime A B) (hpAB : ¬ p ∣ (A + B)) (hz : z ≠ 0)
    (h : A ^ p + B ^ p = C ^ z)
    (hzcop : Nat.Coprime z (Nat.card (torsion K))) :
    haveI := BealCyclotomicUnitIndex.isCMField_cyclotomic (K := K) hp2
    ∃ (s : ℕ) (d : 𝓞 K) (v : (𝓞 K)ˣ),
      A + B = s ^ z ∧ v ∈ realUnits K ∧
      ((∃ w : (𝓞 K)ˣ, v = w ^ z) →
       ∃ D : 𝓞 K, (A : 𝓞 K) + (B : 𝓞 K) * hζ.toInteger = D ^ z) := by
  haveI := BealCyclotomicUnitIndex.isCMField_cyclotomic (K := K) hp2
  obtain ⟨s, d, t, v, hs, hv, himpl⟩ :=
    BealPrimeRealReduction.beal_ppz_reduced_to_real hp2 hζ hAB hpAB hz h
  refine ⟨s, d, v, hs, hv, ?_⟩
  intro hreal
  obtain ⟨ξ, hξ⟩ := torsion_eq_pow_of_coprime t hzcop
  exact himpl ⟨ξ, by rw [← hξ, Subgroup.coe_pow]⟩ hreal

end BealPrimeRealReductionSharp
