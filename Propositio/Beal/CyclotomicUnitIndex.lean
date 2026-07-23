import Mathlib.NumberTheory.NumberField.CMField
import Mathlib.NumberTheory.NumberField.Ideal.Basic
import Mathlib.NumberTheory.NumberField.Cyclotomic.PID
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.RingTheory.RootsOfUnity.CyclotomicUnits
import Mathlib.Tactic

/-!
# The Hasse unit index `Q = 1` for `ℚ(ζ_p)`, every odd prime `p`

`BealHasseIndex` proved the Hasse unit index `Q = 1` for `ℚ(ζ₅)`. The argument is in fact
**uniform over every odd prime conductor `p`**: complex conjugation is the identity modulo
`λ = ζ − 1` (because `𝓞K = ℤ[ζ]` and `ζ ≡ 1 (mod λ)`), so `u·conj(u)⁻¹ ≡ 1 (mod λ)` for every
unit `u`, hence its powers can never reach `−1` (as `λ ∤ 2`, since `N(λ) = p` is odd). So the unit
`u·conj(u)⁻¹` never generates the full group of roots of unity, forcing the index to be `1`.

This file proves it once, for all odd primes (`indexRealUnits_eq_one`), and instantiates the cases
`p = 5` and `p = 7` — the two regular primes for which `𝓞K` is a known PID (`five_pid`,
`seven_pid`), i.e. the primes on the live `(p,p,z)` Beal descent. mathlib computes the unit index
for **no** field; this is the first uniform family.

Consequences (`unit_eq_torsion_mul_real`): for every odd prime `p`, every unit of `𝓞(ℚ(ζ_p))` is
`(root of unity) · (real unit)` — reducing the `(p,p,z)` descent-unit gap to the **maximal real
subfield** `ℚ(ζ_p)⁺` (a totally real field of degree `(p−1)/2`). For `p = 5` that subfield is the
real quadratic field `ℚ(√5)` (see `BealFiveRealReduction`).

`lake env lean BealCyclotomicUnitIndex.lean` to typecheck (SLOW — cyclotomic + CM imports).
-/

open NumberField NumberField.Units NumberField.IsCMField Ideal

namespace BealCyclotomicUnitIndex

variable {p : ℕ} [hpp : Fact (Nat.Prime p)] {K : Type*} [Field K] [NumberField K]
  [IsCyclotomicExtension {p} ℚ K]

/-- `ℚ(ζ_p)` (`p` an odd prime) is a CM field. -/
theorem isCMField_cyclotomic (hodd : p ≠ 2) : IsCMField K :=
  IsCyclotomicExtension.Rat.isCMField K (S := {p})
    ⟨p, by simp, lt_of_le_of_ne hpp.out.two_le (Ne.symm hodd)⟩

/-- **The λ-bridge for odd prime `p`.** `λ = ζ − 1` divides the image of `n : ℤ` iff `p ∣ n`,
via `N(λ) = p`. (Generalizes `BealPrimeDescentFiveFull.lambda_dvd_intCast_iff_five`.) -/
theorem lambda_dvd_intCast_iff (hζ : IsPrimitiveRoot (ζ : K) p) (hodd : p ≠ 2) (n : ℤ) :
    (hζ.toInteger - 1) ∣ ((n : ℤ) : 𝓞 K) ↔ (p : ℤ) ∣ n := by
  have hprime : Prime (Algebra.norm ℤ (hζ.toInteger - 1)) :=
    hζ.prime_norm_toInteger_sub_one_of_prime_ne_two' hodd
  have hnorm : Algebra.norm ℤ (hζ.toInteger - 1) = p :=
    hζ.norm_toInteger_sub_one_of_prime_ne_two' hodd
  have hiff := Ideal.norm_dvd_iff (S := 𝓞 K) hprime (y := n)
  rw [hnorm] at hiff
  rw [← hiff]

section CM
variable [IsCMField K]

/-- **Conjugation is trivial mod `λ`.** For all `x : 𝓞 K`, `conj x ≡ x (mod λ = ζ − 1)`. -/
theorem conj_mk_eq (hζ : IsPrimitiveRoot (ζ : K) p) (x : 𝓞 K) :
    Ideal.Quotient.mk (Ideal.span {hζ.toInteger - 1}) (ringOfIntegersComplexConj K x)
      = Ideal.Quotient.mk (Ideal.span {hζ.toInteger - 1}) x := by
  have hx : x ∈ (⊤ : Subalgebra ℤ (𝓞 K)) := Algebra.mem_top
  rw [← IsCyclotomicExtension.Rat.adjoin_singleton_eq_top hζ] at hx
  induction hx using Algebra.adjoin_induction with
  | mem y hy =>
      rw [Set.mem_singleton_iff] at hy; subst hy
      have hmem : hζ.toInteger - 1 ∈ Ideal.span {hζ.toInteger - 1} :=
        Ideal.mem_span_singleton_self _
      have e1 : Ideal.Quotient.mk (Ideal.span {hζ.toInteger - 1}) hζ.toInteger = 1 :=
        (Ideal.Quotient.mk_eq_one_iff_sub_mem _).mpr hmem
      have hassoc : Associated (hζ.toInteger - 1)
          (ringOfIntegersComplexConj K hζ.toInteger - 1) := by
        have h := hζ.toInteger_isPrimitiveRoot.associated_sub_one_map_sub_one
          (ringOfIntegersComplexConj K)
        simpa [map_sub, map_one] using h
      have e2 : Ideal.Quotient.mk (Ideal.span {hζ.toInteger - 1})
          (ringOfIntegersComplexConj K hζ.toInteger) = 1 := by
        refine (Ideal.Quotient.mk_eq_one_iff_sub_mem _).mpr ?_
        rw [Ideal.mem_span_singleton]
        exact hassoc.dvd
      rw [e1, e2]
  | algebraMap r =>
      have hfix : ringOfIntegersComplexConj K (algebraMap ℤ (𝓞 K) r)
          = algebraMap ℤ (𝓞 K) r := by
        rw [eq_intCast (algebraMap ℤ (𝓞 K)) r, map_intCast]
      rw [hfix]
  | add a b _ _ iha ihb =>
      rw [map_add (ringOfIntegersComplexConj K) a b,
          map_add (Ideal.Quotient.mk _) _ _, iha, ihb,
          map_add (Ideal.Quotient.mk _) a b]
  | mul a b _ _ iha ihb =>
      rw [map_mul (ringOfIntegersComplexConj K) a b,
          map_mul (Ideal.Quotient.mk _) _ _, iha, ihb,
          map_mul (Ideal.Quotient.mk _) a b]

/-- **HEADLINE — the Hasse unit index is `1` for `ℚ(ζ_p)`, every odd prime `p`.**
`[(𝓞 K)ˣ : μ_K · (𝓞 K⁺)ˣ] = 1`. mathlib computes this index for no field. -/
theorem indexRealUnits_eq_one (hζ : IsPrimitiveRoot (ζ : K) p) (hodd : p ≠ 2) :
    NumberField.IsCMField.indexRealUnits K = 1 := by
  rcases indexRealUnits_eq_one_or_two K with h | h
  · exact h
  · exfalso
    rw [indexRealUnits_eq_two_iff] at h
    obtain ⟨u, hu⟩ := h
    set I := Ideal.span {hζ.toInteger - 1} with hI
    set φ : (𝓞 K)ˣ →* (𝓞 K ⧸ I)ˣ := Units.map (Ideal.Quotient.mk I).toMonoidHom with hφ
    have hφcoe : ∀ a : (𝓞 K)ˣ, (φ a : 𝓞 K ⧸ I) = Ideal.Quotient.mk I (a : 𝓞 K) := by
      intro a; rw [hφ]; rfl
    have hconj : φ (unitsComplexConj K u) = φ u := by
      apply Units.ext
      rw [hφcoe, hφcoe]
      have hbridge : ((unitsComplexConj K u : (𝓞 K)ˣ) : 𝓞 K)
          = ringOfIntegersComplexConj K (u : 𝓞 K) := rfl
      rw [hbridge, hI, conj_mk_eq hζ (u : 𝓞 K)]
    have hφt : φ (↑(unitsMulComplexConjInv K u)) = 1 := by
      rw [unitsMulComplexConjInv_apply, map_mul, map_inv, hconj]
      group
    have hneg : (⟨-1, neg_one_mem_torsion⟩ : torsion K) ∈
        Subgroup.zpowers (unitsMulComplexConjInv K u) := by
      rw [hu]; exact Subgroup.mem_top _
    obtain ⟨k, hk⟩ := hneg
    have hk' : (↑(unitsMulComplexConjInv K u) : (𝓞 K)ˣ) ^ k = -1 := by
      have hc := congrArg (fun y : torsion K => (y : (𝓞 K)ˣ)) hk
      simpa [Subgroup.coe_zpow] using hc
    have hcontra : φ (-1 : (𝓞 K)ˣ) = 1 := by
      have hc := congrArg φ hk'
      rwa [map_zpow, hφt, one_zpow, eq_comm] at hc
    have hmk : Ideal.Quotient.mk I (-1 : 𝓞 K) = 1 := by
      have hc := congrArg Units.val hcontra
      rw [hφcoe] at hc
      simpa using hc
    have hsub : (-1 : 𝓞 K) - 1 ∈ I := (Ideal.Quotient.mk_eq_one_iff_sub_mem _).mp hmk
    rw [hI, Ideal.mem_span_singleton] at hsub
    have hdvd2 : (hζ.toInteger - 1) ∣ ((2 : ℤ) : 𝓞 K) := by
      have h2 : ((2 : ℤ) : 𝓞 K) = -((-1 : 𝓞 K) - 1) := by push_cast; ring
      rw [h2]; exact dvd_neg.mpr hsub
    rw [lambda_dvd_intCast_iff hζ hodd 2] at hdvd2
    have hp2 : p ∣ 2 := by exact_mod_cast hdvd2
    exact hodd ((Nat.prime_dvd_prime_iff_eq hpp.out Nat.prime_two).mp hp2)

/-- **Every unit of `𝓞(ℚ(ζ_p))` is a root of unity times a real unit** (odd prime `p`).
Consequence of `Q = 1`: `(𝓞 K)ˣ = μ_K · (𝓞 K⁺)ˣ`. -/
theorem unit_eq_torsion_mul_real (hζ : IsPrimitiveRoot (ζ : K) p) (hodd : p ≠ 2)
    (u : (𝓞 K)ˣ) :
    ∃ (t : torsion K) (v : (𝓞 K)ˣ), v ∈ realUnits K ∧ u = (t : (𝓞 K)ˣ) * v := by
  have htop : realUnits K ⊔ torsion K = ⊤ := by
    have := indexRealUnits_eq_one hζ hodd
    rwa [NumberField.IsCMField.indexRealUnits, Subgroup.index_eq_one] at this
  have hu : u ∈ realUnits K ⊔ torsion K := htop ▸ Subgroup.mem_top u
  rw [Subgroup.mem_sup] at hu
  obtain ⟨v, hv, t, ht, hvt⟩ := hu
  exact ⟨⟨t, ht⟩, v, hv, by rw [← hvt]; exact (mul_comm v t)⟩

end CM

end BealCyclotomicUnitIndex
