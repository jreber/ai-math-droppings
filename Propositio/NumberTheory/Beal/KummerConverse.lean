import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.RingTheory.RootsOfUnity.CyclotomicUnits
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.Tactic
import Propositio.NumberTheory.Beal.LambdaCongruence

/-!
# Converse Kummer condition for `p = 5`

This file proves the converse direction of the Kummer divisibility criterion:

  `(1 - ζ)⁴ ∣ φⁿ − 3ⁿ` in `𝓞(ℚ(ζ₅))` implies `5 ∣ n`.

Combined with `BealLambdaCongruence.phi_pow_cong_mod_lambda4_five_dvd_ring` (forward
direction), this gives the **biconditional** `5 ∣ n ↔ (1-ζ)⁴ ∣ φⁿ − 3ⁿ`.

## Strategy

From `phi_pow_mod_lambda4_ring`:  φⁿ − 3ⁿ = λ²·(n·3^{n-1}·ζ⁴) + λ⁴·c₀.
From hypothesis:                  φⁿ − 3ⁿ = λ⁴·d.
Subtract → cancel λ²:            n·3^{n-1}·ζ⁴ = λ²·(d − c₀).
Hence λ ∣ n·3^{n-1}·ζ⁴.  Since ζ⁴ is a unit and λ ∤ 3 (Bezout with 5), λ ∣ n.
Then `norm_dvd_iff` (N(λ) = 5) gives 5 ∣ n.
-/

open scoped NumberField

namespace BealKummerConverse

variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {5} ℚ K]

private theorem lam_dvd_iff_five {ζ : K} (hζ : IsPrimitiveRoot ζ 5) (n : ℤ) :
    (hζ.toInteger - 1) ∣ ((n : ℤ) : 𝓞 K) ↔ (5 : ℤ) ∣ n := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hprime : Prime (Algebra.norm ℤ (hζ.toInteger - 1)) :=
    hζ.prime_norm_toInteger_sub_one_of_prime_ne_two' (by decide)
  have hnorm : Algebra.norm ℤ (hζ.toInteger - 1) = 5 :=
    hζ.norm_toInteger_sub_one_of_prime_ne_two' (by decide)
  have hiff := Ideal.norm_dvd_iff hprime (y := n)
  rw [hnorm] at hiff
  exact hiff.symm

/-- **Converse Kummer condition** (`p = 5`):
`(1-ζ)⁴ ∣ φⁿ − 3ⁿ` in `𝓞(ℚ(ζ₅))` implies `5 ∣ n`.

See also `BealLambdaCongruence.phi_pow_cong_mod_lambda4_five_dvd_ring` for the forward
direction; together they yield `phi_pow_cong_lambda4_iff`. -/
theorem five_dvd_of_lambda4_dvd_phi_pow_sub_three {ζ : K}
    (hζ : IsPrimitiveRoot ζ 5) (n : ℕ)
    (hdvd : (1 - hζ.toInteger) ^ 4 ∣
      (1 + hζ.toInteger + hζ.toInteger ^ 4) ^ n - (3 : 𝓞 K) ^ n) :
    5 ∣ n := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  set η := hζ.toInteger with hη_def
  have hη : IsPrimitiveRoot η 5 := hζ.toInteger_isPrimitiveRoot
  have h5 : η ^ 5 = 1 := hη.pow_eq_one
  have hne1 : η ≠ 1 := hη.ne_one (by norm_num : 1 < 5)
  have hne : (1 - η) ≠ 0 := fun h => hne1 (sub_eq_zero.mp h).symm
  have hne2 : (1 - η) ^ 2 ≠ 0 := pow_ne_zero 2 hne
  have hlamPrime : Prime (1 - η) := by
    rw [show (1 - η) = -(η - 1) from by ring]; exact hζ.zeta_sub_one_prime'.neg
  have hsum : (1 : 𝓞 K) + η + η ^ 2 + η ^ 3 + η ^ 4 = 0 := by
    have hprod : (η - 1) * (1 + η + η ^ 2 + η ^ 3 + η ^ 4) = 0 := by linear_combination h5
    rcases mul_eq_zero.mp hprod with h | h
    · exact absurd (sub_eq_zero.mp h) hne1
    · exact h
  have hfive_eq : (1 - η) ^ 4 * (-1 - η + η ^ 3 : 𝓞 K) = 5 := by
    linear_combination (5 - 4 * η + η ^ 2) * h5 - hsum
  have hfive_dvd : (1 - η) ∣ (5 : 𝓞 K) :=
    (dvd_pow_self (1 - η) (by norm_num : 4 ≠ 0)).trans ⟨-1 - η + η ^ 3, hfive_eq.symm⟩
  -- Extract witnesses (Classical.choose avoids propRecLargeElim in Prop context)
  let c₀ : 𝓞 K :=
    (BealLambdaCongruence.phi_pow_mod_lambda4_ring h5 hne1 n).choose
  have hc₀ : (1 + η + η ^ 4) ^ n - (3 : 𝓞 K) ^ n =
      (1 - η) ^ 2 * ((n : 𝓞 K) * (3 : 𝓞 K) ^ (n - 1) * η ^ 4) + (1 - η) ^ 4 * c₀ :=
    (BealLambdaCongruence.phi_pow_mod_lambda4_ring h5 hne1 n).choose_spec
  let d : 𝓞 K := hdvd.choose
  have hd : (1 + η + η ^ 4) ^ n - (3 : 𝓞 K) ^ n = (1 - η) ^ 4 * d := hdvd.choose_spec
  have heq : (1 - η) ^ 2 * ((n : 𝓞 K) * (3 : 𝓞 K) ^ (n - 1) * η ^ 4) =
             (1 - η) ^ 4 * (d - c₀) := by linear_combination hd - hc₀
  have hcancel : (n : 𝓞 K) * (3 : 𝓞 K) ^ (n - 1) * η ^ 4 = (1 - η) ^ 2 * (d - c₀) := by
    apply mul_left_cancel₀ hne2
    calc (1 - η) ^ 2 * ((n : 𝓞 K) * (3 : 𝓞 K) ^ (n - 1) * η ^ 4) = (1 - η) ^ 4 * (d - c₀) := heq
      _ = (1 - η) ^ 2 * ((1 - η) ^ 2 * (d - c₀)) := by ring
  have hdvd_prod : (1 - η) ∣ (n : 𝓞 K) * (3 : 𝓞 K) ^ (n - 1) * η ^ 4 :=
    ⟨(1 - η) * (d - c₀), by linear_combination hcancel⟩
  have hdvd_n3 : (1 - η) ∣ (n : 𝓞 K) * (3 : 𝓞 K) ^ (n - 1) := by
    obtain ⟨c, hc⟩ := hdvd_prod
    exact ⟨c * η, by linear_combination η * hc - (n : 𝓞 K) * (3 : 𝓞 K) ^ (n - 1) * h5⟩
  have hn_not_3 : ¬ (1 - η) ∣ (3 : 𝓞 K) := by
    intro h3
    have h1 : (1 - η) ∣ (1 : 𝓞 K) :=
      calc (1 - η) ∣ (2 : 𝓞 K) * 3 - 1 * 5 :=
            dvd_sub (dvd_mul_of_dvd_right h3 2) (dvd_mul_of_dvd_right hfive_dvd 1)
        _ = 1 := by norm_num
    exact absurd (isUnit_of_dvd_one h1) hlamPrime.not_unit
  have hn_dvd_lam : (1 - η) ∣ (n : 𝓞 K) :=
    (hlamPrime.dvd_or_dvd hdvd_n3).resolve_right (mt hlamPrime.dvd_of_dvd_pow hn_not_3)
  have h5n_int : (5 : ℤ) ∣ (n : ℤ) := by
    apply (lam_dvd_iff_five hζ n).mp
    have : (1 - η) ∣ ((n : ℕ) : 𝓞 K) := hn_dvd_lam
    rwa [show ((n : ℕ) : 𝓞 K) = ((n : ℤ) : 𝓞 K) from by push_cast; rfl,
         show (1 - η) = -(η - 1) from by ring, neg_dvd] at this
  exact_mod_cast h5n_int

/-- **Biconditional Kummer condition** (`p = 5`):
`5 ∣ n ↔ (1-ζ)⁴ ∣ φⁿ − 3ⁿ` in `𝓞(ℚ(ζ₅))`. -/
theorem phi_pow_cong_lambda4_iff {ζ : K}
    (hζ : IsPrimitiveRoot ζ 5) (n : ℕ) :
    5 ∣ n ↔
    (1 - hζ.toInteger) ^ 4 ∣
      (1 + hζ.toInteger + hζ.toInteger ^ 4) ^ n - (3 : 𝓞 K) ^ n := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  set η := hζ.toInteger
  have hη : IsPrimitiveRoot η 5 := hζ.toInteger_isPrimitiveRoot
  have h5 : η ^ 5 = 1 := hη.pow_eq_one
  have hne1 : η ≠ 1 := hη.ne_one (by norm_num : 1 < 5)
  exact ⟨BealLambdaCongruence.phi_pow_cong_mod_lambda4_five_dvd_ring h5 hne1 n,
         five_dvd_of_lambda4_dvd_phi_pow_sub_three hζ n⟩

#print axioms five_dvd_of_lambda4_dvd_phi_pow_sub_three
#print axioms phi_pow_cong_lambda4_iff

end BealKummerConverse
