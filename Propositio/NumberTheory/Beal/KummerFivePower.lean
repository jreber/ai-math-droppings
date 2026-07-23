import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.RingTheory.RootsOfUnity.CyclotomicUnits
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.Tactic
import Propositio.NumberTheory.Beal.LambdaCongruence
import Propositio.NumberTheory.Beal.KummerConverse

/-!
# Kummer's p=5 lemma: congruence to ANY integer mod λ⁴ forces 5|n

`BealKummerConverse.five_dvd_of_lambda4_dvd_phi_pow_sub_three` requires the specific
witness `3ⁿ`:  `(1-ζ)⁴ ∣ φⁿ − 3ⁿ → 5∣n`.

This file proves the stronger statement where the witness can be *any* rational integer:

  `(1-ζ)⁴ ∣ φⁿ − r  (r : ℤ) → 5∣n`

and the immediate corollary:

  `(1-ζ)⁴ ∣ φⁿ − r → ∃ w : K, φⁿ = w⁵`

## Proof strategy

1. `phi_pow_mod_lambda4_ring`: `(1-η)²  ∣ φⁿ − 3ⁿ` always.
2. Hypothesis:               `(1-η)⁴  ∣ φⁿ − r`.
3. Subtract (after (1-η)²|φⁿ-r from step 2): `(1-η)² ∣ r − 3ⁿ` in 𝓞K.
4. Since r−3ⁿ ∈ ℤ: `(1-ζ)∣(r−3ⁿ) ↔ 5∣(r−3ⁿ)` (`Ideal.norm_dvd_iff`, N(λ)=5).
5. `r−3ⁿ = 5m`, and `5 = (1-η)⁴·unit`, so `(1-η)⁴ ∣ r−3ⁿ`.
6. Adding the hypothesis: `(1-η)⁴ ∣ φⁿ−3ⁿ`.
7. `BealKummerConverse.five_dvd_of_lambda4_dvd_phi_pow_sub_three` gives `5∣n`.
-/

open scoped NumberField

namespace BealKummerFivePower

variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {5} ℚ K]

private theorem lam_dvd_iff_five' {ζ : K} (hζ : IsPrimitiveRoot ζ 5) (n : ℤ) :
    (1 - hζ.toInteger) ∣ ((n : ℤ) : 𝓞 K) ↔ (5 : ℤ) ∣ n := by
  rw [show (1 - hζ.toInteger) = -(hζ.toInteger - 1) from by ring, neg_dvd]
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hprime : Prime (Algebra.norm ℤ (hζ.toInteger - 1)) :=
    hζ.prime_norm_toInteger_sub_one_of_prime_ne_two' (by decide)
  have hnorm : Algebra.norm ℤ (hζ.toInteger - 1) = 5 :=
    hζ.norm_toInteger_sub_one_of_prime_ne_two' (by decide)
  rw [← hnorm]
  exact (Ideal.norm_dvd_iff hprime).symm

/-- **Extended Kummer converse for p=5**: `(1-ζ)⁴ ∣ φⁿ − r` for ANY `r : ℤ` forces `5 ∣ n`.

Extends `BealKummerConverse.five_dvd_of_lambda4_dvd_phi_pow_sub_three`, which requires the
specific witness `r = 3ⁿ`. The key insight: `λ²∣(r−3ⁿ)` for an integer implies `λ⁴∣(r−3ⁿ)`
because `(λ)²∩ℤ = (λ)⁴∩ℤ = 5ℤ` (totally ramified, `(5)=(λ)⁴`). -/
theorem five_dvd_of_lambda4_dvd_phi_pow_sub_int {ζ : K}
    (hζ : IsPrimitiveRoot ζ 5) (n : ℕ) (r : ℤ)
    (hdvd : (1 - hζ.toInteger) ^ 4 ∣
      (1 + hζ.toInteger + hζ.toInteger ^ 4) ^ n - (r : 𝓞 K)) :
    5 ∣ n := by
  set η := hζ.toInteger with hη_def
  have hη : IsPrimitiveRoot η 5 := hζ.toInteger_isPrimitiveRoot
  have h5 : η ^ 5 = 1 := hη.pow_eq_one
  have hne1 : η ≠ 1 := hη.ne_one (by norm_num : 1 < 5)
  have hsum : (1 : 𝓞 K) + η + η ^ 2 + η ^ 3 + η ^ 4 = 0 := by
    have hprod : (η - 1) * (1 + η + η ^ 2 + η ^ 3 + η ^ 4) = 0 := by linear_combination h5
    rcases mul_eq_zero.mp hprod with h | h
    · exact absurd (sub_eq_zero.mp h) hne1
    · exact h
  -- 5 = (1-η)⁴·(-1-η+η³): key factorization giving λ⁴|(5·anything)
  have hfive_eq : (1 - η) ^ 4 * (-1 - η + η ^ 3 : 𝓞 K) = 5 := by
    linear_combination (5 - 4 * η + η ^ 2) * h5 - hsum
  -- φⁿ - 3ⁿ = (1-η)²·A + (1-η)⁴·c₀
  obtain ⟨c₀, hc₀⟩ := BealLambdaCongruence.phi_pow_mod_lambda4_ring h5 hne1 n
  -- Hypothesis: φⁿ - r = (1-η)⁴·d
  obtain ⟨d, hd⟩ := hdvd
  -- (1-η)² | φⁿ - r  (since (1-η)⁴ divides)
  have hdvd2 : (1 - η) ^ 2 ∣ (1 + η + η ^ 4) ^ n - (r : 𝓞 K) :=
    ⟨(1 - η) ^ 2 * d, by rw [hd]; ring⟩
  -- (1-η)² | φⁿ - 3ⁿ  (extracted from hc₀)
  have hdvd2_3 : (1 - η) ^ 2 ∣ (1 + η + η ^ 4) ^ n - (3 : 𝓞 K) ^ n :=
    ⟨(n : 𝓞 K) * (3 : 𝓞 K) ^ (n - 1) * η ^ 4 + (1 - η) ^ 2 * c₀, by rw [hc₀]; ring⟩
  -- (1-η)² | r - 3ⁿ  (difference of the two)
  have hdvd2_diff : (1 - η) ^ 2 ∣ ((r : 𝓞 K) - (3 : 𝓞 K) ^ n) := by
    obtain ⟨a, ha⟩ := hdvd2
    obtain ⟨b, hb⟩ := hdvd2_3
    exact ⟨b - a, by linear_combination hb - ha⟩
  -- (1-η) | r - 3ⁿ  (from (1-η)² divides)
  have hdvd1_diff : (1 - η) ∣ ((r : 𝓞 K) - (3 : 𝓞 K) ^ n) := by
    obtain ⟨e, he⟩ := hdvd2_diff
    exact ⟨(1 - η) * e, by rw [he]; ring⟩
  -- r - 3ⁿ as integer cast
  have hcast : ((r : 𝓞 K) - (3 : 𝓞 K) ^ n) = ((r - 3 ^ n : ℤ) : 𝓞 K) := by
    push_cast; ring
  rw [hcast] at hdvd1_diff
  -- 5 | (r - 3ⁿ) via norm_dvd_iff (N(λ)=5)
  have h5diff : (5 : ℤ) ∣ (r - 3 ^ n) := (lam_dvd_iff_five' hζ _).mp hdvd1_diff
  obtain ⟨m, hm⟩ := h5diff
  -- (1-η)⁴ | r - 3ⁿ  (since r-3ⁿ = 5m = (1-η)⁴·unit·m)
  have hdvd4_diff : (1 - η) ^ 4 ∣ ((r : 𝓞 K) - (3 : 𝓞 K) ^ n) := by
    rw [hcast, show (r - 3 ^ n : ℤ) = 5 * m from hm]
    exact ⟨(-1 - η + η ^ 3) * (m : 𝓞 K), by
      push_cast
      linear_combination -(m : 𝓞 K) * hfive_eq⟩
  -- (1-η)⁴ | φⁿ - 3ⁿ  (sum of two (1-η)⁴-divisible terms)
  have hdvd4_phi3 : (1 - η) ^ 4 ∣ (1 + η + η ^ 4) ^ n - (3 : 𝓞 K) ^ n := by
    obtain ⟨u, hu⟩ := hdvd4_diff
    exact ⟨d + u, by linear_combination hd + hu⟩
  -- Conclude 5|n by the already-proved converse
  exact BealKummerConverse.five_dvd_of_lambda4_dvd_phi_pow_sub_three hζ n hdvd4_phi3

/-- If φⁿ ≡ r (mod λ⁴) for some integer r, then φⁿ is a 5th power in K. -/
theorem phi_pow_lambda4_is_fifth_power {ζ : K}
    (hζ : IsPrimitiveRoot ζ 5) (n : ℕ) (r : ℤ)
    (hdvd : (1 - hζ.toInteger) ^ 4 ∣
      (1 + hζ.toInteger + hζ.toInteger ^ 4) ^ n - (r : 𝓞 K)) :
    ∃ w : K, (1 + ζ + ζ ^ 4 : K) ^ n = w ^ 5 := by
  obtain ⟨m, rfl⟩ := five_dvd_of_lambda4_dvd_phi_pow_sub_int hζ n r hdvd
  exact ⟨(1 + ζ + ζ ^ 4) ^ m, by rw [← pow_mul, mul_comm]⟩

#print axioms five_dvd_of_lambda4_dvd_phi_pow_sub_int
#print axioms phi_pow_lambda4_is_fifth_power

end BealKummerFivePower
