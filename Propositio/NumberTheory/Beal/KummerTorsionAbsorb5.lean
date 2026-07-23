import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.Tactic

/-!
# Kummer p=5: Torsion Absorption Lemma

**Breaking-monoculture route (2026-06-26):** NOT Baker-class.

The three previously recorded failed approaches (Frobenius expansion, real subfield norm,
λ-adic expansion) all attempted to prove `u ≡ r (mod λ⁴)` directly for u = ζ^k·v WITHOUT
first absorbing the torsion factor ζ^k. This file closes the torsion-absorption sub-target.

## Key insight

Given `A + B·ζ = d^z · u` with `u = ζ^k · v` (v real) and `gcd(z,10)=1`:
- Since `gcd(z,5)=1`, there exists j with `z*j ≡ k (mod 5)`.
- Then `ζ^k = (ζ^j)^z` (using ζ^5=1).
- So `A + B·ζ = d^z · ζ^k · v = (d · ζ^j)^z · v`.
- The torsion factor is ABSORBED into d, leaving only the real unit v.

## What is proved

1. `zeta5_isPow_of_coprime` — ζ₅ is a z-th power in 𝓞(K) when `gcd(z,5)=1`.
   (Analogue of `BealCubeSynthesis.eta_isPow_of_coprime_three` for p=3.)

2. `kummer_absorb_zeta_pow_5` — if x = ζ^k · d^z and `gcd(z,5)=1`, then ∃ d', x = d'^z.
   (Analogue of `BealCubeSynthesis.kummer_absorb_eta_pow` for p=3.)

The remaining gap after this absorption is `beal_descent_lambda2_congruence`: the REAL unit v
is congruent to a rational integer mod λ². That follows from the ℤ-basis of 𝓞(K⁺) = ℤ[η]
(where η = ζ+ζ⁴) combined with the identity `phi_mod_lambda_sq: (1+ζ+ζ⁴) - 3 = (1-ζ)²·ζ⁴`
proved in `BealLambdaCongruence`. See `beal_ring_of_integers_basis_K_plus.json` in the KB.

`lake env lean BealKummerTorsionAbsorb5.lean` to typecheck (fast — no CM imports).
-/

open NumberField

namespace BealKummerTorsionAbsorb5

/-- **ζ₅ is a z-th power in 𝓞(K) when gcd(z,5)=1.**

For any primitive 5th root ζ and any z with gcd(z,5)=1, there exists w ∈ 𝓞(K) such that
w^z = ζ (the integer `toInteger`). The witness is ζ^j where j satisfies z·j ≡ 1 (mod 5).

Proof: since z%5 ∈ {1,2,3,4} (coprimality), find j with z*j ≡ 1 (mod 5) by case analysis.
Then (ζ^j)^z = ζ^(z·j) = ζ^(z·j mod 5) = ζ^1 = ζ (using ζ^5=1 to reduce mod 5). -/
theorem zeta5_isPow_of_coprime {K : Type*} [Field K] [NumberField K]
    [IsCyclotomicExtension {5} ℚ K] {ζ : K} (hζ : IsPrimitiveRoot ζ 5)
    {z : ℕ} (hcop : Nat.Coprime z 5) :
    ∃ w : 𝓞 K, w ^ z = hζ.toInteger := by
  haveI : NeZero 5 := ⟨by norm_num⟩
  have hfive : hζ.toInteger ^ 5 = 1 := hζ.toInteger_isPrimitiveRoot.pow_eq_one
  obtain ⟨j, hj⟩ : ∃ j : ℕ, z * j % 5 = 1 % 5 := by
    have hz5 : z % 5 ≠ 0 := by
      intro h0
      have hdz : (5 : ℕ) ∣ z := Nat.dvd_of_mod_eq_zero h0
      have h51 : (5 : ℕ) ∣ Nat.gcd z 5 := Nat.dvd_gcd hdz (dvd_refl 5)
      rw [hcop] at h51; omega
    have h4 : z % 5 = 1 ∨ z % 5 = 2 ∨ z % 5 = 3 ∨ z % 5 = 4 := by omega
    rcases h4 with h1 | h2 | h3 | h4
    · exact ⟨1, by omega⟩  -- z%5=1 → j=1: z*1 ≡ 1 mod 5
    · exact ⟨3, by omega⟩  -- z%5=2 → j=3: 2*3=6≡1 mod 5
    · exact ⟨2, by omega⟩  -- z%5=3 → j=2: 3*2=6≡1 mod 5
    · exact ⟨4, by omega⟩  -- z%5=4 → j=4: 4*4=16≡1 mod 5
  refine ⟨hζ.toInteger ^ j, ?_⟩
  rw [← pow_mul, mul_comm j z]
  have hmod : hζ.toInteger ^ (z * j) = hζ.toInteger ^ (z * j % 5) := by
    conv_lhs => rw [← Nat.div_add_mod (z * j) 5, pow_add, pow_mul, hfive, one_pow, one_mul]
  rw [hmod]
  simp only [Nat.one_mod] at hj
  rw [hj, pow_one]

/-- **Absorbing a ζ^k torsion factor into a z-th power base (p=5).**

If `x = ζ^k · d^z` and `gcd(z,5)=1`, then `∃ d', x = d'^z`. The torsion factor ζ^k is
absorbed into the new base `d' = ζ^j · d` (where j satisfies z·j ≡ 1 mod 5 so ζ^(j·z) = ζ,
hence ζ^k = (ζ^j)^(z·?) — more precisely (ζ^j)^z = ζ, so (ζ^j)^(z·k) = ζ^k, and the
key identity is: (d · ζ^j)^z = d^z · (ζ^j)^z = d^z · ζ = ζ · d^z... wait.

Correct argument: ζ^k = w^(z·k) where w = ζ^j satisfies w^z = ζ. But actually:
- w^z = ζ  →  (w^k)^z = ζ^k
- x = ζ^k · d^z = (w^k)^z · d^z = (w^k · d)^z

Take d' = w^k · d. -/
theorem kummer_absorb_zeta_pow_5 {K : Type*} [Field K] [NumberField K]
    [IsCyclotomicExtension {5} ℚ K] {ζ : K} (hζ : IsPrimitiveRoot ζ 5)
    {z : ℕ} {x d : 𝓞 K} {k : ℕ}
    (hcop : Nat.Coprime z 5)
    (hx : x = hζ.toInteger ^ k * d ^ z) :
    ∃ d' : 𝓞 K, x = d' ^ z := by
  obtain ⟨w, hw⟩ := zeta5_isPow_of_coprime hζ hcop  -- w^z = ζ
  refine ⟨w ^ k * d, ?_⟩
  -- x = ζ^k · d^z = (w^z)^k · d^z = (w^k)^z · d^z = (w^k · d)^z
  rw [mul_pow, ← pow_mul, mul_comm k z, pow_mul, hw, hx]

end BealKummerTorsionAbsorb5

-- Axiom check: should use only [propext, Classical.choice, Quot.sound]
section AxiomCheck
#print axioms BealKummerTorsionAbsorb5.zeta5_isPow_of_coprime
#print axioms BealKummerTorsionAbsorb5.kummer_absorb_zeta_pow_5
end AxiomCheck
