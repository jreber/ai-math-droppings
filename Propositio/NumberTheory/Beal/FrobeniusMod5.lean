import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.Tactic

/-!
# Frobenius mod λ⁴ for (5,5,z) Beal solutions

**Main theorem** (`beal_55z_frobenius_mod_lambda4`): For any solution A⁵+B⁵ = C^z in ℕ,
the element (A+Bζ)⁵ − C^z is divisible by λ⁴ = (1−ζ)⁴ in 𝓞K.

**Proof**:
1. λ ∣ (A+Bζ) − (A+B) since A+Bζ − (A+B) = −B·(1−ζ) = −B·λ
2. Frobenius ring identity: λ⁴ ∣ (A+Bζ)⁵ − (A+B)⁵  [binomial + 5=(1-ζ)⁴·(-1-ζ+ζ³)]
3. Fermat: 5 ∣ (A+B)⁵ − (A+B) and 5 ∣ C^z − (A+B)  [via ZMod 5 and the equation]
4. λ⁴ ∣ 5, so λ⁴ ∣ (A+B)⁵ − (A+B) and λ⁴ ∣ C^z − (A+B)
5. (A+Bζ)⁵ − C^z = [(A+Bζ)⁵−(A+B)⁵] + [(A+B)⁵−(A+B)] − [C^z−(A+B)]  → λ⁴ divides.

**Corollary** (`beal_55z_descent_fifth_power_mod_lambda4`): From the descent A+Bζ = d^z·v,
this gives d^{5z}·v⁵ ≡ C^z (mod λ⁴), constraining the Kummer unit v via its 5th power.
-/

namespace BealFrobeniusMod5

open scoped NumberField

variable {K : Type*} [Field K] [NumberField K]

/-- Fermat's little theorem (k^5 = k mod 5) for natural numbers, cast to ℤ. -/
private theorem fermat_five (k : ℕ) : (5 : ℤ) ∣ (k : ℤ) ^ 5 - k := by
  have key : ∀ x : ZMod 5, x ^ 5 = x := by decide
  have h0 : ((k : ℤ) : ZMod 5) ^ 5 - ((k : ℤ) : ZMod 5) = 0 := by
    push_cast; rw [key]; ring
  exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ 5).mp (by push_cast; exact h0)

/-- **Frobenius mod λ⁴ for (5,5,z) solutions.**

For any A⁵+B⁵ = C^z with A B C z : ℕ, we have `(1-ζ)⁴ ∣ (A+Bζ)⁵ − C^z` in 𝓞K.

This is the cyclotomic footprint of a (5,5,z) solution: the 5th power of A+Bζ and C^z
agree modulo the 5-ramification ideal `(λ)⁴ = (5)` in 𝓞K. -/
theorem beal_55z_frobenius_mod_lambda4 {ζ : K} (hζ : IsPrimitiveRoot ζ 5)
    {A B C z : ℕ} (h : A ^ 5 + B ^ 5 = C ^ z) :
    (1 - hζ.toInteger) ^ 4 ∣
      ((A : 𝓞 K) + B * hζ.toInteger) ^ 5 - (C : 𝓞 K) ^ z := by
  set η := hζ.toInteger with hη_def
  have hη5 : η ^ 5 = 1 := hζ.toInteger_isPrimitiveRoot.pow_eq_one
  have hηne1 : η ≠ 1 := hζ.toInteger_isPrimitiveRoot.ne_one (by norm_num)
  -- Geometric sum: 1+η+η²+η³+η⁴ = 0
  have hsum : (1 : 𝓞 K) + η + η ^ 2 + η ^ 3 + η ^ 4 = 0 := by
    have hprod : (η - 1) * (1 + η + η ^ 2 + η ^ 3 + η ^ 4) = 0 := by linear_combination hη5
    rcases mul_eq_zero.mp hprod with h1 | h1
    · exact absurd (sub_eq_zero.mp h1) hηne1
    · exact h1
  -- Key ramification identity: (1-η)⁴·(-1-η+η³) = 5
  have hfive : (1 - η) ^ 4 * (-1 - η + η ^ 3 : 𝓞 K) = 5 := by
    linear_combination (5 - 4 * η + η ^ 2) * hη5 - hsum
  -- Step 1: (1-η) ∣ (A+Bη) − (A+B)
  have hstep1 : (1 - η) ∣ ((A : 𝓞 K) + B * η - ((A : 𝓞 K) + B)) :=
    ⟨-(B : 𝓞 K), by ring⟩
  obtain ⟨c, hc⟩ := hstep1
  have hα : (A : 𝓞 K) + B * η = ((A : 𝓞 K) + B) + (1 - η) * c := by
    linear_combination hc
  -- Step 2: (1-η)⁴ ∣ (A+Bη)⁵ − (A+B)⁵  [Frobenius: binomial expansion + 5=(1-η)⁴·u]
  have hfrob : (1 - η) ^ 4 ∣ ((A : 𝓞 K) + B * η) ^ 5 - ((A : 𝓞 K) + B) ^ 5 := by
    set β : 𝓞 K := (A : 𝓞 K) + B
    -- hu : 5 = (1-η)⁴·(-1-η+η³)  [same as hfive, rewritten for linear_combination orientation]
    have hu : (5 : 𝓞 K) = (1 - η) ^ 4 * (-1 - η + η ^ 3) := by linear_combination -hfive
    refine ⟨(-1 - η + η ^ 3) * β ^ 4 * (1 - η) * c
            + 2 * (-1 - η + η ^ 3) * β ^ 3 * (1 - η) ^ 2 * c ^ 2
            + 2 * (-1 - η + η ^ 3) * β ^ 2 * (1 - η) ^ 3 * c ^ 3
            + 5 * β * c ^ 4 + (1 - η) * c ^ 5, ?_⟩
    rw [hα]
    linear_combination
      (β ^ 4 * (1 - η) * c
       + 2 * β ^ 3 * (1 - η) ^ 2 * c ^ 2
       + 2 * β ^ 2 * (1 - η) ^ 3 * c ^ 3) * hu
  -- Step 3a: (1-η)⁴ ∣ (A+B)⁵ − (A+B)  [Fermat for A+B]
  have hfermat_AB : (1 - η) ^ 4 ∣ ((A : 𝓞 K) + B) ^ 5 - ((A : 𝓞 K) + B) := by
    obtain ⟨k, hk⟩ := fermat_five (A + B)
    have h5K : ((A : 𝓞 K) + B) ^ 5 - ((A : 𝓞 K) + B) = 5 * (k : 𝓞 K) := by
      exact_mod_cast hk
    rw [h5K]
    exact ⟨(-1 - η + η ^ 3) * (k : 𝓞 K), by linear_combination -(k : 𝓞 K) * hfive⟩
  -- Step 3b: (1-η)⁴ ∣ C^z − (A+B)  [from h: A⁵+B⁵=C^z and Fermat for A, B]
  have hCz : (1 - η) ^ 4 ∣ (C : 𝓞 K) ^ z - ((A : 𝓞 K) + B) := by
    obtain ⟨kA, hkA⟩ := fermat_five A
    obtain ⟨kB, hkB⟩ := fermat_five B
    have h5 : (5 : ℤ) ∣ (C : ℤ) ^ z - (A + B) := by
      have hAB : (A : ℤ) ^ 5 + B ^ 5 = C ^ z := by exact_mod_cast h
      exact ⟨kA + kB, by linarith⟩
    obtain ⟨m, hm⟩ := h5
    have h5K : (C : 𝓞 K) ^ z - ((A : 𝓞 K) + B) = 5 * (m : 𝓞 K) := by
      exact_mod_cast hm
    rw [h5K]
    exact ⟨(-1 - η + η ^ 3) * (m : 𝓞 K), by linear_combination -(m : 𝓞 K) * hfive⟩
  -- Combine: (A+Bη)⁵ − C^z = [(A+Bη)⁵−(A+B)⁵] + [(A+B)⁵−(A+B)] − [C^z−(A+B)]
  have key : ((A : 𝓞 K) + B * η) ^ 5 - (C : 𝓞 K) ^ z =
      (((A : 𝓞 K) + B * η) ^ 5 - ((A : 𝓞 K) + B) ^ 5) +
      (((A : 𝓞 K) + B) ^ 5 - ((A : 𝓞 K) + B)) -
      ((C : 𝓞 K) ^ z - ((A : 𝓞 K) + B)) := by ring
  rw [key]
  exact (hfrob.add hfermat_AB).sub hCz

/-- **Corollary**: If A+Bζ = d^z·v (Beal descent), then d^{5z}·v⁵ ≡ C^z (mod λ⁴).

This directly constrains the Kummer unit v: since v⁵ = φ^{5n} ≡ 3^{5n} (mod λ⁴)
(because 5∣5n), the mod-λ⁴ value of d^{5z} determines C^z mod 5. -/
theorem beal_55z_descent_fifth_power_mod_lambda4 {ζ : K} (hζ : IsPrimitiveRoot ζ 5)
    {A B C z : ℕ} (h : A ^ 5 + B ^ 5 = C ^ z)
    (d : 𝓞 K) (v : (𝓞 K)ˣ)
    (hdescent : (A : 𝓞 K) + B * hζ.toInteger = d ^ z * v) :
    (1 - hζ.toInteger) ^ 4 ∣ d ^ (5 * z) * (v : 𝓞 K) ^ 5 - (C : 𝓞 K) ^ z := by
  have hmain := beal_55z_frobenius_mod_lambda4 hζ h
  rw [hdescent] at hmain
  convert hmain using 1
  ring

/-- **Outside approach bridge**: the Beal descent A+Bζ = d^z·v takes the EXACT form
  d^z·v = s^z − B·(1−ζ)
when A+B = s^z (which `BealPrimeDescent.prime_sum_descent p=5` provides elementarily).

This bridges the elementary ℤ factorization (s^z = A+B is a perfect z-th power) with
the cyclotomic descent. The equation d^z·v = s^z − B·λ is the starting point for
computing d mod λ^{k} by comparing the λ-adic expansions of both sides. -/
theorem beal_55z_descent_exact_form {ζ : K} (hζ : IsPrimitiveRoot ζ 5)
    {A B z : ℕ} (s : ℕ) (hAB_sum : A + B = s ^ z)
    (d : 𝓞 K) (v : (𝓞 K)ˣ)
    (hdescent : (A : 𝓞 K) + B * hζ.toInteger = d ^ z * v) :
    d ^ z * (v : 𝓞 K) = (s : 𝓞 K) ^ z - B * (1 - hζ.toInteger) := by
  rw [← hdescent]
  have h : (s : 𝓞 K) ^ z = (A : 𝓞 K) + B := by exact_mod_cast hAB_sum.symm
  linear_combination -h

#print axioms beal_55z_frobenius_mod_lambda4
#print axioms beal_55z_descent_fifth_power_mod_lambda4
#print axioms beal_55z_descent_exact_form

end BealFrobeniusMod5
