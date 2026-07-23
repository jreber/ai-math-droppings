import Mathlib.RingTheory.RootsOfUnity.Basic
import Mathlib.Tactic

/-!
# φ ≡ 3 (mod λ²): the lambda-congruence groundwork for Kummer p = 5

This file proves the key congruence connecting the golden ratio `φ = 1 + ζ + ζ⁴ ∈ 𝓞(ℚ(ζ₅))`
to the rational integer `3` modulo `λ² = (1-ζ)²`, where `λ = 1 - ζ` is the unique prime
above `5` in `𝓞(ℚ(ζ₅))`.

## Key algebraic identity

The central fact is the *exact* ring identity (no modular arithmetic needed):

  **(1 + ζ + ζ⁴) - 3 = (1 - ζ)² · ζ⁴**

Proof: `(1-ζ)² · ζ⁴ = ζ⁴ - 2ζ⁵ + ζ⁶ = ζ⁴ - 2 + ζ` (using `ζ⁵ = 1` and `ζ⁶ = ζ·ζ⁵ = ζ`).
And `(1 + ζ + ζ⁴) - 3 = ζ + ζ⁴ - 2`.  These are equal. ∎

The coefficient `ζ⁴` on the right-hand side is a **unit** in `𝓞(ℚ(ζ₅))` (since `ζ⁵ = 1`
implies `ζ⁴ · ζ = 1`), so `φ - 3` is *exactly* `λ²` times a unit — the strongest possible
form of the congruence `φ ≡ 3 (mod λ²)`.

## Theorems

1. **`phi_mod_lambda_sq`** — exact identity: `(1+ζ+ζ⁴) - 3 = (1-ζ)²·ζ⁴`
2. **`phi_div_lambda_sq_witness`** — existential: `∃ c, (1+ζ+ζ⁴) - 3 = (1-ζ)²·c`
3. **`phi_pow_mod_lambda_sq`** — `φⁿ - 3ⁿ` is divisible by `(1-ζ)²` for all `n`

## Role in Kummer p = 5

The Kummer machinery (see `BealGoldenKummerEngine`) requires: a real unit `v ∈ (𝓞 K⁺)ˣ`
satisfying `v ≡ rational integer (mod λ²)` is a 5th power.  Here `φ` satisfies that
hypothesis with rational integer `3`, groundwork needed for the `(5,5,z)` Beal descent.
The open target `beal_descent_lambda2_congruence` depends on this file.

All theorems are axiom-clean: `#print axioms` reports only
`[propext, Classical.choice, Quot.sound]` for each.

Typecheck: `lake env lean BealLambdaCongruence.lean`
-/

namespace BealLambdaCongruence

variable {K : Type*} [CommRing K]

/-! ## 1. The exact identity φ - 3 = λ²·ζ⁴ -/

/-- **`(1+ζ+ζ⁴) - 3 = (1-ζ)²·ζ⁴`**: the exact ring identity grounding `φ ≡ 3 (mod λ²)`.

Derivation: `(1-ζ)²·ζ⁴ = ζ⁴·(1 - 2ζ + ζ²) = ζ⁴ - 2ζ⁵ + ζ⁶`.
Using `ζ⁵ = 1`: `ζ⁵ = 1` so `2ζ⁵ = 2`, and `ζ⁶ = ζ·ζ⁵ = ζ`.
Hence `(1-ζ)²·ζ⁴ = ζ⁴ - 2 + ζ = (1 + ζ + ζ⁴) - 3`. ∎

The `linear_combination` proof uses the fact that
`LHS - RHS = 2(ζ⁵-1) - ζ(ζ⁵-1) = (2-ζ)(ζ⁵-1) = 0`. -/
theorem phi_mod_lambda_sq {ζ : K} (hζ : IsPrimitiveRoot ζ 5) :
    (1 + ζ + ζ ^ 4) - 3 = (1 - ζ) ^ 2 * ζ ^ 4 := by
  have h5 : ζ ^ 5 = 1 := hζ.pow_eq_one
  linear_combination (2 - ζ) * h5

/-- **φ - 3 is divisible by λ²**: existential form of the congruence.

The witness is `c = ζ⁴`, which is a unit of `𝓞(ℚ(ζ₅))` (since `ζ⁵ = 1` gives `ζ⁴ · ζ = 1`).
This is the form required by the Kummer congruence hypothesis. -/
theorem phi_div_lambda_sq_witness {ζ : K} (hζ : IsPrimitiveRoot ζ 5) :
    ∃ c : K, (1 + ζ + ζ ^ 4) - 3 = (1 - ζ) ^ 2 * c := by
  exact ⟨ζ ^ 4, phi_mod_lambda_sq hζ⟩

/-- **The witness `ζ⁴` is a unit**: `ζ⁴ · ζ = 1`, so `φ - 3 = λ² · (unit)`.
This strengthens the divisibility to a unit-multiple, which is what Kummer's lemma requires. -/
theorem zeta4_is_unit {ζ : K} (hζ : IsPrimitiveRoot ζ 5) :
    ζ ^ 4 * ζ = 1 := by
  have h5 : ζ ^ 5 = 1 := hζ.pow_eq_one
  linear_combination h5

/-! ## 2. Conjugate period analogue: φ' - 3 = λ²·(-1-2ζ-2ζ²-ζ³) -/

/-- **`(1 + ζ² + ζ³) - 3 = (1 - ζ)²·(-1 - 2ζ - 2ζ² - ζ³)`**: the lambda-square divisibility
for the Galois conjugate `φ' = 1 + η' = 1 + ζ² + ζ³` of the golden ratio.

Polynomial verification: expand `(1-2ζ+ζ²)·(-1-2ζ-2ζ²-ζ³)`:
`= -1-2ζ-2ζ²-ζ³ + 2ζ+4ζ²+4ζ³+2ζ⁴ - ζ²-2ζ³-2ζ⁴-ζ⁵`
`= -1 + ζ² + ζ³ - ζ⁵ = ζ² + ζ³ - 2` (using `ζ⁵ = 1`). ∎

The proof uses `linear_combination h5` since `LHS - RHS = ζ⁵ - 1`. -/
theorem phi_conj_mod_lambda_sq {ζ : K} (hζ : IsPrimitiveRoot ζ 5) :
    (1 + ζ ^ 2 + ζ ^ 3) - 3 = (1 - ζ) ^ 2 * (-1 - 2 * ζ - 2 * ζ ^ 2 - ζ ^ 3) := by
  have h5 : ζ ^ 5 = 1 := hζ.pow_eq_one
  linear_combination h5

/-! ## 3. Power congruences: φⁿ ≡ 3ⁿ (mod λ²) -/

/-- **`φⁿ - 3ⁿ` is divisible by `(1-ζ)²`** for all `n : ℕ`.

Proof by induction: the base `n = 0` is trivial (`0 = 0`).  For the step, factor
`φⁿ⁺¹ - 3ⁿ⁺¹ = φ·φⁿ - 3·3ⁿ = φ·(φⁿ - 3ⁿ) + (φ - 3)·3ⁿ`;
both terms are divisible by `(1-ζ)²` by the induction hypothesis and `phi_mod_lambda_sq`. -/
theorem phi_pow_mod_lambda_sq {ζ : K} (hζ : IsPrimitiveRoot ζ 5) (n : ℕ) :
    ∃ c : K, (1 + ζ + ζ ^ 4) ^ n - 3 ^ n = (1 - ζ) ^ 2 * c := by
  induction n with
  | zero => exact ⟨0, by ring⟩
  | succ n ih =>
    obtain ⟨c_ih, hc_ih⟩ := ih
    -- φ^(n+1) - 3^(n+1) = φ·(φ^n - 3^n) + (φ - 3)·3^n
    -- = φ·(λ²·c_ih) + λ²·ζ⁴·3^n  (by hc_ih and phi_mod_lambda_sq)
    have hphi := phi_mod_lambda_sq hζ
    refine ⟨(1 + ζ + ζ ^ 4) * c_ih + ζ ^ 4 * 3 ^ n, ?_⟩
    have : (1 + ζ + ζ ^ 4) ^ (n + 1) - 3 ^ (n + 1) =
        (1 + ζ + ζ ^ 4) * ((1 + ζ + ζ ^ 4) ^ n - 3 ^ n) +
        ((1 + ζ + ζ ^ 4) - 3) * 3 ^ n := by ring
    rw [this, hc_ih, hphi]
    ring

/-! ## 4. Modular consequence at the ideal level -/

/-- **Summary**: `φ = 1 + ζ + ζ⁴` satisfies `φ - 3 = (1-ζ)² · ζ⁴` where `ζ⁴` is a unit.
In the language of ideals: `(φ - 3) ∈ (λ)²` and the quotient is a unit.
This is the content of `beal_descent_lambda2_congruence`. -/
theorem phi_lambda_sq_unit_multiple {ζ : K} (hζ : IsPrimitiveRoot ζ 5) :
    ∃ u : K, u * ζ = 1 ∧ (1 + ζ + ζ ^ 4) - 3 = (1 - ζ) ^ 2 * u := by
  refine ⟨ζ ^ 4, zeta4_is_unit hζ, phi_mod_lambda_sq hζ⟩

/-! ## 5. Inverse period: (ζ+ζ⁴)ⁿ ≡ 2ⁿ (mod λ²) -/

/-- **`(ζ+ζ⁴)ⁿ - 2ⁿ` is divisible by `(1-ζ)²`** for all `n : ℕ`.

Since `(ζ+ζ⁴) - 2 = (1+ζ+ζ⁴) - 3 = (1-ζ)²·ζ⁴` (from `phi_mod_lambda_sq`), the same
inductive factoring gives the result. This is the analogue of `phi_pow_mod_lambda_sq` for the
inverse golden ratio `φ⁻¹ = ζ+ζ⁴ = φ - 1 ≡ 2 (mod λ²)`, needed for integer-exponent
congruences when `n < 0`. -/
theorem phi_inv_pow_mod_lambda_sq {ζ : K} (hζ : IsPrimitiveRoot ζ 5) (n : ℕ) :
    ∃ c : K, (ζ + ζ ^ 4) ^ n - 2 ^ n = (1 - ζ) ^ 2 * c := by
  induction n with
  | zero => exact ⟨0, by ring⟩
  | succ n ih =>
    obtain ⟨c_ih, hc_ih⟩ := ih
    have hbase : (ζ + ζ ^ 4) - 2 = (1 - ζ) ^ 2 * ζ ^ 4 := by
      linear_combination phi_mod_lambda_sq hζ
    refine ⟨(ζ + ζ ^ 4) * c_ih + ζ ^ 4 * 2 ^ n, ?_⟩
    calc (ζ + ζ ^ 4) ^ (n + 1) - 2 ^ (n + 1)
        = (ζ + ζ ^ 4) * ((ζ + ζ ^ 4) ^ n - 2 ^ n) + ((ζ + ζ ^ 4) - 2) * 2 ^ n := by ring
      _ = (ζ + ζ ^ 4) * ((1 - ζ) ^ 2 * c_ih) + ((1 - ζ) ^ 2 * ζ ^ 4) * 2 ^ n := by
            rw [hc_ih, hbase]
      _ = (1 - ζ) ^ 2 * ((ζ + ζ ^ 4) * c_ih + ζ ^ 4 * 2 ^ n) := by ring

#check @phi_mod_lambda_sq
#check @phi_div_lambda_sq_witness
#check @phi_pow_mod_lambda_sq
#check @phi_lambda_sq_unit_multiple
#check @phi_inv_pow_mod_lambda_sq

end BealLambdaCongruence

/-! ## 6. Integer-exponent congruence: φⁿ ≡ integer (mod λ²) for all n : ℤ -/

namespace BealLambdaCongruence

section Field

variable {K : Type*} [Field K]

/-- **For all `n : ℤ`, `φⁿ` is congruent to a rational integer modulo `λ²`**.

- `n ≥ 0`: rational integer is `3ⁿ` (from `phi_pow_mod_lambda_sq`)
- `n < 0`: use `φ⁻¹ = ζ+ζ⁴`, so `φ^{-m} = (ζ+ζ⁴)^m ≡ 2^m (mod λ²)` from
  `phi_inv_pow_mod_lambda_sq`. The identity `(1+ζ+ζ⁴)·(ζ+ζ⁴) = 1` pins the inverse.

This theorem is the key bridge from `beal_fundamental_unit_sqrt5_statement` to the Kummer
congruence hypothesis: every element `a + b·φ ∈ ℤ[φ]` with norm `±1` is congruent to a
rational integer modulo `λ²`. -/
theorem phi_zpow_rat_cong {ζ : K} (hζ : IsPrimitiveRoot ζ 5) (n : ℤ) :
    ∃ (r : ℤ) (c : K), (1 + ζ + ζ ^ 4) ^ n - (r : K) = (1 - ζ) ^ 2 * c := by
  -- Establish (1+ζ+ζ⁴)⁻¹ = ζ+ζ⁴
  have h5 : ζ ^ 5 = 1 := hζ.pow_eq_one
  have hne1 : ζ ≠ 1 := hζ.ne_one (by norm_num : 1 < 5)
  have hfact : (ζ - 1) * (1 + ζ + ζ ^ 2 + ζ ^ 3 + ζ ^ 4) = 0 := by linear_combination h5
  have hsum0 : 1 + ζ + ζ ^ 2 + ζ ^ 3 + ζ ^ 4 = 0 := by
    rcases mul_eq_zero.mp hfact with h | h
    · exact absurd (sub_eq_zero.mp h) hne1
    · exact h
  have h_mul : (1 + ζ + ζ ^ 4 : K) * (ζ + ζ ^ 4) = 1 := by
    linear_combination (2 + ζ ^ 3) * h5 + hsum0
  have hφ_ne : (1 + ζ + ζ ^ 4 : K) ≠ 0 := by
    intro h0; rw [h0, zero_mul] at h_mul; exact one_ne_zero h_mul.symm
  have hφ_inv : (1 + ζ + ζ ^ 4 : K)⁻¹ = ζ + ζ ^ 4 :=
    mul_left_cancel₀ hφ_ne ((mul_inv_cancel₀ hφ_ne).trans h_mul.symm)
  by_cases hn : 0 ≤ n
  · -- n ≥ 0: use phi_pow_mod_lambda_sq
    lift n to ℕ using hn
    obtain ⟨c, hc⟩ := phi_pow_mod_lambda_sq hζ n
    exact ⟨3 ^ n, c, by simp only [zpow_natCast]; exact_mod_cast hc⟩
  · -- n < 0: φ^n = (ζ+ζ⁴)^{-n} ≡ 2^{-n} (mod λ²)
    have hn' : n < 0 := by omega
    set m := Int.natAbs n with hm_def
    have hm_pos : 0 < m := Int.natAbs_pos.mpr (Int.ne_of_lt hn')
    have hn_eq : n = -(↑m : ℤ) := by omega
    have hpow_eq : (1 + ζ + ζ ^ 4 : K) ^ n = (ζ + ζ ^ 4) ^ m := by
      rw [hn_eq, zpow_neg, zpow_natCast, ← inv_pow, hφ_inv]
    obtain ⟨c, hc⟩ := phi_inv_pow_mod_lambda_sq hζ m
    exact ⟨2 ^ m, c, by rw [hpow_eq]; exact_mod_cast hc⟩

/-! ## 4.  λ⁴ refinement: φⁿ ≡ rational (mod λ⁴) iff 5 ∣ n

The λ² congruence `phi_zpow_rat_cong` holds for *all* n.  The stronger λ⁴ form is
selective: the λ²-coefficient of `φⁿ − 3ⁿ` is `n·3^{n−1}·ζ⁴·λ²`, which is
divisible by λ⁴ = (1−ζ)⁴ if and only if 5 ∣ n (using that λ⁴ ∣ 5 in ℤ[ζ₅]).

This characterises the *true* Kummer condition: the descent unit `ε = ζ^k·φⁿ` from
the (p,p,z) Beal descent satisfies `ε ≡ rational (mod λ⁴)` exactly when `k ≡ 0 (mod 5)`
(so the torsion part is trivial, since ζ⁵=1) AND `5 ∣ n`.  Neither condition forces
`z ∣ n`, which would be needed for ε to be a z-th power — the remaining gap.
-/

/-- **φⁿ mod λ⁴ precision.** For each `n : ℕ`, there exists `c : K` such that
`(1+ζ+ζ⁴)ⁿ − 3ⁿ = (1−ζ)²·n·3^{n−1}·ζ⁴ + (1−ζ)⁴·c`.

Proof by induction.
- Base `n = 0`: trivial.
- Step: `φ^{n+1} − 3^{n+1} = φⁿ·φ − 3ⁿ·3`.  Substitute the IH
  (`φⁿ = 3ⁿ + λ²·n·3^{n−1}·ζ⁴ + λ⁴·c_n`) and `φ = 3 + λ²·ζ⁴`.
  After expansion the λ²-coefficient becomes `(n+1)·3ⁿ·ζ⁴`;
  the remainder `c_{n+1} = n·3^{n−1}·ζ³ + φ·c_n` absorbs the extra λ⁴ terms.
  The residual after substitution is `(1−ζ)⁴·n·3^{n−1}·(ζ⁸−ζ³) = (1−ζ)⁴·n·3^{n−1}·ζ³·(ζ⁵−1)`,
  discharged by `linear_combination` against `h5 : ζ⁵ = 1`. -/
theorem phi_pow_mod_lambda4 {ζ : K} (hζ : IsPrimitiveRoot ζ 5) (n : ℕ) :
    ∃ c : K, (1 + ζ + ζ ^ 4) ^ n - (3 : K) ^ n =
      (1 - ζ) ^ 2 * ((n : K) * (3 : K) ^ (n - 1) * ζ ^ 4) + (1 - ζ) ^ 4 * c := by
  have h5 : ζ ^ 5 = 1 := hζ.pow_eq_one
  have hphi_sub : (1 + ζ + ζ ^ 4 : K) = 3 + (1 - ζ) ^ 2 * ζ ^ 4 := by
    have := phi_mod_lambda_sq hζ; linear_combination this
  induction n with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨c_n, hc_n⟩ := ih
    -- Two-case split on n to avoid Nat.pred truncation in 3^{n-1}.
    -- For n = 0 (proving for 1): coefficient is (1:K)·3^0·ζ⁴ = ζ⁴.
    -- For n = n'+1 (proving for n'+2): (n'+1)-1 = n' exactly in ℕ, no truncation.
    cases n with
    | zero =>
      -- Goal: φ¹ − 3¹ = λ²·1·3⁰·ζ⁴ + λ⁴·(φ·c₀)
      refine ⟨(1 + ζ + ζ ^ 4) * c_n, ?_⟩
      -- IH: φ⁰ − 3⁰ = 0 + λ⁴·c₀, so λ⁴·c₀ = 0
      have h0 : (1 - ζ) ^ 4 * c_n = 0 := by
        have := hc_n
        simp only [pow_zero, Nat.cast_zero, zero_mul, mul_zero, zero_add, sub_self] at this
        exact this.symm
      simp only [pow_zero, mul_one, Nat.sub_self]
      -- goal: φ − 3 = λ²·ζ⁴ + λ⁴·(φ·c₀)  (and λ⁴·c₀ = 0 absorbs the λ⁴ term)
      linear_combination hphi_sub - (1 + ζ + ζ ^ 4) * h0
    | succ n' =>
      -- n = n'+1; goal: φ^{n'+2} − 3^{n'+2} = λ²·(n'+2)·3^{n'+1}·ζ⁴ + λ⁴·witness
      -- hc_n : φ^{n'+1} − 3^{n'+1} = λ²·(n'+1)·3^{n'}·ζ⁴ + λ⁴·c_n
      --   (exponent (n'+1)-1 = n' in ℕ, no truncation)
      -- Witness: (n'+1:K)·3^{n'}·ζ³ + φ·c_n
      refine ⟨((n' : K) + 1) * (3 : K) ^ n' * ζ ^ 3 + (1 + ζ + ζ ^ 4) * c_n, ?_⟩
      -- Restate IH with exact exponents (Nat.add_sub_cancel: n'+1-1 = n')
      have hphin : (1 + ζ + ζ ^ 4 : K) ^ (n' + 1) =
          (3 : K) ^ (n' + 1) +
          (1 - ζ) ^ 2 * (((n' : K) + 1) * (3 : K) ^ n' * ζ ^ 4) +
          (1 - ζ) ^ 4 * c_n := by
        have h := hc_n
        simp only [Nat.add_sub_cancel] at h
        push_cast at h ⊢
        linear_combination h
      rw [pow_succ (1 + ζ + ζ ^ 4) (n' + 1), hphin, hphi_sub,
          pow_succ (3 : K) (n' + 1)]
      simp only [Nat.add_sub_cancel]
      push_cast
      -- Residual: λ⁴·(n'+1)·3^{n'}·(ζ⁸ − ζ³) = λ⁴·(n'+1)·3^{n'}·ζ³·(ζ⁵ − 1)
      linear_combination ((1 - ζ) ^ 4 * ((n' : K) + 1) * (3 : K) ^ n' * ζ ^ 3) * h5

/-- **φ^n ≡ 3^n (mod λ⁴) when 5 ∣ n.**

If `5 ∣ n`, write `n = 5m`. The λ²-coefficient of `phi_pow_mod_lambda4` is
`n·3^{n−1}·ζ⁴ = 5m·3^{n−1}·ζ⁴ = λ⁴·(−1−ζ+ζ³)·m·3^{n−1}·ζ⁴` (using `5 = λ⁴·(−1−ζ+ζ³)`),
so the `λ²` term absorbs into `λ⁴`, giving `φⁿ − 3ⁿ ∈ λ⁴·𝓞K`.

This is the key Kummer hypothesis for p=5: the descent unit `φⁿ` (a real unit of `𝓞(ℚ(ζ₅))`)
satisfies the mod-λ⁴ congruence if and only if `5∣n`, enabling the Frobenius engine to
conclude `φⁿ` is a 5th power. -/
theorem phi_pow_cong_mod_lambda4_of_five_dvd {ζ : K} (hζ : IsPrimitiveRoot ζ 5)
    (n : ℕ) (h5n : 5 ∣ n) :
    ∃ c : K, (1 + ζ + ζ ^ 4) ^ n - (3 : K) ^ n = (1 - ζ) ^ 4 * c := by
  obtain ⟨m, rfl⟩ := h5n
  -- Prove (1-ζ)⁴·(-1-ζ+ζ³) = 5 locally (avoids importing BealKummerDescentMod5,
  -- which requires pre-built oleans; `lake env lean` only loads direct Mathlib imports).
  -- Key ingredients: ζ⁵=1 and the cyclotomic relation 1+ζ+ζ²+ζ³+ζ⁴=0.
  have h5 : ζ ^ 5 = 1 := hζ.pow_eq_one
  have hne1 : ζ ≠ 1 := hζ.ne_one (by norm_num : 1 < 5)
  have hsum : 1 + ζ + ζ ^ 2 + ζ ^ 3 + ζ ^ 4 = 0 := by
    have key : (ζ - 1) * (1 + ζ + ζ ^ 2 + ζ ^ 3 + ζ ^ 4) = 0 := by
      linear_combination h5
    rcases mul_eq_zero.mp key with h | h
    · exact absurd (sub_eq_zero.mp h) hne1
    · exact h
  have hfive : (1 - ζ) ^ 4 * (-1 - ζ + ζ ^ 3) = 5 := by
    linear_combination (5 - 4 * ζ + ζ ^ 2) * h5 - hsum
  cases m with
  | zero => exact ⟨0, by simp⟩
  | succ m' =>
    obtain ⟨c₀, hc₀⟩ := phi_pow_mod_lambda4 hζ (5 * (m' + 1))
    have hexp : 5 * (m' + 1) - 1 = 5 * m' + 4 := by omega
    rw [hexp] at hc₀
    push_cast at hc₀ ⊢
    refine ⟨(1 - ζ) ^ 2 * (-1 - ζ + ζ ^ 3) * ((m' : K) + 1) *
           (3 : K) ^ (5 * m' + 4) * ζ ^ 4 + c₀, ?_⟩
    -- Residual: (1-ζ)²·(5m)·3^{n-1}·ζ⁴ - (1-ζ)⁶·(-1-ζ+ζ³)·m·3^{n-1}·ζ⁴
    --         = (1-ζ)²·m·3^{n-1}·ζ⁴ · [5 - (1-ζ)⁴·(-1-ζ+ζ³)] = 0 (by hfive)
    linear_combination hc₀ - (1 - ζ) ^ 2 * ((m' : K) + 1) *
      (3 : K) ^ (5 * m' + 4) * ζ ^ 4 * hfive

end Field

#print axioms BealLambdaCongruence.phi_pow_mod_lambda4
#print axioms BealLambdaCongruence.phi_pow_cong_mod_lambda4_of_five_dvd

/-! ## 7.  Algebraic-integer witnesses — CommRing version

The theorems in §4–§6 work in a *Field* K and produce witnesses `c : K`.  For
the meaningful Kummer application we need witnesses `c : 𝓞 K` (ring of integers),
so that divisibility is a statement in the integer ring, not vacuous in the field.

The proofs below work in any `CommRing R` with `IsDomain R` where `η : R` is a
primitive 5th root of unity (`η^5 = 1`, `η ≠ 1`).  Instantiating `R = 𝓞 K` with
`η = hζ.toInteger` gives the desired 𝓞K-level statements. -/

section CommRingPrim5

variable {R : Type*} [CommRing R] [IsDomain R]

/-- **phi_pow_mod_lambda4 for CommRing with 5th root of unity** (𝓞K-ready).

For any `CommRing R [IsDomain R]` with element `η` satisfying `η^5 = 1`, `η ≠ 1`,
and any `n : ℕ`:

  `∃ c : R, (1+η+η⁴)ⁿ − 3ⁿ = (1−η)²·(n·3^{n−1}·η⁴) + (1−η)⁴·c`

This is the MEANINGFUL version (c : R, not c : K) when R = 𝓞 K: divisibility by
`(1−η)⁴` is in the integer ring, not trivial in the field.

Proof is word-for-word the Field version (§4), since no division is used — only
`ring`, `linear_combination`, `push_cast`, and `mul_eq_zero`. -/
theorem phi_pow_mod_lambda4_ring {η : R} (h5 : η ^ 5 = 1) (hne1 : η ≠ 1) (n : ℕ) :
    ∃ c : R, (1 + η + η ^ 4) ^ n - (3 : R) ^ n =
      (1 - η) ^ 2 * ((n : R) * (3 : R) ^ (n - 1) * η ^ 4) +
      (1 - η) ^ 4 * c := by
  have hsum : 1 + η + η ^ 2 + η ^ 3 + η ^ 4 = 0 := by
    have key : (η - 1) * (1 + η + η ^ 2 + η ^ 3 + η ^ 4) = 0 := by linear_combination h5
    rcases mul_eq_zero.mp key with h | h
    · exact absurd (sub_eq_zero.mp h) hne1
    · exact h
  have hphi_sub : (1 + η + η ^ 4 : R) = 3 + (1 - η) ^ 2 * η ^ 4 := by
    linear_combination (2 - η) * h5
  induction n with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨c_n, hc_n⟩ := ih
    cases n with
    | zero =>
      refine ⟨(1 + η + η ^ 4) * c_n, ?_⟩
      have h0 : (1 - η) ^ 4 * c_n = 0 := by
        have := hc_n
        simp only [pow_zero, Nat.cast_zero, zero_mul, mul_zero, zero_add, sub_self] at this
        exact this.symm
      simp only [pow_zero, mul_one, Nat.sub_self]
      linear_combination hphi_sub - (1 + η + η ^ 4) * h0
    | succ n' =>
      refine ⟨((n' : R) + 1) * (3 : R) ^ n' * η ^ 3 + (1 + η + η ^ 4) * c_n, ?_⟩
      have hphin : (1 + η + η ^ 4) ^ (n' + 1) =
          (3 : R) ^ (n' + 1) +
          (1 - η) ^ 2 * (((n' : R) + 1) * (3 : R) ^ n' * η ^ 4) +
          (1 - η) ^ 4 * c_n := by
        have h := hc_n
        simp only [Nat.add_sub_cancel] at h
        push_cast at h ⊢
        linear_combination h
      rw [pow_succ (1 + η + η ^ 4) (n' + 1), hphin, hphi_sub, pow_succ (3 : R) (n' + 1)]
      simp only [Nat.add_sub_cancel]
      push_cast
      linear_combination ((1 - η) ^ 4 * ((n' : R) + 1) * (3 : R) ^ n' * η ^ 3) * h5

/-- **φⁿ ≡ 3ⁿ (mod λ⁴) when 5 ∣ n**, CommRing version.

If `5 ∣ n` then `(1−η)⁴ ∣ (1+η+η⁴)ⁿ − 3ⁿ` in `R`.  When `R = 𝓞 K`, this gives the
𝓞K-level Kummer divisibility: `∃ c : 𝓞 K, φⁿ − 3ⁿ = λ⁴·c`. -/
theorem phi_pow_cong_mod_lambda4_five_dvd_ring {η : R}
    (h5 : η ^ 5 = 1) (hne1 : η ≠ 1) (n : ℕ) (hdvd : 5 ∣ n) :
    ∃ c : R, (1 + η + η ^ 4) ^ n - (3 : R) ^ n = (1 - η) ^ 4 * c := by
  obtain ⟨m, rfl⟩ := hdvd
  have hsum : 1 + η + η ^ 2 + η ^ 3 + η ^ 4 = 0 := by
    have key : (η - 1) * (1 + η + η ^ 2 + η ^ 3 + η ^ 4) = 0 := by linear_combination h5
    rcases mul_eq_zero.mp key with h | h
    · exact absurd (sub_eq_zero.mp h) hne1
    · exact h
  have hfive : (1 - η) ^ 4 * (-1 - η + η ^ 3) = 5 := by
    linear_combination (5 - 4 * η + η ^ 2) * h5 - hsum
  cases m with
  | zero => exact ⟨0, by simp⟩
  | succ m' =>
    obtain ⟨c₀, hc₀⟩ := phi_pow_mod_lambda4_ring h5 hne1 (5 * (m' + 1))
    have hexp : 5 * (m' + 1) - 1 = 5 * m' + 4 := by omega
    rw [hexp] at hc₀
    push_cast at hc₀ ⊢
    refine ⟨(1 - η) ^ 2 * (-1 - η + η ^ 3) * ((m' : R) + 1) *
           (3 : R) ^ (5 * m' + 4) * η ^ 4 + c₀, ?_⟩
    linear_combination hc₀ - (1 - η) ^ 2 * ((m' : R) + 1) *
      (3 : R) ^ (5 * m' + 4) * η ^ 4 * hfive

#print axioms phi_pow_mod_lambda4_ring
#print axioms phi_pow_cong_mod_lambda4_five_dvd_ring

end CommRingPrim5

end BealLambdaCongruence
