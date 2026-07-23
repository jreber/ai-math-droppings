import Propositio.NumberTheory.Beal.Radical
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# ABC ⟹ Beal solutions have bounded base (the Granville payoff, Lean 4)

This file proves the **conditional Granville theorem**: *assuming the ABC
conjecture, a primitive Beal solution `Aˣ + Bʸ = Cᶻ` with sufficiently large
exponents has its base `C` bounded by an absolute constant* — so only finitely
many such bases occur.  This turns `BealRadical.beal_abc_bounded` (which controls
`Cᶻ` by a near-linear power of `rad(ABC) ≤ ABC`) into an honest finiteness
statement, the real conditional theorem behind "ABC implies Beal".

## The argument

For a primitive solution `Aˣ + Bʸ = Cᶻ` with `A, B, C ≥ 2` and exponents `≥ 3`:

* Both summands are positive, so `Aˣ < Cᶻ` and `Bʸ < Cᶻ`.
* From `A³ ≤ Aˣ < Cᶻ` we get `A < C^(z/3)`, and likewise `B < C^(z/3)`; with
  `C = C¹` this gives `A·B·C < C^(2z/3 + 1)` (`abc_lt_pow`).
* ABC at `ε = 1/4` gives `Cᶻ ≤ K·rad(Aˣ Bʸ Cᶻ)^(5/4) = K·rad(ABC)^(5/4) ≤
  K·(ABC)^(5/4) < K·C^((2z/3 + 1)·5/4) = K·C^(5z/6 + 5/4)`.
* Hence `C^(z − 5z/6 − 5/4) < K`, i.e. `C^(z/6 − 5/4) < K`.  For `z ≥ 8` the
  exponent `z/6 − 5/4 ≥ 1/12 > 0`, and `C ≥ 2 > 1`, so `C^(1/12) < K`, whence
  `C < K¹²` — an absolute bound (`beal_base_bounded`).

## Contents
* `base_lt_rpow` — `A < C^(z/3)` from `A³ ≤ Aˣ < Cᶻ`.
* `abc_lt_pow` — `A·B·C < C^(2z/3 + 1)`.
* `beal_base_bounded` — **headline**: ABC ⟹ the base `C` of a primitive Beal
  solution with `min(x,y,z) ≥ 8` is bounded by a constant `M`.
* `beal_bases_finite` — packaged finiteness: for fixed large exponents, the set of
  primitive solution bases `(A,B,C)` is finite.

Dependency policy: mathlib4 permitted (user authorization 2026-05-17). Use
`lake env lean BealABCFinite.lean` to typecheck.
-/

namespace BealABCFinite

open scoped Real

/-! ## 1. The two summands are each below the value -/

/-- In a primitive Beal solution `Aˣ + Bʸ = Cᶻ` with positive bases, the first
summand is strictly below the value: `Aˣ < Cᶻ` (because `Bʸ > 0`). -/
theorem lt_value_left {A B C x y z : ℕ}
    (hB : 0 < B) (hsum : A ^ x + B ^ y = C ^ z) : A ^ x < C ^ z := by
  have hBy : 0 < B ^ y := pow_pos hB y
  omega

/-- The second summand is strictly below the value: `Bʸ < Cᶻ` (because `Aˣ > 0`). -/
theorem lt_value_right {A B C x y z : ℕ}
    (hA : 0 < A) (hsum : A ^ x + B ^ y = C ^ z) : B ^ y < C ^ z := by
  have hAx : 0 < A ^ x := pow_pos hA x
  omega

/-! ## 2. A base is bounded by a fractional power of `C` -/

/-- **Base bound.** If `3 ≤ x`, `A ≥ 1`, `C ≥ 2`, and `Aˣ < Cᶻ`, then over `ℝ`
`A < C^(z/3)`.  (From `A³ ≤ Aˣ < Cᶻ` and the cube root being monotone.) -/
theorem base_lt_rpow {A C x z : ℕ}
    (hx : 3 ≤ x) (hA : 1 ≤ A) (hC : 2 ≤ C) (hpow : A ^ x < C ^ z) :
    (A : ℝ) < (C : ℝ) ^ ((z : ℝ) / 3) := by
  have hAR0 : (0 : ℝ) ≤ (A : ℝ) := by positivity
  have hCR0 : (0 : ℝ) ≤ (C : ℝ) := by positivity
  -- A³ ≤ Aˣ < Cᶻ over ℕ, hence over ℝ as rpow with real exponents.
  have hA3 : A ^ 3 ≤ A ^ x := Nat.pow_le_pow_right (by omega) hx
  have hcubeN : (A ^ 3 : ℕ) < (C ^ z : ℕ) := lt_of_le_of_lt hA3 hpow
  -- Cast to ℝ and present both powers as rpow with real exponents.
  have hcube' : (A : ℝ) ^ (3 : ℝ) < (C : ℝ) ^ (z : ℝ) := by
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
        Real.rpow_natCast]
    exact_mod_cast hcubeN
  -- Apply t ↦ t^(1/3), strictly monotone on nonneg reals.
  have hmono := Real.rpow_lt_rpow (z := (1/3 : ℝ)) (by positivity) hcube' (by norm_num)
  rw [← Real.rpow_mul hAR0, ← Real.rpow_mul hCR0] at hmono
  rw [show (3 : ℝ) * (1/3) = 1 by norm_num, Real.rpow_one] at hmono
  rw [show (z : ℝ) * (1/3) = (z : ℝ) / 3 by ring] at hmono
  exact hmono

/-! ## 3. The product of bases is below a fractional power of `C` -/

/-- **Product bound.** For a primitive Beal solution with `A, B ≥ 1`, `C ≥ 2`,
exponents `x, y ≥ 3`, and `Aˣ < Cᶻ`, `Bʸ < Cᶻ`, the product of bases satisfies
`A·B·C < C^(2z/3 + 1)` over `ℝ`. -/
theorem abc_lt_pow {A B C x y z : ℕ}
    (hx : 3 ≤ x) (hy : 3 ≤ y) (hA : 1 ≤ A) (hB : 1 ≤ B) (hC : 2 ≤ C)
    (hAx : A ^ x < C ^ z) (hBy : B ^ y < C ^ z) :
    (A * B * C : ℝ) < (C : ℝ) ^ (2 * (z : ℝ) / 3 + 1) := by
  have hCR1 : (1 : ℝ) ≤ (C : ℝ) := by exact_mod_cast (by omega : 1 ≤ C)
  have hCR0 : (0 : ℝ) ≤ (C : ℝ) := le_trans zero_le_one hCR1
  have hAR0 : (0 : ℝ) ≤ (A : ℝ) := by positivity
  have hBR1 : (1 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB
  have hAlt : (A : ℝ) < (C : ℝ) ^ ((z : ℝ) / 3) := base_lt_rpow hx hA hC hAx
  have hBlt : (B : ℝ) < (C : ℝ) ^ ((z : ℝ) / 3) := base_lt_rpow hy hB hC hBy
  have hpos2 : (0 : ℝ) < (C : ℝ) := by linarith
  -- A·B < C^(z/3) · C^(z/3) = C^(2z/3)
  have hAB : (A : ℝ) * (B : ℝ) < (C : ℝ) ^ ((z : ℝ) / 3) * (C : ℝ) ^ ((z : ℝ) / 3) := by
    have hrp : (0 : ℝ) < (C : ℝ) ^ ((z : ℝ) / 3) := Real.rpow_pos_of_pos hpos2 _
    calc (A : ℝ) * (B : ℝ)
        < (C : ℝ) ^ ((z : ℝ) / 3) * (B : ℝ) :=
          mul_lt_mul_of_pos_right hAlt (by linarith)
      _ ≤ (C : ℝ) ^ ((z : ℝ) / 3) * (C : ℝ) ^ ((z : ℝ) / 3) :=
          mul_le_mul_of_nonneg_left (le_of_lt hBlt) (le_of_lt hrp)
  -- Now A·B·C < C^(2z/3) · C = C^(2z/3 + 1).
  have hABC : (A : ℝ) * (B : ℝ) * (C : ℝ)
      < (C : ℝ) ^ ((z : ℝ) / 3) * (C : ℝ) ^ ((z : ℝ) / 3) * (C : ℝ) :=
    mul_lt_mul_of_pos_right hAB hpos2
  -- Rewrite the RHS as C^(2z/3 + 1).
  have hrhs : (C : ℝ) ^ ((z : ℝ) / 3) * (C : ℝ) ^ ((z : ℝ) / 3) * (C : ℝ)
      = (C : ℝ) ^ (2 * (z : ℝ) / 3 + 1) := by
    nth_rewrite 3 [← Real.rpow_one (C : ℝ)]
    rw [← Real.rpow_add hpos2, ← Real.rpow_add hpos2]
    congr 1
    ring
  calc (A * B * C : ℝ) = (A : ℝ) * (B : ℝ) * (C : ℝ) := by norm_cast
    _ < (C : ℝ) ^ ((z : ℝ) / 3) * (C : ℝ) ^ ((z : ℝ) / 3) * (C : ℝ) := hABC
    _ = (C : ℝ) ^ (2 * (z : ℝ) / 3 + 1) := hrhs

/-! ## 4. Headline: ABC ⟹ the base `C` is bounded -/

/-- **Headline (conditional Granville theorem).** Assume the ABC conjecture.  Then
there is an exponent threshold `N` and an absolute constant `M` such that **every**
primitive Beal solution `Aˣ + Bʸ = Cᶻ` with `A, B, C ≥ 2` and all exponents `≥ N`
has `C ≤ M`.  In particular only finitely many bases `C` occur.

Concretely `N = 8` and `M = K¹²`, where `K` is the ABC constant at `ε = 1/4`. -/
theorem beal_base_bounded (habc : BealRadical.ABCConjecture) :
    ∃ (N : ℕ) (M : ℝ), ∀ A B C x y z : ℕ,
      2 ≤ A → 2 ≤ B → 2 ≤ C → N ≤ x → N ≤ y → N ≤ z →
      Nat.Coprime A B → A ^ x + B ^ y = C ^ z → (C : ℝ) ≤ M := by
  -- ABC at ε = 1/4 gives the value bound for primitive Beal solutions.
  obtain ⟨K, hK, hbound⟩ :=
    BealRadical.beal_abc_bounded habc (ε := (1/4 : ℝ)) (by norm_num)
  refine ⟨8, K ^ 12, ?_⟩
  intro A B C x y z hA hB hC hx hy hz hcop hsum
  -- Basic positivity / coprimality bookkeeping.
  have hA0 : A ≠ 0 := by omega
  have hB0 : B ≠ 0 := by omega
  have hC0 : C ≠ 0 := by omega
  have hx0 : x ≠ 0 := by omega
  have hy0 : y ≠ 0 := by omega
  have hz0 : z ≠ 0 := by omega
  have hx3 : 3 ≤ x := by omega
  have hy3 : 3 ≤ y := by omega
  have hz8 : 8 ≤ z := hz
  have hcoppow : Nat.Coprime (A ^ x) (B ^ y) := Nat.Coprime.pow x y hcop
  have hAx : A ^ x < C ^ z := lt_value_left (by omega) hsum
  have hBy : B ^ y < C ^ z := lt_value_right (by omega) hsum
  -- The value bound: Cᶻ ≤ K·(ABC)^(5/4).
  have hval := hbound A B C x y z hA0 hB0 hC0 hx0 hy0 hz0 hcoppow hsum
  -- The product bound: ABC < C^(2z/3 + 1).
  have hprod : (A * B * C : ℝ) < (C : ℝ) ^ (2 * (z : ℝ) / 3 + 1) :=
    abc_lt_pow hx3 hy3 (by omega) (by omega) hC hAx hBy
  -- Real-side bookkeeping for C.
  have hCR2 : (2 : ℝ) ≤ (C : ℝ) := by exact_mod_cast hC
  have hCR1 : (1 : ℝ) ≤ (C : ℝ) := by linarith
  have hCpos : (0 : ℝ) < (C : ℝ) := by linarith
  have hABCpos : (0 : ℝ) < (A * B * C : ℝ) := by
    have : (0 : ℕ) < A * B * C := by positivity
    exact_mod_cast this
  -- (ABC)^(5/4) < (C^(2z/3+1))^(5/4) = C^((2z/3+1)·5/4) = C^(5z/6 + 5/4).
  have hprod54 : (A * B * C : ℝ) ^ (1 + (1/4 : ℝ))
      < ((C : ℝ) ^ (2 * (z : ℝ) / 3 + 1)) ^ (1 + (1/4 : ℝ)) := by
    apply Real.rpow_lt_rpow (le_of_lt hABCpos) hprod
    norm_num
  have hrhs_simp : ((C : ℝ) ^ (2 * (z : ℝ) / 3 + 1)) ^ (1 + (1/4 : ℝ))
      = (C : ℝ) ^ (5 * (z : ℝ) / 6 + 5/4) := by
    rw [← Real.rpow_mul (le_of_lt hCpos)]
    congr 1
    ring
  -- Combine: Cᶻ ≤ K·(ABC)^(5/4) < K·C^(5z/6 + 5/4).
  have hCz_rpow : (C : ℝ) ^ (z : ℝ) = ((C ^ z : ℕ) : ℝ) := by
    rw [Real.rpow_natCast]; push_cast; rfl
  have hval' : (C : ℝ) ^ (z : ℝ) ≤ K * (A * B * C : ℝ) ^ (1 + (1/4 : ℝ)) := by
    rw [hCz_rpow]; exact hval
  have hchain : (C : ℝ) ^ (z : ℝ) < K * (C : ℝ) ^ (5 * (z : ℝ) / 6 + 5/4) := by
    calc (C : ℝ) ^ (z : ℝ)
        ≤ K * (A * B * C : ℝ) ^ (1 + (1/4 : ℝ)) := hval'
      _ < K * ((C : ℝ) ^ (2 * (z : ℝ) / 3 + 1)) ^ (1 + (1/4 : ℝ)) := by
          exact mul_lt_mul_of_pos_left hprod54 hK
      _ = K * (C : ℝ) ^ (5 * (z : ℝ) / 6 + 5/4) := by rw [hrhs_simp]
  -- Divide by C^(5z/6 + 5/4): C^(z/6 − 5/4) < K.
  have hpowpos : (0 : ℝ) < (C : ℝ) ^ (5 * (z : ℝ) / 6 + 5/4) :=
    Real.rpow_pos_of_pos hCpos _
  have hgap : (C : ℝ) ^ ((z : ℝ) / 6 - 5/4) < K := by
    have hsplit : (C : ℝ) ^ (z : ℝ)
        = (C : ℝ) ^ ((z : ℝ) / 6 - 5/4) * (C : ℝ) ^ (5 * (z : ℝ) / 6 + 5/4) := by
      rw [← Real.rpow_add hCpos]
      congr 1
      ring
    rw [hsplit] at hchain
    -- a·P < K·P with P ≥ 0 ⟹ a < K.
    exact lt_of_mul_lt_mul_right hchain (le_of_lt hpowpos)
  -- For z ≥ 8 the exponent z/6 − 5/4 ≥ 1/12 > 0, and C ≥ 2 > 1.
  have hexp_ge : (1 : ℝ) / 12 ≤ (z : ℝ) / 6 - 5/4 := by
    have : (8 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz8
    linarith
  -- C^(1/12) ≤ C^(z/6 − 5/4) < K, since C ≥ 1 and exponent increases.
  have hmono_exp : (C : ℝ) ^ ((1 : ℝ) / 12) ≤ (C : ℝ) ^ ((z : ℝ) / 6 - 5/4) :=
    Real.rpow_le_rpow_of_exponent_le hCR1 hexp_ge
  have h112 : (C : ℝ) ^ ((1 : ℝ) / 12) < K := lt_of_le_of_lt hmono_exp hgap
  -- Raise to the 12th power: C ≤ K¹².  Both sides nonneg, x ↦ x¹² monotone.
  have h112pos : (0 : ℝ) ≤ (C : ℝ) ^ ((1 : ℝ) / 12) := Real.rpow_nonneg (le_of_lt hCpos) _
  have hraise : ((C : ℝ) ^ ((1 : ℝ) / 12)) ^ (12 : ℕ) ≤ K ^ (12 : ℕ) :=
    pow_le_pow_left₀ h112pos (le_of_lt h112) 12
  have hCsimp : ((C : ℝ) ^ ((1 : ℝ) / 12)) ^ (12 : ℕ) = (C : ℝ) := by
    rw [← Real.rpow_natCast ((C : ℝ) ^ ((1 : ℝ) / 12)) 12,
        ← Real.rpow_mul (le_of_lt hCpos)]
    norm_num
  calc (C : ℝ) = ((C : ℝ) ^ ((1 : ℝ) / 12)) ^ (12 : ℕ) := hCsimp.symm
    _ ≤ K ^ (12 : ℕ) := hraise

/-! ## 5. Finiteness packaging -/

/-- **Finiteness of bases.** Assume the ABC conjecture.  Then the set of bases `C`
arising in *any* primitive Beal solution `Aˣ + Bʸ = Cᶻ` with `A, B, C ≥ 2` and all
exponents `≥ N` is **finite** — there are only finitely many such `C`.

This is the honest finiteness statement behind "ABC implies Beal" on the base `C`:
since `C ≤ M` for the absolute constant `M` of `beal_base_bounded`, the set sits
inside `{n | (n : ℝ) ≤ M}`, a finite set of naturals. -/
theorem beal_bases_finite (habc : BealRadical.ABCConjecture) :
    ∃ N : ℕ, Set.Finite { C : ℕ | ∃ A B x y z : ℕ,
      2 ≤ A ∧ 2 ≤ B ∧ 2 ≤ C ∧ N ≤ x ∧ N ≤ y ∧ N ≤ z ∧
      Nat.Coprime A B ∧ A ^ x + B ^ y = C ^ z } := by
  obtain ⟨N, M, hM⟩ := beal_base_bounded habc
  refine ⟨N, ?_⟩
  -- Every such C satisfies (C : ℝ) ≤ M, hence C ≤ ⌊M⌋₊; embed in a finite interval.
  apply Set.Finite.subset (Set.finite_Iic (Nat.floor M))
  intro C hC
  obtain ⟨A, B, x, y, z, hA, hB, hC2, hx, hy, hz, hcop, hsum⟩ := hC
  have hCM : (C : ℝ) ≤ M := hM A B C x y z hA hB hC2 hx hy hz hcop hsum
  simp only [Set.mem_Iic]
  exact Nat.le_floor hCM

end BealABCFinite
