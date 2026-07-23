import Propositio.NumberTheory.Diophantine.DiagonalIntegralLog2IntForm
import Propositio.NumberTheory.Diophantine.PadeCasoratian
import Mathlib.Tactic

/-!
# Toward the central Delannoy recurrence for `cₙ`

`cₙ = intCoeff n n = coeff n((X−1)ⁿ(2−X)ⁿ) = coeff n(Qⁿ)` with `Q = (X−1)(2−X) = −X²+3X−2`
is the central Delannoy number `D(n)` (OEIS A001850), which satisfies
`(n+1)cₙ₊₁ = 3(2n+1)cₙ − n·cₙ₋₁` — the single remaining crux for the unconditional effective
measure of `log 2` (see `DiagonalIntegralLog2Measure.log2_measure_of_recurrence`).

This file proves the first concrete relation of that recurrence, from `(Qⁿ⁺¹)' = (n+1)·Q'·Qⁿ`:
`(n+1)·cₙ₊₁ = (n+1)·(3·cₙ − 2·coeff_{n−1}(Qⁿ))`.  (`Q' = 3 − 2X`.)  Combining this with the
companion within-`n` relation from `Q·(Qⁿ)' = n·Q'·Qⁿ` and the cross-`n` step
`coeff_{n−1}(Qⁿ) = coeff_{n−1}(Q·Qⁿ⁻¹)` closes the recurrence (the remaining creative-telescoping).
-/

namespace DiagonalIntegralLog2

open Polynomial

/-- `Q = (X−1)(2−X) = −X²+3X−2`, so `cₙ = coeff n(Qⁿ)`. -/
noncomputable def Qpoly : ℤ[X] := (X - 1) * (2 - X)

theorem intCoeff_eq_Qpow (n k : ℕ) : intCoeff n k = (Qpoly ^ n).coeff k := by
  rw [intCoeff, Qpoly, mul_pow]

theorem Qpoly_derivative : derivative Qpoly = 3 - 2 * X := by
  rw [Qpoly]; simp [derivative_mul]; ring

/-- **First relation toward the Delannoy recurrence.**  From `(Qⁿ⁺¹)' = (n+1)·Q'·Qⁿ` (with
`Q' = 3 − 2X`), taking the coefficient of `Xⁿ`:
`(n+1)·cₙ₊₁ = (n+1)·(3·cₙ − 2·coeff_{n−1}(Qⁿ))`. -/
theorem coeff_rel_I (n : ℕ) (hn : 1 ≤ n) :
    ((n : ℤ) + 1) * intCoeff (n + 1) (n + 1)
      = ((n : ℤ) + 1) * (3 * intCoeff n n - 2 * (Qpoly ^ n).coeff (n - 1)) := by
  -- LHS = coeff_n of (Qⁿ⁺¹)'
  have hL : ((Qpoly ^ (n + 1)).derivative).coeff n = ((n : ℤ) + 1) * intCoeff (n + 1) (n + 1) := by
    rw [coeff_derivative, intCoeff_eq_Qpow]; ring
  -- (Qⁿ⁺¹)' = (n+1)·Qⁿ·Q'
  have hderiv : (Qpoly ^ (n + 1)).derivative = (C ((n : ℤ) + 1)) * Qpoly ^ n * (3 - 2 * X) := by
    rw [derivative_pow, Qpoly_derivative]; push_cast; ring_nf
  -- RHS = coeff_n of (n+1)·Qⁿ·(3 − 2X)
  have hR : ((C ((n : ℤ) + 1)) * Qpoly ^ n * (3 - 2 * X)).coeff n
      = ((n : ℤ) + 1) * (3 * intCoeff n n - 2 * (Qpoly ^ n).coeff (n - 1)) := by
    have hxmul : (Qpoly ^ n * X).coeff n = (Qpoly ^ n).coeff (n - 1) := by
      have h := coeff_mul_X (Qpoly ^ n) (n - 1)
      rwa [show n - 1 + 1 = n from by omega] at h
    rw [show (C ((n : ℤ) + 1)) * Qpoly ^ n * (3 - 2 * X)
        = C ((n : ℤ) + 1) * (3 * Qpoly ^ n - 2 * (Qpoly ^ n * X)) by ring,
      coeff_C_mul, coeff_sub, coeff_ofNat_mul, coeff_ofNat_mul, hxmul, intCoeff_eq_Qpow]
  rw [← hL, hderiv, hR]

/-! ### The full central Delannoy recurrence via a Gosper/creative-telescoping certificate

The recurrence `(n+2)cₙ₊₂ = 3(2n+3)cₙ₊₁ − (n+1)cₙ` (`cₙ = [Xⁿ]Qⁿ`, the central Delannoy
number `D(n)`, OEIS A001850) is proved by the Almkvist–Zeilberger certificate `ρ = X − 2/X`,
i.e. `H = (X²−2)·Qⁿ⁺¹`.  The certificate makes the whole recurrence collapse to:

* a **fixed `ring` identity** `club` (coefficients linear in `n`, degree ≤ 4 in `X`);
* the polynomial identity `heart` `X·H' − (n+2)·H = −(n+1)X²Qⁿ + 3(2n+3)XQⁿ⁺¹ − (n+2)Qⁿ⁺²`
  (which is `Qⁿ · club`); and
* extracting `[Xⁿ⁺²]`, where the certificate side `X·H' − (n+2)·H` contributes `0` structurally
  (`[Xⁿ⁺²](X·H') = (n+2)[Xⁿ⁺²]H = [Xⁿ⁺²]((n+2)H)`), and the right side reads off the recurrence.
-/

/-- `H = (X²−2)·Qⁿ⁺¹` — the Gosper certificate's numerator. -/
noncomputable def Hcert (n : ℕ) : ℤ[X] := (X ^ 2 - 2) * Qpoly ^ (n + 1)

/-- **The fixed certificate identity (♣).**  A degree-≤4 polynomial identity in `X` with
coefficients linear in `n`, the algebraic heart of the central Delannoy recurrence. -/
theorem club (n : ℕ) :
    2 * X ^ 2 * Qpoly + ((n : ℤ[X]) + 1) * X * (X ^ 2 - 2) * (3 - 2 * X)
        - ((n : ℤ[X]) + 2) * (X ^ 2 - 2) * Qpoly
      = -((n : ℤ[X]) + 1) * X ^ 2 + 3 * (2 * (n : ℤ[X]) + 3) * X * Qpoly
        - ((n : ℤ[X]) + 2) * Qpoly ^ 2 := by
  rw [Qpoly]; ring

/-- The derivative of the certificate numerator, in factored form. -/
theorem Hcert_derivative (n : ℕ) :
    derivative (Hcert n)
      = 2 * X * Qpoly ^ (n + 1) + ((n : ℤ[X]) + 1) * (X ^ 2 - 2) * Qpoly ^ n * (3 - 2 * X) := by
  rw [Hcert, derivative_mul, derivative_pow_succ, Qpoly_derivative]
  have hX2 : derivative (X ^ 2 - 2 : ℤ[X]) = 2 * X := by
    simp [derivative_sub]
  rw [hX2]
  have hC : (C ((n : ℤ) + 1) : ℤ[X]) = (n : ℤ[X]) + 1 := by
    simp [map_add, map_one, map_natCast]
  rw [hC]; ring

/-- **The certificate identity (♥)** `X·H' − (n+2)·H = −(n+1)X²Qⁿ + 3(2n+3)XQⁿ⁺¹ − (n+2)Qⁿ⁺²`,
obtained as `Qⁿ · club`. -/
theorem heart (n : ℕ) :
    X * derivative (Hcert n) - ((n : ℤ[X]) + 2) * Hcert n
      = -((n : ℤ[X]) + 1) * X ^ 2 * Qpoly ^ n
        + 3 * (2 * (n : ℤ[X]) + 3) * X * Qpoly ^ (n + 1)
        - ((n : ℤ[X]) + 2) * Qpoly ^ (n + 2) := by
  rw [Hcert_derivative, Hcert]
  -- both sides are `Qⁿ · (club side)`; reduce to `club n`
  have hpow1 : Qpoly ^ (n + 1) = Qpoly ^ n * Qpoly := by rw [pow_succ]
  have hpow2 : Qpoly ^ (n + 2) = Qpoly ^ n * Qpoly ^ 2 := by ring
  rw [hpow1, hpow2]
  linear_combination (Qpoly ^ n) * club n

/-- **Central Delannoy recurrence (integer form).** `(n+2)·cₙ₊₂ = 3(2n+3)·cₙ₊₁ − (n+1)·cₙ`. -/
theorem central_delannoy_recurrence (n : ℕ) :
    ((n : ℤ) + 2) * intCoeff (n + 2) (n + 2)
      = 3 * (2 * (n : ℤ) + 3) * intCoeff (n + 1) (n + 1) - ((n : ℤ) + 1) * intCoeff n n := by
  -- Take the coefficient of `Xⁿ⁺²` on both sides of `heart n`.
  have hcoeff := congrArg (fun p : ℤ[X] => p.coeff (n + 2)) (heart n)
  simp only at hcoeff
  -- LHS coefficient is structurally `0`.
  have hLHS : (X * derivative (Hcert n) - ((n : ℤ[X]) + 2) * Hcert n).coeff (n + 2) = 0 := by
    rw [coeff_sub, coeff_X_mul, coeff_derivative]
    have hCmul : (((n : ℤ[X]) + 2) * Hcert n).coeff (n + 2)
        = ((n : ℤ) + 2) * (Hcert n).coeff (n + 2) := by
      have hC : ((n : ℤ[X]) + 2) = C ((n : ℤ) + 2) := by
        simp [map_add, map_natCast, map_ofNat]
      rw [hC, coeff_C_mul]
    rw [hCmul]; push_cast; ring
  -- RHS coefficient reads off the recurrence.
  have c1 : (X ^ 2 * Qpoly ^ n).coeff (n + 2) = intCoeff n n := by
    rw [coeff_X_pow_mul, ← intCoeff_eq_Qpow]
  have c2 : (X * Qpoly ^ (n + 1)).coeff (n + 2) = intCoeff (n + 1) (n + 1) := by
    have h := coeff_X_mul (Qpoly ^ (n + 1)) (n + 1)
    simpa using h.trans (intCoeff_eq_Qpow (n + 1) (n + 1)).symm
  have c3 : (Qpoly ^ (n + 2)).coeff (n + 2) = intCoeff (n + 2) (n + 2) :=
    (intCoeff_eq_Qpow (n + 2) (n + 2)).symm
  have hRHS : (-((n : ℤ[X]) + 1) * X ^ 2 * Qpoly ^ n
        + 3 * (2 * (n : ℤ[X]) + 3) * X * Qpoly ^ (n + 1)
        - ((n : ℤ[X]) + 2) * Qpoly ^ (n + 2)).coeff (n + 2)
      = -((n : ℤ) + 1) * intCoeff n n
        + 3 * (2 * (n : ℤ) + 3) * intCoeff (n + 1) (n + 1)
        - ((n : ℤ) + 2) * intCoeff (n + 2) (n + 2) := by
    have e1 : -((n : ℤ[X]) + 1) * X ^ 2 * Qpoly ^ n
        = C (-((n : ℤ) + 1)) * (X ^ 2 * Qpoly ^ n) := by
      have : (C (-((n : ℤ) + 1)) : ℤ[X]) = -((n : ℤ[X]) + 1) := by
        simp [map_neg, map_add, map_one, map_natCast]
      rw [this]; ring
    have e2 : 3 * (2 * (n : ℤ[X]) + 3) * X * Qpoly ^ (n + 1)
        = C (3 * (2 * (n : ℤ) + 3)) * (X * Qpoly ^ (n + 1)) := by
      have : (C (3 * (2 * (n : ℤ) + 3)) : ℤ[X]) = 3 * (2 * (n : ℤ[X]) + 3) := by
        simp [map_mul, map_add, map_natCast, map_ofNat]
      rw [this]; ring
    have e3 : ((n : ℤ[X]) + 2) * Qpoly ^ (n + 2) = C ((n : ℤ) + 2) * Qpoly ^ (n + 2) := by
      have : (C ((n : ℤ) + 2) : ℤ[X]) = (n : ℤ[X]) + 2 := by
        simp [map_add, map_natCast, map_ofNat]
      rw [this]
    rw [e1, e2, e3, coeff_sub, coeff_add, coeff_C_mul, coeff_C_mul, coeff_C_mul, c1, c2, c3]
  rw [hLHS, hRHS] at hcoeff
  linarith [hcoeff]

/-- **Central Delannoy recurrence (real form)** — the `cₙ` input to
`DiagonalIntegralLog2Measure.log2_measure_of_recurrence`, discharging its `hrec_c` hypothesis. -/
theorem intCoeff_diag_recurrence :
    PadeCasoratian.Recurrence (fun n => (intCoeff n n : ℝ)) := by
  intro n
  have h := central_delannoy_recurrence n
  have := congrArg (fun z : ℤ => (z : ℝ)) h
  push_cast at this ⊢
  linarith [this]

end DiagonalIntegralLog2
