import Propositio.NumberTheory.Diophantine.WeightedDiagonalLog43Star
import Propositio.NumberTheory.Diophantine.WeightedDiagonalLog43Residue
import Propositio.NumberTheory.Diophantine.WeightedDiagonalLog43Hsmall
import Mathlib.Tactic

/-!
# `aRes_recurrence` proved **unconditionally** — the lone remaining μ(log 4/3) input

The effective irrationality measure of `log(4/3)` was reduced to a single hypothesis
`aRes_recurrence` (`WeightedDiagonalLog43Star`): the leading partial-fraction residue `aRes(·,1)`
(= the Legendre value `Pₙ(7)`) satisfies the three-term recurrence
`(n+2)·X(n+2) = 7(2n+3)·X(n+1) − (n+1)·X(n)`.

We discharge it here, **non-circularly**, in two steps.

1. `log43_irrational : Irrational (Real.log (4/3))` — proved from the SAME bricks that drive the
   measure *except* the recurrence: `Jstar` (`Jₙ = Pexpl n + aRes(n,1)·log(4/3)`), `J_pos`,
   `D_mul_J_tendsto_zero` (`lcm(1..n)·Jₙ → 0`), and the denominator miracle
   `lcmUpto_mul_Pexpl_int`.  This uses NONE of the recurrence/measure, so the bootstrap is not
   circular.  The argument is the exact analogue of `DiagonalIntegralLog2.log_two_irrational`:
   `Dₙ·Jₙ = N/b` is a positive integer over `b`, hence `≥ 1/b`, contradicting `Dₙ·Jₙ → 0`.

2. `aRes_recurrence_holds : aRes_recurrence` — apply the recurrence operator to `Jstar`.  The
   integral `Jₙ` satisfies the recurrence (`J_recurrence`), so `σₙ + ρₙ·log(4/3) = 0`, where
   `σₙ ∈ ℚ` is the `Pexpl` residual and `ρₙ ∈ ℤ` is the `aRes` residual.  Since `log(4/3)` is
   irrational and `σₙ`, `ρₙ` are rational/integer, `ρₙ = 0` — which is exactly `aRes_recurrence`.

Consequently `log43_measure_unconditional`: the effective irrationality measure of `log(4/3)` with
NO hypotheses.
-/

namespace WeightedDiagonalLog43

open Filter LcmGrowthBound

/-- **`log(4/3)` is irrational.**  If `log(4/3) = a/b` then
`Dₙ·Jₙ = (z·b + (Dₙ·aRes(n,1))·a)/b = N/b` is a positive integer over `b` (using the closed-form
denominator miracle `Dₙ·Pexpl n ∈ ℤ` and `aRes(n,1) ∈ ℤ`), hence `≥ 1/b`, contradicting
`Dₙ·Jₙ → 0`.  Pure analogue of `DiagonalIntegralLog2.log_two_irrational`; uses no recurrence. -/
theorem log43_irrational : Irrational (Real.log (4 / 3)) := by
  rintro ⟨q, hq⟩
  set b : ℤ := (q.den : ℤ) with hb
  have hbpos : (0 : ℝ) < (b : ℝ) := by rw [hb]; exact_mod_cast q.pos
  have hbne : (b : ℝ) ≠ 0 := ne_of_gt hbpos
  have hlog : Real.log (4 / 3) = (q.num : ℝ) / (b : ℝ) := by
    rw [← hq, Rat.cast_def, hb]; push_cast; ring
  -- per `n`, `Dₙ·Jₙ ≥ 1/b`
  have hge : ∀ n : ℕ, (1 : ℝ) / (b : ℝ) ≤ (lcmUpto n : ℝ) * J n := by
    intro n
    obtain ⟨z, hz⟩ := lcmUpto_mul_Pexpl_int n
    have hzR : (lcmUpto n : ℝ) * (Pexpl n : ℝ) = (z : ℝ) := by exact_mod_cast hz
    set A : ℤ := (lcmUpto n : ℤ) * aRes n 1 with hA
    set N : ℤ := z * b + A * q.num with hN
    have hDJ : (lcmUpto n : ℝ) * J n = (N : ℝ) / (b : ℝ) := by
      rw [Jstar n, mul_add, hzR, hlog, hN, hA]
      push_cast
      field_simp
    have hNeq : (N : ℝ) = ((lcmUpto n : ℝ) * J n) * (b : ℝ) := by
      rw [hDJ]; field_simp
    have hNposR : (0 : ℝ) < (N : ℝ) := by
      rw [hNeq]
      exact mul_pos (mul_pos
        (by exact_mod_cast Nat.pos_of_ne_zero (lcmUpto_ne_zero n)) (J_pos n)) hbpos
    have hN1 : (1 : ℝ) ≤ (N : ℝ) := by
      have hNposZ : (0 : ℤ) < N := by exact_mod_cast hNposR
      exact_mod_cast (by omega : (1 : ℤ) ≤ N)
    rw [div_le_iff₀ hbpos, ← hNeq]
    exact hN1
  -- but `Dₙ·Jₙ → 0`, so eventually `< 1/b` — contradiction
  have hb0 : (0 : ℝ) < (1 : ℝ) / (b : ℝ) := by positivity
  obtain ⟨n, hn⟩ := (D_mul_J_tendsto_zero.eventually_lt_const hb0).exists
  exact absurd (hge n) (not_le.mpr hn)

/-- **The leading-residue recurrence, PROVED.**  Apply the integral recurrence `J_recurrence` to
`Jstar`: `σₙ + ρₙ·log(4/3) = 0` with `σₙ ∈ ℚ` (Pexpl residual) and `ρₙ ∈ ℤ` (aRes residual).  By
`log43_irrational`, `ρₙ = 0`.  Discharges the frontier hypothesis `aRes_recurrence`. -/
theorem aRes_recurrence_holds : aRes_recurrence := by
  intro n
  -- The aRes residual is an integer `ρ`, the Pexpl residual a rational `σ` (both as reals).
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℤ, ((n : ℝ) + 2) * (aRes (n + 2) 1 : ℝ)
      - 7 * (2 * (n : ℝ) + 3) * (aRes (n + 1) 1 : ℝ) + ((n : ℝ) + 1) * (aRes n 1 : ℝ) = (ρ : ℝ) := by
    refine ⟨((n : ℤ) + 2) * aRes (n + 2) 1 - 7 * (2 * (n : ℤ) + 3) * aRes (n + 1) 1
      + ((n : ℤ) + 1) * aRes n 1, ?_⟩
    push_cast; ring
  obtain ⟨σ, hσ⟩ : ∃ σ : ℚ, ((n : ℝ) + 2) * (Pexpl (n + 2) : ℝ)
      - 7 * (2 * (n : ℝ) + 3) * (Pexpl (n + 1) : ℝ) + ((n : ℝ) + 1) * (Pexpl n : ℝ) = (σ : ℝ) := by
    refine ⟨((n : ℚ) + 2) * Pexpl (n + 2) - 7 * (2 * (n : ℚ) + 3) * Pexpl (n + 1)
      + ((n : ℚ) + 1) * Pexpl n, ?_⟩
    push_cast; ring
  -- The integral recurrence `J_recurrence`, expanded by `Jstar`, gives `σ + ρ·log(4/3) = 0`.
  have hzero : (σ : ℝ) + (ρ : ℝ) * Real.log (4 / 3) = 0 := by
    have hr := J_recurrence n
    rw [Jstar n, Jstar (n + 1), Jstar (n + 2)] at hr
    rw [← hσ, ← hρ]
    linear_combination hr
  -- If `ρ ≠ 0` then `log(4/3) = −σ/ρ` is rational — contradiction with `log43_irrational`.
  have hρ0 : ρ = 0 := by
    by_contra hρne
    have hirr : Irrational ((σ : ℝ) + (ρ : ℝ) * Real.log (4 / 3)) :=
      Irrational.ratCast_add σ (log43_irrational.intCast_mul hρne)
    rw [hzero] at hirr
    exact not_irrational_zero hirr
  -- `ρ = 0` is exactly the recurrence (over ℝ).
  have hRcast : ((n : ℝ) + 2) * (aRes (n + 2) 1 : ℝ)
      - 7 * (2 * (n : ℝ) + 3) * (aRes (n + 1) 1 : ℝ) + ((n : ℝ) + 1) * (aRes n 1 : ℝ) = 0 := by
    rw [hρ, hρ0]; simp
  linear_combination hRcast

/-- **The leading residue is the Legendre / central-Delannoy value:**
`aRes(n,1) = JαZ n = Σ_{k=0}^n C(n,k)·C(n+k,k)·3ᵏ = Pₙ(7)`.

Now that `aRes_recurrence` is proved, this is a routine two-step induction: both sides obey the SAME
three-term recurrence — `aRes_recurrence_holds` (cast to ℤ) and the Zeilberger-proved `JαZ_rec` — with
matching base values `1, 7`.  This realizes, transcendence-free, the explicit closed form that the
construction conjectured (and gives a second, irrationality-free proof of the recurrence for `JαZ`). -/
theorem aRes_one_eq_JαZ (n : ℕ) : aRes n 1 = JαZ n := by
  have hrec_int : ∀ m : ℕ, ((m : ℤ) + 2) * aRes (m + 2) 1
      = 7 * (2 * (m : ℤ) + 3) * aRes (m + 1) 1 - ((m : ℤ) + 1) * aRes m 1 := by
    intro m; exact_mod_cast aRes_recurrence_holds m
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 =>
      have hA : aRes 0 1 = 1 := by
        unfold aRes serNeg
        simp [Polynomial.coeff_one]
      rw [hA]; decide
    | 1 =>
      have hA : aRes 1 1 = 7 := by
        unfold aRes serNeg
        simp [Finset.sum_range_succ, Finset.sum_range_zero, pow_succ,
          Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
          Polynomial.coeff_X, Polynomial.coeff_one, Polynomial.coeff_ofNat_zero,
          Polynomial.coeff_ofNat_succ, Nat.choose_self, Nat.choose_one_right]
      rw [hA]; decide
    | (m + 2) =>
      have ih0 := ih m (by omega)
      have ih1 := ih (m + 1) (by omega)
      have hne : ((m : ℤ) + 2) ≠ 0 := by positivity
      apply mul_left_cancel₀ hne
      rw [hrec_int m, JαZ_rec m, ih0, ih1]

/-- **Effective irrationality measure of `log(4/3)`, UNCONDITIONAL.**  The frontier hypothesis
`aRes_recurrence` is now a theorem (`aRes_recurrence_holds`), so the conditional measure
`log43_measure_of_aRes_recurrence` becomes unconditional. -/
theorem log43_measure_unconditional :
    ∃ A ρ Q : ℝ, 0 < A ∧ 0 < ρ ∧ ρ < 1 ∧ 1 < Q ∧
      ∃ C > 0, ∀ (p q : ℤ), 1 ≤ q → (1 : ℝ) ≤ 2 * A * q →
        C / (q : ℝ) ^ (1 + Real.log Q / Real.log ρ⁻¹) ≤ |Real.log (4 / 3) - (p : ℝ) / q| :=
  log43_measure_of_aRes_recurrence aRes_recurrence_holds

end WeightedDiagonalLog43
