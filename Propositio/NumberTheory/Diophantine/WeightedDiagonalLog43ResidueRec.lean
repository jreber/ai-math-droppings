import Propositio.NumberTheory.Diophantine.WeightedDiagonalLog43Residue
import Propositio.NumberTheory.Diophantine.PadeRecurrenceGen
import Mathlib.Tactic

/-!
# Sharpening the closed-form gap, and the exact Casoratian value

`WeightedDiagonalLog43Residue` reduced the effective irrationality measure of `log(4/3)` to the
single explicit identity `JP n = Pexpl n` (recurrence rational part = partial-fraction closed form).
Here we

* reduce that identity *further* to **`Pexpl` satisfies the same three-term recurrence** (plus the
  base case `Pexpl 1 = −2`; `Pexpl 0 = 0` is automatic) — `JP_eq_Pexpl_of_rec`.  So the lone
  remaining input for an *unconditional* `μ(log 4/3)` is the recurrence-satisfaction of the closed
  form (a Zeilberger-style second-solution telescoping), and
* record the exact **Casoratian value** `α₁(n)·Pₙ₊₁ − α₁(n+1)·Pₙ = −2/(n+1)` — the closed-form first
  integral of the recurrence pair `(Jα, JP)`.
-/

namespace WeightedDiagonalLog43

open scoped BigOperators
open Polynomial

/-- `Pexpl 0 = 0` (the sum is over the empty range `Icc 1 0`). -/
theorem Pexpl_zero : Pexpl 0 = 0 := by
  simp [Pexpl]

/-- The base residue `aRes 1 2 = −2` (coefficient `[X⁰]((X−1)(2−X)·serNeg 1)`). -/
theorem aRes_one_two : aRes 1 2 = -2 := by
  unfold aRes serNeg; simp [Finset.sum_range_succ, pow_succ, Polynomial.coeff_mul]

/-- The base residue `bRes 1 2 = −6`. -/
theorem bRes_one_two : bRes 1 2 = -6 := by
  unfold bRes serPos; simp [Finset.sum_range_succ, Polynomial.coeff_mul]

/-- `Pexpl 1 = −2` (the single bracket `aRes 1 2·(1−½) + bRes 1 2·(½−⅓) = −1 − 1`). -/
theorem Pexpl_one : Pexpl 1 = -2 := by
  unfold Pexpl
  rw [Finset.Icc_self, Finset.sum_singleton]
  unfold Pbracket
  norm_num [aRes_one_two, bRes_one_two]

/-- **Reduction of the closed-form identity to the recurrence.**  Both base cases are now *proved*
(`Pexpl_zero`, `Pexpl_one`), so if `Pexpl` satisfies the same three-term recurrence as `JP`, then
`JP = Pexpl` everywhere.  Two-step strong induction off `JP_rec`.  Hence the unconditional measure
follows once the explicit closed form is shown to solve the recurrence. -/
theorem JP_eq_Pexpl_of_rec
    (hrec : ∀ n : ℕ, ((n : ℚ) + 2) * Pexpl (n + 2)
        = 7 * (2 * (n : ℚ) + 3) * Pexpl (n + 1) - ((n : ℚ) + 1) * Pexpl n) :
    ∀ n, JP n = Pexpl n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => rw [Pexpl_zero]; rfl
    | 1 => rw [Pexpl_one]; rfl
    | (m + 2) =>
      have ihm := ih m (by omega)
      have ihm1 := ih (m + 1) (by omega)
      have hne : ((m : ℚ) + 2) ≠ 0 := by positivity
      apply mul_left_cancel₀ hne
      rw [JP_rec m, ihm, ihm1, ← hrec m]

/-- **Effective irrationality measure of `log(4/3)`, modulo only the recurrence-satisfaction of the
closed form.**  Both base cases are proved, integrality (`Jα_int`) is proved, and the denominator
miracle (`lcmUpto_mul_Pexpl_int`) is proved; the *sole* remaining input is that the explicit residue
closed form `Pexpl` satisfies the same three-term recurrence as `JP`. -/
theorem log43_measure_of_Pexpl_rec
    (hrec : ∀ n : ℕ, ((n : ℚ) + 2) * Pexpl (n + 2)
        = 7 * (2 * (n : ℚ) + 3) * Pexpl (n + 1) - ((n : ℚ) + 1) * Pexpl n) :
    ∃ A ρ Q : ℝ, 0 < A ∧ 0 < ρ ∧ ρ < 1 ∧ 1 < Q ∧
      ∃ C > 0, ∀ (p q : ℤ), 1 ≤ q → (1 : ℝ) ≤ 2 * A * q →
        C / (q : ℝ) ^ (1 + Real.log Q / Real.log ρ⁻¹) ≤ |Real.log (4 / 3) - (p : ℝ) / q| :=
  log43_measure_of_Pexpl_eq (JP_eq_Pexpl_of_rec hrec)

/-- **The exact Casoratian value** `α₁(n)·Pₙ₊₁ − α₁(n+1)·Pₙ = −2/(n+1)` — the closed-form first
integral of the recurrence pair `(Jα, JP)`, from `PadeRecurrenceGen.casoratian_eq_div` with base
Casoratian `W₀ = Jα₀·P₁ − Jα₁·P₀ = 1·(−2) − 7·0 = −2`. -/
theorem casoratian_value (n : ℕ) :
    Jα n * JP (n + 1) - Jα (n + 1) * JP n = -2 / ((n : ℚ) + 1) := by
  have h := PadeRecurrenceGen.casoratian_eq_div (7 : ℚ) Jα JP Jα_pade JP_pade n
  simp only [PadeRecurrenceGen.W] at h
  rw [h]
  simp only [Jα, JP]
  norm_num

end WeightedDiagonalLog43
