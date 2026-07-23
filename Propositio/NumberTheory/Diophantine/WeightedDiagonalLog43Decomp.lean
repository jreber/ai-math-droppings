import Propositio.NumberTheory.Diophantine.WeightedDiagonalLog43
import Propositio.NumberTheory.Diophantine.PadeRecurrenceGen
import Mathlib.Tactic

/-!
# The single-log decomposition `Jₙ = Pₙ + α₁(n)·log(4/3)`

The weighted two-pole diagonal `Jₙ` collapses to a SINGLE logarithm: there are rational sequences
`Pₙ` (the rational part) and `α₁(n)` (the log-coefficient, in fact a positive integer) with
`Jₙ = Pₙ + α₁(n)·log(4/3)`.  Both obey the `J`-recurrence `(n+2)Xₙ₊₂ = 7(2n+3)Xₙ₊₁ − (n+1)Xₙ`
(`PadeRecurrenceGen.Recurrence 7`), with `α₁(0)=1, α₁(1)=7` and `P₀=0, P₁=−2`.

Here we define `Jα, JP : ℕ → ℚ` by that recurrence and prove the decomposition by two-step
induction, using the proved `J_recurrence` and the base cases `J_zero`, `J_one`.  This is the
single-log core of the unconditional effective irrationality measure of `log(4/3)` (the
log2-template clone); `α₁`'s integrality and the denominator bound `den(Pₙ) | lcm(1..n)` (the
2,3-adic miracle, verified numerically n≤20) remain for the measure assembly.
-/

namespace WeightedDiagonalLog43

open MeasureTheory

/-- The log-coefficient sequence `α₁(n)` (a rational, in fact `1,7,73,847,…`), defined by the
`J`-recurrence with `α₁(0)=1, α₁(1)=7`. -/
def Jα : ℕ → ℚ
  | 0 => 1
  | 1 => 7
  | (n + 2) => (7 * (2 * (n : ℚ) + 3) * Jα (n + 1) - ((n : ℚ) + 1) * Jα n) / ((n : ℚ) + 2)

/-- The rational-part sequence `Pₙ` (`0,−2,−21,…`), same recurrence, `P₀=0, P₁=−2`. -/
def JP : ℕ → ℚ
  | 0 => 0
  | 1 => -2
  | (n + 2) => (7 * (2 * (n : ℚ) + 3) * JP (n + 1) - ((n : ℚ) + 1) * JP n) / ((n : ℚ) + 2)

theorem Jα_rec (n : ℕ) :
    ((n : ℚ) + 2) * Jα (n + 2) = 7 * (2 * (n : ℚ) + 3) * Jα (n + 1) - ((n : ℚ) + 1) * Jα n := by
  have hne : ((n : ℚ) + 2) ≠ 0 := by positivity
  rw [show Jα (n + 2)
      = (7 * (2 * (n : ℚ) + 3) * Jα (n + 1) - ((n : ℚ) + 1) * Jα n) / ((n : ℚ) + 2) from by
    simp only [Jα]]
  field_simp

theorem JP_rec (n : ℕ) :
    ((n : ℚ) + 2) * JP (n + 2) = 7 * (2 * (n : ℚ) + 3) * JP (n + 1) - ((n : ℚ) + 1) * JP n := by
  have hne : ((n : ℚ) + 2) ≠ 0 := by positivity
  rw [show JP (n + 2)
      = (7 * (2 * (n : ℚ) + 3) * JP (n + 1) - ((n : ℚ) + 1) * JP n) / ((n : ℚ) + 2) from by
    simp only [JP]]
  field_simp

/-- **The single-log decomposition** `Jₙ = Pₙ + α₁(n)·log(4/3)` (`Pₙ = JP n`, `α₁(n) = Jα n`). -/
theorem J_decomp (n : ℕ) : J n = (JP n : ℝ) + (Jα n : ℝ) * Real.log (4 / 3) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => simp only [Jα, JP]; rw [J_zero]; push_cast; ring
    | 1 => simp only [Jα, JP]; rw [J_one]; push_cast; ring
    | (m + 2) =>
      have ihm := ih m (by omega)
      have ihm1 := ih (m + 1) (by omega)
      have hJ := J_recurrence m
      -- the integer/rational recurrences, cast to ℝ
      have hαR : ((m : ℝ) + 2) * (Jα (m + 2) : ℝ)
          = 7 * (2 * (m : ℝ) + 3) * (Jα (m + 1) : ℝ) - ((m : ℝ) + 1) * (Jα m : ℝ) := by
        have := Jα_rec m; push_cast at this ⊢; exact_mod_cast this
      have hPR : ((m : ℝ) + 2) * (JP (m + 2) : ℝ)
          = 7 * (2 * (m : ℝ) + 3) * (JP (m + 1) : ℝ) - ((m : ℝ) + 1) * (JP m : ℝ) := by
        have := JP_rec m; push_cast at this ⊢; exact_mod_cast this
      have hne : ((m : ℝ) + 2) ≠ 0 := by positivity
      -- show (m+2)·J(m+2) = (m+2)·(JP(m+2) + Jα(m+2)·log), then cancel
      apply mul_left_cancel₀ hne
      rw [hJ, ihm, ihm1]
      linear_combination -hPR - Real.log (4 / 3) * hαR

/-- **Positivity and monotonicity** of the log-coefficient `α₁`: `0 < α₁(n) ≤ α₁(n+1)`.
By a combined induction off the recurrence (`(13m+19)·α₁(m+1) ≥ (m+1)·α₁ m` from monotonicity). -/
theorem Jα_pos_mono (n : ℕ) : 0 < Jα n ∧ Jα n ≤ Jα (n + 1) := by
  induction n with
  | zero => exact ⟨by norm_num [Jα], by norm_num [Jα]⟩
  | succ m ih =>
    obtain ⟨hpos, hmono⟩ := ih
    have hpos1 : 0 < Jα (m + 1) := lt_of_lt_of_le hpos hmono
    refine ⟨hpos1, ?_⟩
    have hm2 : (0 : ℚ) < (m : ℚ) + 2 := by positivity
    have hrec := Jα_rec m
    have hmnn : (0 : ℚ) ≤ (m : ℚ) := Nat.cast_nonneg m
    have key : ((m : ℚ) + 2) * Jα (m + 1) ≤ ((m : ℚ) + 2) * Jα (m + 2) := by
      rw [hrec]; nlinarith [hpos, hpos1, hmono, hmnn]
    exact le_of_mul_le_mul_left key hm2

/-- `0 < α₁(n)` — the `hapos` input. -/
theorem Jα_pos (n : ℕ) : 0 < Jα n := (Jα_pos_mono n).1

/-- `Jα` satisfies the constant-`7` Padé recurrence. -/
theorem Jα_pade : PadeRecurrenceGen.Recurrence (7 : ℚ) Jα := Jα_rec

/-- `JP` satisfies the constant-`7` Padé recurrence. -/
theorem JP_pade : PadeRecurrenceGen.Recurrence (7 : ℚ) JP := JP_rec

/-- **The Casoratian (`hdet`) input.**  `α₁(n)·Pₙ₊₁ − α₁(n+1)·Pₙ ≠ 0` for every `n` — the
determinant non-vanishing of the consecutive Padé forms, from `PadeRecurrenceGen.casoratian_ne_zero`
(base Casoratian `α₁(0)P₁ − α₁(1)P₀ = 1·(−2) − 7·0 = −2 ≠ 0`; closed form `−2/(n+1)`). -/
theorem casoratian_nonzero (n : ℕ) : Jα n * JP (n + 1) - Jα (n + 1) * JP n ≠ 0 := by
  have h0 : PadeRecurrenceGen.W Jα JP 0 ≠ 0 := by
    simp only [PadeRecurrenceGen.W, Jα, JP]; norm_num
  exact PadeRecurrenceGen.casoratian_ne_zero (7 : ℚ) Jα JP Jα_pade JP_pade h0 n

end WeightedDiagonalLog43
