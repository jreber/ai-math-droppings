import Mathlib.Tactic

/-!
# Constant-parametrized Padé / Casoratian recurrence

`PadeCasoratian.lean` hard-codes the central-Delannoy constant `3` in its recurrence
`(n+2)Xₙ₊₂ = 3(2n+3)Xₙ₊₁ − (n+1)Xₙ`.  The weighted two-pole diagonal `Jₙ` (`WeightedDiagonalLog43`)
satisfies the SAME shape with `3` replaced by `7`, and other diagonals give other constants.

The Casoratian machinery is **constant-independent**: in `(n+2)·Wₙ₊₁ = (n+1)·Wₙ` the middle term
`k(2n+3)·Xₙ₊₁·Yₙ₊₁` cancels against its `Y`-counterpart, so the telescoping and non-vanishing hold
for every constant `k`.  This file proves that once, parametrized by `k`, so the determinant
(`hdet`) input of `IrrMeasureCombination.irrationality_measure_le` is available for any such
recurrence — in particular the `J`-family (`k = 7`), discharging its Casoratian non-vanishing
(numerically `α₁(n)·Pₙ₊₁ − α₁(n+1)·Pₙ = −2/(n+1) ≠ 0`).
-/

namespace PadeRecurrenceGen

variable {K : Type*} [Field K] [CharZero K]

/-- `(n : K) + 1 ≠ 0` in a characteristic-zero field. -/
theorem n_add_one_ne_zero (n : ℕ) : ((n : K) + 1) ≠ 0 := by
  have : ((n : K) + 1) = ((n + 1 : ℕ) : K) := by push_cast; ring
  rw [this]; exact_mod_cast Nat.succ_ne_zero n

/-- The constant-`k` Padé recurrence `(n+2)·Xₙ₊₂ = k(2n+3)·Xₙ₊₁ − (n+1)·Xₙ`. -/
def Recurrence (k : K) (X : ℕ → K) : Prop :=
  ∀ n : ℕ, ((n : K) + 2) * X (n + 2) = k * (2 * (n : K) + 3) * X (n + 1) - ((n : K) + 1) * X n

/-- The Casoratian `Wₙ = Xₙ·Yₙ₊₁ − Xₙ₊₁·Yₙ`. -/
def W (X Y : ℕ → K) (n : ℕ) : K := X n * Y (n + 1) - X (n + 1) * Y n

set_option linter.unusedSectionVars false

/-- **One-step Casoratian relation** `(n+2)·Wₙ₊₁ = (n+1)·Wₙ` — independent of the constant `k`
(the middle terms cancel). -/
theorem casoratian_step (k : K) (X Y : ℕ → K) (hX : Recurrence k X) (hY : Recurrence k Y) (n : ℕ) :
    ((n : K) + 2) * W X Y (n + 1) = ((n : K) + 1) * W X Y n := by
  unfold W
  have hx := hX n
  have hy := hY n
  linear_combination X (n + 1) * hy - Y (n + 1) * hx

/-- **Casoratian telescoping** `(n+1)·Wₙ = W₀`. -/
theorem casoratian_telescope (k : K) (X Y : ℕ → K) (hX : Recurrence k X) (hY : Recurrence k Y)
    (n : ℕ) : ((n : K) + 1) * W X Y n = W X Y 0 := by
  induction n with
  | zero => push_cast; ring
  | succ m ih =>
    have key := casoratian_step k X Y hX hY m
    have goal_cast : ((↑(m + 1) : K) + 1) = (↑m + 2) := by push_cast; ring
    rw [goal_cast, key]; exact ih

/-- **Closed form** `Wₙ = W₀/(n+1)`. -/
theorem casoratian_eq_div (k : K) (X Y : ℕ → K) (hX : Recurrence k X) (hY : Recurrence k Y)
    (n : ℕ) : W X Y n = W X Y 0 / ((n : K) + 1) := by
  rw [eq_div_iff (n_add_one_ne_zero n), mul_comm]
  exact casoratian_telescope k X Y hX hY n

/-- **Non-vanishing**: if `W₀ ≠ 0` then every `Wₙ ≠ 0` — the determinant/`hdet` input. -/
theorem casoratian_ne_zero (k : K) (X Y : ℕ → K) (hX : Recurrence k X) (hY : Recurrence k Y)
    (h0 : W X Y 0 ≠ 0) (n : ℕ) : W X Y n ≠ 0 := by
  rw [casoratian_eq_div k X Y hX hY n]
  exact div_ne_zero h0 (n_add_one_ne_zero n)

end PadeRecurrenceGen
