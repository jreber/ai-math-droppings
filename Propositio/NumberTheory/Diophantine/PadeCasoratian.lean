import Mathlib.Tactic

/-!
# Casoratian telescoping for the Padé / Alladi–Robinson recurrence

The diagonal `log 2` construction's denominator `cₙ = coeff n((X−1)ⁿ(2−X)ⁿ)` and rational part
`rₙ` both satisfy the same three-term recurrence (verified numerically, n≤15,
`experiments/log2_construction_measure_inputs.clj`):

  `(m+1)·Xₘ₊₁ = 3(2m+1)·Xₘ − m·Xₘ₋₁`,   i.e.   `(n+2)·Xₙ₊₂ = 3(2n+3)·Xₙ₊₁ − (n+1)·Xₙ`.

This file proves, abstractly, that **any** two sequences obeying this recurrence have a Casoratian
`Wₙ = Xₙ·Yₙ₊₁ − Xₙ₊₁·Yₙ` that telescopes: `(n+1)·Wₙ = W₀`, hence `Wₙ = W₀/(n+1)`.

This is the structural heart of the determinant / non-vanishing condition
(`IrrMeasureCombination.irrationality_measure_le`'s `hdet`): with `Xₙ = cₙ`, `Yₙ = rₙ`,
`W₀ = c₀r₁ − c₁r₀ = −2`, it gives `cₙrₙ₊₁ − cₙ₊₁rₙ = −2/(n+1) ≠ 0`.  It reduces the entire
determinant condition for the `log 2` measure to a single fact: that the construction's sequences
obey the recurrence (a creative-telescoping/Zeilberger target on the integral
`(n+1)Iₙ₊₁ = 3(2n+1)Iₙ − n·Iₙ₋₁`).
-/

namespace PadeCasoratian

variable {K : Type*} [Field K] [CharZero K]

/-- `(n : K) + 1 ≠ 0` in a characteristic-zero field. -/
theorem n_add_one_ne_zero (n : ℕ) : ((n : K) + 1) ≠ 0 := by
  have : ((n : K) + 1) = ((n + 1 : ℕ) : K) := by push_cast; ring
  rw [this]; exact_mod_cast Nat.succ_ne_zero n

/-- The Padé recurrence `(n+2)·Xₙ₊₂ = 3(2n+3)·Xₙ₊₁ − (n+1)·Xₙ` (shifted so all indices are `ℕ`). -/
def Recurrence (X : ℕ → K) : Prop :=
  ∀ n : ℕ, ((n : K) + 2) * X (n + 2) = 3 * (2 * (n : K) + 3) * X (n + 1) - ((n : K) + 1) * X n

/-- The Casoratian `Wₙ = Xₙ·Yₙ₊₁ − Xₙ₊₁·Yₙ`. -/
def W (X Y : ℕ → K) (n : ℕ) : K := X n * Y (n + 1) - X (n + 1) * Y n

/-- **One-step Casoratian relation** `(n+2)·Wₙ₊₁ = (n+1)·Wₙ`, from the two recurrences. -/
theorem casoratian_step (X Y : ℕ → K) (hX : Recurrence X) (hY : Recurrence Y) (n : ℕ) :
    ((n : K) + 2) * W X Y (n + 1) = ((n : K) + 1) * W X Y n := by
  unfold W
  have hx := hX n
  have hy := hY n
  linear_combination X (n + 1) * hy - Y (n + 1) * hx

/-- **Casoratian telescoping** `(n+1)·Wₙ = W₀`. -/
theorem casoratian_telescope (X Y : ℕ → K) (hX : Recurrence X) (hY : Recurrence Y) (n : ℕ) :
    ((n : K) + 1) * W X Y n = W X Y 0 := by
  induction n with
  | zero => push_cast; ring
  | succ m ih =>
    have key := casoratian_step X Y hX hY m
    have goal_cast : ((↑(m + 1) : K) + 1) = (↑m + 2) := by push_cast; ring
    rw [goal_cast, key]
    exact ih

/-- **Closed form** `Wₙ = W₀/(n+1)`; in particular `Wₙ ≠ 0` whenever `W₀ ≠ 0`. -/
theorem casoratian_eq_div (X Y : ℕ → K) (hX : Recurrence X) (hY : Recurrence Y) (n : ℕ) :
    W X Y n = W X Y 0 / ((n : K) + 1) := by
  rw [eq_div_iff (n_add_one_ne_zero n), mul_comm]
  exact casoratian_telescope X Y hX hY n

/-- **Non-vanishing**: if `W₀ ≠ 0` then every `Wₙ ≠ 0` — the determinant/non-vanishing input. -/
theorem casoratian_ne_zero (X Y : ℕ → K) (hX : Recurrence X) (hY : Recurrence Y)
    (h0 : W X Y 0 ≠ 0) (n : ℕ) : W X Y n ≠ 0 := by
  rw [casoratian_eq_div X Y hX hY n]
  exact div_ne_zero h0 (n_add_one_ne_zero n)

/-! ## Positivity (the `hapos` input) -/

section Positivity
variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]

/-- **Positivity + monotonicity** of a recurrence sequence with `0 < X₀ ≤ X₁`.  The invariant
`0 < Xₙ ≤ Xₙ₊₁` propagates: from `(n+2)Xₙ₊₂ = 3(2n+3)Xₙ₊₁ − (n+1)Xₙ` and `Xₙ ≤ Xₙ₊₁`,
`(m+2)·Xₙ₊₂ ≥ (m+2)·Xₙ₊₁` since `(5n+7)Xₙ₊₁ ≥ (n+1)Xₙ`.  Gives `cₙ > 0` (the `hapos` input)
once the construction's denominator is known to obey the recurrence. -/
theorem rec_pos_mono (X : ℕ → F) (hrec : Recurrence X) (h0 : 0 < X 0) (h01 : X 0 ≤ X 1) :
    ∀ n, 0 < X n ∧ X n ≤ X (n + 1) := by
  intro n
  induction n with
  | zero => exact ⟨h0, h01⟩
  | succ m ih =>
    obtain ⟨hpos, hmono⟩ := ih
    have hpos1 : 0 < X (m + 1) := lt_of_lt_of_le hpos hmono
    have hrec_m := hrec m
    have hmnn : (0 : F) ≤ (m : F) := Nat.cast_nonneg m
    have hm2 : (0 : F) < (m : F) + 2 := by positivity
    refine ⟨hpos1, ?_⟩
    -- `(m+2)·(Xₘ₊₂ − Xₘ₊₁) = (5m+7)Xₘ₊₁ − (m+1)Xₘ ≥ 0`, and `m+2 > 0` ⟹ `Xₘ₊₁ ≤ Xₘ₊₂`.
    have hdiff : ((m : F) + 2) * (X (m + 2) - X (m + 1))
        = (5 * (m : F) + 7) * X (m + 1) - ((m : F) + 1) * X m := by
      rw [mul_sub, hrec_m]; ring
    have hrhs : (0 : F) ≤ (5 * (m : F) + 7) * X (m + 1) - ((m : F) + 1) * X m := by
      nlinarith [mul_nonneg (by positivity : (0:F) ≤ 5 * (m:F) + 7) (sub_nonneg.mpr hmono),
        mul_nonneg (by positivity : (0:F) ≤ 4 * (m:F) + 6) (le_of_lt hpos)]
    have hge : (0 : F) ≤ X (m + 2) - X (m + 1) :=
      (mul_nonneg_iff_of_pos_left hm2).mp (hdiff ▸ hrhs)
    linarith [hge]

/-- `0 < Xₙ` for all `n`, from `0 < X₀ ≤ X₁` and the recurrence (the `hapos` input). -/
theorem rec_pos (X : ℕ → F) (hrec : Recurrence X) (h0 : 0 < X 0) (h01 : X 0 ≤ X 1) (n : ℕ) :
    0 < X n := (rec_pos_mono X hrec h0 h01 n).1

end Positivity

end PadeCasoratian
