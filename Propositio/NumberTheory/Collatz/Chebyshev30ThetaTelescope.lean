import Propositio.NumberTheory.Collatz.Chebyshev30ThetaTight

/-!
# Chebyshev-30: a *log²-additive* tight upper bound on `θ`

`CollatzChebyshev30.theta_tight` telescopes the per-step inequality only above the
huge threshold `x ≥ 57600`, so its additive constant is `θ(57600) ≈ 57600` — a
catastrophe once it is exponentiated.

Here we telescope the *raw* per-step bound `hstep_real`
(`θ(x) − θ(x/6) ≤ A·x + 4·log x + 4`, valid for `x ≥ 30`) directly, carrying a
logarithmic additive term `F(x) = (log x / log 6 + 1)·(4 log x + 4)` of size
`O(log² x)` instead of absorbing it into a linear slack.  The clean telescoping
identity is

  `F(x) − F(x/6) = 8·log x + 4`,

so a single step drops the additive budget by `A·x + 8 log x + 4`, which dominates
the per-step cost `A·x + 4 log x + 4` (since `log x ≥ 0`).  The result is the tight
bound

  `θ(x) ≤ (6·A/5)·x + (log x / log 6 + 1)·(4 log x + 4) + θ(30)`,

with the *small* base `θ(30) ≈ 22.6` and leading slope `6·A/5 ≈ 1.105`.
-/

namespace CollatzChebyshev30

open Chebyshev Real

/-- **Tight Chebyshev upper bound on `θ` with `O(log² x)` additive error.**

Replaces `theta_tight`'s catastrophic additive constant `θ(57600)` with the small
base `θ(30) ≈ 22.6` plus a logarithmic tail. -/
theorem theta_loglin (x : ℝ) (hx : 1 ≤ x) :
    theta x ≤ (6 * Aentropy / 5) * x
            + (Real.log x / Real.log 6 + 1) * (4 * Real.log x + 4) + theta 30 := by
  have hL6 : Real.log 6 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have hL6pos : 0 < Real.log 6 := Real.log_pos (by norm_num)
  have key : ∀ n : ℕ, ∀ x : ℝ, 1 ≤ x → ⌊x⌋₊ ≤ n →
      theta x ≤ (6 * Aentropy / 5) * x
              + (Real.log x / Real.log 6 + 1) * (4 * Real.log x + 4) + theta 30 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro x hx hxn
      have hlogx : 0 ≤ Real.log x := Real.log_nonneg hx
      -- the logarithmic additive term is nonnegative
      have hFnn : 0 ≤ (Real.log x / Real.log 6 + 1) * (4 * Real.log x + 4) := by
        apply mul_nonneg
        · have : 0 ≤ Real.log x / Real.log 6 := div_nonneg hlogx (le_of_lt hL6pos)
          linarith
        · linarith
      have hAx : 0 ≤ (6 * Aentropy / 5) * x :=
        mul_nonneg (by linarith [Aentropy_nonneg]) (by linarith)
      rcases lt_or_ge x 30 with hlt | hge
      · -- base region: θ x ≤ θ 30, and the extra terms are ≥ 0
        have hmono : theta x ≤ theta 30 := theta_mono (le_of_lt hlt)
        linarith
      · -- inductive step: x ≥ 30
        have hxpos : 0 < x := by linarith
        have hx6 : (1:ℝ) ≤ x / 6 := by linarith
        have hfloor6 : ⌊x / 6⌋₊ < ⌊x⌋₊ := by
          rw [Nat.floor_lt (by linarith : (0:ℝ) ≤ x / 6)]
          have h1 : x - 1 < (⌊x⌋₊ : ℝ) := by
            have := Nat.lt_floor_add_one x; linarith
          have h2 : x / 6 ≤ x - 1 := by linarith
          linarith
        have hlt_n : ⌊x / 6⌋₊ < n := lt_of_lt_of_le hfloor6 hxn
        have hih := ih ⌊x / 6⌋₊ hlt_n (x / 6) hx6 (le_refl _)
        have hs := hstep_real x hge
        -- log (x/6) = log x − log 6
        have hlog6 : Real.log (x / 6) = Real.log x - Real.log 6 := by
          rw [Real.log_div (ne_of_gt hxpos) (by norm_num)]
        -- the clean telescoping identity F(x) − F(x/6) = 8 log x + 4
        have key_id :
            (Real.log x / Real.log 6 + 1) * (4 * Real.log x + 4)
              - (Real.log (x / 6) / Real.log 6 + 1) * (4 * Real.log (x / 6) + 4)
              = 8 * Real.log x + 4 := by
          rw [hlog6]; field_simp; ring
        -- the A·x products cancel exactly across the step
        have hAcancel :
            (6 * Aentropy / 5) * (x / 6) + Aentropy * x = (6 * Aentropy / 5) * x := by
          ring
        linarith [hih, hs, key_id, hAcancel, hlogx]
  exact key ⌊x⌋₊ x hx (le_refl _)

end CollatzChebyshev30

#print axioms CollatzChebyshev30.theta_loglin
