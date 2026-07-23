import Propositio.NumberTheory.Collatz.Chebyshev30
import Mathlib.NumberTheory.Chebyshev

/-!
# Chebyshev-30: the telescoping step `θ(x) − θ(x/6) ≤ A·x ⟹ θ(x) ≤ (6A/5)·x`

This is the analytic backbone of the Chebyshev-30 primorial bound, with the hard input
(`stirling_M_bound`: `θ(x) − θ(x/6) ≤ A·x` for `A = log2/2 + log3/3 + log5/5 − log30/30 ≈ 0.921`)
isolated as a hypothesis `hstep`.  Telescoping the per-step inequality over the geometric ladder
`x, x/6, x/36, …` gives the global Chebyshev bound `θ(x) ≤ (6A/5)·x ≈ 1.106·x`, which beats
mathlib's `Chebyshev.theta_le_log4_mul_x` (`log 4 ≈ 1.386`).  Combined with
`Chebyshev.theta_eq_log_primorial`, this yields `primorial ⌊x⌋₊ ≤ exp((6A/5)·x)` — base
`e^{1.106} ≈ 3.02 < 3.5`, the bound the prize's `DenIntN` wall needs.

The remaining gap to discharge `hstep` (i.e. to make this unconditional) is `stirling_M_bound`,
queued; it needs an explicit log-factorial estimate.  The telescoping here is unconditional and
axiom-clean.
-/

namespace CollatzChebyshev30

open Chebyshev Real

/-- **Telescoping the Chebyshev-30 step.**  If `θ(x) − θ(x/6) ≤ A·x` for all `x ≥ 0` (with
`A ≥ 0`), then `θ(x) ≤ (6A/5)·x` for all `x ≥ 0`.  Proof: strong induction on `⌊x⌋₊`; for `x < 2`,
`θ x = 0`; for `x ≥ 2`, `⌊x/6⌋₊ < ⌊x⌋₊`, so `θ x ≤ θ(x/6) + A·x ≤ (6A/5)(x/6) + A·x = (6A/5)x`. -/
theorem theta_le_of_step (A : ℝ) (hA : 0 ≤ A)
    (hstep : ∀ x : ℝ, 0 ≤ x → θ x - θ (x / 6) ≤ A * x) :
    ∀ x : ℝ, 0 ≤ x → θ x ≤ (6 * A / 5) * x := by
  have key : ∀ n : ℕ, ∀ x : ℝ, 0 ≤ x → ⌊x⌋₊ ≤ n → θ x ≤ (6 * A / 5) * x := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro x hx hxn
      rcases lt_or_ge x 2 with hlt | hge
      · rw [theta_eq_zero_of_lt_two hlt]
        exact mul_nonneg (by linarith) hx
      · have hx6 : (0 : ℝ) ≤ x / 6 := by linarith
        have hfloor6 : ⌊x / 6⌋₊ < ⌊x⌋₊ := by
          rw [Nat.floor_lt hx6]
          have h1 : x - 1 < (⌊x⌋₊ : ℝ) := by
            have := Nat.lt_floor_add_one x; linarith
          have h2 : x / 6 ≤ x - 1 := by linarith
          linarith
        have hlt_n : ⌊x / 6⌋₊ < n := lt_of_lt_of_le hfloor6 hxn
        have hih := ih ⌊x / 6⌋₊ hlt_n (x / 6) hx6 (le_refl _)
        have hs := hstep x hx
        calc θ x ≤ θ (x / 6) + A * x := by linarith
          _ ≤ (6 * A / 5) * (x / 6) + A * x := by linarith
          _ = (6 * A / 5) * x := by ring
  intro x hx
  exact key ⌊x⌋₊ x hx (le_refl _)

/-- **Chebyshev-30 primorial bound, conditional on `hstep`.**  From the per-step factorial bound,
`primorial ⌊x⌋₊ ≤ exp((6A/5)·x)`.  With `A ≈ 0.921` this is base `e^{1.106} ≈ 3.02`. -/
theorem primorial_le_exp_of_step (A : ℝ) (hA : 0 ≤ A)
    (hstep : ∀ x : ℝ, 0 ≤ x → θ x - θ (x / 6) ≤ A * x) (x : ℝ) (hx : 0 ≤ x) :
    (primorial ⌊x⌋₊ : ℝ) ≤ Real.exp ((6 * A / 5) * x) := by
  have hθ : θ x ≤ (6 * A / 5) * x := theta_le_of_step A hA hstep x hx
  have hlog : Real.log (primorial ⌊x⌋₊) ≤ (6 * A / 5) * x := by
    rw [← theta_eq_log_primorial]; exact hθ
  have hpos : (0 : ℝ) < (primorial ⌊x⌋₊ : ℝ) := by
    exact_mod_cast (primorial_pos ⌊x⌋₊)
  calc (primorial ⌊x⌋₊ : ℝ) = Real.exp (Real.log (primorial ⌊x⌋₊)) := (Real.exp_log hpos).symm
    _ ≤ Real.exp ((6 * A / 5) * x) := Real.exp_le_exp.mpr hlog

end CollatzChebyshev30
