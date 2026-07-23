import Propositio.NumberTheory.Collatz.Chebyshev30MSize
import Propositio.NumberTheory.Collatz.Chebyshev30ThetaLower
import Propositio.NumberTheory.Collatz.Chebyshev30Theta
import Mathlib.NumberTheory.Chebyshev

/-!
# Chebyshev-30: the *tight* Chebyshev upper bound on `θ`

This is the analytic half of the prize `Den` wall.  Combining the lower input
`theta_sub_le_logM` with the explicit size estimate `logM_le_linear` gives the
real-variable per-step inequality `θ(x) − θ(x/6) ≤ A·x + 4·log x + 4` for `x ≥ 30`
(`hstep_real`).  Absorbing the logarithmic tail into a `x/30` slack (`log_absorb`)
upgrades this to a clean linear step `θ(x) − θ(x/6) ≤ (A + 1/30)·x` for `x ≥ 57600`,
which telescopes (`theta_le_of_step_above`) to the global tight bound

  `θ(x) ≤ (6(A + 1/30)/5)·x + θ(57600)`,

with `A = Aentropy ≈ 0.921`, i.e. base `e^{6·0.9543/5} ≈ e^{1.145}` after the slack.
-/

namespace CollatzChebyshev30

open Chebyshev Real

/-- **(L0)** `Aentropy ≥ 0`. -/
theorem Aentropy_nonneg : 0 ≤ Aentropy := by
  have h30 : Real.log 30 = Real.log 2 + Real.log 3 + Real.log 5 := by
    rw [show (30:ℝ) = 2*3*5 by norm_num, Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num)]
  have hsplit : Aentropy = 7/15 * Real.log 2 + 3/10 * Real.log 3 + 1/6 * Real.log 5 := by
    unfold Aentropy; rw [h30]; ring
  rw [hsplit]
  linarith [Real.log_nonneg (show (1:ℝ) ≤ 2 by norm_num),
    Real.log_nonneg (show (1:ℝ) ≤ 3 by norm_num),
    Real.log_nonneg (show (1:ℝ) ≤ 5 by norm_num)]

/-- **(L1)** `θ` only depends on `⌊x⌋₊`. -/
theorem theta_floor (x : ℝ) : θ x = θ (⌊x⌋₊ : ℝ) := by
  simp only [Chebyshev.theta, Nat.floor_natCast]

/-- **(L2)** Real-variable per-step bound for `x ≥ 30`. -/
theorem hstep_real (x : ℝ) (hx : 30 ≤ x) :
    θ x - θ (x / 6) ≤ Aentropy * x + 4 * Real.log x + 4 := by
  have hxpos : (0:ℝ) ≤ x := by linarith
  have hN30 : 30 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx)
  have hNpos : (0:ℝ) < (⌊x⌋₊ : ℝ) := by
    have : (0:ℕ) < ⌊x⌋₊ := by omega
    exact_mod_cast this
  have hfloor_le : ((⌊x⌋₊ : ℕ) : ℝ) ≤ x := Nat.floor_le hxpos
  have h6 : ⌊x/6⌋₊ = ⌊x⌋₊ / 6 := by
    rw [show (6:ℝ) = ((6:ℕ):ℝ) by norm_num]; exact Nat.floor_div_natCast x 6
  -- rewrite θ at x and x/6 to nat arguments
  have hθx : θ x = θ ((⌊x⌋₊ : ℕ) : ℝ) := theta_floor x
  have hθx6 : θ (x/6) = θ ((⌊x⌋₊ / 6 : ℕ) : ℝ) := by
    rw [theta_floor (x/6), h6]
  have hlow : θ x - θ (x/6) ≤ Real.log (M ⌊x⌋₊) := by
    rw [hθx, hθx6]; exact theta_sub_le_logM ⌊x⌋₊
  have hsize : Real.log (M ⌊x⌋₊) ≤ Aentropy * ⌊x⌋₊ + 4 * Real.log ⌊x⌋₊ + 4 :=
    logM_le_linear ⌊x⌋₊ hN30
  have hlogle : Real.log (⌊x⌋₊ : ℝ) ≤ Real.log x :=
    Real.log_le_log hNpos hfloor_le
  nlinarith [hlow, hsize, hlogle, Aentropy_nonneg, hfloor_le]

/-- **(L3)** The logarithmic tail is absorbed by an `x/30` slack for `x ≥ 57600`. -/
theorem log_absorb (x : ℝ) (hx : 57600 ≤ x) : 4 * Real.log x + 4 ≤ x / 30 := by
  have hxpos : 0 < x := by linarith
  have hlog : Real.log (Real.sqrt x) ≤ Real.sqrt x - 1 :=
    Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hxpos)
  have heq : Real.log x = 2 * Real.log (Real.sqrt x) := by
    rw [Real.log_sqrt (le_of_lt hxpos)]; ring
  have hsqrt : Real.log x ≤ 2 * Real.sqrt x - 2 := by linarith [heq, hlog]
  have hu : (240:ℝ) ≤ Real.sqrt x := by
    rw [Real.le_sqrt (by norm_num) (by linarith)]; nlinarith [hx]
  have hsq : Real.sqrt x ^ 2 = x := Real.sq_sqrt (le_of_lt hxpos)
  nlinarith [hsqrt, hu, hsq]

/-- **(L4)** Telescoping a step valid only above a threshold `x₀ ≥ 2`. -/
theorem theta_le_of_step_above (A x₀ : ℝ) (hA : 0 ≤ A) (hx0 : 2 ≤ x₀)
    (hstep : ∀ x, x₀ ≤ x → θ x - θ (x / 6) ≤ A * x) :
    ∀ x, 0 ≤ x → θ x ≤ (6 * A / 5) * x + θ x₀ := by
  have key : ∀ n : ℕ, ∀ x : ℝ, 0 ≤ x → ⌊x⌋₊ ≤ n → θ x ≤ (6 * A / 5) * x + θ x₀ := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro x hx hxn
      rcases lt_or_ge x x₀ with hlt | hge
      · have hmono : θ x ≤ θ x₀ := theta_mono (le_of_lt hlt)
        have hnn : 0 ≤ (6 * A / 5) * x := mul_nonneg (by linarith) hx
        linarith
      · have hx6 : (0 : ℝ) ≤ x / 6 := by linarith
        have hx2 : (2:ℝ) ≤ x := le_trans hx0 hge
        have hfloor6 : ⌊x / 6⌋₊ < ⌊x⌋₊ := by
          rw [Nat.floor_lt hx6]
          have h1 : x - 1 < (⌊x⌋₊ : ℝ) := by
            have := Nat.lt_floor_add_one x; linarith
          have h2 : x / 6 ≤ x - 1 := by linarith
          linarith
        have hlt_n : ⌊x / 6⌋₊ < n := lt_of_lt_of_le hfloor6 hxn
        have hih := ih ⌊x / 6⌋₊ hlt_n (x / 6) hx6 (le_refl _)
        have hs := hstep x hge
        calc θ x ≤ θ (x / 6) + A * x := by linarith
          _ ≤ ((6 * A / 5) * (x / 6) + θ x₀) + A * x := by linarith
          _ = (6 * A / 5) * x + θ x₀ := by ring
  intro x hx
  exact key ⌊x⌋₊ x hx (le_refl _)

/-- **(L5) Main: tight Chebyshev upper bound on `θ`.** -/
theorem theta_tight (x : ℝ) (hx : 0 ≤ x) :
    θ x ≤ (6 * (Aentropy + 1/30) / 5) * x + θ 57600 := by
  refine theta_le_of_step_above (Aentropy + 1/30) 57600
    (by linarith [Aentropy_nonneg]) (by norm_num) ?_ x hx
  intro y hy
  have h1 := hstep_real y (by linarith)
  have h2 := log_absorb y hy
  nlinarith [h1, h2]

end CollatzChebyshev30
