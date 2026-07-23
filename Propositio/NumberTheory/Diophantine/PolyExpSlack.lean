import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

/-!
# Polynomial-vs-exponential slack for an **arbitrary** real exponent

`CollatzPowGapBaker` hardcodes the exponent `14` (`poly14_le_two_pow : a^14 ≤ 2^a` for `a ≥ 100`),
matching `μ(log₂3) ≤ 13.3 < 14`.  But the cleanest formalizable construction for `μ(log₂3)` (the
Zeilberger–Zudilin `oSALIKHOV` system, `conj-2026-06-23-R04`) gives `ν ≤ 20.02 > 14`.  To let *any*
explicit finite measure exponent close the Collatz `PowGap`, we need the slack `a^μ ≤ 2^a` for
**every** real `μ` (eventually).

This file proves exactly that, cleanly, from mathlib's asymptotics
(`Asymptotics.isLittleO_rpow_exp_pos_mul_atTop`: `xˢ = o(exp(b·x))` for `b > 0`) — no `native_decide`,
no concrete base case.  It is the analytic ingredient for a future
`powGap_of_irrMeasure`-with-arbitrary-`μ` generalization (`conj-2026-06-23-R04`, action 1).
-/

namespace PolyExpSlack

open Filter Asymptotics

/-- **General polynomial-vs-exponential slack.**  For every real `μ` there is a threshold `a₀` with
`(a : ℝ)^μ ≤ 2^a` for all `a ≥ a₀`.  Proof: `xᵘ = o(exp(log 2 · x))` (`= o(2^x)`) at `+∞`, so
eventually `‖xᵘ‖ ≤ ‖2^x‖`; specialize to natural `a ≥ ⌈threshold⌉`. -/
theorem exists_rpow_le_two_pow (μ : ℝ) :
    ∃ a0 : ℕ, ∀ a : ℕ, a0 ≤ a → (a : ℝ) ^ μ ≤ (2 : ℝ) ^ a := by
  have hb : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlo := isLittleO_rpow_exp_pos_mul_atTop μ hb
  have hev := hlo.def (by norm_num : (0 : ℝ) < 1)
  rw [Filter.eventually_atTop] at hev
  obtain ⟨X, hX⟩ := hev
  refine ⟨Nat.ceil X + 1, fun a ha => ?_⟩
  have haX : X ≤ (a : ℝ) := by
    have h1 : X ≤ (Nat.ceil X : ℝ) := Nat.le_ceil X
    have h2 : (Nat.ceil X : ℝ) ≤ (a : ℝ) := by exact_mod_cast (by omega : Nat.ceil X ≤ a)
    linarith
  have hapos : (0 : ℝ) < (a : ℝ) := by exact_mod_cast (by omega : 0 < a)
  have hbnd := hX (a : ℝ) haX
  rw [one_mul] at hbnd
  have hn1 : ‖(a : ℝ) ^ μ‖ = (a : ℝ) ^ μ := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hapos μ)]
  have hn2 : ‖Real.exp (Real.log 2 * (a : ℝ))‖ = (2 : ℝ) ^ a := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
      ← Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2) (a : ℝ), Real.rpow_natCast]
  rw [hn1, hn2] at hbnd
  exact hbnd

end PolyExpSlack
