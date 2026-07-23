import Propositio.NumberTheory.Diophantine.DiagonalIntegralLog2IntForm
import Propositio.NumberTheory.Diophantine.DiagonalIntegralLog2Tendsto
import Mathlib.Tactic

/-!
# `log 2` is irrational, via the diagonal Legendre integral

The diagonal construction yields the integer linear form `Dₙ·Iₙ = aₙ·log 2 + uₙ`
(`D_mul_I_int_form`, `aₙ = Dₙ·cₙ`, `uₙ ∈ ℤ`) with `Dₙ = lcmUpto n`.  Two analytic facts finish
irrationality:

* `D_mul_I_pos`     — `0 < Dₙ·Iₙ`  (the form is a *nonzero* integer combination of `1, log 2`);
* `D_mul_I_tendsto_zero` — `Dₙ·Iₙ → 0`.

The size estimate `Dₙ·Iₙ ≤ Dₙ·(3−2√2)ⁿ·log 2` (`I_le`) together with the sharp Chebyshev bound
`log Dₙ = ψ(n) ≤ log 4·n + 2√n·log n` (`LcmGrowthBound.log_lcmUpto_eq_psi`, `Chebyshev.psi_le`)
gives `log(Dₙ·(3−2√2)ⁿ) ≤ (log 4 + log(3−2√2))·n + 2√n·log n`, whose leading constant
`log(4·(3−2√2)) = log 0.686… < 0` drives the whole thing to `−∞`, hence `Dₙ·Iₙ → 0`.

If `log 2 = a/b` were rational then `Dₙ·Iₙ = (aₙa + b·uₙ)/b` is a positive multiple of `1/b`, so
`≥ 1/b` — contradicting `Dₙ·Iₙ → 0`.
-/

namespace DiagonalIntegralLog2

open Polynomial LcmGrowthBound Filter Real

/-- `0 < Dₙ·Iₙ` : the integer linear form is strictly positive. -/
theorem D_mul_I_pos (n : ℕ) : 0 < (lcmUpto n : ℝ) * I n := by
  apply mul_pos
  · exact_mod_cast Nat.pos_of_ne_zero (lcmUpto_ne_zero n)
  · exact I_pos n

/-- `Dₙ·Iₙ ≤ Dₙ·(3−2√2)ⁿ·log 2` : the geometric size estimate, from `I_le`. -/
theorem D_mul_I_le_geom (n : ℕ) :
    (lcmUpto n : ℝ) * I n ≤ (lcmUpto n : ℝ) * ((3 - 2 * Real.sqrt 2) ^ n * Real.log 2) := by
  apply mul_le_mul_of_nonneg_left (I_le n)
  positivity

/-- **`Dₙ·Iₙ → 0`** : the integer linear form is a null sequence.  Squeeze between `0` and
`Dₙ·(3−2√2)ⁿ·log 2`, the latter `→ 0` by `geom_lcm_tendsto_zero`. -/
theorem D_mul_I_tendsto_zero :
    Tendsto (fun n => (lcmUpto n : ℝ) * I n) atTop (nhds 0) := by
  have hgeom : Tendsto
      (fun n : ℕ => (lcmUpto n : ℝ) * (3 - 2 * Real.sqrt 2) ^ n * Real.log 2) atTop (nhds 0) := by
    have h := geom_lcm_tendsto_zero.mul_const (Real.log 2)
    simpa using h
  refine squeeze_zero (fun n => le_of_lt (D_mul_I_pos n)) (fun n => ?_) hgeom
  have h := D_mul_I_le_geom n
  rwa [← mul_assoc] at h

/-- **`log 2` is irrational.**  If `log 2 = a/b` then `Dₙ·Iₙ = (aₙa + b·uₙ)/b ≥ 1/b` (a positive
integer over `b`), contradicting `Dₙ·Iₙ → 0`.  Built entirely from the diagonal Legendre integral:
positivity (`I_pos`), the integer linear form (`D_mul_I_int_form`, resting on the 2-adic miracle and
`lcm`-clearing), and the size estimate (`I_le` + sharp Chebyshev bound). -/
theorem log_two_irrational : Irrational (Real.log 2) := by
  rintro ⟨q, hq⟩
  -- `hq : (q : ℝ) = Real.log 2`.  Set `a = q.num`, `b = q.den > 0`, so `log 2 = a / b`.
  set b : ℤ := (q.den : ℤ) with hb
  have hbpos : (0 : ℝ) < (b : ℝ) := by rw [hb]; exact_mod_cast q.pos
  have hbne : (b : ℝ) ≠ 0 := ne_of_gt hbpos
  have hlog : Real.log 2 = (q.num : ℝ) / (b : ℝ) := by
    rw [← hq, Rat.cast_def, hb]; push_cast; ring
  -- per `n`, `Dₙ·Iₙ ≥ 1/b`
  have hge : ∀ n : ℕ, (1 : ℝ) / (b : ℝ) ≤ (lcmUpto n : ℝ) * I n := by
    intro n
    obtain ⟨u, hu⟩ := D_mul_I_int_form n
    -- N := aₙ·q.num + b·u  is a positive integer with Dₙ·Iₙ = N / b
    set A : ℤ := (lcmUpto n : ℤ) * intCoeff n n with hA
    set N : ℤ := A * q.num + b * u with hN
    have hval : (lcmUpto n : ℝ) * I n = (N : ℝ) / (b : ℝ) := by
      rw [hu, hlog, hN, hA]; push_cast; field_simp
    have hNeq : (N : ℝ) = ((lcmUpto n : ℝ) * I n) * (b : ℝ) := by
      rw [hval]; field_simp
    have hNposR : (0 : ℝ) < (N : ℝ) := by
      rw [hNeq]; exact mul_pos (D_mul_I_pos n) hbpos
    have hN1 : (1 : ℝ) ≤ (N : ℝ) := by
      have hNposZ : (0 : ℤ) < N := by exact_mod_cast hNposR
      exact_mod_cast (by omega : (1 : ℤ) ≤ N)
    rw [div_le_iff₀ hbpos, ← hNeq]
    exact hN1
  -- but `Dₙ·Iₙ → 0`, so eventually `< 1/b` — contradiction
  have hb0 : (0 : ℝ) < (1 : ℝ) / (b : ℝ) := by positivity
  obtain ⟨n, hn⟩ := (D_mul_I_tendsto_zero.eventually_lt_const hb0).exists
  exact absurd (hge n) (not_le.mpr hn)

end DiagonalIntegralLog2
