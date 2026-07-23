import Mathlib.NumberTheory.ZetaValues
import Mathlib.Analysis.PSeries
import Mathlib.Tactic

/-!
# Odd-index Basel value

`Σ_{k} 1/(2k+1)² = π²/8`.

Mathlib provides `hasSum_zeta_two : HasSum (fun n => 1/(n:ℝ)^2) (π²/6)`.
We split `ℕ` into even and odd indices (`HasSum.even_add_odd`):
* the even part `Σ_k 1/(2k)² = (1/4)·Σ_k 1/k² = π²/24`,
* the odd part is then `π²/6 − π²/24 = π²/8`.
-/

open Real

/-- The even-index part of `ζ(2)`: `Σ_k 1/(2k)² = π²/24`. -/
theorem hasSum_inv_even_sq :
    HasSum (fun k : ℕ => (1 : ℝ) / ((2 * k : ℕ) : ℝ) ^ 2) (Real.pi ^ 2 / 24) := by
  have h := hasSum_zeta_two.mul_left ((1 : ℝ) / 4)
  rw [show (1 : ℝ) / 4 * (Real.pi ^ 2 / 6) = Real.pi ^ 2 / 24 by ring] at h
  exact h.congr_fun fun k => by push_cast; ring

/-- The odd-index Basel value: `Σ_k 1/(2k+1)² = π²/8`. -/
theorem hasSum_inv_odd_sq :
    HasSum (fun k : ℕ => (1 : ℝ) / ((2 * k + 1 : ℕ) : ℝ) ^ 2) (Real.pi ^ 2 / 8) := by
  -- Work with `F n = 1/n²` so the even/odd split is a first-order match for
  -- `HasSum.even_add_odd` (the lambdas are literally `fun k => F (2*k)` etc.).
  set F : ℕ → ℝ := fun n => (1 : ℝ) / (n : ℝ) ^ 2 with hF
  have hz : HasSum F (Real.pi ^ 2 / 6) := by rw [hF]; exact hasSum_zeta_two
  -- even part: Σ_k F(2k) = π²/24
  have heven : HasSum (fun k : ℕ => F (2 * k)) (Real.pi ^ 2 / 24) := by
    rw [hF]
    have h := hasSum_zeta_two.mul_left ((1 : ℝ) / 4)
    rw [show (1 : ℝ) / 4 * (Real.pi ^ 2 / 6) = Real.pi ^ 2 / 24 by ring] at h
    exact h.congr_fun fun k => by push_cast; ring
  -- odd subsequence is summable (reindex of the summable ζ(2) series)
  have hoddInj : Function.Injective (fun k : ℕ => 2 * k + 1) := by
    intro a b hab
    simpa using hab
  have hoSummable : Summable (fun k : ℕ => F (2 * k + 1)) :=
    hz.summable.comp_injective hoddInj
  have ho : HasSum (fun k : ℕ => F (2 * k + 1)) (∑' k, F (2 * k + 1)) := hoSummable.hasSum
  -- even + odd = total = π²/6
  have htot : HasSum F (Real.pi ^ 2 / 24 + ∑' k, F (2 * k + 1)) := heven.even_add_odd ho
  have heq : Real.pi ^ 2 / 24 + (∑' k, F (2 * k + 1)) = Real.pi ^ 2 / 6 := htot.unique hz
  have hval : (∑' k, F (2 * k + 1)) = Real.pi ^ 2 / 8 := by linarith
  rw [hval] at ho
  exact ho.congr_fun fun k => by rw [hF]

/-- `tsum` corollary. -/
theorem tsum_inv_odd_sq :
    ∑' k : ℕ, (1 : ℝ) / ((2 * k + 1 : ℕ) : ℝ) ^ 2 = Real.pi ^ 2 / 8 :=
  hasSum_inv_odd_sq.tsum_eq
