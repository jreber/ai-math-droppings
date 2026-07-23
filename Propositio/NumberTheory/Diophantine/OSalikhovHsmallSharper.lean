import Propositio.NumberTheory.Diophantine.OSalikhovHsmallSharp
import Propositio.NumberTheory.Diophantine.OSalikhovE2Sharper

/-!
# Sharpest `hsmall` assembly:  `ρ = C·(27/1000)`

Combines the exact integral identity `V = log2·E1 − log(3/2)·E2` (`V_eq_integral_combo`) with the
**sharper** integral decay `|E2 n| ≤ 5·(27/1000)ⁿ` (`E2_abs_le_sharper`) to get the tightest cleared
decay `|Den·V| ≤ 8D·(C·27/1000)ⁿ`.  With the sharp Apéry lcm bound `Den ≤ D·21ⁿ` (`C = 21`):
`ρ = 21·27/1000 ≈ 0.567`, `μ = 1 + logQ/log(1/ρ) ≈ 19 ≤ 22` — the prize's measure budget, reached
without any Poincaré–Perron input.  (Compare `form_decay_sharp`'s `ρ = C/32`, which with `C = 21`
gives `ρ ≈ 0.656`, `μ ≈ 25.6 > 22`.) -/

namespace OSalikhovTwoLog

open Real

/-- **Sharpest `hsmall` assembly.**  `|Den·V| ≤ 8D·(C·27/1000)ⁿ` from the decomposition, the lcm
bound `|Den| ≤ D·Cⁿ`, and the proven integral decays (with `E2` sharpened to `(27/1000)ⁿ`). -/
theorem form_decay_sharper (A1 A2 B Den : ℕ → ℝ) (D C : ℝ) (hD : 0 ≤ D) (hC : 1 ≤ C)
    (hDen : ∀ n, |Den n| ≤ D * C ^ n)
    (hdec1 : ∀ n, E1 n = A1 n + B n * Real.log (2 / 3))
    (hdec2 : ∀ n, E2 n = A2 n - B n * Real.log 2) :
    ∀ n, |Den n * ((A1 n + A2 n) * Real.log 2 - A2 n * Real.log 3)|
      ≤ (8 * D) * (C * (27 / 1000)) ^ n := by
  intro n
  rw [V_eq_integral_combo (A1 n) (A2 n) (B n) (E1 n) (E2 n) (hdec1 n) (hdec2 n)]
  have hlog2_le : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num); linarith
  have hlog32_le : Real.log (3 / 2) ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 3 / 2 by norm_num); linarith
  have hlog2_nn : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlog32_nn : 0 ≤ Real.log (3 / 2) := Real.log_nonneg (by norm_num)
  have hE1 : |E1 n| ≤ 3 * (27 / 1000) ^ n := by
    refine (E1_abs_le n).trans ?_
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by norm_num) (by norm_num) n) (by norm_num)
  have hE2 : |E2 n| ≤ 5 * (27 / 1000) ^ n := E2_abs_le_sharper n
  have hV : |Real.log 2 * E1 n - Real.log (3 / 2) * E2 n| ≤ 8 * (27 / 1000) ^ n := by
    calc |Real.log 2 * E1 n - Real.log (3 / 2) * E2 n|
        ≤ |Real.log 2 * E1 n| + |Real.log (3 / 2) * E2 n| := by
          rw [sub_eq_add_neg]; exact (abs_add_le _ _).trans (by rw [abs_neg])
      _ = Real.log 2 * |E1 n| + Real.log (3 / 2) * |E2 n| := by
          rw [abs_mul, abs_mul, abs_of_nonneg hlog2_nn, abs_of_nonneg hlog32_nn]
      _ ≤ 1 * (3 * (27 / 1000) ^ n) + 1 * (5 * (27 / 1000) ^ n) := by
          apply add_le_add
          · exact mul_le_mul hlog2_le hE1 (abs_nonneg _) (by norm_num)
          · exact mul_le_mul hlog32_le hE2 (abs_nonneg _) (by norm_num)
      _ = 8 * (27 / 1000) ^ n := by ring
  rw [abs_mul]
  calc |Den n| * |Real.log 2 * E1 n - Real.log (3 / 2) * E2 n|
      ≤ (D * C ^ n) * (8 * (27 / 1000) ^ n) :=
        mul_le_mul (hDen n) hV (abs_nonneg _) (by positivity)
    _ = (8 * D) * (C * (27 / 1000)) ^ n := by rw [mul_pow]; ring

end OSalikhovTwoLog
