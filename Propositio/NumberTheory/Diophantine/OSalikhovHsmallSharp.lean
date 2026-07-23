import Propositio.NumberTheory.Diophantine.OSalikhovDecomp

/-!
# `hsmall` is NOT Poincaré–Perron-gated — the cleared form is an exact integral combination

The cleared two-log form `V = (A1+A2)·log2 − A2·log3` admits an **exact elementary identity** once the
decomposition `E1 = A1 + B·log(2/3)`, `E2 = A2 − B·log2` is in hand:

`V = log2·E1 − log(3/2)·E2`

(the `B`-terms cancel because `log(2/3) + log(3/2) = 0`).  So `V` is a *fixed* linear combination of the
two integrals — its decay is inherited DIRECTLY from the proven integral bounds `|E1 n| ≤ 3(1/100)ⁿ`,
`|E2 n| ≤ 5(1/32)ⁿ` (`OSalikhovDecomp`), with NO growth bound on `A1,A2`, NO lower bound on `B`, and NO
dominant-root asymptotics.  An adversarial-recon pass had declared `hsmall` blocked on a
Poincaré–Perron "common-rate" fact; this identity **refutes** that — the only genuinely remaining
`hsmall` ingredient is the lcm bound `Den ≤ D·Cⁿ` (Apéry/Beukers, Phase-2-gated).

This gives the sharp assembly `Den·|V| ≤ 8D·(C/32)ⁿ` (`ρ = C/32`, with `C ≈ 23` the measured Den
rate ⇒ `ρ ≈ 0.72 < 1`), far cleaner than `OSalikhovHsmall.form_decay_of_decomp`'s crude
`ρ = 315/352 ≈ 0.895` (which needed the separate `|A1|,|A2| ≤ 1500ⁿ`, `|B| ≥ 1100ⁿ` bounds). -/

namespace OSalikhovTwoLog

open Real

/-- **The cleared two-log form is an exact integral combination.**  `V = log2·E1 − log(3/2)·E2`. -/
theorem V_eq_integral_combo (A1 A2 B e1 e2 : ℝ)
    (hE1 : e1 = A1 + B * Real.log (2 / 3)) (hE2 : e2 = A2 - B * Real.log 2) :
    (A1 + A2) * Real.log 2 - A2 * Real.log 3
      = Real.log 2 * e1 - Real.log (3 / 2) * e2 := by
  rw [hE1, hE2, Real.log_div (by norm_num) (by norm_num),
    Real.log_div (by norm_num) (by norm_num)]
  ring

/-- `log 2 ≤ 1` and `log (3/2) ≤ 1`, both nonneg (used to fold the integral constants). -/
private theorem log_two_le_one : Real.log 2 ≤ 1 := by
  have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num); linarith
private theorem log_threehalf_le_one : Real.log (3 / 2) ≤ 1 := by
  have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 3 / 2 by norm_num); linarith
private theorem log_two_nonneg : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
private theorem log_threehalf_nonneg : 0 ≤ Real.log (3 / 2) := Real.log_nonneg (by norm_num)

/-- **Sharp `hsmall` assembly via the integral identity.**  Given the decomposition forms and the
lcm bound `|Den| ≤ D·Cⁿ` (`1 ≤ C`), the cleared two-log form decays at `ρ = C/32`:
`|Den·V| ≤ 8D·(C/32)ⁿ`.  No growth/lower bounds on `A1,A2,B` — only the proven integral decays. -/
theorem form_decay_sharp (A1 A2 B Den : ℕ → ℝ) (D C : ℝ) (hD : 0 ≤ D) (hC : 1 ≤ C)
    (hDen : ∀ n, |Den n| ≤ D * C ^ n)
    (hdec1 : ∀ n, E1 n = A1 n + B n * Real.log (2 / 3))
    (hdec2 : ∀ n, E2 n = A2 n - B n * Real.log 2) :
    ∀ n, |Den n * ((A1 n + A2 n) * Real.log 2 - A2 n * Real.log 3)| ≤ (8 * D) * (C / 32) ^ n := by
  intro n
  rw [V_eq_integral_combo (A1 n) (A2 n) (B n) (E1 n) (E2 n) (hdec1 n) (hdec2 n)]
  -- |V| ≤ 8·(1/32)ⁿ
  have hE1 : |E1 n| ≤ 3 * (1 / 32) ^ n := by
    refine (E1_abs_le n).trans ?_; gcongr; norm_num
  have hE2 : |E2 n| ≤ 5 * (1 / 32) ^ n := E2_abs_le_sharp n
  have hpow : (0 : ℝ) ≤ (1 / 32 : ℝ) ^ n := by positivity
  have hV : |Real.log 2 * E1 n - Real.log (3 / 2) * E2 n| ≤ 8 * (1 / 32) ^ n := by
    calc |Real.log 2 * E1 n - Real.log (3 / 2) * E2 n|
        ≤ |Real.log 2 * E1 n| + |Real.log (3 / 2) * E2 n| := by
          rw [sub_eq_add_neg]; exact (abs_add_le _ _).trans (by rw [abs_neg])
      _ = Real.log 2 * |E1 n| + Real.log (3 / 2) * |E2 n| := by
          rw [abs_mul, abs_mul, abs_of_nonneg log_two_nonneg, abs_of_nonneg log_threehalf_nonneg]
      _ ≤ 1 * (3 * (1 / 32) ^ n) + 1 * (5 * (1 / 32) ^ n) := by
          gcongr
          · exact log_two_le_one
          · exact log_threehalf_le_one
      _ = 8 * (1 / 32) ^ n := by ring
  -- assemble with the Den bound
  rw [abs_mul]
  calc |Den n| * |Real.log 2 * E1 n - Real.log (3 / 2) * E2 n|
      ≤ (D * C ^ n) * (8 * (1 / 32) ^ n) :=
        mul_le_mul (hDen n) hV (abs_nonneg _) (by positivity)
    _ = (8 * D) * (C / 32) ^ n := by
        rw [show (C / 32 : ℝ) = C * (1 / 32) by ring, mul_pow]; ring

end OSalikhovTwoLog
