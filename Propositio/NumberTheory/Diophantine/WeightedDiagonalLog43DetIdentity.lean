import Propositio.NumberTheory.Diophantine.DiagonalIntegralLog2Delannoy
import Propositio.NumberTheory.Diophantine.DiagonalIntegralLog2IntegralRec
import Propositio.NumberTheory.Diophantine.DiagonalIntegralLog2Measure
import Propositio.NumberTheory.Diophantine.WeightedDiagonalLog43Star
import Propositio.NumberTheory.Diophantine.PadeCasoratian
import Mathlib.Tactic

/-!
# The `{I, J}` one-height determinant identity `det₃[Iₙ; Jₙ; Iₙ₊₁] = 2·aRes(n,1)/(n+1)`

The two single-log diagonal families combine into a `3 × 3` system in the basis `(1, log2, log3)`:

* `Iₙ = ∫₁² ((t−1)(2−t))ⁿ/tⁿ⁺¹ = rₙ + cₙ·log2`  (`DiagonalIntegralLog2`, direction `(1,0)`),
  real row `(rₙ, cₙ, 0)` with `cₙ = intCoeff n n`;
* `Jₙ = ∫₀¹ xⁿ(1−x)ⁿ/((1+x)(2+x))ⁿ⁺¹ = Pₙ + aRes(n,1)·log(4/3)` (`WeightedDiagonalLog43`,
  `log(4/3) = 2log2 − log3`), real row `(Pₙ, 2·aRes(n,1), −aRes(n,1))`.

The consecutive `3 × 3` determinant of `Iₙ, Jₙ, Iₙ₊₁` is the **one-height** (Apéry-small) value
`2·aRes(n,1)/(n+1)`: expanding along the third column collapses it to `aRes(n,1)·(rₙcₙ₊₁ − cₙrₙ₊₁)`,
and the `I`-family Casoratian `rₙcₙ₊₁ − cₙrₙ₊₁ = −W(c,r)(n)` telescopes to `2/(n+1)` (its `W₀ = −2`).

## Status (2026-06-23)

This determinant is `≠ 0`, so it discharges the `hdet` input of the 3-D engine — i.e. it certifies
the **qualitative** linear independence of `{1, log2, log3}` (Nesterenko's criterion: forms `→ 0` +
consecutive dets `≠ 0`).  It does **NOT** yield an effective measure of `log₂3` via
`LinIndepMeasure3DMain.linindep_measure_3d_of_budget`: the budget fan-out (2026-06-23) showed the
additive budget term `|cof₁||Lₐ| + |cof₂|·|L_b|` diverges after the mandatory lcm-clearing of the
integer rows (`Dₘ² ~ e^{2m}`), independently of this determinant's smallness (which only bounds the
*leading cofactor*, hypothesis (iii), not the budget (ii)).  See `failed-attempts.json`
("twolog_prize_budget via {I,J}").  This file records the true, reusable identity.
-/

namespace WeightedDiagonalLog43DetIdentity

open DiagonalIntegralLog2

/-- The `I`-family Casoratian base value `W₀ = c₀·r₁ − c₁·r₀ = 1·(−2) − 3·0 = −2`. -/
theorem casoratian_I_zero :
    PadeCasoratian.W (fun m => (intCoeff m m : ℝ)) r 0 = -2 := by
  simp only [PadeCasoratian.W]
  rw [show (0 : ℕ) + 1 = 1 from rfl, r_zero, r_one, intCoeff_zero_zero, intCoeff_one_one]
  norm_num

/-- **The `I`-family Casoratian closed form** `cₙ·rₙ₊₁ − cₙ₊₁·rₙ = −2/(n+1)`, hence
`rₙ·cₙ₊₁ − cₙ·rₙ₊₁ = 2/(n+1)`.  Both `c = intCoeff··` and `r` obey the same Padé (`k = 3`) recurrence,
so `PadeCasoratian.casoratian_eq_div` telescopes `Wₙ = W₀/(n+1)`. -/
theorem casoratian_I_value (n : ℕ) :
    (r n) * (intCoeff (n + 1) (n + 1) : ℝ) - (intCoeff n n : ℝ) * (r (n + 1))
      = 2 / ((n : ℝ) + 1) := by
  have hWn := PadeCasoratian.casoratian_eq_div (fun m => (intCoeff m m : ℝ)) r
      intCoeff_diag_recurrence r_recurrence n
  rw [casoratian_I_zero] at hWn
  simp only [PadeCasoratian.W] at hWn
  linear_combination -hWn

/-- **The one-height determinant identity** `det₃[Iₙ; Jₙ; Iₙ₊₁] = 2·aRes(n,1)/(n+1)`.

The `3 × 3` determinant is written in the explicit cofactor form consumed by
`LinIndepMeasure3D.det_pair_lower_bound`/`linform3_det_atom` (rows
`Iₙ = (rₙ, cₙ, 0)`, `Jₙ = (Pₙ, 2a, −a)`, `Iₙ₊₁ = (rₙ₊₁, cₙ₊₁, 0)` with `a = aRes(n,1)`,
`c = intCoeff··`).  Column-3 expansion (`ring`) gives `a·(rₙcₙ₊₁ − cₙrₙ₊₁)`, which is
`a·2/(n+1)` by `casoratian_I_value`. -/
theorem detIJI_eq (n : ℕ) :
    (r n) * ((2 * (WeightedDiagonalLog43.aRes n 1 : ℝ)) * 0
          - (-(WeightedDiagonalLog43.aRes n 1 : ℝ)) * (intCoeff (n + 1) (n + 1) : ℝ))
      - (intCoeff n n : ℝ) * ((WeightedDiagonalLog43.Pexpl n : ℝ) * 0
          - (-(WeightedDiagonalLog43.aRes n 1 : ℝ)) * (r (n + 1)))
      + (0 : ℝ) * ((WeightedDiagonalLog43.Pexpl n : ℝ) * (intCoeff (n + 1) (n + 1) : ℝ)
          - (2 * (WeightedDiagonalLog43.aRes n 1 : ℝ)) * (r (n + 1)))
      = 2 * (WeightedDiagonalLog43.aRes n 1 : ℝ) / ((n : ℝ) + 1) := by
  have hexp :
      (r n) * ((2 * (WeightedDiagonalLog43.aRes n 1 : ℝ)) * 0
            - (-(WeightedDiagonalLog43.aRes n 1 : ℝ)) * (intCoeff (n + 1) (n + 1) : ℝ))
        - (intCoeff n n : ℝ) * ((WeightedDiagonalLog43.Pexpl n : ℝ) * 0
            - (-(WeightedDiagonalLog43.aRes n 1 : ℝ)) * (r (n + 1)))
        + (0 : ℝ) * ((WeightedDiagonalLog43.Pexpl n : ℝ) * (intCoeff (n + 1) (n + 1) : ℝ)
            - (2 * (WeightedDiagonalLog43.aRes n 1 : ℝ)) * (r (n + 1)))
      = (WeightedDiagonalLog43.aRes n 1 : ℝ)
          * ((r n) * (intCoeff (n + 1) (n + 1) : ℝ) - (intCoeff n n : ℝ) * (r (n + 1))) := by
    ring
  rw [hexp, casoratian_I_value n]; ring

end WeightedDiagonalLog43DetIdentity
