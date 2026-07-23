/-
# Monsky dichromatic-line lemma

Monsky's theorem 3-colours the plane `ℚ × ℚ` using the 2-adic valuation
`v q = padicValRat 2 q` (mathlib convention `padicValRat 2 0 = 0`), exactly as
set up in `MonskyRainbowDeterminant.lean`:

* colour 0 : `0 ≤ v x` and `0 ≤ v y`
* colour 1 : `v x < 0` and `v x ≤ v y`
* colour 2 : `v y < 0` and `v y < v x`

The combinatorial hypothesis feeding Sperner's lemma in Monsky's proof is that
**no line meets all three colour classes** ("no dichromatic/rainbow line").
This file derives that fact as a direct corollary of the rainbow-triangle
determinant lemma `MonskyRainbow.rainbow_det_valuation`: three points of the
three respective colours are never collinear (their signed-area determinant
is provably nonzero), so in particular they cannot all lie on a common line
`a·x + b·y = c`.

Main result: `MonskyDichromaticLine.no_dichromatic_line`.

The only new mathematics here is the elementary linear-algebra fact that three
points on a common line have vanishing signed-area determinant (`ring`/
`linear_combination` from the two line equations); the hard 2-adic content is
entirely reused from `MonskyRainbowDeterminant`.
-/
import Propositio.Geometry.Monsky.MonskyRainbowDeterminant

namespace MonskyDichromaticLine

open MonskyRainbow

/--
**No dichromatic line.**

Let `a·x + b·y = c` be a genuine line in `ℚ × ℚ` (i.e. `a ≠ 0 ∨ b ≠ 0`). If
`(x₀,y₀)` has colour 0, `(x₁,y₁)` has colour 1 and `(x₂,y₂)` has colour 2 (the
2-adic-valuation colouring of `MonskyRainbowDeterminant`), then the three
points cannot all lie on the line.

Proof idea: the two line equations force the rainbow determinant
`D = (x₁-x₀)(y₂-y₀) - (x₂-x₀)(y₁-y₀)` to satisfy `a·D = 0` and `b·D = 0`
(a short linear-algebra computation), hence `D = 0` since `a ≠ 0 ∨ b ≠ 0`. But
`MonskyRainbow.rainbow_det_valuation` proves `D ≠ 0` for any rainbow triple.
Contradiction. -/
theorem no_dichromatic_line
    (a b c : ℚ) (hab : a ≠ 0 ∨ b ≠ 0)
    (x0 y0 x1 y1 x2 y2 : ℚ)
    (h0x : 0 ≤ padicValRat 2 x0) (h0y : 0 ≤ padicValRat 2 y0)
    (h1x : padicValRat 2 x1 < 0) (h1xy : padicValRat 2 x1 ≤ padicValRat 2 y1)
    (h2y : padicValRat 2 y2 < 0) (h2yx : padicValRat 2 y2 < padicValRat 2 x2)
    (hx1 : x1 ≠ 0) (hy2 : y2 ≠ 0)
    (hL0 : a * x0 + b * y0 = c)
    (hL1 : a * x1 + b * y1 = c)
    (hL2 : a * x2 + b * y2 = c) : False := by
  have hD :=
    (rainbow_det_valuation x0 y0 x1 y1 x2 y2 h0x h0y h1x h1xy h2y h2yx hx1 hy2).2
  apply hD
  -- The two line equations, differenced against `hL0`.
  have e1 : a * (x1 - x0) + b * (y1 - y0) = 0 := by linear_combination hL1 - hL0
  have e2 : a * (x2 - x0) + b * (y2 - y0) = 0 := by linear_combination hL2 - hL0
  rcases hab with ha | hb
  · have haD : a * ((x1 - x0) * (y2 - y0) - (x2 - x0) * (y1 - y0)) = 0 := by
      linear_combination (y2 - y0) * e1 - (y1 - y0) * e2
    exact (mul_eq_zero.mp haD).resolve_left ha
  · have hbD : b * ((x1 - x0) * (y2 - y0) - (x2 - x0) * (y1 - y0)) = 0 := by
      linear_combination (x1 - x0) * e2 - (x2 - x0) * e1
    exact (mul_eq_zero.mp hbD).resolve_left hb

end MonskyDichromaticLine
