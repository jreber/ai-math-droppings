/-
# Monsky area/parity contradiction: no rainbow triangle can have odd-denominator area

This file closes the "final area/parity contradiction" step flagged open in
`docs/kb/frontier/_meta.json`'s `_goal_monsky_OPEN_2026_07_05` note.

`MonskyRainbowDetCorrected.rainbow_det_valuation` shows that for a rainbow
triangle `(x0,y0), (x1,y1), (x2,y2) : ℝ × ℝ` under the Aigner-Ziegler/Fan
colour convention (colour 0 strict: `νR x0 < 1 ∧ νR y0 < 1`; colour 1
non-strict: `1 ≤ νR x1 ∧ νR y1 ≤ νR x1`; colour 2 non-strict: `1 ≤ νR y2 ∧
νR x2 < νR y2`), the signed-area determinant
`D = (x1-x0)*(y2-y0) - (x2-x0)*(y1-y0)` satisfies `νR D = νR x1 * νR y2`.
Since both factors are `≥ 1`, this forces `νR D ≥ 1`.

On the other hand, if the *actual* (unsigned) area `|D|/2` of the triangle
equals `1/n` for some **odd** natural number `n`, then `|D| = 2/n`, and since
`νR` is multiplicative and satisfies `νR (odd integer) = 1`
(`MonskyDichromaticLineReal.νR_spec`), `νR D = νR |D| = νR 2 / νR n = νR 2`,
which is **strictly less than 1** (`νR_spec`'s first conjunct). This
contradicts `νR D ≥ 1`.

This is exactly the step needed to turn a genuine rainbow triangle (produced
once the triangulation wall is crossed) into "no odd equal-area dissection of
the unit square exists" — the heart of Monsky's theorem.

Axiom-clean: depends only on `[propext, Classical.choice, Quot.sound]`
(inherited from `MonskyRainbowDetCorrected` / `MonskyDichromaticLineReal` /
`MonskyTwoAdicValuation`).
-/
import Propositio.Geometry.Monsky.MonskyRainbowDetCorrected
import Propositio.Geometry.Monsky.MonskyDichromaticLineReal
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.Algebra.Order.GroupWithZero.Canonical

namespace MonskyAreaValuationContradiction

open MonskyDichromaticLineReal

/-- **Area/parity contradiction.** A rainbow triangle (in the
Aigner-Ziegler/Fan colour convention used by `MonskyRainbowDetCorrected`,
via the genuine 2-adic valuation `νR` on `ℝ`) cannot have area `1/n` for an
odd natural number `n`. This is the "final area/parity contradiction" step
of Monsky's theorem: combined with a genuine rainbow triangle produced from
an actual odd equal-area dissection of the unit square, it shows no such
dissection exists. -/
theorem no_odd_area_rainbow_triangle
    (x0 y0 x1 y1 x2 y2 : ℝ)
    (h0x : νR x0 < 1) (h0y : νR y0 < 1)
    (h1x : 1 ≤ νR x1) (h1xy : νR y1 ≤ νR x1)
    (h2y : 1 ≤ νR y2) (h2yx : νR x2 < νR y2)
    (n : ℕ) (hn : Odd n)
    (harea :
      |((x1 - x0) * (y2 - y0) - (x2 - x0) * (y1 - y0))| / 2 = 1 / (n : ℝ)) :
    False := by
  set det : ℝ := (x1 - x0) * (y2 - y0) - (x2 - x0) * (y1 - y0) with hdet_def
  -- Step 1: the rainbow-determinant valuation fact.
  obtain ⟨hval, -⟩ :=
    MonskyRainbowDetCorrected.rainbow_det_valuation νR x0 y0 x1 y1 x2 y2
      h0x h0y h1x h1xy h2y h2yx
  -- Step 2: `νR x1 * νR y2 ≥ 1`, hence `νR det ≥ 1`.
  have hge : (1 : ΓR) ≤ νR x1 * νR y2 := by
    calc (1 : ΓR) ≤ νR y2 := h2y
      _ = 1 * νR y2 := (one_mul _).symm
      _ ≤ νR x1 * νR y2 := mul_le_mul_of_nonneg_right h1x zero_le'
  have hge_det : (1 : ΓR) ≤ νR det := by rw [hval]; exact hge
  -- Step 3: `n ≠ 0` (as a real number), from oddness.
  have hnpos : 0 < n := hn.pos
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hnpos.ne'
  -- Step 4: unwind `|det| / 2 = 1 / n` into `|det| = 2 / n`.
  have habs : |det| = 2 / (n : ℝ) := by
    have h2 : (2 : ℝ) ≠ 0 := two_ne_zero
    rw [div_eq_div_iff h2 hn0] at harea
    rw [eq_div_iff hn0]
    linarith [harea]
  -- Step 5: `νR det = νR |det|` (valuations are even functions).
  have hdetabs : νR det = νR |det| := by
    rcases abs_choice det with h | h
    · rw [h]
    · rw [h, νR.map_neg]
  -- Step 6: `νR (n : ℝ) = 1` since `n` is odd.
  have hnodd_int : Odd (n : ℤ) := Int.odd_coe_nat n |>.mpr hn
  have hνn : νR (n : ℝ) = 1 := by
    have h := MonskyDichromaticLineReal.νR_spec.2 (n : ℤ) hnodd_int
    simpa using h
  -- Step 7: `νR det = νR 2`, which is strictly `< 1`.
  have hval2 : νR det = νR 2 := by
    rw [hdetabs, habs, νR.map_div, hνn, div_one]
  have hlt : νR det < 1 := hval2 ▸ MonskyDichromaticLineReal.νR_spec.1
  -- Step 8: contradiction between `νR det ≥ 1` and `νR det < 1`.
  exact absurd hge_det (not_le.mpr hlt)

end MonskyAreaValuationContradiction
