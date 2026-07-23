/-
# Rainbow-triangle determinant valuation, under the corrected (Aigner-Ziegler/Fan)
  3-colouring convention

`MonskyDichromaticLineReal.rainbow_det_valuation` proves the rainbow-triangle
determinant-valuation fact for the colouring convention

* colour 0 : `ν x ≤ 1 ∧ ν y ≤ 1`     (non-strict)
* colour 1 : `1 < ν x ∧ ν y ≤ ν x`   (strict on `x`)
* colour 2 : `1 < ν y ∧ ν x < ν y`   (strict on `y`)

which is **degenerate at the unit square's corners** (all four corners
collapse to colour 0). `MonskyBoundaryOddness.col` instead uses the
non-degenerate convention sourced from Aigner–Ziegler / Fan §3.1:

* colour 0 : `ν x < 1 ∧ ν y < 1`     (strict)
* colour 1 : `1 ≤ ν x ∧ ν y ≤ ν x`   (non-strict on `x`)
* colour 2 : `1 ≤ ν y ∧ ν x < ν y`   (non-strict on `y`)

i.e. the strictness at the `ν = 1` threshold is swapped between the
colour-0 regime and the colour-1/2 regime, relative to
`MonskyDichromaticLineReal`.

This file **mechanically re-verifies** (does not just hand-check) the claim
made in `MonskyBoundaryOddness`'s docstring: `rainbow_det_valuation`'s
five-step off-diagonal domination argument still goes through under the
swapped strictness, with the needed strict inequality in each step supplied
by whichever of the six hypotheses is strict under the *new* convention
instead of the *old* one. Concretely:

* Steps bounding `x1*y0` and `x0*y2` against the dominant `x1*y2`: in the
  old file these used the strict colour-1/2 hypotheses (`1 < ν x1`,
  `1 < ν y2`) applied *after* a non-strict colour-0 bound. Under the new
  convention they use the strict colour-0 hypotheses (`ν y0 < 1`,
  `ν x0 < 1`) directly, transitively against the now non-strict colour-1/2
  side (`1 ≤ ν x1`, `1 ≤ ν y2`) — actually simpler than the original
  two-step chain, collapsing to a single `mul_lt_mul_of_pos_{left,right}`.
* The step bounding `x2*y1`: unchanged. It only ever used `h1xy : ν y1 ≤ ν
  x1` and `h2yx : ν x2 < ν y2`, both of which are **identical** under the
  two conventions (colour 1's `y ≤ x` cross-condition and colour 2's `x <
  y` cross-condition never had their strictness swapped — only the
  threshold-vs-1 conditions did).
* The step bounding `x2*y0`: structurally unchanged; its strictness comes
  from `h2yx` (unchanged), so it survives with `h0y` used in its (now
  weaker, but still sufficient) `.le` form and `h1x` used directly (already
  non-strict, so no `.le` needed).
* The step bounding `x0*y1`: this is the one step that genuinely needed
  rerouting — in the old file its strictness came from `h2y : 1 < ν y2`
  applied *after* a non-strict `h0x`-bound; under swapped strictness `h2y`
  is no longer strict, so the strict link is moved earlier in the chain,
  supplied by `h0x : ν x0 < 1` instead (via
  `mul_lt_mul_of_pos_right h0x hx1pos`), with the `h2y`-step downgraded to
  `≤` (which suffices since the chain already has its one strict link).

The algebraic identity (`D = x1*y2 + <five off-diagonal monomials>`) and the
ultrametric folding of the five strict bounds into one are verbatim
unchanged from `MonskyDichromaticLineReal`.

Main results:
* `rainbow_det_valuation` — generic version (any field + valuation), corrected
  convention.
* `no_dichromatic_line` — generic version, corrected convention.
* `no_dichromatic_line_real` — the `ℝ × ℝ` specialisation via `νR`
  (`MonskyDichromaticLineReal.νR`), matching `MonskyBoundaryOddness.col`'s
  convention exactly.

Axiom-clean: depends only on `[propext, Classical.choice, Quot.sound]`
(inherited from `MonskyDichromaticLineReal`/`MonskyTwoAdicValuation`).
-/
import Propositio.Geometry.Monsky.MonskyDichromaticLineReal
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.Algebra.Order.GroupWithZero.Canonical

namespace MonskyRainbowDetCorrected

/-! ## Generic version: any field, any (multiplicative) valuation -/

section Generic

variable {K : Type*} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    (ν : Valuation K Γ₀)

/-- **Rainbow-triangle determinant valuation, generic form, corrected
convention.** For a colour-0 vertex `(x₀,y₀)` (strict: `ν x₀ < 1 ∧ ν y₀ <
1`), a colour-1 vertex `(x₁,y₁)` (non-strict: `1 ≤ ν x₁`, `ν y₁ ≤ ν x₁`) and
a colour-2 vertex `(x₂,y₂)` (non-strict: `1 ≤ ν y₂`, `ν x₂ < ν y₂`) — the
Aigner-Ziegler/Fan convention used by `MonskyBoundaryOddness.col` — the
signed-area determinant has valuation exactly `ν x₁ * ν y₂` and is nonzero.
This is `MonskyDichromaticLineReal.rainbow_det_valuation` with the
colour-0-vs-colour-1/2 strictness swapped. -/
theorem rainbow_det_valuation
    (x0 y0 x1 y1 x2 y2 : K)
    (h0x : ν x0 < 1) (h0y : ν y0 < 1)
    (h1x : 1 ≤ ν x1) (h1xy : ν y1 ≤ ν x1)
    (h2y : 1 ≤ ν y2) (h2yx : ν x2 < ν y2) :
    ν ((x1 - x0) * (y2 - y0) - (x2 - x0) * (y1 - y0)) = ν x1 * ν y2
    ∧ (x1 - x0) * (y2 - y0) - (x2 - x0) * (y1 - y0) ≠ 0 := by
  have hx1pos : (0 : Γ₀) < ν x1 := lt_of_lt_of_le zero_lt_one h1x
  have hy2pos : (0 : Γ₀) < ν y2 := lt_of_lt_of_le zero_lt_one h2y
  -- the five off-diagonal monomials each have valuation strictly below the
  -- dominant diagonal monomial `x1 * y2` -- strictness rerouted through the
  -- (now strict) colour-0 hypotheses where the old proof used the (now
  -- non-strict) colour-1/2 hypotheses `h1x`/`h2y`.
  have hA : ν (x1 * y0) < ν (x1 * y2) := by
    rw [ν.map_mul, ν.map_mul]
    exact mul_lt_mul_of_pos_left (lt_of_lt_of_le h0y h2y) hx1pos
  have hB : ν (x0 * y2) < ν (x1 * y2) := by
    rw [ν.map_mul, ν.map_mul]
    exact mul_lt_mul_of_pos_right (lt_of_lt_of_le h0x h1x) hy2pos
  have hC : ν (x2 * y1) < ν (x1 * y2) := by
    rw [ν.map_mul, ν.map_mul]
    calc ν x2 * ν y1 ≤ ν x2 * ν x1 := mul_le_mul_of_nonneg_left h1xy zero_le'
      _ < ν y2 * ν x1 := mul_lt_mul_of_pos_right h2yx hx1pos
      _ = ν x1 * ν y2 := mul_comm _ _
  have hD : ν (x2 * y0) < ν (x1 * y2) := by
    rw [ν.map_mul, ν.map_mul]
    calc ν x2 * ν y0 ≤ ν x2 * 1 := mul_le_mul_of_nonneg_left h0y.le zero_le'
      _ = ν x2 := mul_one _
      _ < ν y2 := h2yx
      _ ≤ ν x1 * ν y2 := by
          have h := mul_le_mul_of_nonneg_right h1x (zero_le' (a := ν y2))
          simpa using h
  have hE : ν (x0 * y1) < ν (x1 * y2) := by
    rw [ν.map_mul, ν.map_mul]
    calc ν x0 * ν y1 ≤ ν x0 * ν x1 := mul_le_mul_of_nonneg_left h1xy zero_le'
      _ < 1 * ν x1 := mul_lt_mul_of_pos_right h0x hx1pos
      _ = ν x1 := one_mul _
      _ ≤ ν x1 * ν y2 := by
          have h := mul_le_mul_of_nonneg_left h2y (zero_le' (a := ν x1))
          simpa using h
  -- fold the five negated off-diagonal terms via the ultrametric inequality
  have hA' : ν (-(x1 * y0)) < ν (x1 * y2) := by rwa [ν.map_neg]
  have hB' : ν (-(x0 * y2)) < ν (x1 * y2) := by rwa [ν.map_neg]
  have hC' : ν (-(x2 * y1)) < ν (x1 * y2) := by rwa [ν.map_neg]
  have hDE : ν (x2 * y0 + x0 * y1) < ν (x1 * y2) := ν.map_add_lt hD hE
  have hCDE : ν (-(x2 * y1) + (x2 * y0 + x0 * y1)) < ν (x1 * y2) :=
    ν.map_add_lt hC' hDE
  have hBCDE : ν (-(x0 * y2) + (-(x2 * y1) + (x2 * y0 + x0 * y1))) < ν (x1 * y2) :=
    ν.map_add_lt hB' hCDE
  have hE_total :
      ν (-(x1 * y0) + (-(x0 * y2) + (-(x2 * y1) + (x2 * y0 + x0 * y1)))) < ν (x1 * y2) :=
    ν.map_add_lt hA' hBCDE
  -- algebraic expansion of the determinant: D = x1*y2 + E
  have hDeq : (x1 - x0) * (y2 - y0) - (x2 - x0) * (y1 - y0)
      = x1 * y2 + (-(x1 * y0) + (-(x0 * y2) + (-(x2 * y1) + (x2 * y0 + x0 * y1)))) := by
    ring
  have hval : ν ((x1 - x0) * (y2 - y0) - (x2 - x0) * (y1 - y0)) = ν x1 * ν y2 := by
    rw [hDeq, ν.map_add_eq_of_lt_left hE_total, ν.map_mul]
  refine ⟨hval, ?_⟩
  have hprod_pos : (0 : Γ₀) < ν x1 * ν y2 := mul_pos hx1pos hy2pos
  have hne : ν ((x1 - x0) * (y2 - y0) - (x2 - x0) * (y1 - y0)) ≠ 0 := by
    rw [hval]; exact hprod_pos.ne'
  exact (ν.ne_zero_iff).mp hne

/-- **No dichromatic line, generic form, corrected convention.** Let
`a·x + b·y = c` be a genuine line in `K × K`. If `(x₀,y₀)` has colour 0,
`(x₁,y₁)` has colour 1 and `(x₂,y₂)` has colour 2 (Aigner-Ziegler/Fan
convention), the three points cannot all lie on the line. -/
theorem no_dichromatic_line
    (a b c : K) (hab : a ≠ 0 ∨ b ≠ 0)
    (x0 y0 x1 y1 x2 y2 : K)
    (h0x : ν x0 < 1) (h0y : ν y0 < 1)
    (h1x : 1 ≤ ν x1) (h1xy : ν y1 ≤ ν x1)
    (h2y : 1 ≤ ν y2) (h2yx : ν x2 < ν y2)
    (hL0 : a * x0 + b * y0 = c)
    (hL1 : a * x1 + b * y1 = c)
    (hL2 : a * x2 + b * y2 = c) : False := by
  have hD := (rainbow_det_valuation ν x0 y0 x1 y1 x2 y2 h0x h0y h1x h1xy h2y h2yx).2
  apply hD
  have e1 : a * (x1 - x0) + b * (y1 - y0) = 0 := by linear_combination hL1 - hL0
  have e2 : a * (x2 - x0) + b * (y2 - y0) = 0 := by linear_combination hL2 - hL0
  rcases hab with ha | hb
  · have haD : a * ((x1 - x0) * (y2 - y0) - (x2 - x0) * (y1 - y0)) = 0 := by
      linear_combination (y2 - y0) * e1 - (y1 - y0) * e2
    exact (mul_eq_zero.mp haD).resolve_left ha
  · have hbD : b * ((x1 - x0) * (y2 - y0) - (x2 - x0) * (y1 - y0)) = 0 := by
      linear_combination (x1 - x0) * e2 - (x2 - x0) * e1
    exact (mul_eq_zero.mp hbD).resolve_left hb

end Generic

/-! ## Specialisation to `ℝ`, via `MonskyDichromaticLineReal.νR` -/

/-- **No dichromatic line, over ℝ, corrected convention.** The `ℝ × ℝ`
specialisation of `no_dichromatic_line` via the genuine 2-adic valuation
`MonskyDichromaticLineReal.νR`, using the same colour convention as
`MonskyBoundaryOddness.col`. -/
theorem no_dichromatic_line_real
    (a b c : ℝ) (hab : a ≠ 0 ∨ b ≠ 0)
    (x0 y0 x1 y1 x2 y2 : ℝ)
    (h0x : MonskyDichromaticLineReal.νR x0 < 1)
    (h0y : MonskyDichromaticLineReal.νR y0 < 1)
    (h1x : 1 ≤ MonskyDichromaticLineReal.νR x1)
    (h1xy : MonskyDichromaticLineReal.νR y1 ≤ MonskyDichromaticLineReal.νR x1)
    (h2y : 1 ≤ MonskyDichromaticLineReal.νR y2)
    (h2yx : MonskyDichromaticLineReal.νR x2 < MonskyDichromaticLineReal.νR y2)
    (hL0 : a * x0 + b * y0 = c)
    (hL1 : a * x1 + b * y1 = c)
    (hL2 : a * x2 + b * y2 = c) : False :=
  no_dichromatic_line MonskyDichromaticLineReal.νR a b c hab
    x0 y0 x1 y1 x2 y2 h0x h0y h1x h1xy h2y h2yx hL0 hL1 hL2

end MonskyRainbowDetCorrected
