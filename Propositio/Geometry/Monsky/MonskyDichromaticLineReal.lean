/-
# Monsky dichromatic-line lemma over ℝ (real coordinates, not just ℚ)

`MonskyDichromaticLine.no_dichromatic_line` proves "no line meets all three
colour classes" for the 2-adic 3-colouring of `ℚ × ℚ`, using the *concrete*
valuation `padicValRat 2 : ℚ → ℤ` (additive convention).  Equidissections of
the unit square can have **irrational** vertex coordinates in general, so the
combinatorial Sperner argument ultimately needs the analogous fact for
`ℝ × ℝ`.

This file shows the `ℚ`-restriction in `MonskyDichromaticLine` was a
convenience, not a necessity: the entire argument (rainbow-triangle
determinant has non-zero, exactly-computed valuation; a line cannot meet all
three colour classes) is proved here **generically** for *any* field `K`
equipped with a (multiplicatively-normalised) valuation `ν : Valuation K Γ₀`
into a linearly ordered commutative group with zero.  The only facts used are
`Valuation.map_mul`, `Valuation.map_neg`, `Valuation.map_add_eq_of_lt_left`,
and order-theoretic monotonicity of multiplication in `Γ₀` — none of this is
specific to `ℚ` or to `padicValRat`.

We then specialise to `K = ℝ` using the genuine 2-adic valuation on `ℝ`
constructed (via the Chevalley/Zorn valuation-extension theorem) in
`MonskyTwoAdicValuation.exists_two_adic_valuation_on_real_strong`, producing
`no_dichromatic_line_real` — a real-coordinate, non-`ℚ`-restricted analogue of
`MonskyDichromaticLine.no_dichromatic_line`.

Colour convention (multiplicative valuation `ν`, matching
`MonskyRainbowDeterminant`'s additive `v = padicValRat 2` colouring up to the
order-reversal `ν ↔ 2^{-v}`):

* colour 0 : `ν x ≤ 1` and `ν y ≤ 1`   (↔ `0 ≤ v x`, `0 ≤ v y`)
* colour 1 : `1 < ν x` and `ν y ≤ ν x`  (↔ `v x < 0`, `v x ≤ v y`)
* colour 2 : `1 < ν y` and `ν x < ν y`  (↔ `v y < 0`, `v y < v x`)

Main results:
* `rainbow_det_valuation` — generic version, any field + valuation.
* `no_dichromatic_line` — generic version, any field + valuation.
* `no_dichromatic_line_real` — the `ℝ × ℝ` specialisation via the
  Chevalley-extension 2-adic valuation on `ℝ`.

Axiom-clean: depends only on `[propext, Classical.choice, Quot.sound]`
(inherited from `MonskyTwoAdicValuation`'s use of the Chevalley/Zorn
valuation-extension theorem, which is itself axiom-free — it is a mathlib
*theorem*, not an axiom).
-/
import Propositio.Geometry.Monsky.MonskyTwoAdicValuation
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.Algebra.Order.GroupWithZero.Canonical

namespace MonskyDichromaticLineReal

/-! ## Generic version: any field, any (multiplicative) valuation -/

section Generic

variable {K : Type*} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    (ν : Valuation K Γ₀)

/-- **Rainbow-triangle determinant valuation, generic form.**  For a colour-0
vertex `(x₀,y₀)`, a colour-1 vertex `(x₁,y₁)` and a colour-2 vertex `(x₂,y₂)`
(colours given by the valuation-order inequalities above, for *any* field `K`
and valuation `ν : Valuation K Γ₀`), the signed-area determinant has valuation
exactly `ν x₁ * ν y₂` and is nonzero.  This is
`MonskyRainbow.rainbow_det_valuation` with `ℚ` and `padicValRat 2` replaced by
an arbitrary field and valuation. -/
theorem rainbow_det_valuation
    (x0 y0 x1 y1 x2 y2 : K)
    (h0x : ν x0 ≤ 1) (h0y : ν y0 ≤ 1)
    (h1x : 1 < ν x1) (h1xy : ν y1 ≤ ν x1)
    (h2y : 1 < ν y2) (h2yx : ν x2 < ν y2) :
    ν ((x1 - x0) * (y2 - y0) - (x2 - x0) * (y1 - y0)) = ν x1 * ν y2
    ∧ (x1 - x0) * (y2 - y0) - (x2 - x0) * (y1 - y0) ≠ 0 := by
  have hx1pos : (0 : Γ₀) < ν x1 := lt_of_le_of_lt zero_le' h1x
  have hy2pos : (0 : Γ₀) < ν y2 := lt_of_le_of_lt zero_le' h2y
  -- the five off-diagonal monomials each have valuation strictly below the
  -- dominant diagonal monomial `x1 * y2`
  have hA : ν (x1 * y0) < ν (x1 * y2) := by
    rw [ν.map_mul, ν.map_mul]
    calc ν x1 * ν y0 ≤ ν x1 * 1 := mul_le_mul_of_nonneg_left h0y zero_le'
      _ = ν x1 := mul_one _
      _ < ν x1 * ν y2 := by
          have h := mul_lt_mul_of_pos_left h2y hx1pos; simpa using h
  have hB : ν (x0 * y2) < ν (x1 * y2) := by
    rw [ν.map_mul, ν.map_mul]
    calc ν x0 * ν y2 ≤ 1 * ν y2 := mul_le_mul_of_nonneg_right h0x zero_le'
      _ = ν y2 := one_mul _
      _ < ν x1 * ν y2 := by
          have h := mul_lt_mul_of_pos_right h1x hy2pos; simpa using h
  have hC : ν (x2 * y1) < ν (x1 * y2) := by
    rw [ν.map_mul, ν.map_mul]
    calc ν x2 * ν y1 ≤ ν x2 * ν x1 := mul_le_mul_of_nonneg_left h1xy zero_le'
      _ < ν y2 * ν x1 := mul_lt_mul_of_pos_right h2yx hx1pos
      _ = ν x1 * ν y2 := mul_comm _ _
  have hD : ν (x2 * y0) < ν (x1 * y2) := by
    rw [ν.map_mul, ν.map_mul]
    calc ν x2 * ν y0 ≤ ν x2 * 1 := mul_le_mul_of_nonneg_left h0y zero_le'
      _ = ν x2 := mul_one _
      _ < ν y2 := h2yx
      _ ≤ ν x1 * ν y2 := by
          have h := mul_le_mul_of_nonneg_right h1x.le (zero_le' (a := ν y2))
          simpa using h
  have hE : ν (x0 * y1) < ν (x1 * y2) := by
    rw [ν.map_mul, ν.map_mul]
    calc ν x0 * ν y1 ≤ ν x0 * ν x1 := mul_le_mul_of_nonneg_left h1xy zero_le'
      _ ≤ 1 * ν x1 := mul_le_mul_of_nonneg_right h0x zero_le'
      _ = ν x1 := one_mul _
      _ < ν x1 * ν y2 := by
          have h := mul_lt_mul_of_pos_left h2y hx1pos; simpa using h
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

/-- **No dichromatic line, generic form.**  Let `a·x + b·y = c` be a genuine
line in `K × K`.  If `(x₀,y₀)` has colour 0, `(x₁,y₁)` has colour 1 and
`(x₂,y₂)` has colour 2, the three points cannot all lie on the line.  This is
`MonskyDichromaticLine.no_dichromatic_line` with `ℚ` and `padicValRat 2`
replaced by an arbitrary field and valuation. -/
theorem no_dichromatic_line
    (a b c : K) (hab : a ≠ 0 ∨ b ≠ 0)
    (x0 y0 x1 y1 x2 y2 : K)
    (h0x : ν x0 ≤ 1) (h0y : ν y0 ≤ 1)
    (h1x : 1 < ν x1) (h1xy : ν y1 ≤ ν x1)
    (h2y : 1 < ν y2) (h2yx : ν x2 < ν y2)
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

/-! ## Specialisation to `ℝ`, via the Chevalley-extension 2-adic valuation -/

/-- The value group of the genuine 2-adic valuation on `ℝ` produced by
`MonskyTwoAdic.exists_two_adic_valuation_on_real_strong`. -/
noncomputable def ΓR : Type :=
  MonskyTwoAdic.exists_two_adic_valuation_on_real_strong.choose

noncomputable instance : LinearOrderedCommGroupWithZero ΓR :=
  MonskyTwoAdic.exists_two_adic_valuation_on_real_strong.choose_spec.choose

/-- The genuine 2-adic valuation on `ℝ` (obtained by dominating `ℤ_(2) ⊂ ℝ` by
a valuation subring, via `MonskyTwoAdic`). -/
noncomputable def νR : Valuation ℝ ΓR :=
  MonskyTwoAdic.exists_two_adic_valuation_on_real_strong.choose_spec.choose_spec.choose

theorem νR_spec : νR 2 < 1 ∧ ∀ n : ℤ, Odd n → νR (n : ℝ) = 1 :=
  MonskyTwoAdic.exists_two_adic_valuation_on_real_strong.choose_spec.choose_spec.choose_spec

/-- **No dichromatic line, over ℝ.**  Let `a·x + b·y = c` be a genuine line in
`ℝ × ℝ`.  If `(x₀,y₀)` has colour 0, `(x₁,y₁)` has colour 1 and `(x₂,y₂)` has
colour 2 for the genuine 2-adic valuation `νR` on `ℝ` (not just `ℚ`), the three
points cannot all lie on the line.  This is the real-coordinate analogue of
`MonskyDichromaticLine.no_dichromatic_line`, needed because equidissections of
the unit square can have irrational vertex coordinates. -/
theorem no_dichromatic_line_real
    (a b c : ℝ) (hab : a ≠ 0 ∨ b ≠ 0)
    (x0 y0 x1 y1 x2 y2 : ℝ)
    (h0x : νR x0 ≤ 1) (h0y : νR y0 ≤ 1)
    (h1x : 1 < νR x1) (h1xy : νR y1 ≤ νR x1)
    (h2y : 1 < νR y2) (h2yx : νR x2 < νR y2)
    (hL0 : a * x0 + b * y0 = c)
    (hL1 : a * x1 + b * y1 = c)
    (hL2 : a * x2 + b * y2 = c) : False :=
  no_dichromatic_line νR a b c hab x0 y0 x1 y1 x2 y2 h0x h0y h1x h1xy h2y h2yx hL0 hL1 hL2

end MonskyDichromaticLineReal
