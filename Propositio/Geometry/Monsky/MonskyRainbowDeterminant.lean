/-
# Monsky rainbow-triangle determinant valuation lemma

The combinatorial heart of Monsky's theorem (a unit square admits no dissection
into an odd number of equal-area triangles) is the *rainbow triangle* fact for the
2-adic 3-colouring of the plane: a triangle whose three vertices carry the three
distinct colours has nonzero signed area — and, sharper, the 2-adic valuation of
that signed area is exactly `v(x₁) + v(y₂)`, which is strictly negative.

Here we work over `ℚ` with the 2-adic valuation `v q = padicValRat 2 q`
(mathlib convention `padicValRat 2 0 = 0`).  The standard colouring of `(x, y)`:

* colour 0 : `0 ≤ v x` and `0 ≤ v y`
* colour 1 : `v x < 0` and `v x ≤ v y`
* colour 2 : `v y < 0` and `v y < v x`

Given a colour-0 vertex `(x₀, y₀)`, a colour-1 vertex `(x₁, y₁)` and a colour-2
vertex `(x₂, y₂)`, the signed-area determinant
`D = (x₁-x₀)(y₂-y₀) - (x₂-x₀)(y₁-y₀)`
expands to six monomials; the monomial `x₁·y₂` has valuation `v x₁ + v y₂` and is
the unique strict minimiser, so by the ultrametric inequality `v D = v x₁ + v y₂`,
which is `< 0`, whence `D ≠ 0`.

Main result: `MonskyRainbow.rainbow_det_valuation`.

Axiom-clean: depends only on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic.LinearCombination

namespace MonskyRainbow

/-- Closure of the predicate `P q r := (r = 0 ∨ v q < v r)` under addition of
rationals, for the 2-adic valuation.  This is the folding step used to bound the
valuation of the five "off-diagonal" monomials of the determinant. -/
private lemma val_lt_or_eq_zero_add {q s t : ℚ}
    (hs : s = 0 ∨ padicValRat 2 q < padicValRat 2 s)
    (ht : t = 0 ∨ padicValRat 2 q < padicValRat 2 t) :
    s + t = 0 ∨ padicValRat 2 q < padicValRat 2 (s + t) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases hs with hs | hs
  · subst hs; simpa using ht
  · rcases ht with ht | ht
    · subst ht; simpa using Or.inr hs
    · by_cases hst : s + t = 0
      · exact Or.inl hst
      · exact Or.inr (padicValRat.lt_add_of_lt hst hs ht)

/-- **Rainbow-triangle determinant valuation.**  For a colour-0 vertex `(x₀,y₀)`,
a colour-1 vertex `(x₁,y₁)` and a colour-2 vertex `(x₂,y₂)` (colours given by the
explicit 2-adic valuation inequalities), the signed-area determinant has 2-adic
valuation exactly `v x₁ + v y₂` and is nonzero. -/
theorem rainbow_det_valuation
    (x0 y0 x1 y1 x2 y2 : ℚ)
    (h0x : 0 ≤ padicValRat 2 x0) (h0y : 0 ≤ padicValRat 2 y0)
    (h1x : padicValRat 2 x1 < 0) (h1xy : padicValRat 2 x1 ≤ padicValRat 2 y1)
    (h2y : padicValRat 2 y2 < 0) (h2yx : padicValRat 2 y2 < padicValRat 2 x2)
    (hx1 : x1 ≠ 0) (hy2 : y2 ≠ 0) :
    padicValRat 2 ((x1 - x0) * (y2 - y0) - (x2 - x0) * (y1 - y0))
      = padicValRat 2 x1 + padicValRat 2 y2
    ∧ (x1 - x0) * (y2 - y0) - (x2 - x0) * (y1 - y0) ≠ 0 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  -- valuation of the diagonal monomial x1*y2
  have hT : padicValRat 2 (x1 * y2) = padicValRat 2 x1 + padicValRat 2 y2 :=
    padicValRat.mul hx1 hy2
  -- each off-diagonal monomial is either 0 or has valuation strictly above v(x1*y2)
  have ht1 : -(x1 * y0) = 0 ∨ padicValRat 2 (x1 * y2) < padicValRat 2 (-(x1 * y0)) := by
    by_cases hy0 : y0 = 0
    · left; simp [hy0]
    · right
      rw [padicValRat.neg, padicValRat.mul hx1 hy0, padicValRat.mul hx1 hy2]
      omega
  have ht2 : -(x0 * y2) = 0 ∨ padicValRat 2 (x1 * y2) < padicValRat 2 (-(x0 * y2)) := by
    by_cases hx0 : x0 = 0
    · left; simp [hx0]
    · right
      rw [padicValRat.neg, padicValRat.mul hx0 hy2, padicValRat.mul hx1 hy2]
      omega
  have ht3 : -(x2 * y1) = 0 ∨ padicValRat 2 (x1 * y2) < padicValRat 2 (-(x2 * y1)) := by
    by_cases hx2 : x2 = 0
    · left; simp [hx2]
    · by_cases hy1 : y1 = 0
      · left; simp [hy1]
      · right
        rw [padicValRat.neg, padicValRat.mul hx2 hy1, padicValRat.mul hx1 hy2]
        omega
  have ht4 : x2 * y0 = 0 ∨ padicValRat 2 (x1 * y2) < padicValRat 2 (x2 * y0) := by
    by_cases hx2 : x2 = 0
    · left; simp [hx2]
    · by_cases hy0 : y0 = 0
      · left; simp [hy0]
      · right
        rw [padicValRat.mul hx2 hy0, padicValRat.mul hx1 hy2]
        omega
  have ht5 : x0 * y1 = 0 ∨ padicValRat 2 (x1 * y2) < padicValRat 2 (x0 * y1) := by
    by_cases hx0 : x0 = 0
    · left; simp [hx0]
    · by_cases hy1 : y1 = 0
      · left; simp [hy1]
      · right
        rw [padicValRat.mul hx0 hy1, padicValRat.mul hx1 hy2]
        omega
  -- fold the five off-diagonal terms: their sum E is 0 or has valuation > v(x1*y2)
  have hR := val_lt_or_eq_zero_add ht1
    (val_lt_or_eq_zero_add ht2
      (val_lt_or_eq_zero_add ht3
        (val_lt_or_eq_zero_add ht4 ht5)))
  -- algebraic expansion of the determinant: D = x1*y2 + E
  have hDeq : (x1 - x0) * (y2 - y0) - (x2 - x0) * (y1 - y0)
      = x1 * y2 + (-(x1 * y0) + (-(x0 * y2) + (-(x2 * y1) + (x2 * y0 + x0 * y1)))) := by
    ring
  set E := (-(x1 * y0) + (-(x0 * y2) + (-(x2 * y1) + (x2 * y0 + x0 * y1)))) with hEdef
  rcases hR with hS | hlt
  · -- E = 0 : the determinant is exactly x1*y2
    rw [hDeq, hS, add_zero]
    exact ⟨hT, mul_ne_zero hx1 hy2⟩
  · -- v(x1*y2) < v E : diagonal term is the strict minimiser
    by_cases hS : E = 0
    · rw [hDeq, hS, add_zero]
      exact ⟨hT, mul_ne_zero hx1 hy2⟩
    · rw [hDeq]
      have hne : x1 * y2 + E ≠ 0 := by
        intro h
        have hSe : E = -(x1 * y2) := by linear_combination h
        rw [hSe, padicValRat.neg] at hlt
        exact lt_irrefl _ hlt
      refine ⟨?_, hne⟩
      rw [padicValRat.add_eq_of_lt hne (mul_ne_zero hx1 hy2) hS hlt, hT]

end MonskyRainbow
