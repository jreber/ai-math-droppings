import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
import Mathlib.Tactic

/-!
# The signature-(2,3,n) Frey (Mordell) curve for `a² + b³ = c^n` (Lean 4 / mathlib)

This file formalizes the **Mordell-type Frey elliptic curve** attached to a
putative solution of the generalized-Fermat / Beal equation in signature
`(2, 3, n)`,

  `a² + b³ = c^n`,

and proves its discriminant in closed form. The signature `(2, 3, n)` is the
**most-studied** generalized-Fermat family (the "spherical-to-hyperbolic boundary"
case): Poonen–Schaefer–Stoll resolved `(2, 3, 7)`, Bennett–Chen and many others
treat further members. This complements the cube-sum Kraus curve of
`BealFreyCurve.lean` (`A³ + B³ = C^z`) and the general Hellegouarch–Frey model of
`BealFreyGeneral.lean`.

## The curve

For the equation `a² + b³ = c^n` we attach the short Weierstrass / Mordell curve

  `E : Y² = X³ + 3·b·X − 2·a`,

i.e. `a₁ = a₂ = a₃ = 0`, `a₄ = 3·b`, `a₆ = −2·a` (`frey23`). The combination
`a² + b³` appears directly in its discriminant.

## The discriminant

For a short Weierstrass curve `Y² = X³ + a₄·X + a₆`, mathlib's discriminant
convention (LMFDB sign) gives `Δ = -64·a₄³ - 432·a₆²`. Specialising to
`a₄ = 3·b`, `a₆ = −2·a`:

  `-64·(3b)³ - 432·(−2a)² = -1728·b³ - 1728·a² = -1728·(a² + b³)`.

Hence

  `Δ = -1728·(a² + b³)`  (`frey23_Δ`),

and substituting `a² + b³ = c^n` (`frey23_Δ_eq`),

  `Δ = -1728·c^n = -2⁶·3³·c^n`.

So the discriminant is supported only at `2`, `3`, and the primes dividing `c`.
This small-conductor support condition (`{2, 3} ∪ primes(c)`) is precisely the
input that the modular method consumes:

* **Modularity** (Wiles, Breuil–Conrad–Diamond–Taylor) attaches a weight-`2`
  newform to `E`;
* **Ribet level-lowering** strips the primes dividing `c` from the level, forcing
  a newform of small level.

The modularity and level-lowering steps require FLT-project infrastructure not
present in this mathlib snapshot; the curve and its discriminant formalized here
are the concrete, machine-checked groundwork.

## House style

Follows `BealFreyCurve.lean`: a module doc-comment, per-theorem doc-comments, and
proofs that `simp` the `WeierstrassCurve` quantity definitions then `ring`.
Dependency policy: mathlib4 permitted. Use `lake env lean BealFrey23.lean` to
typecheck.

Key mathlib API relied on:
* `WeierstrassCurve R` — structure with fields `a₁ a₂ a₃ a₄ a₆`.
* `WeierstrassCurve.Δ` and the intermediates `b₂ b₄ b₆ b₈`.
* `WeierstrassCurve.c₄ = b₂² - 24·b₄`.
* `WeierstrassCurve.IsElliptic` — typeclass asserting `IsUnit Δ`.
-/

namespace BealFrey23

open WeierstrassCurve

/-! ## 1. The Frey curve -/

/-- The signature-`(2,3,n)` Mordell-type Frey curve `Y² = X³ + 3·b·X − 2·a`
attached to the equation `a² + b³ = c^n`. In short Weierstrass form:
`a₁ = a₂ = a₃ = 0`, `a₄ = 3·b`, `a₆ = −2·a`. -/
def frey23 (a b : ℚ) : WeierstrassCurve ℚ :=
  { a₁ := 0, a₂ := 0, a₃ := 0, a₄ := 3 * b, a₆ := -2 * a }

/-! ## 2. The discriminant -/

/-- The discriminant of the signature-`(2,3,n)` Frey curve in closed form:
`Δ = -1728·(a² + b³)`.

Proof: unfold the `b`-coefficients and `Δ` of a short Weierstrass curve and let
`ring` verify `-64·(3b)³ - 432·(−2a)² = -1728·(a² + b³)`. -/
theorem frey23_Δ (a b : ℚ) : (frey23 a b).Δ = -1728 * (a ^ 2 + b ^ 3) := by
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈, frey23]
  ring

/-- **Headline.** Substituting the signature-`(2,3,n)` hypothesis `a² + b³ = c^n`
into the discriminant gives `Δ = -1728·c^n`. With `a² + b³ = c^n`, the
discriminant of the Frey curve is

  `Δ = -1728·c^n = -2⁶·3³·c^n`,

supported only at `2`, `3` and the primes dividing `c`. This small conductor is
the input to the `(2,3,n)` modular attack. -/
theorem frey23_Δ_eq (a b c : ℚ) (n : ℕ) (h : a ^ 2 + b ^ 3 = c ^ n) :
    (frey23 a b).Δ = -1728 * c ^ n := by
  rw [frey23_Δ, h]

/-- The constant `-1728` is `-2⁶·3³` (`1728 = 12³`), exhibiting the
`Δ = -2⁶·3³·c^n` form of the Frey discriminant. -/
theorem neg_1728_eq : (-1728 : ℚ) = -2 ^ 6 * 3 ^ 3 := by norm_num

/-! ## 3. Non-degeneracy: a genuine elliptic curve when `a² + b³ ≠ 0` -/

/-- The Frey curve is non-singular (its discriminant is nonzero) whenever
`a² + b³ ≠ 0`. Equivalently, since `a² + b³ = c^n` in the Beal setting, the curve
is a genuine elliptic curve as long as `c ≠ 0`. -/
theorem frey23_Δ_ne_zero (a b : ℚ) (h : a ^ 2 + b ^ 3 ≠ 0) :
    (frey23 a b).Δ ≠ 0 := by
  rw [frey23_Δ]
  exact mul_ne_zero (by norm_num) h

/-- The Frey curve, packaged with mathlib's `IsElliptic` instance, is a genuine
elliptic curve over `ℚ` whenever `a² + b³ ≠ 0`: its discriminant is a unit
(every nonzero rational is a unit). -/
theorem frey23_isElliptic (a b : ℚ) (h : a ^ 2 + b ^ 3 ≠ 0) :
    (frey23 a b).IsElliptic :=
  ⟨isUnit_iff_ne_zero.mpr (frey23_Δ_ne_zero a b h)⟩

/-! ## 4. The `c₄` invariant

The `c₄` invariant feeds the `j`-invariant `j = c₄³ / Δ` and the conductor /
level analysis that Ribet level-lowering consumes. For the Frey curve we record
its closed form. -/

/-- The `c₄` invariant of the signature-`(2,3,n)` Frey curve: `c₄ = -144·b`.
(Note `c₄ = b₂² - 24·b₄` with `b₂ = 0`, `b₄ = 2·a₄ = 6·b`, so
`c₄ = -24·6·b = -144·b`.)

Together with `frey23_Δ`, the `j`-invariant is `j = c₄³ / Δ`, and the conductor of
the curve divides a quantity supported on `2`, `3` and the radical of `c` — the
inputs Ribet level-lowering would consume. -/
theorem frey23_c4 (a b : ℚ) : (frey23 a b).c₄ = -144 * b := by
  simp only [WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    frey23]
  ring

end BealFrey23
