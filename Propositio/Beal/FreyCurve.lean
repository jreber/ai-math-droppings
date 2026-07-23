import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
import Mathlib.Tactic

/-!
# The Kraus Frey curve for the Beal cube-sum case (Lean 4 / mathlib)

This file formalizes the **Frey–Hellegouarch elliptic curve** attached, following
Kraus (1998), to a putative primitive cube-sum Beal solution

  `A³ + B³ = C^z`,

and proves its discriminant in closed form. This is the concrete entry point to
the *modular method* for the cube-sum case of the Beal conjecture.

## The curve

For the cube-sum equation `A³ + B³ = C^z`, Kraus attaches the Weierstrass curve

  `E : Y² = X³ + 3·A·B·X + (B³ − A³)`,

i.e. the short Weierstrass form with `a₁ = a₂ = a₃ = 0`, `a₄ = 3·A·B`,
`a₆ = B³ − A³`. We realise it as a `WeierstrassCurve ℚ` (`freyCurve`).

## The discriminant

For a short Weierstrass curve `Y² = X³ + a₄·X + a₆`, mathlib's discriminant
convention (LMFDB sign) gives `Δ = -64·a₄³ - 432·a₆²`. Specialising to
`a₄ = 3AB`, `a₆ = B³ − A³`:

  `-64·(3AB)³ - 432·(B³−A³)² = -1728·A³B³ - 432·(B³−A³)²`
                            `= -432·(4A³B³ + (B³−A³)²)`
                            `= -432·(A³+B³)²`,

since `4·A³·B³ + (B³−A³)² = (A³+B³)²`. Hence

  `Δ = -432·(A³+B³)²` (`freyCurve_Δ`),

and substituting `A³+B³ = C^z` (`freyCurve_Δ_eq`),

  `Δ = -432·(C^z)² = -2⁴·3³·C^{2z}`.

So the discriminant is supported only at `2`, `3`, and the primes dividing `C`.
This support condition is precisely the input that the modular method consumes:

* **Modularity** (Wiles, Breuil–Conrad–Diamond–Taylor) attaches a weight-`2`
  newform to `E`;
* **Ribet level-lowering** strips the primes dividing `C` from the level, forcing
  a newform of small level that does not exist — a contradiction — for prime
  exponents `z ≥ 17` (Kraus 1998, "Sur l'équation a³ + b³ = c^p").

The modularity and level-lowering steps require the FLT-project infrastructure
that is **not** present in this mathlib snapshot; the curve and its discriminant
formalized here are the concrete, machine-checked groundwork.

## House style

Follows `BealEisenstein.lean`: a module doc-comment, per-theorem doc-comments,
and proofs that lean on mathlib (`simp` of the `WeierstrassCurve` quantity
definitions, then `ring`) rather than re-deriving arithmetic. Dependency policy:
mathlib4 permitted. Use `lake env lean BealFreyCurve.lean` to typecheck.

Key mathlib API relied on:
* `WeierstrassCurve R` — structure with fields `a₁ a₂ a₃ a₄ a₆`.
* `WeierstrassCurve.Δ` and the intermediates `b₂ b₄ b₆ b₈`, with
  `Δ = -b₂²·b₈ - 8·b₄³ - 27·b₆² + 9·b₂·b₄·b₆`.
* `WeierstrassCurve.c₄ = b₂² - 24·b₄`.
* `WeierstrassCurve.IsElliptic` — typeclass asserting `IsUnit Δ`.
-/

namespace BealFreyCurve

open WeierstrassCurve

/-! ## 1. The Frey curve -/

/-- The Kraus Frey curve `Y² = X³ + 3·A·B·X + (B³ − A³)` attached to the cube-sum
equation `A³ + B³ = C^z`. In short Weierstrass form: `a₁ = a₂ = a₃ = 0`,
`a₄ = 3·A·B`, `a₆ = B³ − A³`. -/
def freyCurve (A B : ℚ) : WeierstrassCurve ℚ :=
  { a₁ := 0, a₂ := 0, a₃ := 0, a₄ := 3 * A * B, a₆ := B ^ 3 - A ^ 3 }

/-! ## 2. The discriminant -/

/-- The discriminant of the Frey curve in closed form:
`Δ = -432·(A³ + B³)²`.

Proof: unfold the `b`-coefficients and `Δ` of a short Weierstrass curve and let
`ring` verify `-64·(3AB)³ - 432·(B³−A³)² = -432·(A³+B³)²`. -/
theorem freyCurve_Δ (A B : ℚ) : (freyCurve A B).Δ = -432 * (A ^ 3 + B ^ 3) ^ 2 := by
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈, freyCurve]
  ring

/-- **Headline.** Substituting the cube-sum hypothesis `A³ + B³ = C^z` into the
discriminant gives `Δ = -432·(C^z)²`. With `A³ + B³ = C^z`, the discriminant of
the Frey curve is

  `Δ = -432·(C^z)² = -2⁴·3³·C^{2z}`,

supported only at `2`, `3` and the primes dividing `C`. This is the start of the
modular method for the cube-sum Beal case. -/
theorem freyCurve_Δ_eq (A B C : ℚ) (z : ℕ) (h : A ^ 3 + B ^ 3 = C ^ z) :
    (freyCurve A B).Δ = -432 * (C ^ z) ^ 2 := by
  rw [freyCurve_Δ, h]

/-- The constant `-432` is `-2⁴·3³`, exhibiting the `Δ = -2⁴·3³·C^{2z}` form of
the Frey discriminant. -/
theorem neg_432_eq : (-432 : ℚ) = -2 ^ 4 * 3 ^ 3 := by norm_num

/-! ## 3. Non-degeneracy: a genuine elliptic curve when `A³ + B³ ≠ 0` -/

/-- The Frey curve is non-singular (its discriminant is nonzero) whenever
`A³ + B³ ≠ 0`. Equivalently, since `A³ + B³ = C^z` in the Beal setting, the curve
is a genuine elliptic curve as long as `C ≠ 0`. -/
theorem freyCurve_Δ_ne_zero (A B : ℚ) (hAB : A ^ 3 + B ^ 3 ≠ 0) :
    (freyCurve A B).Δ ≠ 0 := by
  rw [freyCurve_Δ]
  exact mul_ne_zero (by norm_num) (pow_ne_zero 2 hAB)

/-- The Frey curve, packaged with mathlib's `IsElliptic` instance, is a genuine
elliptic curve over `ℚ` whenever `A³ + B³ ≠ 0`: its discriminant is a unit
(every nonzero rational is a unit). -/
theorem freyCurve_isElliptic (A B : ℚ) (hAB : A ^ 3 + B ^ 3 ≠ 0) :
    (freyCurve A B).IsElliptic :=
  ⟨isUnit_iff_ne_zero.mpr (freyCurve_Δ_ne_zero A B hAB)⟩

/-! ## 4. The `c₄` invariant

The `c₄` invariant feeds the `j`-invariant `j = c₄³ / Δ` and the conductor /
level analysis that Ribet level-lowering consumes. For the Frey curve we record
its closed form. -/

/-- The `c₄` invariant of the Frey curve: `c₄ = -144·A·B`. (Note `c₄ = b₂² - 24·b₄`
with `b₂ = 0`, `b₄ = 2·a₄ = 6·A·B`, so `c₄ = -24·6·A·B = -144·A·B`.)

Together with `freyCurve_Δ`, the `j`-invariant is `j = c₄³ / Δ`, and the
conductor of the curve divides a quantity supported on `2`, `3` and the radical
of `C` — the inputs Ribet level-lowering would consume. -/
theorem freyCurve_c4 (A B : ℚ) : (freyCurve A B).c₄ = -144 * A * B := by
  simp only [WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    freyCurve]
  ring

end BealFreyCurve
