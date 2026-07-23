import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
import Mathlib.Tactic

/-!
# The general Hellegouarch–Frey curve for the Beal equation (Lean 4 / mathlib)

This file formalizes the **Hellegouarch–Frey elliptic curve** attached to a
putative Beal solution

  `A^x + B^y = C^z`

in its full generality (all signatures), and proves its discriminant in closed
form. This generalizes the cube-specific Kraus curve of `BealFreyCurve.lean`
(`Y² = X³ + 3·A·B·X + (B³ − A³)`) to the standard Frey model with prescribed
2-torsion.

## The curve

Write `α = A^x` and `β = B^y`, so the Beal equation reads `α + β = C^z`. The Frey
curve is the curve whose 2-torsion sits at `0, α, −β`:

  `E : Y² = X·(X − α)·(X + β) = X³ + (β − α)·X² − α·β·X`.

As a `WeierstrassCurve`: `a₁ = 0`, `a₂ = β − α`, `a₃ = 0`, `a₄ = −α·β`,
`a₆ = 0` (`freyG`).

## The discriminant

For a model `Y² = X·(X − e₁)·(X − e₂)·(X − e₃)` the discriminant is
`Δ = 16·∏_{i<j}(eᵢ − eⱼ)²`. With roots `0, α, −β` this gives

  `Δ = 16·(α − 0)²·(−β − 0)²·(−β − α)² = 16·α²·β²·(α + β)²`  (`freyG_Δ`).

mathlib's `WeierstrassCurve.Δ` (built from `b₂, b₄, b₆, b₈`) reproduces exactly
this value — the sign convention agrees, and the constant comes out `+16`.
Substituting the Beal hypothesis `α + β = C^z`:

  `Δ = 16·α²·β²·(C^z)² = 16·(α·β·C^z)² = 16·(A^x·B^y·C^z)²`  (`freyG_Δ_beal`).

So `rad(Δ) = 2·rad(A·B·C)`: the discriminant is supported only at `2` and the
primes dividing `A·B·C`. This support condition is precisely the input the
modular method consumes:

* **Modularity** (Wiles, Breuil–Conrad–Diamond–Taylor) attaches a weight-`2`
  newform to `E`;
* **Ribet level-lowering** strips the primes dividing `A·B·C` from the level,
  forcing a newform of impossibly small level — a contradiction for suitable
  prime exponents.

The modularity and level-lowering steps require FLT-project infrastructure that
is **not** present in this mathlib snapshot; the curve and its discriminant
formalized here are the concrete, machine-checked groundwork.

## House style

Follows `BealFreyCurve.lean` / `BealEisenstein.lean`: a module doc-comment,
per-theorem doc-comments, and proofs that lean on mathlib (`simp` of the
`WeierstrassCurve` quantity definitions, then `ring`). Dependency policy:
mathlib4 permitted. Use `lake env lean BealFreyGeneral.lean` to typecheck.

Key mathlib API relied on:
* `WeierstrassCurve R` — structure with fields `a₁ a₂ a₃ a₄ a₆`.
* `WeierstrassCurve.Δ` and the intermediates `b₂ b₄ b₆ b₈`.
* `WeierstrassCurve.c₄ = b₂² - 24·b₄`.
* `WeierstrassCurve.IsElliptic` — typeclass asserting `IsUnit Δ`.
-/

namespace BealFreyGeneral

open WeierstrassCurve

/-! ## 1. The general Frey curve -/

/-- The Hellegouarch–Frey curve `Y² = X·(X − α)·(X + β) = X³ + (β − α)·X² − α·β·X`
attached to a Beal solution with `α = A^x`, `β = B^y`. In Weierstrass form:
`a₁ = 0`, `a₂ = β − α`, `a₃ = 0`, `a₄ = −α·β`, `a₆ = 0`. Its 2-torsion sits at
`0, α, −β`. -/
def freyG (α β : ℚ) : WeierstrassCurve ℚ :=
  { a₁ := 0, a₂ := β - α, a₃ := 0, a₄ := -(α * β), a₆ := 0 }

/-! ## 2. The discriminant -/

/-- The discriminant of the general Frey curve in closed form:
`Δ = 16·α²·β²·(α + β)²`.

Proof: unfold the `b`-coefficients and `Δ` and let `ring` verify the identity.
This confirms that mathlib's `Δ` convention reproduces the classical
`Δ = 16·∏(eᵢ − eⱼ)²` for roots `0, α, −β`, with constant `+16`. -/
theorem freyG_Δ (α β : ℚ) : (freyG α β).Δ = 16 * α ^ 2 * β ^ 2 * (α + β) ^ 2 := by
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈, freyG]
  ring

/-- **Headline.** For a Beal solution `A^x + B^y = C^z`, the discriminant of the
Frey curve `freyG (A^x) (B^y)` is

  `Δ = 16·(A^x · B^y · C^z)²`,

supported only at `2` and the primes dividing `A·B·C` (so `rad(Δ) = 2·rad(ABC)`).
This is the concrete starting point of the modular attack on the general Beal
equation. -/
theorem freyG_Δ_beal (A B C : ℚ) (x y z : ℕ) (h : A ^ x + B ^ y = C ^ z) :
    (freyG (A ^ x) (B ^ y)).Δ = 16 * (A ^ x * B ^ y * C ^ z) ^ 2 := by
  rw [freyG_Δ, h]
  ring

/-- The constant `16` is `2⁴`, exhibiting `Δ = 2⁴·(A^x·B^y·C^z)²` and hence
`rad(Δ) = 2·rad(A·B·C)`. -/
theorem sixteen_eq : (16 : ℚ) = 2 ^ 4 := by norm_num

/-! ## 3. The `c₄` invariant

The `c₄` invariant feeds the `j`-invariant `j = c₄³ / Δ` and the conductor /
level analysis that Ribet level-lowering consumes. -/

/-- The `c₄` invariant of the general Frey curve: `c₄ = 16·(α² + α·β + β²)`.
(Note `c₄ = b₂² − 24·b₄` with `b₂ = 4·a₂ = 4·(β − α)` and `b₄ = 2·a₄ = −2·α·β`,
so `c₄ = 16·(β − α)² + 48·α·β = 16·(α² + α·β + β²)`.) -/
theorem freyG_c4 (α β : ℚ) :
    (freyG α β).c₄ = 16 * (α ^ 2 + α * β + β ^ 2) := by
  simp only [WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    freyG]
  ring

/-! ## 4. Non-degeneracy: a genuine elliptic curve -/

/-- The general Frey curve is non-singular (its discriminant is nonzero) whenever
`α ≠ 0`, `β ≠ 0` and `α + β ≠ 0`. In the Beal setting `α = A^x`, `β = B^y`,
`α + β = C^z`, so this holds as long as `A, B, C` are nonzero. -/
theorem freyG_Δ_ne_zero (α β : ℚ) (hα : α ≠ 0) (hβ : β ≠ 0) (hαβ : α + β ≠ 0) :
    (freyG α β).Δ ≠ 0 := by
  rw [freyG_Δ]
  exact mul_ne_zero
    (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hα)) (pow_ne_zero 2 hβ))
    (pow_ne_zero 2 hαβ)

/-- The general Frey curve, packaged with mathlib's `IsElliptic` instance, is a
genuine elliptic curve over `ℚ` whenever `α ≠ 0`, `β ≠ 0` and `α + β ≠ 0`: its
discriminant is a unit (every nonzero rational is a unit). -/
theorem freyG_isElliptic (α β : ℚ) (hα : α ≠ 0) (hβ : β ≠ 0) (hαβ : α + β ≠ 0) :
    (freyG α β).IsElliptic :=
  ⟨isUnit_iff_ne_zero.mpr (freyG_Δ_ne_zero α β hα hβ hαβ)⟩

end BealFreyGeneral
