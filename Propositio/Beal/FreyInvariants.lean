import Propositio.Beal.FreyGeneral
import Propositio.Beal.FreyCurve
import Propositio.Beal.Frey23
import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
import Mathlib.Tactic

/-!
# The `c₆` invariant and the universal `c₄³ − c₆² = 1728·Δ` relation (Lean 4 / mathlib)

This file **completes the Weierstrass invariant package**
`(b₂, b₄, b₆, b₈, c₄, c₆, Δ, j)` for the three Beal Frey–Hellegouarch curves of
this development:

* `BealFreyGeneral.freyG α β` — the general Frey curve
  `Y² = X·(X − α)·(X + β)` (`a₂ = β − α`, `a₄ = −α·β`);
* `BealFreyCurve.freyCurve A B` — the Kraus cube-sum curve
  `Y² = X³ + 3AB·X + (B³ − A³)`;
* `BealFrey23.frey23 a b` — the signature-`(2,3,n)` Mordell curve
  `Y² = X³ + 3b·X − 2a`.

`BealFreyGeneral`/`BealFreyCurve`/`BealFrey23` already record `Δ` and `c₄`. Here
we add the remaining invariant `c₆` in closed form, the full `b`-invariant
package `(b₂, b₄, b₆, b₈)`, and verify the **universal Weierstrass identity**

  `c₄³ − c₆² = 1728·Δ`,

which holds for *every* `WeierstrassCurve` (mathlib's `WeierstrassCurve.c_relation`,
stated `1728·Δ = c₄³ − c₆²`). For the Frey curves this is a consistency check on
the closed forms computed across `BealFreyGeneral`/`BealFreyJ`/`BealFreyReduction`:
the same invariants `(c₄, c₆, Δ, j = c₄³/Δ)` are the inputs to the reduction-type
and conductor analysis driving the modular method (Ribet level-lowering).

## House style

Follows `BealFreyCurve.lean`: a module doc-comment, per-theorem doc-comments, and
proofs that `simp` the `WeierstrassCurve` quantity definitions then `ring`.
Dependency policy: mathlib4 permitted. Use `lake env lean BealFreyInvariants.lean`
to typecheck.

Key mathlib API relied on:
* `WeierstrassCurve.c₆ = -b₂³ + 36·b₂·b₄ − 216·b₆`.
* `WeierstrassCurve.b₈` and `b₂, b₄, b₆`; for `a₁ = a₃ = 0`: `b₂ = 4·a₂`,
  `b₄ = 2·a₄`, `b₆ = 4·a₆`, `b₈ = 4·a₂·a₆ − a₄²`.
* `WeierstrassCurve.c_relation : 1728·Δ = c₄³ − c₆²` — the universal identity.
-/

namespace BealFreyInvariants

open WeierstrassCurve

/-! ## 1. The `c₆` invariant of the general Frey curve -/

/-- The `c₆` invariant of the general Frey curve `freyG α β`:
`c₆ = -64·(β − α)³ − 288·α·β·(β − α)`.

(Here `a₁ = a₃ = a₆ = 0`, `a₂ = β − α`, `a₄ = −α·β`, so `b₂ = 4·(β − α)`,
`b₄ = −2·α·β`, `b₆ = 0`, and `c₆ = -b₂³ + 36·b₂·b₄ − 216·b₆`.) -/
theorem freyG_c6 (α β : ℚ) :
    (BealFreyGeneral.freyG α β).c₆ =
      -64 * (β - α) ^ 3 - 288 * α * β * (β - α) := by
  simp only [WeierstrassCurve.c₆, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, BealFreyGeneral.freyG]
  ring

/-! ## 2. The `c₆` invariant of the Kraus and signature-`(2,3,n)` curves -/

/-- The `c₆` invariant of the Kraus cube-sum Frey curve `freyCurve A B`:
`c₆ = -864·(B³ − A³)`.

(Here `a₁ = a₂ = a₃ = 0`, `a₄ = 3AB`, `a₆ = B³ − A³`, so `b₂ = 0`,
`b₄ = 6AB`, `b₆ = 4·(B³ − A³)`, and `c₆ = -216·b₆ = -864·(B³ − A³)`.) -/
theorem freyCurve_c6 (A B : ℚ) :
    (BealFreyCurve.freyCurve A B).c₆ = -864 * (B ^ 3 - A ^ 3) := by
  simp only [WeierstrassCurve.c₆, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, BealFreyCurve.freyCurve]
  ring

/-- The `c₆` invariant of the signature-`(2,3,n)` Mordell Frey curve `frey23 a b`:
`c₆ = 1728·a`.

(Here `a₁ = a₂ = a₃ = 0`, `a₄ = 3b`, `a₆ = −2a`, so `b₂ = 0`, `b₄ = 6b`,
`b₆ = -8a`, and `c₆ = -216·b₆ = 1728·a`.) -/
theorem frey23_c6 (a b : ℚ) :
    (BealFrey23.frey23 a b).c₆ = 1728 * a := by
  simp only [WeierstrassCurve.c₆, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, BealFrey23.frey23]
  ring

/-! ## 3. The universal Weierstrass identity `c₄³ − c₆² = 1728·Δ`

mathlib's `WeierstrassCurve.c_relation` states `1728·Δ = c₄³ − c₆²` for every
Weierstrass curve. Each Frey curve is an instance, so the identity holds for all
of them; we record it explicitly as a consistency check on the closed forms. -/

/-- The universal Weierstrass identity for the general Frey curve:
`c₄³ − c₆² = 1728·Δ`. This is `WeierstrassCurve.c_relation` specialised to
`freyG α β`. -/
theorem freyG_c4_cubed_sub_c6_sq (α β : ℚ) :
    (BealFreyGeneral.freyG α β).c₄ ^ 3 - (BealFreyGeneral.freyG α β).c₆ ^ 2 =
      1728 * (BealFreyGeneral.freyG α β).Δ :=
  ((BealFreyGeneral.freyG α β).c_relation).symm

/-- The universal Weierstrass identity for the Kraus cube-sum Frey curve:
`c₄³ − c₆² = 1728·Δ`. -/
theorem freyCurve_c4_cubed_sub_c6_sq (A B : ℚ) :
    (BealFreyCurve.freyCurve A B).c₄ ^ 3 - (BealFreyCurve.freyCurve A B).c₆ ^ 2 =
      1728 * (BealFreyCurve.freyCurve A B).Δ :=
  ((BealFreyCurve.freyCurve A B).c_relation).symm

/-- The universal Weierstrass identity for the signature-`(2,3,n)` Frey curve:
`c₄³ − c₆² = 1728·Δ`. -/
theorem frey23_c4_cubed_sub_c6_sq (a b : ℚ) :
    (BealFrey23.frey23 a b).c₄ ^ 3 - (BealFrey23.frey23 a b).c₆ ^ 2 =
      1728 * (BealFrey23.frey23 a b).Δ :=
  ((BealFrey23.frey23 a b).c_relation).symm

/-! ## 4. The `b`-invariant package of the general Frey curve

For completeness/reference we record the full `(b₂, b₄, b₆, b₈)` package of the
general Frey curve; these are the building blocks of `c₄, c₆, Δ`. -/

/-- The `b`-invariant package of the general Frey curve `freyG α β`:
`b₂ = 4·(β − α)`, `b₄ = -2·α·β`, `b₆ = 0`, `b₈ = -α²·β²`.

(For `a₁ = a₃ = a₆ = 0`: `b₂ = 4·a₂`, `b₄ = 2·a₄`, `b₆ = 4·a₆ = 0`,
`b₈ = -a₄²`, with `a₂ = β − α`, `a₄ = −α·β`.) -/
theorem freyG_b_invariants (α β : ℚ) :
    (BealFreyGeneral.freyG α β).b₂ = 4 * (β - α) ∧
    (BealFreyGeneral.freyG α β).b₄ = -2 * α * β ∧
    (BealFreyGeneral.freyG α β).b₆ = 0 ∧
    (BealFreyGeneral.freyG α β).b₈ = -α ^ 2 * β ^ 2 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
      WeierstrassCurve.b₈, BealFreyGeneral.freyG] <;>
    ring

end BealFreyInvariants
