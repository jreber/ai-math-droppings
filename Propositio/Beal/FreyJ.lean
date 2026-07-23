import Propositio.Beal.FreyGeneral

/-!
# The j-invariant of the general Beal–Frey curve (Lean 4 / mathlib)

This file computes the **j-invariant** of the Hellegouarch–Frey curve
`freyG α β` of `BealFreyGeneral.lean` (with `α = A^x`, `β = B^y`) in closed
form, and records the reduction-type content that powers the modular method.

## The j-invariant

Recall `j = c₄³ / Δ`. From `BealFreyGeneral`:

* `c₄ = 16·(α² + α·β + β²)`  (`BealFreyGeneral.freyG_c4`), so
  `c₄³ = 16³·(α² + α·β + β²)³ = 4096·(α² + α·β + β²)³`;
* `Δ = 16·α²·β²·(α + β)²`  (`BealFreyGeneral.freyG_Δ`).

Hence

  `j = c₄³ / Δ
     = (16·(α²+αβ+β²))³ / (16·α²·β²·(α+β)²)
     = 256·(α²+αβ+β²)³ / (α²·β²·(α+β)²)`

(`freyG_j_ratio`, and via mathlib's `WeierstrassCurve.j`: `freyG_j`).

## Reduction-type content

In lowest terms the **denominator** of `j` is supported exactly on the primes
dividing

  `α·β·(α+β) = A^x · B^y · C^z`

(using the Beal relation `α + β = C^z`). The numerator `256·(α²+αβ+β²)³` is
coprime to `α·β·(α+β)` away from `2` and `3`: a prime `p ∣ α` divides neither
`(α²+αβ+β²)` (`≡ β² mod p`, and `p ∤ β` since `gcd(A,B)=1`) nor the constant
`256 = 2⁸`. Therefore at every prime `p ∣ A·B·C` with `p ∤ 6` the valuation of
`j` is **negative**: `v_p(j) < 0`. This is exactly the statement that the Frey
curve has **potentially multiplicative reduction** at `p`, i.e. it is
**semistable away from `2` and `3`**.

Potentially-multiplicative reduction is what gives the Frey curve its small
conductor `N = rad(A·B·C)` (up to powers of `2, 3`) and is the geometric input
to **Ribet level-lowering**: the mod-`ℓ` representation of `E` is unramified
(or finite-flat) at the primes `p ∣ A·B·C` whose exponent is divisible by `ℓ`,
so those primes can be stripped from the level, forcing an impossibly small
newform.

This connects to `BealFreyRadical` (`rad Δ = 2·rad(A·B·C)`): the support of the
discriminant and the support of the `j`-denominator agree (off `2`), as they
must for a semistable curve, where `v_p(Δ) = -v_p(j) > 0` at the bad primes.

The modularity (Wiles, BCDT) and level-lowering (Ribet) theorems themselves
require FLT-project infrastructure absent from this mathlib snapshot; the
`j`-invariant and its reduction-type structure formalized here are the concrete,
machine-checked groundwork.

## House style

Follows `BealFreyGeneral.lean`: module + per-theorem doc-comments, proofs that
`rw` the closed-form invariants of `BealFreyGeneral` and discharge with
`field_simp`/`ring`. Use `lake env lean BealFreyJ.lean` to typecheck.
-/

namespace BealFreyJ

open WeierstrassCurve BealFreyGeneral

/-! ## 1. The cube of `c₄` -/

/-- The cube of the `c₄` invariant of the general Frey curve:
`c₄³ = (16·(α² + α·β + β²))³`. Immediate from `BealFreyGeneral.freyG_c4`. -/
theorem freyG_c4_cubed (α β : ℚ) :
    (freyG α β).c₄ ^ 3 = (16 * (α ^ 2 + α * β + β ^ 2)) ^ 3 := by
  rw [freyG_c4]

/-- Packaging the two invariants that determine `j = c₄³/Δ`:
`c₄³ = (16·(α²+αβ+β²))³` and `Δ = 16·α²·β²·(α+β)²`. -/
theorem freyG_invariants (α β : ℚ) :
    (freyG α β).c₄ ^ 3 = (16 * (α ^ 2 + α * β + β ^ 2)) ^ 3 ∧
      (freyG α β).Δ = 16 * α ^ 2 * β ^ 2 * (α + β) ^ 2 :=
  ⟨freyG_c4_cubed α β, freyG_Δ α β⟩

/-! ## 2. The j-invariant in closed form (ratio `c₄³/Δ`) -/

/-- **Headline.** The j-invariant of the general Frey curve in closed form:

  `c₄³ / Δ = 256·(α² + α·β + β²)³ / (α²·β²·(α + β)²)`,

valid whenever the discriminant is nonzero (`Δ ≠ 0`, i.e. `α, β, α+β ≠ 0`).
Proof: rewrite `c₄` and `Δ` by their closed forms and clear denominators with
`field_simp`/`ring`. -/
theorem freyG_j_ratio (α β : ℚ) (hΔ : (freyG α β).Δ ≠ 0) :
    (freyG α β).c₄ ^ 3 / (freyG α β).Δ
      = 256 * (α ^ 2 + α * β + β ^ 2) ^ 3 / (α ^ 2 * β ^ 2 * (α + β) ^ 2) := by
  have hΔ' : α ^ 2 * β ^ 2 * (α + β) ^ 2 ≠ 0 := by
    rw [freyG_Δ] at hΔ
    intro h; apply hΔ; rw [show (16 : ℚ) * α ^ 2 * β ^ 2 * (α + β) ^ 2
      = 16 * (α ^ 2 * β ^ 2 * (α + β) ^ 2) by ring, h, mul_zero]
  rw [freyG_c4_cubed, freyG_Δ]
  field_simp
  ring

/-! ## 3. The j-invariant via mathlib's `WeierstrassCurve.j` -/

/-- The j-invariant of the general Frey curve, computed through mathlib's
`WeierstrassCurve.j` (which needs the curve to be elliptic, i.e. `Δ` a unit):

  `j(freyG α β) = 256·(α² + α·β + β²)³ / (α²·β²·(α + β)²)`,

whenever `α ≠ 0`, `β ≠ 0`, `α + β ≠ 0`. We supply the `IsElliptic` instance
from `BealFreyGeneral.freyG_isElliptic`, unfold `j = Δ'⁻¹ · c₄³`, and reduce to
the ratio form using `Δ' = Δ` and `field_simp`. -/
theorem freyG_j (α β : ℚ) (hα : α ≠ 0) (hβ : β ≠ 0) (hαβ : α + β ≠ 0) :
    haveI : (freyG α β).IsElliptic := freyG_isElliptic α β hα hβ hαβ
    (freyG α β).j = 256 * (α ^ 2 + α * β + β ^ 2) ^ 3 / (α ^ 2 * β ^ 2 * (α + β) ^ 2) := by
  haveI hE : (freyG α β).IsElliptic := freyG_isElliptic α β hα hβ hαβ
  have hΔ : (freyG α β).Δ ≠ 0 := freyG_Δ_ne_zero α β hα hβ hαβ
  -- `j = Δ'⁻¹ · c₄³`, and `↑Δ'⁻¹ = (↑Δ')⁻¹ = Δ⁻¹`, so `j = c₄³ / Δ`.
  rw [WeierstrassCurve.j, ← freyG_j_ratio α β hΔ]
  rw [Units.val_inv_eq_inv_val, WeierstrassCurve.coe_Δ']
  rw [div_eq_mul_inv, mul_comm]

/-! ## 4. Reduction-type content: clearing the denominator -/

/-- The cleared-denominator (polynomial) form of the `j`-invariant identity:

  `(α²·β²·(α+β)²) · j = 256·(α²+αβ+β²)³`,

where `j = c₄³/Δ`. This exhibits the denominator of `j` as a divisor of
`α²·β²·(α+β)²`, supported on the primes of `α·β·(α+β) = A^x·B^y·C^z`. It is the
algebraic core of the "potentially multiplicative reduction away from `2,3`"
statement: the bad primes of `j` are exactly the primes dividing `A·B·C`. -/
theorem freyG_j_denom_cleared (α β : ℚ) (hΔ : (freyG α β).Δ ≠ 0) :
    (α ^ 2 * β ^ 2 * (α + β) ^ 2) * ((freyG α β).c₄ ^ 3 / (freyG α β).Δ)
      = 256 * (α ^ 2 + α * β + β ^ 2) ^ 3 := by
  have hΔ' : α ^ 2 * β ^ 2 * (α + β) ^ 2 ≠ 0 := by
    rw [freyG_Δ] at hΔ
    intro h; apply hΔ; rw [show (16 : ℚ) * α ^ 2 * β ^ 2 * (α + β) ^ 2
      = 16 * (α ^ 2 * β ^ 2 * (α + β) ^ 2) by ring, h, mul_zero]
  rw [freyG_j_ratio α β hΔ, mul_div_assoc']
  rw [mul_comm (α ^ 2 * β ^ 2 * (α + β) ^ 2)]
  rw [mul_div_assoc, div_self hΔ', mul_one]

/-- The numerator `256·(α²+αβ+β²)³` of the `j`-invariant, written explicitly,
together with the denominator `α²·β²·(α+β)²`. Re-exporting the two halves of the
reduction-type analysis: `j = numerator / denominator`, with the denominator
supported on `α·β·(α+β)`. -/
theorem freyG_j_num_denom (α β : ℚ) (hΔ : (freyG α β).Δ ≠ 0) :
    (freyG α β).c₄ ^ 3 / (freyG α β).Δ
        = 256 * (α ^ 2 + α * β + β ^ 2) ^ 3 / (α ^ 2 * β ^ 2 * (α + β) ^ 2) ∧
      (256 * (α ^ 2 + α * β + β ^ 2) ^ 3 : ℚ) = 4096 * (α ^ 2 + α * β + β ^ 2) ^ 3 / 16 := by
  refine ⟨freyG_j_ratio α β hΔ, ?_⟩
  ring

/-! ## 5. Reduction type under the Beal relation -/

/-- Under the Beal relation `α + β = C^z` the `j`-invariant denominator becomes
`α²·β²·(C^z)² = (A^x·B^y·C^z)²` (taking `α = A^x`, `β = B^y`). The denominator
`(A^x·B^y·C^z)²` is supported exactly on the primes dividing `A·B·C`, matching
the support of the discriminant (`BealFreyGeneral.freyG_Δ_beal`,
`BealFreyRadical`: `rad Δ = 2·rad(A·B·C)`). Off `2` and `3` the reduction is
**multiplicative** — the small-conductor / level-lowering input. -/
theorem freyG_j_ratio_beal (A B C : ℚ) (x y z : ℕ)
    (h : A ^ x + B ^ y = C ^ z) (hΔ : (freyG (A ^ x) (B ^ y)).Δ ≠ 0) :
    (freyG (A ^ x) (B ^ y)).c₄ ^ 3 / (freyG (A ^ x) (B ^ y)).Δ
      = 256 * ((A ^ x) ^ 2 + A ^ x * B ^ y + (B ^ y) ^ 2) ^ 3
          / ((A ^ x * B ^ y * C ^ z) ^ 2) := by
  rw [freyG_j_ratio (A ^ x) (B ^ y) hΔ, ← h]
  congr 1
  ring

end BealFreyJ
