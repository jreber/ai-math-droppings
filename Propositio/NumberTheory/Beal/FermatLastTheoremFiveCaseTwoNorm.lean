import Propositio.NumberTheory.Beal.FermatLastTheoremFiveCaseTwo
import Propositio.NumberTheory.Beal.FundamentalUnitPell
import Mathlib.Tactic

/-!
# Fermat's Last Theorem for exponent 5, Case II — the ring identity + norm factorization

`FermatLastTheoremFiveCaseTwo.lean` proves the classical `5`-adic factorization step of Case
II: given pairwise coprime `x, y, z` with `x^5+y^5=z^5` and `5 ∣ z`, either
`x + y = 5·d⁵` and `Φ(x,y) = 5^(5n+4)·e⁵`, or the mirror, where
`Φ(x,y) = x⁴ - x³y + x²y² - xy³ + y⁴` is the quartic cofactor of `x⁵+y⁵ = (x+y)·Φ(x,y)`.

The genuinely hard remaining content of Case II (Legendre's 1825 contribution) is transplanting
this factorization into the ring of integers of `ℚ(√5)` (the golden-ratio ring `ℤ[φ]`, whose
fundamental-unit theory is built in `BealFundamentalUnitPell.lean`) and pinning the resulting
unit to construct a strictly smaller solution. Per the scoping note left in
`docs/kb/failed/2026-07-12__fermatLastTheoremFive_caseTwo_descent.json`, that full descent does
**not** converge in one shot; this file lands the first two of the three recommended sub-bricks:

1. `case2_difference_of_squares_identity` — the classical ring identity
   `4·Φ(x,y) = 5·(x²+y²)² − (x+y)⁴` (pure `ring`).
2. `case2_phi_eq_neg_norm` / `case2_phi_eq_neg_real_norm` / `case2_phi_factorization` — the
   **norm factorization of `Φ(x,y)` over the concrete `a + b·φ` model** already used in
   `BealFundamentalUnitPell.lean` (we do **not** construct `ℚ(√5)` as an abstract `NumberField`
   / `RingOfIntegers` — we reuse the same `(a, b) ↦ a + b·φ ∈ ℝ` representation directly, exactly
   as instructed). Concretely, writing `a₁ := -(x² + xy + y²)`, `a₂ := xy`, `b := x² + y²`:
   * `case2_phi_eq_neg_norm`: the **integer** identity `a₁² + a₁b − b² = −Φ(x,y)`, i.e. `Φ(x,y)`
     is (minus) the field norm `N(a₁ + b·φ) = (a₁+bφ)(a₁+bψ)` in the `(a,b)`-coordinates of
     `BealFundamentalUnitPell.norm_form_identity`.
   * `case2_phi_eq_neg_real_norm`: the same fact transported to `ℝ` via `norm_form_identity`
     directly, exhibiting `Φ(x,y)` as `−(a₁+bφ)(a₁+bψ)`.
   * `case2_phi_factorization`: the sharper, self-contained fact that `Φ(x,y)` is *literally* the
     product `(a₁ + b·φ)·(a₂ + b·φ)` of two elements of `ℤ[φ]` sharing the same `b`-coordinate
     (the `φ`-terms cancel because `a₁ + a₂ + b = 0` identically — the key structural
     coincidence that makes this a *rational* product at all, proved via `φ² = φ + 1`).
   * `case2_sqrt5_factor_left` / `case2_sqrt5_factor_right` connect the two forms: they show the
     two factors of the ring identity's `5·(x²+y²)² − (x+y)⁴ = (√5·(x²+y²) − (x+y)²)·(√5·(x²+y²)
     + (x+y)²)` splitting are, up to the constant `2`, exactly `a₁ + b·φ` and `a₂ + b·φ` (using
     `√5 = 2φ − 1`, `BealFundamentalUnitPell.two_phi_sub_one`) — i.e. this file's two norm-form
     lemmas are genuinely *the same fact* as the ring identity, just repackaged through `φ`.

## What is NOT proved here (honest scope note)

Step 3 — pinning the unit via `BealFundamentalUnitPell.beal_fundamental_unit_sqrt5` (every unit
of `ℤ[φ]` is `±φⁿ`) and constructing a strictly smaller solution to close the infinite descent —
is **not attempted** in this file. That requires genuine unique-factorization / GCD-domain
structure on the concrete `a + b·φ` model (e.g. that `5 = ±N(2φ−1)` can be "divided out" of
`N(a₁+bφ) = ∓5^k·e⁵` and the residual cofactor pinned as a fifth power up to a unit), which is
not established anywhere in this repository — `BealFundamentalUnitPell.lean` only proves real
number identities about `φ` and the unit group, not a divisibility/GCD theory for the subring it
generates. Building that divisibility theory (or an alternative that avoids it) is future work.

**No `sorry`, no project axiom** in what follows.
-/

namespace FermatLastTheoremFiveCaseTwoNorm

open Real BealFundamentalUnitPell

/-- **Step 1: the classical ring identity.** `4·Φ(x,y) = 5·(x²+y²)² − (x+y)⁴`, where
`Φ(x,y) = x⁴ - x³y + x²y² - xy³ + y⁴` is the quartic cofactor from `x⁵+y⁵ = (x+y)·Φ(x,y)`.
Pure polynomial identity, verified by hand before formalizing:
`4Φ = 4x⁴-4x³y+4x²y²-4xy³+4y⁴` and `5(x²+y²)² - (x+y)⁴
  = (5x⁴+10x²y²+5y⁴) - (x⁴+4x³y+6x²y²+4xy³+y⁴) = 4x⁴-4x³y+4x²y²-4xy³+4y⁴`. -/
theorem case2_difference_of_squares_identity (x y : ℤ) :
    4 * (x ^ 4 - x ^ 3 * y + x ^ 2 * y ^ 2 - x * y ^ 3 + y ^ 4) =
      5 * (x ^ 2 + y ^ 2) ^ 2 - (x + y) ^ 4 := by
  ring

/-- **Step 2, integer norm identity.** With `a₁ := -(x²+xy+y²)` and `b := x²+y²`,
`a₁² + a₁·b − b² = −Φ(x,y)`. In `BealFundamentalUnitPell.norm_form_identity`'s coordinates,
this says `Φ(x,y)` is minus the field norm `N(a₁ + b·φ)`. Pure `ring`. -/
theorem case2_phi_eq_neg_norm (x y : ℤ) :
    (-(x ^ 2 + x * y + y ^ 2)) ^ 2 + (-(x ^ 2 + x * y + y ^ 2)) * (x ^ 2 + y ^ 2)
        - (x ^ 2 + y ^ 2) ^ 2
      = -(x ^ 4 - x ^ 3 * y + x ^ 2 * y ^ 2 - x * y ^ 3 + y ^ 4) := by
  ring

/-- **Step 2, real norm form.** Transporting `case2_phi_eq_neg_norm` to `ℝ` via
`BealFundamentalUnitPell.norm_form_identity`: `Φ(x,y)` equals `−(a₁+b·φ)(a₁+b·ψ)`, the *field
norm* of `a₁ + b·φ ∈ ℤ[φ]` in the concrete `a + b·φ ∈ ℝ` model, negated. -/
theorem case2_phi_eq_neg_real_norm (x y : ℤ) :
    (((-(x ^ 2 + x * y + y ^ 2) : ℤ) : ℝ) + ((x ^ 2 + y ^ 2 : ℤ) : ℝ) * goldenRatio) *
      (((-(x ^ 2 + x * y + y ^ 2) : ℤ) : ℝ) + ((x ^ 2 + y ^ 2 : ℤ) : ℝ) * goldenConj) =
      -(((x ^ 4 - x ^ 3 * y + x ^ 2 * y ^ 2 - x * y ^ 3 + y ^ 4 : ℤ) : ℝ)) := by
  rw [norm_form_identity, case2_phi_eq_neg_norm]
  push_cast
  ring

/-- **Step 2, sharper direct factorization.** `Φ(x,y)` is *literally* the product
`(a₁ + b·φ)·(a₂ + b·φ)` of two elements of `ℤ[φ]` sharing the same `b`-coordinate `b = x²+y²`,
with `a₁ = -(x²+xy+y²)` and `a₂ = xy`. The `φ`-terms cancel because `a₁ + a₂ + b = 0` identically
(the key structural fact making this product rational at all): expanding
`(a₁+bφ)(a₂+bφ) = a₁a₂ + (a₁+a₂)bφ + b²φ²` and using `φ² = φ+1` gives
`a₁a₂ + b² + bφ(a₁+a₂+b) = a₁a₂+b²` since `a₁+a₂+b=0`, which equals `Φ(x,y)`. -/
theorem case2_phi_factorization (x y : ℤ) :
    (((-(x ^ 2 + x * y + y ^ 2) : ℤ) : ℝ) + ((x ^ 2 + y ^ 2 : ℤ) : ℝ) * goldenRatio) *
      (((x * y : ℤ) : ℝ) + ((x ^ 2 + y ^ 2 : ℤ) : ℝ) * goldenRatio) =
      ((x ^ 4 - x ^ 3 * y + x ^ 2 * y ^ 2 - x * y ^ 3 + y ^ 4 : ℤ) : ℝ) := by
  have hsq : goldenRatio ^ 2 = goldenRatio + 1 := goldenRatio_sq
  push_cast
  linear_combination ((x : ℝ) ^ 2 + (y : ℝ) ^ 2) ^ 2 * hsq

/-- **Bridge, left factor.** The left factor `√5·(x²+y²) − (x+y)²` of the difference-of-squares
identity equals `2·(a₁ + b·φ)` (using `√5 = 2φ−1`), tying `case2_difference_of_squares_identity`
directly to the `φ`-coordinates of `case2_phi_factorization`. -/
theorem case2_sqrt5_factor_left (x y : ℤ) :
    Real.sqrt 5 * ((x : ℝ) ^ 2 + (y : ℝ) ^ 2) - ((x : ℝ) + (y : ℝ)) ^ 2 =
      2 * (((-(x ^ 2 + x * y + y ^ 2) : ℤ) : ℝ) + ((x ^ 2 + y ^ 2 : ℤ) : ℝ) * goldenRatio) := by
  rw [← two_phi_sub_one]
  push_cast
  ring

/-- **Bridge, right factor.** The right factor `√5·(x²+y²) + (x+y)²` equals `2·(a₂ + b·φ)`. -/
theorem case2_sqrt5_factor_right (x y : ℤ) :
    Real.sqrt 5 * ((x : ℝ) ^ 2 + (y : ℝ) ^ 2) + ((x : ℝ) + (y : ℝ)) ^ 2 =
      2 * (((x * y : ℤ) : ℝ) + ((x ^ 2 + y ^ 2 : ℤ) : ℝ) * goldenRatio) := by
  rw [← two_phi_sub_one]
  push_cast
  ring

end FermatLastTheoremFiveCaseTwoNorm
