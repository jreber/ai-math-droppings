import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.NumberTheory.Real.Irrational
import Propositio.Beal.FiveRealSubfieldIso
import Mathlib.Tactic

/-!
# The minimal polynomial of the golden element is `X² + X − 1`

Completes the `ℚ(ζ₅)⁺ ≅ ℚ(√5)` field-iso wrapper (`BealFiveRealSubfieldIso`) at the algebra level:
the golden generator `η = ζ + ζ⁴` (and the golden ratio `φ = 1 + η`) has minimal polynomial
`X² + X − 1` over `ℚ`, an irreducible quadratic. Hence `ℚ(η)` is a degree-`2` extension — exactly
`ℚ(√5)` (`disc = 5`). This pins `[ℚ(ζ₅)⁺ : ℚ] = 2` and is the rigorous form of the identification.

* `not_isSquare_five_rat` — `5` is not a square in `ℚ` (via `Irrational √5`).
* `golden_poly_irreducible` — `Irreducible (X² + X − 1 : ℚ[X])` (degree 2, no rational root since a
  root `x` gives `(2x+1)² = 5`).
* `golden_minpoly` — for **any** `y` in a nontrivial `ℚ`-algebra with `y² + y − 1 = 0`,
  `minpoly ℚ y = X² + X − 1`. Applies to `η` and `φ − 1` in `ℚ(ζ₅)` (`golden_subfield_poly`).
-/

open Polynomial

namespace BealGoldenMinPoly

/-- **`5` is not a square in `ℚ`.** If `q² = 5` then `√5 = |q|` is rational, contradicting that
`√5` is irrational (`5` prime). -/
theorem not_isSquare_five_rat (q : ℚ) : q ^ 2 ≠ 5 := by
  intro h
  have hirr : Irrational (Real.sqrt 5) := by
    have h5 : Nat.Prime 5 := by norm_num
    simpa using h5.irrational_sqrt
  refine hirr ⟨|q|, ?_⟩
  have hq : ((q : ℝ)) ^ 2 = 5 := by exact_mod_cast h
  rw [Rat.cast_abs, ← Real.sqrt_sq_eq_abs, hq]

/-- **`X² + X − 1` is irreducible over `ℚ`.** A quadratic with no rational root: a root `x` would
give `(2x+1)² = 5`, impossible in `ℚ`. -/
theorem golden_poly_irreducible : Irreducible (X ^ 2 + X - 1 : ℚ[X]) := by
  apply irreducible_of_degree_le_three_of_not_isRoot
  · have hdeg : (X ^ 2 + X - 1 : ℚ[X]).natDegree = 2 := by compute_degree!
    rw [hdeg]; decide
  · intro x hx
    rw [IsRoot, eval_sub, eval_add, eval_pow, eval_X, eval_one] at hx
    exact not_isSquare_five_rat (2 * x + 1) (by linear_combination 4 * hx)

/-- **The minimal polynomial of a golden element is `X² + X − 1`.** For any `y` in a nontrivial
commutative `ℚ`-algebra with `y² + y − 1 = 0`, `minpoly ℚ y = X² + X − 1`. In particular the
golden ratio `φ = 1 + ζ + ζ⁴` and the real generator `η = ζ + ζ⁴` of `ℚ(ζ₅)` (via
`BealFiveRealSubfieldIso.golden_subfield_poly` / `golden_ratio_eq`) generate a degree-`2`
extension `ℚ(√5)`. -/
theorem golden_minpoly {B : Type*} [CommRing B] [Algebra ℚ B] [Nontrivial B]
    {y : B} (hy : y ^ 2 + y - 1 = 0) : minpoly ℚ y = X ^ 2 + X - 1 := by
  refine (minpoly.eq_of_irreducible_of_monic golden_poly_irreducible ?_ ?_).symm
  · rw [map_sub, map_add, map_pow, aeval_X, map_one]; exact hy
  · monicity!

/-- **Concrete cyclotomic minimal polynomial.** In any characteristic-`0` field `K` containing a
primitive `5`-th root of unity `ζ`, the real generator `η = ζ + ζ⁴` of the maximal real subfield has
`minpoly ℚ η = X² + X − 1`. Hence `[ℚ(ζ₅)⁺ : ℚ] = 2` and `ℚ(ζ₅)⁺ = ℚ(√5)` — the rigorous
identification underlying the Kummer `p = 5` reduction. -/
theorem golden_minpoly_cyclotomic {K : Type*} [Field K] [Algebra ℚ K] {ζ : K}
    (hζ : IsPrimitiveRoot ζ 5) : minpoly ℚ (ζ + ζ ^ 4) = X ^ 2 + X - 1 :=
  golden_minpoly (BealFiveRealSubfieldIso.golden_subfield_poly hζ)

/-! ## The golden ratio `φ = 1 + η` and its minimal polynomial `X² − X − 1`

`φ = (1 + √5)/2` is the fundamental unit of `ℚ(√5)`; its minimal polynomial is the golden equation
`X² − X − 1`. -/

/-- `X² − X − 1` is irreducible over `ℚ` (a root `x` gives `(2x−1)² = 5`, impossible in `ℚ`). -/
theorem golden_ratio_poly_irreducible : Irreducible (X ^ 2 - X - 1 : ℚ[X]) := by
  apply irreducible_of_degree_le_three_of_not_isRoot
  · have hdeg : (X ^ 2 - X - 1 : ℚ[X]).natDegree = 2 := by compute_degree!
    rw [hdeg]; decide
  · intro x hx
    rw [IsRoot, eval_sub, eval_sub, eval_pow, eval_X, eval_one] at hx
    exact not_isSquare_five_rat (2 * x - 1) (by linear_combination 4 * hx)

/-- **The minimal polynomial of the golden ratio is `X² − X − 1`.** For any `y` with `y² − y − 1 = 0`
in a nontrivial `ℚ`-algebra, `minpoly ℚ y = X² − X − 1`. -/
theorem golden_ratio_minpoly {B : Type*} [CommRing B] [Algebra ℚ B] [Nontrivial B]
    {y : B} (hy : y ^ 2 - y - 1 = 0) : minpoly ℚ y = X ^ 2 - X - 1 := by
  refine (minpoly.eq_of_irreducible_of_monic golden_ratio_poly_irreducible ?_ ?_).symm
  · rw [map_sub, map_sub, map_pow, aeval_X, map_one]; exact hy
  · monicity!

/-- **The cyclotomic golden ratio `φ = 1 + ζ + ζ⁴` has `minpoly ℚ φ = X² − X − 1`** — the golden
equation, realized inside `ℚ(ζ₅)`. The fundamental unit of `ℚ(ζ₅)⁺ = ℚ(√5)`. -/
theorem golden_ratio_minpoly_cyclotomic {K : Type*} [Field K] [Algebra ℚ K] {ζ : K}
    (hζ : IsPrimitiveRoot ζ 5) : minpoly ℚ (1 + ζ + ζ ^ 4) = X ^ 2 - X - 1 :=
  golden_ratio_minpoly (BealFiveRealSubfieldIso.golden_ratio_eq hζ)

end BealGoldenMinPoly
