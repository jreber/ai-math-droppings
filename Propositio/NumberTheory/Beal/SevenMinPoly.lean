import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.Algebra.Polynomial.Eval.Irreducible
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.Data.ZMod.Basic
import Propositio.NumberTheory.Beal.SevenRealSubfield
import Mathlib.Tactic

/-!
# The minimal polynomial of the `ℚ(ζ₇)⁺` generator is `X³ + X² − 2X − 1`

Completes the `p = 7` real-subfield core (`BealSevenRealSubfield`) at the algebra level: the cubic
`X³ + X² − 2X − 1` is irreducible over `ℚ` (irreducible mod `2`, lifted by Gauss's lemma over the
integrally closed `ℤ`), so the period `η = ζ + ζ⁶` has `minpoly ℚ η = X³ + X² − 2X − 1` and
`[ℚ(ζ₇)⁺ : ℚ] = 3` — the cubic totally real field of the `(7,7,z)` reduction.
-/

open Polynomial

namespace BealSevenMinPoly

/-- The cubic `X³ + X² + 1` is irreducible over `𝔽₂` (no root in `ZMod 2`). -/
theorem cubic_irreducible_zmod2 : Irreducible (X ^ 3 + X ^ 2 + 1 : (ZMod 2)[X]) := by
  apply irreducible_of_degree_le_three_of_not_isRoot
  · have hdeg : (X ^ 3 + X ^ 2 + 1 : (ZMod 2)[X]).natDegree = 3 := by compute_degree!
    rw [hdeg]; decide
  · intro x
    rw [IsRoot, eval_add, eval_add, eval_pow, eval_pow, eval_X, eval_one]
    revert x; decide

/-- `X³ + X² − 2X − 1` is irreducible over `ℚ`: reduce mod `2` (to `X³ + X² + 1`, irreducible there),
lift to `ℤ` by `Monic.irreducible_of_irreducible_map`, then to `ℚ` by Gauss's lemma. -/
theorem seven_cubic_irreducible : Irreducible (X ^ 3 + X ^ 2 - 2 * X - 1 : ℚ[X]) := by
  have hmonZ : (X ^ 3 + X ^ 2 - 2 * X - 1 : ℤ[X]).Monic := by monicity!
  have hmapℚ : (X ^ 3 + X ^ 2 - 2 * X - 1 : ℤ[X]).map (algebraMap ℤ ℚ)
      = (X ^ 3 + X ^ 2 - 2 * X - 1 : ℚ[X]) := by
    simp only [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_mul,
      Polynomial.map_X, Polynomial.map_one, Polynomial.map_ofNat]
  rw [← hmapℚ, ← hmonZ.irreducible_iff_irreducible_map_fraction_map (K := ℚ)]
  have h20 : (2 : (ZMod 2)[X]) = 0 := by
    have h := CharP.cast_eq_zero ((ZMod 2)[X]) 2; simpa using h
  have hmap2 : (X ^ 3 + X ^ 2 - 2 * X - 1 : ℤ[X]).map (Int.castRingHom (ZMod 2))
      = (X ^ 3 + X ^ 2 + 1 : (ZMod 2)[X]) := by
    simp only [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_mul,
      Polynomial.map_X, Polynomial.map_one, Polynomial.map_ofNat]
    linear_combination (-(X + 1)) * h20
  have h_irr : Irreducible ((X ^ 3 + X ^ 2 - 2 * X - 1 : ℤ[X]).map (Int.castRingHom (ZMod 2))) := by
    rw [hmap2]; exact cubic_irreducible_zmod2
  exact Monic.irreducible_of_irreducible_map (Int.castRingHom (ZMod 2))
    (X ^ 3 + X ^ 2 - 2 * X - 1 : ℤ[X]) hmonZ h_irr

/-- **The minimal polynomial of a `ℚ(ζ₇)⁺` generator is `X³ + X² − 2X − 1`.** For any `y` with
`y³ + y² − 2y − 1 = 0` in a nontrivial `ℚ`-algebra, `minpoly ℚ y = X³ + X² − 2X − 1`. -/
theorem seven_minpoly {B : Type*} [CommRing B] [Algebra ℚ B] [Nontrivial B]
    {y : B} (hy : y ^ 3 + y ^ 2 - 2 * y - 1 = 0) : minpoly ℚ y = X ^ 3 + X ^ 2 - 2 * X - 1 := by
  refine (minpoly.eq_of_irreducible_of_monic seven_cubic_irreducible ?_ ?_).symm
  · simp only [map_sub, map_add, map_mul, map_pow, aeval_X, map_one, map_ofNat]; exact hy
  · monicity!

/-- **`minpoly ℚ (ζ + ζ⁶) = X³ + X² − 2X − 1`** in any char-`0` field with a primitive `7`-th root:
the concrete `[ℚ(ζ₇)⁺ : ℚ] = 3`. -/
theorem seven_minpoly_cyclotomic {K : Type*} [Field K] [Algebra ℚ K] {ζ : K}
    (hζ : IsPrimitiveRoot ζ 7) : minpoly ℚ (ζ + ζ ^ 6) = X ^ 3 + X ^ 2 - 2 * X - 1 :=
  seven_minpoly (BealSevenRealSubfield.seven_real_cubic hζ)

end BealSevenMinPoly
