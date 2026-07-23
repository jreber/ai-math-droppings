import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Discriminant
import Mathlib.RingTheory.Polynomial.Eisenstein.IsIntegral
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.RingTheory.Trace.Basic
import Mathlib.RingTheory.Norm.Basic
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Tactic
import Propositio.Beal.FiveRealSubfieldIso
import Propositio.Beal.GoldenMinPoly
import Propositio.Beal.LambdaCongruence

/-!
# Ring of Integers Basis for K⁺ = ℚ(ζ₅)⁺

This file proves the ring-of-integers basis theorem for K⁺ (the maximal real
subfield of the 5th cyclotomic field), using the Eisenstein/discriminant method.

## Key results
- `eta0_poly_of_golden` : algebraic identity η₀ = ζ+ζ⁴−2 satisfies x²+5x+5=0
- `eta0_poly_cyclotomic` : same for the actual ζ+ζ⁴ in a primitive root ring
- `eta0Poly_isEisenstein` : x²+5x+5 is Eisenstein at the prime ⟨5⟩ of ℤ
- `descent_congruence` : a+b(ζ+ζ⁴)−(a+2b) = (1−ζ)²·(b·ζ⁴) for integers a,b
- `integralElements_in_adjoin` : every ℤ-integral element of L lies in ℤ[η₀]
-/

-- safe-lean.sh bounds wall-clock via systemd scope; 0 = no per-declaration limit
set_option maxHeartbeats 0

open Polynomial
namespace BealRingOfIntegersBasisKPlus

/-! ## Section 1: Algebraic identities -/

/-- The substitution η₀ = y−2 sends solutions of y²+y−1=0 to solutions of x²+5x+5=0. -/
theorem eta0_poly_of_golden {R : Type*} [CommRing R] {y : R} (hy : y ^ 2 + y - 1 = 0) :
    (y - 2) ^ 2 + 5 * (y - 2) + 5 = 0 := by linear_combination hy

/-- For ζ a primitive 5th root of unity in a field K, η₀ = ζ+ζ⁴−2 satisfies x²+5x+5=0.
    Requires Field K because BealFiveRealSubfieldIso.golden_subfield_poly works over fields. -/
theorem eta0_poly_cyclotomic {K : Type*} [Field K] {ζ : K} (hζ : IsPrimitiveRoot ζ 5) :
    ((ζ + ζ ^ 4) - 2) ^ 2 + 5 * ((ζ + ζ ^ 4) - 2) + 5 = 0 :=
  eta0_poly_of_golden (BealFiveRealSubfieldIso.golden_subfield_poly hζ)

/-! ## Section 2: Eisenstein at ⟨5⟩ -/

/-- The minimal polynomial of η₀ over ℤ. -/
noncomputable def eta0Poly : ℤ[X] := X ^ 2 + C 5 * X + C 5

theorem eta0Poly_monic : eta0Poly.Monic := by unfold eta0Poly; monicity!

theorem eta0Poly_natDegree : eta0Poly.natDegree = 2 := by unfold eta0Poly; compute_degree!

/-- X²+5X+5 is Eisenstein at the prime ideal ⟨5⟩ of ℤ. -/
theorem eta0Poly_isEisenstein : eta0Poly.IsEisensteinAt (Ideal.span {(5 : ℤ)}) := by
  refine ⟨?_, ?_, ?_⟩
  · -- leading coefficient 1 ∉ ⟨5⟩
    rw [eta0Poly_monic.leadingCoeff]
    simp [Ideal.mem_span_singleton]
  · -- each non-leading coeff lies in ⟨5⟩
    intro n hn
    rw [eta0Poly_natDegree] at hn
    interval_cases n <;> simp [eta0Poly, Ideal.mem_span_singleton]
  · -- constant term 5 ∉ ⟨5⟩² = ⟨25⟩; simp closes this completely
    rw [Ideal.span_singleton_pow]
    simp [eta0Poly, Ideal.mem_span_singleton]

/-! ## Section 3: Descent congruence -/

/-- For a primitive 5th root ζ (in a CommRing K) and integers a, b:
    a + b(ζ+ζ⁴) − (a+2b) = (1−ζ)² · (b·ζ⁴). -/
theorem descent_congruence {K : Type*} [CommRing K] {ζ : K}
    (hζ : IsPrimitiveRoot ζ 5) (a b : ℤ) :
    (a : K) + b * (ζ + ζ ^ 4) - (a + 2 * b) = (1 - ζ) ^ 2 * (b * ζ ^ 4) := by
  have h := BealLambdaCongruence.phi_mod_lambda_sq hζ
  push_cast
  linear_combination (b : K) * h

/-! ## Section 4: Ring-of-integers basis for L = AdjoinRoot(x²+5x+5) -/

/-- The ℚ-polynomial. -/
noncomputable def eta0PolyQ : ℚ[X] := X ^ 2 + C 5 * X + C 5

theorem eta0PolyQ_monic : eta0PolyQ.Monic := by unfold eta0PolyQ; monicity!

theorem eta0PolyQ_ne_zero : eta0PolyQ ≠ 0 := eta0PolyQ_monic.ne_zero

theorem eta0PolyQ_natDegree : eta0PolyQ.natDegree = 2 := by unfold eta0PolyQ; compute_degree!

/-- The number field L = ℚ[x]/(x²+5x+5). -/
noncomputable abbrev L := AdjoinRoot eta0PolyQ

/-- Power basis for L over ℚ. -/
noncomputable def B : PowerBasis ℚ L := AdjoinRoot.powerBasis eta0PolyQ_ne_zero

theorem B_gen_eq_root : B.gen = AdjoinRoot.root eta0PolyQ :=
  AdjoinRoot.powerBasis_gen eta0PolyQ_ne_zero

theorem B_dim_eq_two : B.dim = 2 := by
  show eta0PolyQ.natDegree = 2; exact eta0PolyQ_natDegree

/-- B.gen satisfies its defining polynomial x²+5x+5=0. -/
theorem B_gen_poly : B.gen ^ 2 + 5 * B.gen + 5 = 0 := by
  have h : aeval B.gen eta0PolyQ = 0 := by
    rw [B_gen_eq_root, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  simp only [eta0PolyQ, map_add, map_mul, map_pow, aeval_X, map_ofNat] at h
  exact h

theorem B_gen_sq : B.gen ^ 2 = -5 * B.gen - 5 := by linear_combination B_gen_poly

/-- eta0PolyQ is irreducible over ℚ (no rational roots, since discriminant 5 is not a square). -/
theorem eta0PolyQ_irreducible : Irreducible eta0PolyQ := by
  apply irreducible_of_degree_le_three_of_not_isRoot
  · rw [eta0PolyQ_natDegree]; decide
  · intro x hx
    simp only [IsRoot.def, eta0PolyQ, eval_add, eval_pow, eval_mul, eval_C, eval_X] at hx
    exact absurd (show (2 * x + 5) ^ 2 = 5 from by nlinarith)
                 (BealGoldenMinPoly.not_isSquare_five_rat (2 * x + 5))

/-- The minimal polynomial of B.gen over ℚ is eta0PolyQ. -/
theorem B_minpoly_Q : minpoly ℚ B.gen = eta0PolyQ := by
  haveI : Fact (Irreducible eta0PolyQ) := ⟨eta0PolyQ_irreducible⟩
  exact (minpoly.eq_of_irreducible_of_monic eta0PolyQ_irreducible
    (by rw [B_gen_eq_root, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self])
    eta0PolyQ_monic).symm

/-- eta0PolyQ is the image of eta0Poly under the inclusion ℤ → ℚ. -/
theorem eta0PolyQ_eq_map : eta0PolyQ = eta0Poly.map (algebraMap ℤ ℚ) := by
  ext n
  simp only [coeff_map, eta0Poly, eta0PolyQ, coeff_add, coeff_mul, coeff_X_pow,
             coeff_C, coeff_X]
  norm_cast

/-- B.gen is integral over ℤ, witnessed by eta0Poly. -/
theorem B_gen_integral : IsIntegral ℤ B.gen :=
  ⟨eta0Poly, eta0Poly_monic, by
    show eval₂ (algebraMap ℤ L) B.gen eta0Poly = 0
    rw [IsScalarTower.algebraMap_eq ℤ ℚ L, ← Polynomial.eval₂_map,
        show eta0Poly.map (algebraMap ℤ ℚ) = eta0PolyQ from eta0PolyQ_eq_map.symm,
        ← aeval_def, B_gen_eq_root, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]⟩

/-- The minimal polynomial of B.gen over ℤ is eta0Poly. -/
theorem B_minpoly_Z : minpoly ℤ B.gen = eta0Poly := by
  haveI : Fact (Irreducible eta0PolyQ) := ⟨eta0PolyQ_irreducible⟩
  have h1 : minpoly ℚ B.gen = (minpoly ℤ B.gen).map (algebraMap ℤ ℚ) :=
    minpoly.isIntegrallyClosed_eq_field_fractions' (K := ℚ) B_gen_integral
  have h2 : eta0Poly.map (algebraMap ℤ ℚ) = (minpoly ℤ B.gen).map (algebraMap ℤ ℚ) :=
    eta0PolyQ_eq_map.symm.trans (B_minpoly_Q.symm.trans h1)
  exact (Polynomial.map_injective (algebraMap ℤ ℚ) (IsFractionRing.injective ℤ ℚ) h2).symm

/-- The minimal polynomial of B.gen over ℤ is Eisenstein at ⟨5⟩. -/
theorem B_minpoly_isEisenstein :
    (minpoly ℤ B.gen).IsEisensteinAt (Ideal.span {(5 : ℤ)}) := by
  rw [B_minpoly_Z]; exact eta0Poly_isEisenstein

/-- (2·B.gen+5)² = 5 in L. -/
theorem two_gen_plus_five_sq : (2 * B.gen + 5) ^ 2 = 5 := by
  linear_combination 4 * B_gen_poly

/-- The discriminant of the ℚ-power-basis equals 5.

    Elementary: for a degree-2 power basis,
    `discr = (-1)^1 * norm ℚ (aeval gen (derivative minpoly))`, and here
    `aeval gen (derivative eta0PolyQ) = 2·gen + 5`, whose norm is `-5`
    (computed via the `2×2` left-multiplication matrix determinant), giving
    `(-1)·(-5) = 5`. -/
theorem discr_eta0 : Algebra.discr ℚ B.basis = 5 := by
  classical
  -- NOTE: all instance-sensitive facts (`minpoly`/`norm` over L) are established BEFORE
  -- introducing `Fact (Irreducible eta0PolyQ)`. That `Fact` provides `Field L`, whose ring
  -- path differs from the bare `CommRing` path used in the theorem statement and helper
  -- lemmas; establishing these facts first keeps the instances syntactically aligned.
  -- finrank ℚ L = 2
  have hfr : Module.finrank ℚ L = 2 := by rw [B.finrank]; exact B_dim_eq_two
  -- aeval gen (derivative minpoly) = 2·gen + 5
  have hval : aeval B.gen (derivative (minpoly ℚ B.gen)) = 2 * B.gen + 5 := by
    have hd : derivative eta0PolyQ = C 2 * X + C 5 := by
      unfold eta0PolyQ
      simp only [derivative_add, derivative_mul, derivative_X_pow, derivative_C, derivative_X,
        zero_add, add_zero, mul_one, zero_mul, Nat.cast_ofNat]
      rw [show (2 : ℕ) - 1 = 1 from rfl, pow_one]
    rw [B_minpoly_Q, hd]
    simp only [map_add, map_mul, aeval_X, map_ofNat]
  -- a basis of L over ℚ indexed by `Fin 2`
  set e := finCongr B_dim_eq_two with he
  set bb := B.basis.reindex e with hbb
  have hb0 : bb 0 = 1 := by
    simp only [hbb, he, Module.Basis.coe_reindex, Function.comp_apply, PowerBasis.coe_basis,
      finCongr_symm_apply_coe, Fin.val_zero, pow_zero]
  have hb1 : bb 1 = B.gen := by
    simp only [hbb, he, Module.Basis.coe_reindex, Function.comp_apply, PowerBasis.coe_basis,
      finCongr_symm_apply_coe, Fin.val_one, pow_one]
  -- express α·(basis elements) in the basis, where α = 2·gen + 5
  have e00 : (2 * B.gen + 5) * bb 0 = (5 : ℚ) • bb 0 + (2 : ℚ) • bb 1 := by
    rw [hb0, hb1]; simp only [Algebra.smul_def, map_ofNat]; ring
  have e01 : (2 * B.gen + 5) * bb 1 = (-10 : ℚ) • bb 0 + (-5 : ℚ) • bb 1 := by
    rw [hb0, hb1]; simp only [Algebra.smul_def, map_neg, map_ofNat]
    linear_combination (2 : L) * B_gen_poly
  -- norm ℚ (2·gen + 5) = -5 via the 2×2 determinant
  have hnorm : Algebra.norm ℚ (2 * B.gen + 5) = -5 := by
    rw [Algebra.norm_eq_matrix_det bb, Matrix.det_fin_two]
    simp only [Algebra.leftMulMatrix_eq_repr_mul, e00, e01, map_add, map_smul,
      Module.Basis.repr_self, Finsupp.smul_single, smul_eq_mul, mul_one, Finsupp.coe_add,
      Pi.add_apply, Finsupp.single_apply]
    norm_num
  -- assemble, now introducing the field/separability instances for the discriminant formula.
  -- `Module.Finite ℚ L` is supplied explicitly from the power basis `B` to avoid a
  -- sorry-tainted global instance in the wider import graph.
  haveI : Fact (Irreducible eta0PolyQ) := ⟨eta0PolyQ_irreducible⟩
  haveI : Module.Finite ℚ L := B.finite
  haveI : Algebra.IsSeparable ℚ L := inferInstance
  rw [Algebra.discr_powerBasis_eq_norm, hval, hfr, hnorm]
  norm_num

/-- Every element of L that is integral over ℤ lies in ℤ[η₀] = adjoin ℤ {root of eta0Poly}. -/
theorem integralElements_in_adjoin {z : L} (hz : IsIntegral ℤ z) :
    z ∈ Algebra.adjoin ℤ ({AdjoinRoot.root eta0PolyQ} : Set L) := by
  haveI hfact : Fact (Irreducible eta0PolyQ) := ⟨eta0PolyQ_irreducible⟩
  haveI hSep : Algebra.IsSeparable ℚ L := inferInstance
  -- Step 1: discriminant argument — use ▸ to avoid coercion mismatch with rw
  have hmem5Q : (5 : ℚ) • z ∈ Algebra.adjoin ℤ ({B.gen} : Set L) :=
    discr_eta0 ▸ Algebra.discr_mul_isIntegral_mem_adjoin (K := ℚ) B_gen_integral hz
  -- Step 2: convert ℚ-smul to ℤ-smul; use ▸ which handles the definitional equality
  have hmem5 : (5 : ℤ) • z ∈ Algebra.adjoin ℤ ({B.gen} : Set L) := by
    have heq : (5 : ℤ) • z = (5 : ℚ) • z := by
      rw [show (5 : ℤ) • z = ((5 : ℤ) : L) * z from zsmul_eq_mul _ _]
      rw [show (5 : ℚ) • z = ((5 : ℚ) : L) * z from Algebra.smul_def _ _]
      norm_cast
    exact heq ▸ hmem5Q
  -- Step 3: Eisenstein descent — 5 • z ∈ ℤ[η₀] implies z ∈ ℤ[η₀]
  rw [← B_gen_eq_root]
  exact mem_adjoin_of_smul_prime_smul_of_minpoly_isEisensteinAt
    (by norm_num : Prime (5 : ℤ))
    B_gen_integral hz hmem5 B_minpoly_isEisenstein

end BealRingOfIntegersBasisKPlus
