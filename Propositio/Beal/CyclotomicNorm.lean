import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.Tactic

open scoped NumberField

/-!
# Cyclotomic norm identity for Φ₅(A,B) and descent element norm

For K = ℚ(ζ₅) and A, B ∈ ℕ, the product of all Galois conjugates of (A+Bζ)
equals the cyclotomic factor Φ₅(A,B) = A⁴−A³B+A²B²−AB³+B⁴.

This is the "outside approach" bridge connecting:
- BealPrimeDescent.prime_sum_descent (p=5): Φ₅(A,B) = t^z elementarily
- The cyclotomic descent: A+Bζ = d^z · v with d ∈ 𝓞K

The product formula is proved by a pure ring identity (linear_combination witness
using ζ^5=1 and 1+ζ+ζ²+ζ³+ζ⁴=0), requiring no number field machinery.

## Main results

- `cyclotomic5_conjugate_product`: ring identity (any CommRing)
- `beal_55z_descent_norm_eq`: the descent element d satisfies
  N_{K/Q}(d)^z = Φ₅(A,B) = t^z, so N_{K/Q}(d) = t (given N_{K/Q}(A+Bζ) = Φ₅(A,B))
-/

namespace BealCyclotomicNorm

/-- **Ring identity**: the product of (A + B·ζᵏ) for k = 1,2,3,4 equals
Φ₅(A,B) = A⁴−A³B+A²B²−AB³+B⁴ in any commutative ring where ζ is a
primitive 5th root of unity (uses only ζ^5 = 1 and ∑_{k=0}^{4} ζ^k = 0).

Proof: The `linear_combination` certificate was derived by decomposing
`P(ζ,A,B) − Φ₅(A,B)` into `c₁·(ζ^5−1) + c₂·(1+ζ+ζ²+ζ³+ζ⁴)` where
  c₁ = A²B²(2+ζ+ζ²) + AB³(ζ+ζ²+ζ³+ζ⁴) + B⁴(ζ^5+1)
  c₂ = A³B + A²B² + AB³
The key intermediate fact: (ζ+ζ⁴)+(ζ²+ζ³) = −1 and (ζ+ζ⁴)·(ζ²+ζ³) = −1. -/
theorem cyclotomic5_conjugate_product {R : Type*} [CommRing R] (ζ A B : R)
    (h5 : ζ ^ 5 = 1) (hsum : 1 + ζ + ζ ^ 2 + ζ ^ 3 + ζ ^ 4 = 0) :
    (A + B * ζ) * (A + B * ζ ^ 2) * (A + B * ζ ^ 3) * (A + B * ζ ^ 4) =
    A ^ 4 - A ^ 3 * B + A ^ 2 * B ^ 2 - A * B ^ 3 + B ^ 4 := by
  linear_combination
    (A ^ 2 * B ^ 2 * (2 + ζ + ζ ^ 2) + A * B ^ 3 * (ζ + ζ ^ 2 + ζ ^ 3 + ζ ^ 4) +
      B ^ 4 * (ζ ^ 5 + 1)) * h5 +
    (A ^ 3 * B + A ^ 2 * B ^ 2 + A * B ^ 3) * hsum

/-- **Corollary in 𝓞K**: for a primitive 5th root ζ and A, B : ℕ,
the product of Galois conjugates of (A+Bζ) over ℤ equals Φ₅(A,B). -/
theorem cyclotomic5_product_in_ring_of_integers
    {K : Type*} [Field K] [NumberField K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ 5)
    (A B : ℕ) :
    ((A : 𝓞 K) + B * hζ.toInteger) *
    ((A : 𝓞 K) + B * hζ.toInteger ^ 2) *
    ((A : 𝓞 K) + B * hζ.toInteger ^ 3) *
    ((A : 𝓞 K) + B * hζ.toInteger ^ 4) =
    (A : 𝓞 K) ^ 4 - (A : 𝓞 K) ^ 3 * B + (A : 𝓞 K) ^ 2 * B ^ 2 -
    (A : 𝓞 K) * B ^ 3 + (B : 𝓞 K) ^ 4 := by
  -- toInteger_isPrimitiveRoot: hζ.toInteger is a primitive 5th root in 𝓞K
  have hζ' : IsPrimitiveRoot hζ.toInteger 5 := hζ.toInteger_isPrimitiveRoot
  have h5 : hζ.toInteger ^ 5 = 1 := hζ'.pow_eq_one
  -- Cyclotomic sum: use IsDomain and ζ^5-1 = (ζ-1)·Φ₅(ζ) with ζ≠1
  have hne1 : hζ.toInteger ≠ 1 := hζ'.ne_one (by norm_num)
  have hfact : (hζ.toInteger - 1) *
      (1 + hζ.toInteger + hζ.toInteger ^ 2 + hζ.toInteger ^ 3 + hζ.toInteger ^ 4) = 0 := by
    linear_combination h5
  have hsum : 1 + hζ.toInteger + hζ.toInteger ^ 2 + hζ.toInteger ^ 3 + hζ.toInteger ^ 4 = 0 :=
    (mul_eq_zero.mp hfact).resolve_left (sub_ne_zero.mpr hne1)
  exact cyclotomic5_conjugate_product hζ.toInteger (A : 𝓞 K) (B : 𝓞 K) h5 hsum

/-- **Descent element norm** (conditional on the cyclotomic norm formula).
If the algebraic norm satisfies N_{K/Q}(A+Bζ) = Φ₅(A,B) and v is a unit
with N_{K/Q}(v) = 1, then N_{K/Q}(d)^z = Φ₅(A,B).

This connects the elementary ℤ-factorization (Φ₅(A,B) = t^z from
BealPrimeDescent.prime_sum_descent) to the cyclotomic descent: N_{K/Q}(d) = t. -/
theorem beal_55z_descent_norm_eq
    {K : Type*} [Field K] [NumberField K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ 5)
    {A B z : ℕ}
    (d : 𝓞 K) (v : (𝓞 K)ˣ)
    (hdescent : (A : 𝓞 K) + B * hζ.toInteger = d ^ z * v)
    -- The norm formula (to be supplied by the caller or proved separately):
    (hnorm_sum : Algebra.norm ℤ ((A : 𝓞 K) + B * hζ.toInteger) =
      A ^ 4 - A ^ 3 * B + A ^ 2 * B ^ 2 - A * B ^ 3 + B ^ 4)
    -- Real units have norm 1 in K (follows from K^+ = ℚ(√5)):
    (hunit_norm : Algebra.norm ℤ (v : 𝓞 K) = 1) :
    Algebra.norm ℤ (d : 𝓞 K) ^ z =
      A ^ 4 - A ^ 3 * B + A ^ 2 * B ^ 2 - A * B ^ 3 + B ^ 4 := by
  have hmul : Algebra.norm ℤ ((d ^ z * v : 𝓞 K)) =
      Algebra.norm ℤ (d : 𝓞 K) ^ z := by
    rw [map_mul, map_pow]
    simp [hunit_norm]
  rw [← hdescent, hnorm_sum] at hmul
  linarith [hmul]

#print axioms cyclotomic5_conjugate_product
#print axioms cyclotomic5_product_in_ring_of_integers
#print axioms beal_55z_descent_norm_eq

end BealCyclotomicNorm
