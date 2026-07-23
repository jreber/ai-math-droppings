import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.Tactic
import Propositio.NumberTheory.Beal.PrimeDescent

/-!
# Cyclotomic factorization of `Aᵖ ± Bᵖ` — the ℤ[ζ_p] setup for (p, p, z) descent

**NEW mathematics — no LaTTe sibling.** This file gives the **cyclotomic**
(ring `ℤ[ζ_p]`, here a general integral domain carrying a primitive `p`-th root of
unity `ζ`) factorization of `Aᵖ ± Bᵖ`, the general-`p` analogue of the Eisenstein
factorization `A³ + B³ = (A + B)(A² − A·B + B²)` that
`BealEisensteinDescent.lean` / `BealEisenstein.lean` perform for `p = 3`.

For a primitive `p`-th root of unity `ζ`, the geometric factorization of
`Xᵖ − 1 = ∏_{i<p}(X − ζⁱ)` evaluates (homogenized) to

  `Aᵖ − Bᵖ = ∏_{i=0}^{p−1} (A − ζⁱ·B)`,    and for odd `p`,
  `Aᵖ + Bᵖ = ∏_{i=0}^{p−1} (A + ζⁱ·B)`.

The `i = 0` factor is `A − B` (resp. `A + B`); the remaining product
`∏_{i=1}^{p−1}(A + ζⁱ·B)` is the **cyclotomic cofactor**, the general-`p`
analogue of the Eisenstein form `A² − A·B + B²` (the `p = 3` instance
`(A + ζB)(A + ζ²B) = A² − A·B + B²`). This cofactor is the cyclotomic incarnation
of the *elementary* cofactor `Φ = Σ_i (−1)ⁱ Aᵖ⁻¹⁻ⁱ Bⁱ` of
`BealPrimeDescent.lean`: both equal `(Aᵖ + Bᵖ)/(A + B)`. This file is the bridge
between the elementary and the cyclotomic descent.

## The obstruction for general `p`

The cyclotomic *descent* (the analogue of `BealEisensteinDescent` for `p = 3`)
needs the ring `ℤ[ζ_p]` to be a UFD / PID so that the coprime cyclotomic factors
of a perfect power are themselves (up to units) perfect powers. This holds
**only when `ℤ[ζ_p]` has class number 1** — i.e. for the finitely many regular /
small primes; the cube case `p = 3` is the principal-ideal-domain input
`IsCyclotomicExtension.Rat.three_pid` used by `BealEisensteinDescent`. For
general `p` the class group is the obstruction (Kummer's regular-prime theory).
This file provides only the *algebraic factorization*, which is unconditional.

## Key mathlib lemmas relied on

* `IsPrimitiveRoot.pow_sub_pow_eq_prod_sub_mul` — over an integral domain,
  `xⁿ − yⁿ = ∏_{μ ∈ nthRootsFinset} (x − μ·y)`. This is the product-of-roots
  identity (the homogenized `Xⁿ − 1 = ∏(X − μ)`); the companion
  `IsPrimitiveRoot.pow_add_pow_eq_prod_add_mul` handles the odd `+` case.
* `IsPrimitiveRoot.injOn_pow`, `IsPrimitiveRoot.card_nthRootsFinset`,
  `IsPrimitiveRoot.mem_nthRootsFinset` — the reindexing of the `nthRootsFinset`
  product into the `i ↦ ζⁱ`, `i ∈ range p`, product.
* `Finset.prod_eq_prod_diff_singleton_mul` — extracting the `i = 0` factor.

Dependency policy: mathlib4 permitted (user authorization 2026-05-17). Use
`lake env lean BealCyclotomicFactor.lean` to typecheck.
-/

namespace BealCyclotomicFactor

open Finset Polynomial

variable {R : Type*} [CommRing R] [IsDomain R]

/-! ## 0. Reindexing the `nthRootsFinset` product into `i ↦ ζⁱ`, `i ∈ range p`

Mathlib's `IsPrimitiveRoot.pow_sub_pow_eq_prod_sub_mul` states the product over
`nthRootsFinset p (1 : R)`. For the Beal setup we want it indexed by the exponents
`i ∈ range p`, via `i ↦ ζⁱ`. Since `ζ` is a primitive `p`-th root, `i ↦ ζⁱ` is a
bijection `range p ≃ nthRootsFinset p 1` (injective by `injOn_pow`, surjective by
the equal-cardinality count `card_nthRootsFinset = p`).
-/

/-- The product over `nthRootsFinset p (1 : R)` of any `f` equals the product over
`i ∈ range p` of `f (ζⁱ)`, when `ζ` is a primitive `p`-th root of unity.

The map `i ↦ ζⁱ` is a bijection `range p ≃ nthRootsFinset p 1`: into
`nthRootsFinset` because `(ζⁱ)ᵖ = (ζᵖ)ⁱ = 1`; injective by
`IsPrimitiveRoot.injOn_pow`; surjective by `IsPrimitiveRoot.eq_pow_of_pow_eq_one`
(every `p`-th root of unity is a power of `ζ`). -/
theorem prod_nthRootsFinset_eq_prod_range {p : ℕ} (hp : 0 < p) {ζ : R}
    (hζ : IsPrimitiveRoot ζ p) (f : R → R) :
    ∏ μ ∈ nthRootsFinset p (1 : R), f μ = ∏ i ∈ Finset.range p, f (ζ ^ i) := by
  haveI : NeZero p := ⟨Nat.pos_iff_ne_zero.mp hp⟩
  refine (Finset.prod_nbij (fun i => ζ ^ i) ?_ ?_ ?_ (fun i _ => rfl)).symm
  · -- maps range p into nthRootsFinset p 1: (ζ^i)^p = 1
    intro i _
    rw [mem_nthRootsFinset hp, ← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  · -- injective on range p
    intro i hi j hj e
    exact hζ.injOn_pow hi hj e
  · -- surjective onto nthRootsFinset p 1
    intro μ hμ
    rw [Finset.mem_coe, mem_nthRootsFinset hp] at hμ
    obtain ⟨i, hi, hiμ⟩ := hζ.eq_pow_of_pow_eq_one hμ
    exact ⟨i, by rwa [Finset.coe_range, Set.mem_Iio], hiμ⟩

/-! ## 1. The cyclotomic factorization `Aᵖ − Bᵖ = ∏ (A − ζⁱ B)`

The homogenized product-of-roots identity, indexed by exponents.
-/

/-- **Cyclotomic difference factorization.**
For a primitive `p`-th root of unity `ζ` (over an integral domain),
`Aᵖ − Bᵖ = ∏_{i=0}^{p−1} (A − ζⁱ·B)`.

This is the general-`p` analogue of the Eisenstein difference factorization;
mathlib's `IsPrimitiveRoot.pow_sub_pow_eq_prod_sub_mul` gives the product over
`nthRootsFinset`, which `prod_nthRootsFinset_eq_prod_range` reindexes to `range p`. -/
theorem prod_sub_eq_pow_sub {p : ℕ} (hp : 0 < p) {ζ : R}
    (hζ : IsPrimitiveRoot ζ p) (A B : R) :
    ∏ i ∈ Finset.range p, (A - ζ ^ i * B) = A ^ p - B ^ p := by
  rw [← prod_nthRootsFinset_eq_prod_range hp hζ (fun μ => A - μ * B)]
  exact (IsPrimitiveRoot.pow_sub_pow_eq_prod_sub_mul (x := A) (y := B) hp hζ).symm

/-- **Cyclotomic sum factorization (odd `p`).**
For a primitive `p`-th root of unity `ζ` with `p` odd (over an integral domain),
`Aᵖ + Bᵖ = ∏_{i=0}^{p−1} (A + ζⁱ·B)`.

Obtained from `prod_sub_eq_pow_sub` with `B ↦ −B`: `Aᵖ − (−B)ᵖ = Aᵖ + Bᵖ` for odd
`p` (`Odd.neg_pow`), and each factor `A − ζⁱ·(−B) = A + ζⁱ·B`. -/
theorem prod_add_eq_pow_add {p : ℕ} (hodd : Odd p) {ζ : R}
    (hζ : IsPrimitiveRoot ζ p) (A B : R) :
    ∏ i ∈ Finset.range p, (A + ζ ^ i * B) = A ^ p + B ^ p := by
  have hp : 0 < p := hodd.pos
  have h := prod_sub_eq_pow_sub hp hζ A (-B)
  rw [Odd.neg_pow hodd, sub_neg_eq_add] at h
  rw [← h]
  apply Finset.prod_congr rfl
  intro i _
  ring

/-! ## 2. Extracting the `i = 0` factor: the cyclotomic cofactor

The `i = 0` factor of the sum product is `A + ζ⁰·B = A + B`; the remaining product
`∏_{i ∈ range p \ {0}} (A + ζⁱ B)` is the **cyclotomic cofactor**.
-/

/-- **Cofactor extraction (odd `p`).**
`Aᵖ + Bᵖ = (A + B) · ∏_{i ∈ range p \ {0}} (A + ζⁱ·B)`.

The `i = 0` factor `A + ζ⁰·B = A + B` is split off via
`Finset.prod_eq_prod_diff_singleton_mul`; the residual product is the cyclotomic
cofactor, the general-`p` analogue of the Eisenstein quadratic `A² − A·B + B²`. -/
theorem pow_add_eq_sum_mul_cofactor {p : ℕ} (hodd : Odd p) {ζ : R}
    (hζ : IsPrimitiveRoot ζ p) (A B : R) :
    A ^ p + B ^ p =
      (A + B) * ∏ i ∈ Finset.range p \ {0}, (A + ζ ^ i * B) := by
  have hp : 0 < p := hodd.pos
  have h0 : (0 : ℕ) ∈ Finset.range p := Finset.mem_range.mpr hp
  have hsplit := Finset.prod_eq_prod_diff_singleton_mul h0 (fun i => A + ζ ^ i * B)
  rw [← prod_add_eq_pow_add hodd hζ A B, hsplit, pow_zero, one_mul, mul_comm]

/-- The cyclotomic cofactor, named: `∏_{i ∈ range p \ {0}} (A + ζⁱ·B)`. -/
def cyclotomicCofactor (p : ℕ) (ζ A B : R) : R :=
  ∏ i ∈ Finset.range p \ {0}, (A + ζ ^ i * B)

/-! ## 3. The bridge to the elementary cofactor `Φ`

`BealPrimeDescent.Phi p A B = Σ_i (−1)ⁱ Aᵖ⁻¹⁻ⁱ Bⁱ` and the cyclotomic cofactor
both equal `(Aᵖ + Bᵖ)/(A + B)`. We state the faithful bridge:
`(A + B) · cofactor = (A + B) · Φ` (both equal `Aᵖ + Bᵖ`), and — when `A + B` is a
nonzerodivisor (in particular `A + B ≠ 0` in the domain `R`) — cancel to
`cofactor = Φ`.

We work over the same domain `R`, with `A, B : R` directly (no cast needed: `Phi`
is defined over `ℤ`, but its defining sum and the factorization `sum_pow_eq` are
ring identities that hold over any commutative ring; here we transport the
*value* identity `(A+B)·Φ_R = Aᵖ + Bᵖ` by re-deriving it over `R`).
-/

/-- The elementary cofactor `Φ`, re-expressed over the ambient ring `R`
(the same alternating sum as `BealPrimeDescent.Phi`, evaluated in `R`). -/
def PhiR (p : ℕ) (A B : R) : R :=
  ∑ i ∈ Finset.range p, (-1) ^ i * A ^ (p - 1 - i) * B ^ i

omit [IsDomain R] in
/-- `(A + B) · Φ_R = Aᵖ + Bᵖ` over `R` — the ring-level factorization, a transport
of `BealPrimeDescent.sum_pow_eq` to the ambient domain `R` (holds over any
commutative ring; `IsDomain` not needed here). -/
theorem add_mul_PhiR (p : ℕ) (hodd : Odd p) (A B : R) :
    (A + B) * PhiR p A B = A ^ p + B ^ p := by
  -- mathlib geometric factorization with y := -B (same proof as BealPrimeDescent.sum_pow_eq)
  have hg := geom_sum₂_mul A (-B) p
  rw [Odd.neg_pow hodd, sub_neg_eq_add, sub_neg_eq_add] at hg
  have hsum : (∑ i ∈ Finset.range p, A ^ i * (-B) ^ (p - 1 - i)) = PhiR p A B := by
    rw [PhiR, ← Finset.sum_range_reflect (fun i => A ^ i * (-B) ^ (p - 1 - i)) p]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    have h1 : p - 1 - (p - 1 - i) = i := by omega
    rw [h1, show ((-B) ^ i : R) = (-1) ^ i * B ^ i by rw [← neg_one_mul, mul_pow]]
    ring
  rw [← hsum, mul_comm]
  exact hg

/-- **BRIDGE: `(A + B) · cofactor = (A + B) · Φ_R`** (both equal `Aᵖ + Bᵖ`).
The cyclotomic cofactor `∏_{i ∈ range p \ {0}}(A + ζⁱ B)` and the elementary
cofactor `Φ_R = Σ_i (−1)ⁱ Aᵖ⁻¹⁻ⁱ Bⁱ` agree after multiplication by `A + B`. -/
theorem add_mul_cofactor_eq_add_mul_PhiR {p : ℕ} (hodd : Odd p) {ζ : R}
    (hζ : IsPrimitiveRoot ζ p) (A B : R) :
    (A + B) * cyclotomicCofactor p ζ A B = (A + B) * PhiR p A B := by
  rw [cyclotomicCofactor, ← pow_add_eq_sum_mul_cofactor hodd hζ A B, add_mul_PhiR p hodd A B]

/-- **BRIDGE (cancelled): the cyclotomic cofactor equals `Φ_R`** when `A + B ≠ 0`.
In the integral domain `R`, `A + B ≠ 0` is a nonzerodivisor, so the common factor
cancels: `∏_{i ∈ range p \ {0}}(A + ζⁱ B) = Σ_i (−1)ⁱ Aᵖ⁻¹⁻ⁱ Bⁱ`. -/
theorem cyclotomic_cofactor_eq_Phi {p : ℕ} (hodd : Odd p) {ζ : R}
    (hζ : IsPrimitiveRoot ζ p) (A B : R) (hAB : A + B ≠ 0) :
    cyclotomicCofactor p ζ A B = PhiR p A B :=
  mul_left_cancel₀ hAB (add_mul_cofactor_eq_add_mul_PhiR hodd hζ A B)

/-- `PhiR` agrees with `BealPrimeDescent.Phi` over `ℤ` — they are the literal same
alternating sum, so the bridge `cyclotomic_cofactor_eq_Phi` is faithful to the
elementary `BealPrimeDescent.Phi`. -/
theorem PhiR_int_eq_Phi (p : ℕ) (A B : ℤ) :
    PhiR p A B = BealPrimeDescent.Phi p A B := rfl

/-! ## 4. The `p = 3` sanity corollary — ties to `BealEisenstein` / `BealEisensteinDescent`

Specializing `p = 3` recovers the Eisenstein form `(A + ζB)(A + ζ²B) = A² − A·B + B²`.
-/

/-- **`p = 3` difference sanity.**
`(A − ζ⁰B)(A − ζ¹B)(A − ζ²B) = A³ − B³` for a primitive cube root `ζ`. -/
theorem prod_sub_eq_pow_sub_three {ζ : R} (hζ : IsPrimitiveRoot ζ 3) (A B : R) :
    (A - ζ ^ 0 * B) * (A - ζ ^ 1 * B) * (A - ζ ^ 2 * B) = A ^ 3 - B ^ 3 := by
  have h := prod_sub_eq_pow_sub (p := 3) (by norm_num) hζ A B
  rw [Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_succ,
    Finset.prod_range_zero, one_mul] at h
  exact h

/-- **`p = 3` sum sanity, with the Eisenstein norm form.**
The cyclotomic cofactor at `p = 3` is the Eisenstein quadratic:
`(A + ζB)(A + ζ²B) = A² − A·B + B²`. Combined with the `i = 0` factor `A + B`,
this is `(A + B)(A² − A·B + B²) = A³ + B³`, recovering
`BealEisenstein.cube_sum_factor`. The middle identity uses
`1 + ζ + ζ² = 0` (`hζ.geom_sum_eq_zero`), the defining relation of `ℤ[ζ₃]`. -/
theorem prod_add_eq_norm_three {ζ : R} (hζ : IsPrimitiveRoot ζ 3) (A B : R) :
    (A + ζ ^ 1 * B) * (A + ζ ^ 2 * B) = A ^ 2 - A * B + B ^ 2 := by
  -- 1 + ζ + ζ² = 0, i.e. ζ + ζ² = -1, and ζ·ζ² = ζ³ = 1.
  have hgeom : (1 : R) + ζ + ζ ^ 2 = 0 := by
    have := hζ.geom_sum_eq_zero (by norm_num)
    simpa [Finset.sum_range_succ, pow_zero, pow_one] using this
  have hprod : ζ ^ 1 * ζ ^ 2 = 1 := by
    rw [← pow_add]; exact hζ.pow_eq_one
  -- (A + ζB)(A + ζ²B) = A² + (ζ + ζ²)·A·B + (ζ·ζ²)·B²
  -- with ζ + ζ² = -1 and ζ·ζ² = 1.
  linear_combination (A * B) * hgeom + B ^ 2 * hprod

end BealCyclotomicFactor
