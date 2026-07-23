import Propositio.Beal.GoldenIntRamification
import Mathlib.Tactic

/-!
# Coprimality transport into `ℤ[φ]`, away from the ramified prime `√5`

`BealGoldenIntRamification.lean` supplied the single-prime `√5`-adic layer for FLT-5 Case II
(`prime_sqrt5`, `sqrt5_dvd_iff_five_dvd_norm`, `sqrt5_valuation_one_of_five_dvd_norm_not_25`).
Its own scope note flags the next brick (item **(a)** of the descent): transporting the
**ℤ-coprimality** of the two integer factors of `x⁵+y⁵ = (x+y)·Φ(x,y)` — established over `ℤ`
in `FermatLastTheoremFiveCaseTwo.case2_core` as `gcd(x+y, Φ) = 5` exactly — into a
"`gcd = √5^j`" statement in `ℤ[φ]`, i.e. the two factors are coprime *away from the ramified
prime `√5`*.

This file builds exactly that transport layer, plus the concrete `ℤ[φ]`-elements of the
factorization.

## Main results (proved, axiom-clean, no `sorry`)

* `GoldenInt.ofInt_eq_intCast` — `ofInt n = (n : GoldenInt)`, identifying the concrete embedding
  with the ring's own `Int.cast` (they are set equal in the `AddGroupWithOne` instance).
* `GoldenInt.ofInt_isCoprime` — **coprimality transport**: `IsCoprime m n` in `ℤ` implies
  `IsCoprime (ofInt m) (ofInt n)` in `ℤ[φ]`, via `IsCoprime.map` along `Int.castRingHom`.
* `GoldenInt.sqrt5_dvd_ofInt_iff` — for a *rational* integer, `√5 ∣ ofInt n ↔ 5 ∣ n` (the
  norm-form specializes to `n²`, and `5` is a rational prime).
* `GoldenInt.dvd_of_isCoprime_mul` — the elementary Bézout fact `IsCoprime a b → g ∣ c·a →
  g ∣ c·b → g ∣ c`, the engine that peels a shared factor off coprime cofactors.
* `GoldenInt.caseTwoFactor_common_dvd_sqrt5_sq` — **the item-(a) headline**: under the
  `case2_core` coprimality data (`IsCoprime A B`, `x+y = 5·A`, `Φ = 5·B`), *any* common divisor
  `g` of `ofInt (x+y)` and `ofInt Φ` in `ℤ[φ]` divides `√5² = 5`. This is precisely
  "`gcd(x+y, Φ) = √5²` up to units" — the two factors share only the ramified prime `√5`
  (to total multiplicity `2`), and are coprime away from it.
* `GoldenInt.caseTwoFactorL` / `GoldenInt.caseTwoFactorR` — the concrete `ℤ[φ]`-factors
  `a₁+bφ = ⟨-(x²+xy+y²), x²+y²⟩` and `a₂+bφ = ⟨xy, x²+y²⟩` of
  `FermatLastTheoremFiveCaseTwoNorm.case2_phi_factorization`, with:
  - `caseTwoFactor_mul` : `caseTwoFactorL · caseTwoFactorR = ofInt Φ` (the factorization *in the
    ring `ℤ[φ]` itself*, not just in the `ℝ`-model).
  - `caseTwoFactorR_eq_neg_conj` : `caseTwoFactorR = -conj (caseTwoFactorL)` (the right factor is
    the Galois conjugate of the left, up to sign — the reason the product is rational).
  - `norm_caseTwoFactorL` : `norm caseTwoFactorL = -Φ`, matching
    `FermatLastTheoremFiveCaseTwoNorm.case2_phi_eq_neg_norm`.
  - `sqrt5_dvd_caseTwoFactorL` : once `5 ∣ Φ` (always the case in Case II), `√5 ∣ caseTwoFactorL`.
  - `caseTwoFactor_common_dvd` : any common divisor of the two concrete factors divides both
    `ofInt ((x+y)²)` and `ofInt Φ` (the structural constraint feeding a future exact-valuation
    argument).

## What this does NOT do (honest scope note)

This is the coprimality-transport half of item (a). It proves the two *ℤ-level* factors
`x+y` and `Φ` are coprime away from `√5` (`caseTwoFactor_common_dvd_sqrt5_sq`), and it exhibits
the two *concrete `ℤ[φ]`-factors* `caseTwoFactorL/R` with their structural divisibility
constraints. It does **not** yet pin the exact `√5`-valuation of `caseTwoFactorL` (which is
case-split on which of `x+y`, `Φ` carries the high `5`-power, and needs the `25 ∤ N` control of
`sqrt5_valuation_one_of_five_dvd_norm_not_25` fed the right branch), nor item (b) (unit × fifth
power extraction). Those remain the open bricks for the full descent.

**No `sorry`, no project axiom** in what follows.
-/

namespace GoldenInt

/-! ## `ofInt` is the ring's own `Int.cast` -/

/-- `ofInt n = (n : GoldenInt)`. The concrete embedding coincides with the ring's `Int.cast`
because the `AddGroupWithOne` instance defines `intCast := ofInt`. -/
theorem ofInt_eq_intCast (n : ℤ) : ofInt n = (n : GoldenInt) := rfl

/-! ## Coprimality transport `ℤ → ℤ[φ]` -/

/-- **Coprimality transport.** If `m, n` are coprime in `ℤ`, then `ofInt m, ofInt n` are coprime
in `ℤ[φ]`. This is `IsCoprime.map` along the ring homomorphism `Int.castRingHom GoldenInt`,
re-expressed through `ofInt`. -/
theorem ofInt_isCoprime {m n : ℤ} (h : IsCoprime m n) :
    IsCoprime (ofInt m) (ofInt n) := by
  have hmap := h.map (Int.castRingHom GoldenInt)
  simpa only [Int.coe_castRingHom, ofInt_eq_intCast] using hmap

/-! ## `√5`-divisibility of a rational integer -/

/-- **`√5 ∣ ofInt n ↔ 5 ∣ n`.** For a *rational* integer, `√5`-divisibility is detected by
ordinary divisibility by `5`: `N(ofInt n) = n²`, and `5` is a rational prime, so `5 ∣ n² ↔ 5 ∣ n`. -/
theorem sqrt5_dvd_ofInt_iff (n : ℤ) : sqrt5 ∣ ofInt n ↔ (5 : ℤ) ∣ n := by
  rw [sqrt5_dvd_iff_five_dvd_norm, norm_ofInt]
  have hp : Prime (5 : ℤ) := by norm_num
  constructor
  · intro h
    exact hp.dvd_of_dvd_pow h
  · intro h
    exact dvd_pow h (by norm_num)

/-! ## The Bézout peeling engine -/

/-- **Peel a shared factor off coprime cofactors.** If `a, b` are coprime and `g` divides both
`c·a` and `c·b`, then `g ∣ c`. (`c = c·(u·a+v·b) = u·(c·a)+v·(c·b)` via a Bézout identity.) -/
theorem dvd_of_isCoprime_mul {a b c g : GoldenInt} (h : IsCoprime a b)
    (ha : g ∣ c * a) (hb : g ∣ c * b) : g ∣ c := by
  obtain ⟨u, v, huv⟩ := h
  have hc : c = u * (c * a) + v * (c * b) := by
    have : c * (u * a + v * b) = c * 1 := by rw [huv]
    calc c = c * (u * a + v * b) := by rw [huv]; ring
      _ = u * (c * a) + v * (c * b) := by ring
  rw [hc]
  exact dvd_add (ha.mul_left u) (hb.mul_left v)

/-! ## Item (a): the two `ℤ`-factors are coprime away from `√5` -/

/-- **Item (a) headline — the two factors of `x⁵+y⁵ = (x+y)·Φ` are coprime away from `√5`.**
Under the `case2_core` coprimality data — coprime cofactors `A, B` with `x+y = 5·A` and
`Φ = 5·B` (`gcd(x+y, Φ) = 5` exactly) — any common divisor `g` of `ofInt (x+y)` and `ofInt Φ`
in `ℤ[φ]` divides `√5² = 5`. So in `ℤ[φ]` the two factors share *only* the ramified prime `√5`
(to combined multiplicity `2`), and are otherwise coprime. This is the transported `gcd = √5^j`
statement (`j = 2`) that item (a) of the descent asked for. -/
theorem caseTwoFactor_common_dvd_sqrt5_sq
    {x y A B : ℤ} (hcop : IsCoprime A B)
    (hxyA : x + y = 5 * A)
    (hPhiB : x ^ 4 - x ^ 3 * y + x ^ 2 * y ^ 2 - x * y ^ 3 + y ^ 4 = 5 * B)
    {g : GoldenInt}
    (hg1 : g ∣ ofInt (x + y))
    (hg2 : g ∣ ofInt (x ^ 4 - x ^ 3 * y + x ^ 2 * y ^ 2 - x * y ^ 3 + y ^ 4)) :
    g ∣ sqrt5 * sqrt5 := by
  have hcopφ : IsCoprime (ofInt A) (ofInt B) := ofInt_isCoprime hcop
  have hxy : ofInt (x + y) = ofInt 5 * ofInt A := by rw [hxyA, ofInt_mul]
  have hphi :
      ofInt (x ^ 4 - x ^ 3 * y + x ^ 2 * y ^ 2 - x * y ^ 3 + y ^ 4) = ofInt 5 * ofInt B := by
    rw [hPhiB, ofInt_mul]
  rw [hxy] at hg1
  rw [hphi] at hg2
  have hg5 : g ∣ ofInt 5 := dvd_of_isCoprime_mul hcopφ hg1 hg2
  rwa [← sqrt5_sq] at hg5

/-! ## The concrete `ℤ[φ]`-factors of the quartic cofactor -/

/-- The left concrete factor `a₁ + b·φ = ⟨-(x²+xy+y²), x²+y²⟩ ∈ ℤ[φ]` of
`FermatLastTheoremFiveCaseTwoNorm.case2_phi_factorization`. -/
def caseTwoFactorL (x y : ℤ) : GoldenInt := ⟨-(x ^ 2 + x * y + y ^ 2), x ^ 2 + y ^ 2⟩

/-- The right concrete factor `a₂ + b·φ = ⟨xy, x²+y²⟩ ∈ ℤ[φ]`. -/
def caseTwoFactorR (x y : ℤ) : GoldenInt := ⟨x * y, x ^ 2 + y ^ 2⟩

@[simp] theorem a_caseTwoFactorL (x y : ℤ) : (caseTwoFactorL x y).a = -(x ^ 2 + x * y + y ^ 2) := rfl
@[simp] theorem b_caseTwoFactorL (x y : ℤ) : (caseTwoFactorL x y).b = x ^ 2 + y ^ 2 := rfl
@[simp] theorem a_caseTwoFactorR (x y : ℤ) : (caseTwoFactorR x y).a = x * y := rfl
@[simp] theorem b_caseTwoFactorR (x y : ℤ) : (caseTwoFactorR x y).b = x ^ 2 + y ^ 2 := rfl

/-- **The factorization holds in the ring `ℤ[φ]` itself.**
`caseTwoFactorL · caseTwoFactorR = ofInt Φ`, where `Φ = x⁴-x³y+x²y²-xy³+y⁴`. The `φ`-coordinate
of the product vanishes because `a₁ + a₂ + b = 0` (the structural fact behind
`case2_phi_factorization`), leaving the rational integer `a₁·a₂ + b² = Φ`. -/
theorem caseTwoFactor_mul (x y : ℤ) :
    caseTwoFactorL x y * caseTwoFactorR x y =
      ofInt (x ^ 4 - x ^ 3 * y + x ^ 2 * y ^ 2 - x * y ^ 3 + y ^ 4) := by
  ext <;> simp [caseTwoFactorL, caseTwoFactorR, ofInt] <;> ring

/-- The right factor is the Galois conjugate of the left, up to sign:
`caseTwoFactorR = -conj (caseTwoFactorL)`. This is why the product is a rational integer. -/
theorem caseTwoFactorR_eq_neg_conj (x y : ℤ) :
    caseTwoFactorR x y = -conj (caseTwoFactorL x y) := by
  ext <;> simp [caseTwoFactorL, caseTwoFactorR, conj] <;> ring

/-- **`norm (caseTwoFactorL) = -Φ`.** Matches `FermatLastTheoremFiveCaseTwoNorm.case2_phi_eq_neg_norm`:
`Φ(x,y)` is (minus) the field norm of the concrete element `a₁ + b·φ`. -/
@[simp] theorem norm_caseTwoFactorL (x y : ℤ) :
    norm (caseTwoFactorL x y) = -(x ^ 4 - x ^ 3 * y + x ^ 2 * y ^ 2 - x * y ^ 3 + y ^ 4) := by
  simp only [norm, a_caseTwoFactorL, b_caseTwoFactorL]; ring

/-- **`√5 ∣ caseTwoFactorL` once `5 ∣ Φ`.** In Case II `5 ∣ Φ(x,y)` always (it shares the prime
`5` with `x+y`), so the concrete left factor is divisible by the ramified prime `√5`. -/
theorem sqrt5_dvd_caseTwoFactorL {x y : ℤ}
    (hΦ : (5 : ℤ) ∣ (x ^ 4 - x ^ 3 * y + x ^ 2 * y ^ 2 - x * y ^ 3 + y ^ 4)) :
    sqrt5 ∣ caseTwoFactorL x y := by
  apply sqrt5_dvd_of_five_dvd_norm
  rw [norm_caseTwoFactorL]
  exact hΦ.neg_right

/-- **Structural constraint on common divisors of the two concrete factors.** Any `g` dividing
both `caseTwoFactorL` and `caseTwoFactorR` divides `ofInt ((x+y)²)` (from the difference
`caseTwoFactorL - caseTwoFactorR = ofInt (-(x+y)²)`) and `ofInt Φ` (from their product). This is
the structural input a future exact-`√5`-valuation argument consumes. -/
theorem caseTwoFactor_common_dvd {x y : ℤ} {g : GoldenInt}
    (hgL : g ∣ caseTwoFactorL x y) (hgR : g ∣ caseTwoFactorR x y) :
    g ∣ ofInt ((x + y) ^ 2) ∧
      g ∣ ofInt (x ^ 4 - x ^ 3 * y + x ^ 2 * y ^ 2 - x * y ^ 3 + y ^ 4) := by
  refine ⟨?_, ?_⟩
  · have hdiff : caseTwoFactorR x y - caseTwoFactorL x y = ofInt ((x + y) ^ 2) := by
      ext <;> simp [caseTwoFactorL, caseTwoFactorR, ofInt] <;> ring
    rw [← hdiff]
    exact dvd_sub hgR hgL
  · rw [← caseTwoFactor_mul]
    exact hgL.mul_right _

end GoldenInt

section AxiomCheck
open GoldenInt
#print axioms ofInt_eq_intCast
#print axioms ofInt_isCoprime
#print axioms sqrt5_dvd_ofInt_iff
#print axioms dvd_of_isCoprime_mul
#print axioms caseTwoFactor_common_dvd_sqrt5_sq
#print axioms caseTwoFactor_mul
#print axioms caseTwoFactorR_eq_neg_conj
#print axioms norm_caseTwoFactorL
#print axioms sqrt5_dvd_caseTwoFactorL
#print axioms caseTwoFactor_common_dvd
end AxiomCheck
