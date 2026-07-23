import Propositio.NumberTheory.Beal.ABCQuality
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Data.Nat.Factors

/-!
# The `Ω`-count (prime factors with multiplicity) obstruction for Beal solutions

This file proves a **complementary** obstruction to the radical-based ABC-quality
bound of `BealABCQuality.abc_lt_c_pow`. Where that file bounds the *radical*
(distinct prime factors) of a primitive Beal solution, here we bound
`Ω = ArithmeticFunction.cardFactors`, the count of prime factors *with
multiplicity* (`Ω(n) = n.primeFactorsList.length`, mathlib notation `Ω` in scope
`ArithmeticFunction.Omega`, unfolded here without that scoped notation to keep the
file self-contained).

## The argument

* **`two_pow_cardFactors_le`**: for `n ≠ 0`, `2 ^ Ω(n) ≤ n`. Every prime factor
  in `n.primeFactorsList` is `≥ 2`, and the list's product is `n`
  (`Nat.prod_primeFactorsList`), so `2 ^ (list length) ≤ (list product) = n`
  via `List.pow_card_le_prod`. The list length is `Ω(n)` by
  `ArithmeticFunction.cardFactors_apply`.
* **`cardFactors_mul_three`**: `Ω` is additive over a triple product
  `Ω(A·B·C) = Ω(A) + Ω(B) + Ω(C)` for `A, B, C ≠ 0`, by two applications of the
  existing mathlib lemma `ArithmeticFunction.cardFactors_mul`.
* **`two_pow_bigOmega_lt_c_pow`** (headline): combining `2 ^ Ω(A) ≤ A`,
  `2 ^ Ω(B) ≤ B`, `2 ^ Ω(C) ≤ C` with `BealABCQuality.abc_lt_c_pow`
  (`A·B·C < C^z`) gives

    `2 ^ (Ω(A) + Ω(B) + Ω(C)) < C^z`

  for every primitive Beal solution `A^x + B^y = C^z` with `A, B, C ≥ 2` and
  exponents `x, y, z ≥ 3`. This bounds the *total prime-factor-count-with-
  multiplicity* of the bases, complementary to the radical bound.

Dependency policy: mathlib4 permitted (per project convention, see
`BealABCQuality.lean`). Typecheck with
`lake env lean BealBigOmegaBound.lean` (or `scripts/safe-lean.sh`).
-/

namespace BealBigOmegaBound

/-! ## 1. `2 ^ Ω(n) ≤ n` -/

/-- **`2 ^ Ω(n) ≤ n`** for `n ≠ 0`. Every prime factor of `n` (with multiplicity)
contributes at least a factor of `2`, so the product of the `Ω(n)`-element list
`n.primeFactorsList` — which equals `n` — is at least `2 ^ Ω(n)`. -/
theorem two_pow_cardFactors_le {n : ℕ} (hn : n ≠ 0) :
    2 ^ (ArithmeticFunction.cardFactors n) ≤ n := by
  rw [ArithmeticFunction.cardFactors_apply]
  have hall : ∀ x ∈ n.primeFactorsList, 2 ≤ x := fun x hx =>
    (Nat.prime_of_mem_primeFactorsList hx).two_le
  have hle := List.pow_card_le_prod n.primeFactorsList 2 hall
  rwa [Nat.prod_primeFactorsList hn] at hle

/-! ## 2. Additivity of `Ω` over a triple product -/

/-- **`Ω` is additive over a triple product**: `Ω(A·B·C) = Ω(A) + Ω(B) + Ω(C)` for
`A, B, C ≠ 0`. Two applications of `ArithmeticFunction.cardFactors_mul`. -/
theorem cardFactors_mul_three {A B C : ℕ} (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0) :
    ArithmeticFunction.cardFactors (A * B * C)
      = ArithmeticFunction.cardFactors A + ArithmeticFunction.cardFactors B
        + ArithmeticFunction.cardFactors C := by
  rw [ArithmeticFunction.cardFactors_mul (mul_ne_zero hA hB) hC,
      ArithmeticFunction.cardFactors_mul hA hB]

/-! ## 3. The combined `Ω`-count obstruction -/

/-- **Headline — the `Ω`-count obstruction.** Every primitive Beal solution
`A^x + B^y = C^z` with `A, B, C ≥ 2` and exponents `x, y, z ≥ 3` satisfies

  `2 ^ (Ω(A) + Ω(B) + Ω(C)) < C ^ z`,

bounding the total number of prime factors of `A, B, C`, counted with
multiplicity, in terms of the value `C^z`. This is the `Ω`-analogue of
`BealABCQuality.beal_radical_lt_c` (which uses the radical — distinct prime
factors only): from `2 ^ Ω(A) ≤ A`, `2 ^ Ω(B) ≤ B`, `2 ^ Ω(C) ≤ C`
(`two_pow_cardFactors_le`) and the core inequality `A · B · C < C ^ z`
(`BealABCQuality.abc_lt_c_pow`). -/
theorem two_pow_bigOmega_lt_c_pow {A B C x y z : ℕ}
    (hA : 2 ≤ A) (hB : 2 ≤ B) (hC : 2 ≤ C)
    (hx : 3 ≤ x) (hy : 3 ≤ y) (hz : 3 ≤ z)
    (h : A ^ x + B ^ y = C ^ z) :
    2 ^ (ArithmeticFunction.cardFactors A + ArithmeticFunction.cardFactors B
          + ArithmeticFunction.cardFactors C) < C ^ z := by
  have hABC : A * B * C < C ^ z := BealABCQuality.abc_lt_c_pow hA hB hC hx hy hz h
  have h2A : 2 ^ (ArithmeticFunction.cardFactors A) ≤ A :=
    two_pow_cardFactors_le (by omega)
  have h2B : 2 ^ (ArithmeticFunction.cardFactors B) ≤ B :=
    two_pow_cardFactors_le (by omega)
  have h2C : 2 ^ (ArithmeticFunction.cardFactors C) ≤ C :=
    two_pow_cardFactors_le (by omega)
  calc 2 ^ (ArithmeticFunction.cardFactors A + ArithmeticFunction.cardFactors B
        + ArithmeticFunction.cardFactors C)
      = 2 ^ (ArithmeticFunction.cardFactors A) * 2 ^ (ArithmeticFunction.cardFactors B)
          * 2 ^ (ArithmeticFunction.cardFactors C) := by
        rw [pow_add, pow_add]
    _ ≤ A * B * C := Nat.mul_le_mul (Nat.mul_le_mul h2A h2B) h2C
    _ < C ^ z := hABC

end BealBigOmegaBound
