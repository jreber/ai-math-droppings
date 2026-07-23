import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.Algebra.GCDMonoid.IntegrallyClosed
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic

/-!
# The norm bridge: `λ² ∣ m ⟹ 5 ∣ m` for a rational integer `m`, `λ = 1 - ζ₅`

This file supplies the missing elementary-but-nontrivial algebraic-number-theory ingredient
identified in `BealKummerLambda4Congruence`: the `⟹` direction of

  `φⁿ ≡ (rational integer) (mod λ⁴)  ⟺  5 ∣ n`

(`φ = 1 + ζ₅ + ζ₅⁴` the golden unit of `ℚ(ζ₅)⁺`) has been reduced by
`BealKummerLambda4Congruence.golden_pow_cong_lambda4_iff_coeff` to the finite-ring obstruction
`BealKummerLambda4Congruence.obstruction_zmod5`, modulo one purely algebraic transfer fact:

  **for a rational integer `m : ℤ`, if `λ² ∣ m` in `𝓞(ℚ(ζ₅))`, then `5 ∣ m` in `ℤ`.**

## The norm argument

`N(λ) = N(1 - ζ₅) = Φ₅(1) = 5` (the norm of `1 - ζ₅` from `ℚ(ζ₅)` to `ℚ` is the cyclotomic
polynomial evaluated at `1`, which equals `5` since `5` is prime — `mathlib` has this precomputed
as `IsPrimitiveRoot.norm_sub_one_of_prime_ne_two'`). Hence `N(λ²) = N(λ)² = 25`. If `λ² ∣ m` for
a rational integer `m` (witnessed by an algebraic integer `c` with `m = λ²·c`), taking norms:
`N(m) = N(λ²)·N(c) = 25·N(c)`. Since `m` is a rational integer, `N(m) = m⁴` (`[ℚ(ζ₅):ℚ] = 4`).
Since `c` is an algebraic integer, `N(c)` is a rational number integral over `ℤ`, hence (`ℤ` being
integrally closed in `ℚ`) an ordinary integer `k`. So `m⁴ = 25·k`, giving `25 ∣ m⁴`, hence
`5 ∣ m⁴`, hence (`5` prime) `5 ∣ m`.

## Main results (all axiom-clean: `[propext, Classical.choice, Quot.sound]`)

1. `cyclotomic_five_irreducible_rat` — `Irreducible (cyclotomic 5 ℚ)`.
2. `finrank_eq_four` — `[L : ℚ] = 4` for a 5th cyclotomic extension `L` of `ℚ`.
3. `norm_zeta_sub_one` — `N(ζ₅ - 1) = 5`.
4. `norm_one_sub_zeta` — `N(1 - ζ₅) = 5` (the sign flip; even degree kills the `(-1)`).
5. `five_dvd_of_lambda_sq_dvd` — **the norm bridge itself**: `λ² ∣ m ⟹ 5 ∣ m` for `m : ℤ`,
   with the divisibility witnessed by an algebraic integer `c` (`IsIntegral ℤ c`).

Typecheck: `lake env lean BealLambdaNormBridge.lean` (or `scripts/safe-lean.sh`).
-/

namespace BealLambdaNormBridge

open Polynomial

variable {L : Type*} [Field L] [Algebra ℚ L] [IsCyclotomicExtension {5} ℚ L]

/-! ## 1. Basic cyclotomic-5 facts over `ℚ` -/

/-- `cyclotomic 5` is irreducible over `ℚ` (true for every `n > 0`, via the general
Gauss/Eisenstein-descent argument already in `mathlib`). -/
theorem cyclotomic_five_irreducible_rat : Irreducible (cyclotomic 5 ℚ) :=
  cyclotomic.irreducible_rat (by norm_num)

/-- `[L : ℚ] = 4` for any field `L` that is a 5th cyclotomic extension of `ℚ`
(`Nat.totient 5 = 4`). -/
theorem finrank_eq_four : Module.finrank ℚ L = 4 := by
  have h := IsCyclotomicExtension.finrank L cyclotomic_five_irreducible_rat
  rw [h]
  decide

/-! ## 2. The norm of `λ = 1 - ζ₅` -/

/-- **`N(ζ₅ - 1) = 5`**, the norm from `L` (a 5th cyclotomic extension of `ℚ`) down to `ℚ`.
This is `mathlib`'s `IsPrimitiveRoot.norm_sub_one_of_prime_ne_two'`, specialized to `p = 5`. -/
theorem norm_zeta_sub_one {ζ : L} (hζ : IsPrimitiveRoot ζ 5) :
    Algebra.norm ℚ (ζ - 1) = 5 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  exact hζ.norm_sub_one_of_prime_ne_two' cyclotomic_five_irreducible_rat (by norm_num)

/-- **`N(1 - ζ₅) = 5`.** Sign flip of `norm_zeta_sub_one`: `1 - ζ = (-1)·(ζ - 1)`, and
`N(-1) = (-1)^{[L:ℚ]} = (-1)^4 = 1` since `[L:ℚ] = 4` is even. -/
theorem norm_one_sub_zeta {ζ : L} (hζ : IsPrimitiveRoot ζ 5) :
    Algebra.norm ℚ (1 - ζ) = 5 := by
  have hsplit : (1 : L) - ζ = (-1 : L) * (ζ - 1) := by ring
  have hnegone : (algebraMap ℚ L (-1 : ℚ)) = (-1 : L) := by simp
  have hnorm_neg_one : Algebra.norm ℚ (-1 : L) = 1 := by
    have hkey : Algebra.norm ℚ (algebraMap ℚ L (-1 : ℚ)) = (-1 : ℚ) ^ Module.finrank ℚ L :=
      Algebra.norm_algebraMap (-1 : ℚ)
    rw [hnegone, finrank_eq_four] at hkey
    simpa using hkey
  rw [hsplit, map_mul, hnorm_neg_one, one_mul, norm_zeta_sub_one hζ]

/-! ## 3. The norm bridge -/

/-- **The norm bridge**: if a rational integer `m` is divisible, in `L`, by `λ² = (1-ζ₅)²`
with an *algebraic-integer* witness `c` (i.e. the divisibility genuinely happens inside
`𝓞(ℚ(ζ₅))`, not just in the field), then `5 ∣ m` as an ordinary integer.

Proof: take `Algebra.norm ℚ` of both sides of `(m : L) = λ²·c`. The left side becomes `m⁴`
(`Algebra.norm_algebraMap` + `finrank_eq_four`); the right side becomes `25 · N(c)`
(`norm_one_sub_zeta` squared, times multiplicativity of the norm). Since `c` is integral over
`ℤ`, so is `N(c)` (`Algebra.isIntegral_norm`), and `ℤ` is integrally closed in `ℚ`, so
`N(c) = (k : ℚ)` for some `k : ℤ`. Then `m⁴ = 25·k` in `ℤ`, so `5 ∣ m⁴`, so (`5` prime) `5 ∣ m`. -/
theorem five_dvd_of_lambda_sq_dvd {ζ : L} (hζ : IsPrimitiveRoot ζ 5)
    (m : ℤ) (c : L) (hc : IsIntegral ℤ c)
    (hdvd : algebraMap ℚ L (m : ℚ) = (1 - ζ) ^ 2 * c) : (5 : ℤ) ∣ m := by
  -- Step 1: take norms of both sides of `hdvd`.
  have hL : Algebra.norm ℚ (algebraMap ℚ L (m : ℚ)) =
      Algebra.norm ℚ ((1 - ζ) ^ 2 * c) := congrArg (Algebra.norm ℚ) hdvd
  rw [map_mul, map_pow, norm_one_sub_zeta hζ, Algebra.norm_algebraMap, finrank_eq_four] at hL
  -- hL : (m : ℚ) ^ 4 = 5 ^ 2 * Algebra.norm ℚ c
  -- Step 2: `Algebra.norm ℚ c` is integral over `ℤ`, hence an ordinary integer.
  have hcInt : IsIntegral ℤ (Algebra.norm ℚ c) := Algebra.isIntegral_norm ℚ hc
  haveI : IsIntegrallyClosed ℤ := GCDMonoid.toIsIntegrallyClosed
  obtain ⟨k, hk⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hcInt
  have hk' : (k : ℚ) = Algebra.norm ℚ c := by
    rw [← hk]; simp
  rw [← hk'] at hL
  -- hL : (m : ℚ) ^ 4 = 5 ^ 2 * (k : ℚ)
  -- Step 3: transfer the equation to `ℤ`.
  have hZ : m ^ 4 = 25 * k := by exact_mod_cast hL
  -- Step 4: `5 ∣ m ^ 4`, hence `5 ∣ m` since `5` is prime.
  have hdvd4 : (5 : ℤ) ∣ m ^ 4 := ⟨5 * k, by linarith [hZ]⟩
  have hprime5 : Prime (5 : ℤ) := Int.prime_iff_natAbs_prime.mpr (by norm_num)
  exact hprime5.dvd_of_dvd_pow hdvd4

#print axioms cyclotomic_five_irreducible_rat
#print axioms finrank_eq_four
#print axioms norm_zeta_sub_one
#print axioms norm_one_sub_zeta
#print axioms five_dvd_of_lambda_sq_dvd

end BealLambdaNormBridge
