import Propositio.NumberTheory.Beal.FermatLastTheoremFiveCaseTwo
import Propositio.NumberTheory.Beal.GoldenIntCoprime
import Mathlib.Tactic

/-!
# Exposing the coprime cofactors of Case II, and their `√5`-valuation in `ℤ[φ]`

`FermatLastTheoremFiveCaseTwo.case2_core` proves the classical `5`-adic factorization of Case II,
but its public conclusion only exposes the *final* `d, e` form (`x+y = 5·d⁵` etc.). Internally it
first extracts the **coprime cofactors** `A, B` with `x+y = 5·A`, `Φ = 5·B`, `gcd(A,B)=1` — and it
is *that* intermediate data (not the final fifth-power form) that the `ℤ[φ]`-transport bricks
(`BealGoldenIntCoprime.caseTwoFactor_common_dvd_sqrt5_sq`,
`BealGoldenIntRamification.sqrt5_valuation_one_of_five_dvd_norm_not_25`) actually consume.

This file re-derives that intermediate cofactor data as a **standalone public lemma**
(`case2_coprime_cofactors`) — leaving the gated `case2_core` completely untouched — and then wires
it directly into the transport layer:

## Main results (proved, axiom-clean, no `sorry`)

* `case2_coprime_cofactors` — **item-(a) input, now exposed.** For coprime `x, y` with
  `x⁵+y⁵ = z⁵` and `5 ∣ z`, there exist coprime `A, B` with `x + y = 5·A` and `Φ(x,y) = 5·B`.
  (This is steps 1–4 of `case2_core`, lifted out of its `∃ d e …` conclusion so downstream code
  can name `A, B` and apply the Bézout peeling engine directly.)
* `GoldenInt.caseTwoFactor_common_dvd_sqrt5_sq_of_solution` — **`caseTwoFactor_common_dvd_sqrt5_sq`
  applied directly.** For any Case-II solution, *any* common divisor `g` of `ofInt (x+y)` and
  `ofInt Φ` in `ℤ[φ]` divides `√5² = 5`. No hand-threading of `A, B` at the call site: the
  cofactor data is produced internally by `case2_coprime_cofactors`.
* `GoldenInt.sqrt5_valuation_one_caseTwoFactorL` — **item-(2), the exact `√5`-valuation.** When
  `5 ∣ Φ` but `25 ∤ Φ`, the concrete left factor `caseTwoFactorL x y` has `√5`-valuation exactly
  `1` (`√5 ∣ L` but `√5² ∤ L`), via `norm (caseTwoFactorL) = -Φ` fed to
  `sqrt5_valuation_one_of_five_dvd_norm_not_25`.
* `GoldenInt.sqrt5_valuation_one_caseTwoFactorL_of_cofactor` — the same, keyed on the **cofactor
  branch**: given `Φ = 5·B` with `5 ∤ B` (the `case2_core` `¬ 5 ∣ B` branch, where the high
  `5`-power lives in `x+y`, not in `Φ`), the left factor has `√5`-valuation exactly `1`. This makes
  explicit the case split "which of `x+y`, `Φ` carries the high `5`-power": `25 ∣ Φ ↔ 5 ∣ B`.
* `GoldenInt.sqrt5_sq_dvd_caseTwoFactorL_of_25_dvd` — the complementary high-valuation side: when
  `25 ∣ Φ` (the branch where the high `5`-power lives in `Φ`), `√5² ∣ caseTwoFactorL`.

## What this does NOT do (honest scope note)

This finishes the **coprimality-transport + single-factor exact-valuation** layer of item (a): the
cofactor data is now a first-class lemma, the `√5²`-common-divisor bound is applicable directly to
any solution, and the `√5`-valuation of the concrete left factor is pinned in both branches. It does
**not** perform the "unit × fifth power" extraction (item (b)) — pulling the peeled residual back to
an exact fifth power up to a unit and pinning the unit via `BealGoldenIntUnits.unit_eq_pm_phiZpow` —
nor does it assemble the well-founded descent. Those remain the open bricks.

**No `sorry`, no project axiom** in what follows.
-/

namespace FermatLastTheoremFiveCaseTwo

open FermatLastTheoremFiveCaseOne
open GoldenInt

/-! ## Item (a) input: the coprime cofactors, exposed -/

/-- **Coprime cofactors of Case II, exposed.** For coprime `x, y` with `x⁵+y⁵ = z⁵` and `5 ∣ z`,
there exist coprime `A, B` with `x + y = 5·A` and `Φ(x,y) = 5·B`. This is exactly steps 1–4 of
`case2_core` (`5 ∣ x+y` via Frobenius; `5 ∣ Φ`; `gcd(x+y, Φ) = 5`; peel the `5`), lifted out of
`case2_core`'s `∃ d e …` conclusion so that downstream `ℤ[φ]`-transport code can name `A, B` and
feed them to `caseTwoFactor_common_dvd_sqrt5_sq` directly. -/
theorem case2_coprime_cofactors {x y z : ℤ}
    (hxy : IsCoprime x y)
    (heq : x ^ 5 + y ^ 5 = z ^ 5) (h5z : (5 : ℤ) ∣ z) :
    ∃ (A B : ℤ),
      IsCoprime A B ∧
      x + y = 5 * A ∧
      x ^ 4 - x ^ 3 * y + x ^ 2 * y ^ 2 - x * y ^ 3 + y ^ 4 = 5 * B := by
  -- Step 1: 5 ∣ (x+y), by the Frobenius/"freshman's dream" trick.
  have h5xy : (5 : ℤ) ∣ (x + y) := by
    have hcast := cast_add_eq_cast_of_pow_five_eq heq
    have hz_zero : (z : ZMod 5) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd z 5).mpr h5z
    have hxy0 : ((x + y : ℤ) : ZMod 5) = 0 := by rw [hcast, hz_zero]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd (x + y) 5).mp hxy0
  -- Step 2: 5 ∣ Φ(x,y), from the cofactor identity Φ = 5x⁴ + (x+y)·(...).
  have h5Phi : (5 : ℤ) ∣ (x ^ 4 - x ^ 3 * y + x ^ 2 * y ^ 2 - x * y ^ 3 + y ^ 4) := by
    have hident := quintic_cofactor_identity x y
    rw [hident]
    exact dvd_add (dvd_mul_right 5 (x ^ 4)) (h5xy.mul_right _)
  -- Step 3: gcd(x+y, Φ) = 5 exactly.
  have hd5 : Int.gcd (x + y) (x ^ 4 - x ^ 3 * y + x ^ 2 * y ^ 2 - x * y ^ 3 + y ^ 4) ∣ 5 := by
    have h := quintic_factor_gcd_dvd_five hxy (Int.gcd_dvd_left (x + y)
      (x ^ 4 - x ^ 3 * y + x ^ 2 * y ^ 2 - x * y ^ 3 + y ^ 4))
      (Int.gcd_dvd_right (x + y) (x ^ 4 - x ^ 3 * y + x ^ 2 * y ^ 2 - x * y ^ 3 + y ^ 4))
    exact_mod_cast h
  have h5_dvd_gcd : (5 : ℕ) ∣
      Int.gcd (x + y) (x ^ 4 - x ^ 3 * y + x ^ 2 * y ^ 2 - x * y ^ 3 + y ^ 4) :=
    Int.dvd_gcd (c := 5) (by exact_mod_cast h5xy) (by exact_mod_cast h5Phi)
  have hgcd5 : Int.gcd (x + y) (x ^ 4 - x ^ 3 * y + x ^ 2 * y ^ 2 - x * y ^ 3 + y ^ 4) = 5 :=
    Nat.dvd_antisymm hd5 h5_dvd_gcd
  -- Step 4: extract coprime cofactors A, B with x+y = 5A, Φ = 5B.
  have hgcd_pos :
      0 < Int.gcd (x + y) (x ^ 4 - x ^ 3 * y + x ^ 2 * y ^ 2 - x * y ^ 3 + y ^ 4) := by
    rw [hgcd5]; norm_num
  obtain ⟨A, B, hAB1, hxyA, hPhiB⟩ := Int.exists_gcd_one hgcd_pos
  rw [hgcd5] at hxyA hPhiB
  have hcopAB : IsCoprime A B := Int.isCoprime_iff_gcd_eq_one.mpr hAB1
  have hxyA' : x + y = 5 * A := by rw [hxyA]; push_cast; ring
  have hPhiB' : x ^ 4 - x ^ 3 * y + x ^ 2 * y ^ 2 - x * y ^ 3 + y ^ 4 = 5 * B := by
    rw [hPhiB]; push_cast; ring
  exact ⟨A, B, hcopAB, hxyA', hPhiB'⟩

/-! ## `caseTwoFactor_common_dvd_sqrt5_sq`, applied directly to a solution -/

/-- **The item-(a) headline, applied to any Case-II solution.** For coprime `x, y` with
`x⁵+y⁵ = z⁵` and `5 ∣ z`, *any* common divisor `g` of `ofInt (x+y)` and `ofInt Φ` in `ℤ[φ]` divides
`√5² = 5`. The coprime cofactor data `A, B` is produced internally by `case2_coprime_cofactors`, so
the call site no longer has to thread it by hand — this is the "apply directly" upgrade the
`BealGoldenIntCoprime` scope note asked for. -/
theorem caseTwoFactor_common_dvd_sqrt5_sq_of_solution {x y z : ℤ}
    (hxy : IsCoprime x y)
    (heq : x ^ 5 + y ^ 5 = z ^ 5) (h5z : (5 : ℤ) ∣ z)
    {g : GoldenInt}
    (hg1 : g ∣ ofInt (x + y))
    (hg2 : g ∣ ofInt (x ^ 4 - x ^ 3 * y + x ^ 2 * y ^ 2 - x * y ^ 3 + y ^ 4)) :
    g ∣ sqrt5 * sqrt5 := by
  obtain ⟨A, B, hcop, hxyA, hPhiB⟩ := case2_coprime_cofactors hxy heq h5z
  exact caseTwoFactor_common_dvd_sqrt5_sq hcop hxyA hPhiB hg1 hg2

/-! ## Item (2): exact `√5`-valuation of the concrete left factor -/

/-- **Exact `√5`-valuation `= 1` of `caseTwoFactorL`, via the `25 ∤ Φ` control.** When `5 ∣ Φ` but
`25 ∤ Φ`, the concrete left factor `caseTwoFactorL x y` (with `norm = -Φ`) is divisible by `√5`
exactly once: `√5 ∣ L` and `√5² ∤ L`. This is `sqrt5_valuation_one_of_five_dvd_norm_not_25` fed the
factor's norm `-Φ` (`5 ∣ -Φ ↔ 5 ∣ Φ`, `25 ∣ -Φ ↔ 25 ∣ Φ`). -/
theorem sqrt5_valuation_one_caseTwoFactorL {x y : ℤ}
    (h5 : (5 : ℤ) ∣ (x ^ 4 - x ^ 3 * y + x ^ 2 * y ^ 2 - x * y ^ 3 + y ^ 4))
    (h25 : ¬ (25 : ℤ) ∣ (x ^ 4 - x ^ 3 * y + x ^ 2 * y ^ 2 - x * y ^ 3 + y ^ 4)) :
    sqrt5 ∣ caseTwoFactorL x y ∧ ¬ (sqrt5 * sqrt5 ∣ caseTwoFactorL x y) := by
  apply sqrt5_valuation_one_of_five_dvd_norm_not_25
  · rw [norm_caseTwoFactorL, dvd_neg]; exact h5
  · rw [norm_caseTwoFactorL, dvd_neg]; exact h25

/-- **Exact `√5`-valuation `= 1` of `caseTwoFactorL`, keyed on the cofactor branch.** Given the
cofactor form `Φ = 5·B` with `5 ∤ B` — this is the `case2_core` `¬ 5 ∣ B` branch, in which the high
`5`-power sits in `x+y` rather than in `Φ` — the left factor `caseTwoFactorL x y` has `√5`-valuation
exactly `1`. The equivalence `25 ∣ Φ ↔ 5 ∣ B` (from `Φ = 5·B`) is exactly the "which factor carries
the high `5`-power" case split. -/
theorem sqrt5_valuation_one_caseTwoFactorL_of_cofactor {x y B : ℤ}
    (hPhiB : x ^ 4 - x ^ 3 * y + x ^ 2 * y ^ 2 - x * y ^ 3 + y ^ 4 = 5 * B)
    (h5B : ¬ (5 : ℤ) ∣ B) :
    sqrt5 ∣ caseTwoFactorL x y ∧ ¬ (sqrt5 * sqrt5 ∣ caseTwoFactorL x y) := by
  apply sqrt5_valuation_one_caseTwoFactorL
  · rw [hPhiB]; exact dvd_mul_right 5 B
  · rw [hPhiB]
    intro h
    apply h5B
    have h55 : (5 : ℤ) * 5 ∣ 5 * B := by rwa [show (25 : ℤ) = 5 * 5 from by norm_num] at h
    exact (mul_dvd_mul_iff_left (by norm_num : (5 : ℤ) ≠ 0)).mp h55

/-- **High `√5`-valuation side.** When `25 ∣ Φ` — the `case2_core` branch in which the high
`5`-power sits in `Φ` rather than in `x+y` — the concrete left factor is divisible by `√5²`. Proof:
`5 ∣ Φ ⟹ √5 ∣ L`, write `L = √5·β`; then `norm L = -5·norm β = -Φ`, so `norm β = Φ/5` and
`25 ∣ Φ ⟹ 5 ∣ norm β ⟹ √5 ∣ β ⟹ √5² ∣ L`. -/
theorem sqrt5_sq_dvd_caseTwoFactorL_of_25_dvd {x y : ℤ}
    (h25 : (25 : ℤ) ∣ (x ^ 4 - x ^ 3 * y + x ^ 2 * y ^ 2 - x * y ^ 3 + y ^ 4)) :
    sqrt5 * sqrt5 ∣ caseTwoFactorL x y := by
  have h5 : (5 : ℤ) ∣ (x ^ 4 - x ^ 3 * y + x ^ 2 * y ^ 2 - x * y ^ 3 + y ^ 4) :=
    dvd_trans (by norm_num) h25
  -- √5 ∣ L
  have hL : sqrt5 ∣ caseTwoFactorL x y := sqrt5_dvd_caseTwoFactorL h5
  obtain ⟨β, hβ⟩ := hL
  -- norm β is divisible by 5, because 25 ∣ Φ = -norm L = 5·norm β.
  have hnorm : norm (caseTwoFactorL x y) = -5 * norm β := sqrt5_cofactor_norm hβ
  have hnormL : norm (caseTwoFactorL x y) =
      -(x ^ 4 - x ^ 3 * y + x ^ 2 * y ^ 2 - x * y ^ 3 + y ^ 4) := norm_caseTwoFactorL x y
  have h5nb : (5 : ℤ) ∣ norm β := by
    obtain ⟨k, hk⟩ := h25
    -- -5 * norm β = -Φ = -25k = -5·(5k), so norm β = 5k.
    refine ⟨k, ?_⟩
    have hthis : (-5 : ℤ) * norm β = -5 * (5 * k) := by
      rw [← hnorm, hnormL, hk]; ring
    exact mul_left_cancel₀ (by norm_num : (-5 : ℤ) ≠ 0) hthis
  -- hence √5 ∣ β, so √5² ∣ L.
  have hβ5 : sqrt5 ∣ β := sqrt5_dvd_of_five_dvd_norm h5nb
  obtain ⟨γ, hγ⟩ := hβ5
  exact ⟨γ, by rw [hβ, hγ]; ring⟩

end FermatLastTheoremFiveCaseTwo

section AxiomCheck
open FermatLastTheoremFiveCaseTwo GoldenInt
#print axioms case2_coprime_cofactors
#print axioms caseTwoFactor_common_dvd_sqrt5_sq_of_solution
#print axioms sqrt5_valuation_one_caseTwoFactorL
#print axioms sqrt5_valuation_one_caseTwoFactorL_of_cofactor
#print axioms sqrt5_sq_dvd_caseTwoFactorL_of_25_dvd
end AxiomCheck
