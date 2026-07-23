import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The 3-adic bias of the Syracuse map — Lean 4 (NEW)

This file formalizes the **deterministic 3-adic congruence** that drives the bias at
the heart of Tao's Syracuse-distribution program (T. Tao, *Almost all orbits of the
Collatz map attain almost bounded values*, Forum Math. Pi 2022).  No part of Tao's
Collatz paper has been formalized in any proof system before; this is the elementary
arithmetic seed of it.

## The map

For a natural number `N`, let `v = padicValNat 2 (3*N+1)` be the 2-adic valuation of
`3N+1`.  The **Syracuse map** is the *odd part* of `3N+1`:

    Syr N = (3*N+1) / 2 ^ v.

## The deterministic congruence (headline)

Working mod 3, `2 ≡ -1`, so `2^v ≡ (-1)^v`.  Since `Syr N · 2^v = 3N+1 ≡ 1 (mod 3)`,

    Syr N ≡ (-1)^v   (mod 3).

In particular `Syr N ≡ 1 (mod 3)` when `v` is even, `≡ 2 (mod 3)` when `v` is odd, and
**never `≡ 0`** — the Syracuse map never lands on a multiple of 3.  Because the 2-adic
valuation `v = v₂(3N+1)` is geometrically distributed (`P(v=k)=2^{-k}`), the odd-`v`
residue `2` occurs with mass `Σ_{k odd}2^{-k}=2/3`, twice the even-`v` residue `1`
(mass `1/3`).  That `2:1` split is the geometric series proved in `geometric_*_mass`.

## What is proved (all sorry-free, axiom-clean)

  * `Syr_mod_three`      — `(Syr N : ZMod 3) = (-1)^v`               (PRIMARY headline)
  * `Syr_mod_three_eq`   — explicit residue: `1` if `v` even else `2`
  * `Syr_not_dvd_three`  — `Syr N` is never divisible by 3
  * `geometric_odd_mass` — `∑_{j} 2^{-(2j+1)} = 2/3`   (odd-valuation mass)
  * `geometric_even_mass`— `∑_{j} 2^{-(2j+2)} = 1/3`   (even-valuation mass, ≥2)

The congruence is purely arithmetic — it needs only that `2^v` exactly divides `3N+1`
(`pow_padicValNat_dvd`) and `3N+1 ≡ 1 (mod 3)`.  The probabilistic `2:1` bias is stated
as the two closed-form geometric sums (no probability-space construction).
-/

namespace SyracuseThreeAdicBias

open scoped BigOperators

/-- The Syracuse map: the odd part of `3N+1`, i.e. `(3N+1)` with all factors of `2`
removed.  `Syr N = (3*N+1) / 2 ^ v₂(3N+1)`. -/
noncomputable def Syr (N : ℕ) : ℕ := (3 * N + 1) / 2 ^ (padicValNat 2 (3 * N + 1))

/-- **Exact-division identity.** `Syr N · 2^{v₂(3N+1)} = 3N+1`.  This holds because
`2^{v₂(3N+1)}` divides `3N+1` exactly (`pow_padicValNat_dvd`). -/
theorem Syr_mul_pow (N : ℕ) :
    Syr N * 2 ^ (padicValNat 2 (3 * N + 1)) = 3 * N + 1 :=
  Nat.div_mul_cancel pow_padicValNat_dvd

/-- Helper: `(-1)^v` squares to `1` in `ZMod 3` — i.e. it is its own inverse, hence a
unit (and nonzero). -/
private theorem neg_one_pow_sq (v : ℕ) :
    ((-1 : ZMod 3) ^ v) * ((-1 : ZMod 3) ^ v) = 1 := by
  rw [← mul_pow]; norm_num

/-- **PRIMARY headline — the deterministic 3-adic congruence.**
For any `N` (odd or not), the Syracuse iterate satisfies, in `ZMod 3`,

    Syr N = (-1) ^ v₂(3N+1).

(The oddness hypothesis is recorded to match the Syracuse setting but is not needed:
the congruence is forced by `2^v ∣ 3N+1` and `3N+1 ≡ 1 mod 3`.) -/
theorem Syr_mod_three (N : ℕ) (hN : Odd N) :
    (Syr N : ZMod 3) = (-1) ^ (padicValNat 2 (3 * N + 1)) := by
  set v := padicValNat 2 (3 * N + 1) with hv
  -- Cast the exact-division identity into `ZMod 3`.
  have hc : ((Syr N * 2 ^ v : ℕ) : ZMod 3) = ((3 * N + 1 : ℕ) : ZMod 3) := by
    rw [Syr_mul_pow N]
  have h2 : (2 : ZMod 3) = -1 := by decide
  push_cast at hc
  -- hc : (Syr N) * (2 : ZMod 3) ^ v = 3 * N + 1   (in ZMod 3)
  rw [h2, show (3 : ZMod 3) = 0 from by decide, zero_mul, zero_add] at hc
  -- hc : (Syr N) * (-1) ^ v = 1
  calc (Syr N : ZMod 3)
        = (Syr N : ZMod 3) * ((-1 : ZMod 3) ^ v * (-1 : ZMod 3) ^ v) := by
          rw [neg_one_pow_sq, mul_one]
    _ = ((Syr N : ZMod 3) * (-1 : ZMod 3) ^ v) * (-1 : ZMod 3) ^ v := by ring
    _ = 1 * (-1 : ZMod 3) ^ v := by rw [hc]
    _ = (-1 : ZMod 3) ^ v := one_mul _

/-- **Explicit residues.** `Syr N ≡ 1 (mod 3)` if the 2-adic valuation is even, and
`≡ 2 (mod 3)` if it is odd. -/
theorem Syr_mod_three_eq (N : ℕ) (hN : Odd N) :
    (Syr N : ZMod 3)
      = if Even (padicValNat 2 (3 * N + 1)) then 1 else (2 : ZMod 3) := by
  rw [Syr_mod_three N hN]
  by_cases h : Even (padicValNat 2 (3 * N + 1))
  · rw [if_pos h, h.neg_one_pow]
  · rw [if_neg h, (Nat.not_even_iff_odd.mp h).neg_one_pow]
    decide

/-- **The Syracuse map never hits a multiple of 3.** -/
theorem Syr_not_dvd_three (N : ℕ) (hN : Odd N) : ¬ (3 ∣ Syr N) := by
  intro hdvd
  have hz : (Syr N : ZMod 3) = 0 := (ZMod.natCast_eq_zero_iff (Syr N) 3).mpr hdvd
  rw [Syr_mod_three N hN] at hz
  -- (-1)^v = 0 contradicts ((-1)^v)² = 1.
  have := neg_one_pow_sq (padicValNat 2 (3 * N + 1))
  rw [hz, mul_zero] at this
  exact zero_ne_one this

/-! ## The `2:1` geometric bias of the valuation `v = v₂(3N+1)`

`v` is geometrically distributed with `P(v = k) = 2^{-k}`.  We record the two closed
forms that exhibit the `2:1` split: the odd-`v` mass is `2/3`, the even-`v` (`≥2`) mass
is `1/3`. -/

/-- `∑_{j≥0} 2^{-(2j+1)} = 2/3` — the total mass of **odd** 2-adic valuations
(`v = 1,3,5,…`), i.e. the residue-`2` Syracuse outputs. -/
theorem geometric_odd_mass :
    HasSum (fun j : ℕ => (2 : ℝ) ^ (-(2 * (j : ℤ) + 1))) (2 / 3) := by
  have hgeo : HasSum (fun j : ℕ => ((1 : ℝ) / 4) ^ j) (1 - 1 / 4)⁻¹ :=
    hasSum_geometric_of_lt_one (r := 1 / 4) (by norm_num) (by norm_num)
  have h := hgeo.mul_left ((1 : ℝ) / 2)
  have hval : (1 : ℝ) / 2 * (1 - 1 / 4)⁻¹ = 2 / 3 := by norm_num
  rw [hval] at h
  refine h.congr_fun (fun j => ?_)
  rw [zpow_neg, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
  rw [zpow_mul, zpow_one]
  rw [zpow_natCast, div_pow]
  norm_num

/-- `∑_{j≥0} 2^{-(2j+2)} = 1/3` — the total mass of **even** 2-adic valuations `≥ 2`
(`v = 2,4,6,…`), i.e. the residue-`1` Syracuse outputs. -/
theorem geometric_even_mass :
    HasSum (fun j : ℕ => (2 : ℝ) ^ (-(2 * (j : ℤ) + 2))) (1 / 3) := by
  have hgeo : HasSum (fun j : ℕ => ((1 : ℝ) / 4) ^ j) (1 - 1 / 4)⁻¹ :=
    hasSum_geometric_of_lt_one (r := 1 / 4) (by norm_num) (by norm_num)
  have h := hgeo.mul_left ((1 : ℝ) / 4)
  have hval : (1 : ℝ) / 4 * (1 - 1 / 4)⁻¹ = 1 / 3 := by norm_num
  rw [hval] at h
  refine h.congr_fun (fun j => ?_)
  rw [zpow_neg, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
  rw [zpow_mul]
  rw [zpow_natCast, div_pow]
  norm_num

end SyracuseThreeAdicBias
