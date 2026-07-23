import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Int.CardIntervalMod
import Mathlib.Data.Nat.Count
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Positivity

/-!
# The valuation distribution of the Syracuse map — Lean 4 (NEW)

This file proves the **exact counting fact** behind the geometric law
`P(v₂(3N+1) = j) = 2^{-j}` that underlies Tao's Syracuse-distribution program
(T. Tao, *Almost all orbits of the Collatz map attain almost bounded values*,
Forum Math. Pi 2022).  It is the genuine *distributional* content that the sibling
file `SyracuseThreeAdicBias.lean` was missing: that file proved the closed-form
geometric masses (`geometric_odd_mass`, `geometric_even_mass`) but did not connect
them to the actual map.  Here we connect them by **counting residues**.

## The map and the counting law

For `N : ℕ` write `v N = padicValNat 2 (3 * N + 1)` for the 2-adic valuation of `3N+1`.
The key structural facts proved below, for `j ≥ 1`:

* `v_eq_iff`        — `v N = j ↔ 2^j ∣ 3N+1 ∧ ¬ 2^(j+1) ∣ 3N+1`.
* `v_eq_iff_modEq`  — `v N = j ↔ 3N+1 ≡ 2^j (mod 2^(j+1))`  (single-period congruence).
* `exists_residue`  — `v N = j` selects **exactly one residue class** mod `2^(j+1)`
                      (3 is a unit mod `2^(j+1)`, so the linear congruence has a unique root).

From the unique-residue description, an arithmetic-progression count gives the headline:

* `card_valuation_eq_one_per_period` — over one period `[0, 2^(j+1))` there is
  **exactly one** `N` with `v N = j`                                    (PRIMARY).
* `card_valuation_eq`               — over `[0, 2^K)` (with `j+1 ≤ K`) there are
  exactly `2^(K-j-1)` such `N`                                          (HEADLINE).
* `density_valuation_eq`            — hence the proportion among all `N < 2^K` is
  `2^{-(j+1)}`, matching the geometric masses of the sibling file    (corollary).

Everything is elementary 2-adic periodicity + a residue count; no probability space is
built.  All theorems are `sorry`-free and axiom-clean.
-/

namespace SyracuseValuationDistribution

open Finset

/-- The 2-adic valuation of `3N+1`. -/
def v (N : ℕ) : ℕ := padicValNat 2 (3 * N + 1)

/-- **Valuation characterization.** `v N = j` iff `2^j` divides `3N+1` but `2^(j+1)`
does not.  Pure consequence of `padicValNat_dvd_iff_le`. -/
theorem v_eq_iff (N j : ℕ) :
    v N = j ↔ (2 ^ j ∣ 3 * N + 1 ∧ ¬ 2 ^ (j + 1) ∣ 3 * N + 1) := by
  have ha : (3 * N + 1) ≠ 0 := by omega
  unfold v
  rw [padicValNat_dvd_iff_le ha, padicValNat_dvd_iff_le ha]
  omega

/-- Elementary divisibility lemma: for `p > 0`, an integer is divisible by `p` but not
by `2p` exactly when it is `≡ p (mod 2p)`.  This is the "one residue per period" core. -/
private theorem dvd_not_dvd_iff_modEq {a p : ℕ} (hp : 0 < p) :
    (p ∣ a ∧ ¬ 2 * p ∣ a) ↔ a ≡ p [MOD 2 * p] := by
  unfold Nat.ModEq
  rw [Nat.mod_eq_of_lt (show p < 2 * p by omega)]
  constructor
  · rintro ⟨⟨q, rfl⟩, h2⟩
    have hodd : ¬ 2 ∣ q := fun ⟨k, hk⟩ => h2 ⟨k, by rw [hk]; ring⟩
    obtain ⟨k, rfl⟩ : ∃ k, q = 2 * k + 1 := ⟨q / 2, by omega⟩
    have hexp : p * (2 * k + 1) = p + 2 * p * k := by ring
    rw [hexp, Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt (by omega)
  · intro h
    have hdm := Nat.div_add_mod a (2 * p)
    rw [h] at hdm
    set Q := a / (2 * p) with hQ
    refine ⟨⟨2 * Q + 1, ?_⟩, ?_⟩
    · rw [← hdm]; ring
    · rintro ⟨t, ht⟩
      have hcancel : 2 * Q + 1 = 2 * t := by
        apply Nat.eq_of_mul_eq_mul_left hp
        have e1 : p * (2 * Q + 1) = a := by rw [← hdm]; ring
        have e2 : p * (2 * t) = a := by rw [ht]; ring
        rw [e1, e2]
      omega

/-- **Single-period congruence.** `v N = j ↔ 3N+1 ≡ 2^j (mod 2^(j+1))`. -/
theorem v_eq_iff_modEq (N j : ℕ) :
    v N = j ↔ 3 * N + 1 ≡ 2 ^ j [MOD 2 ^ (j + 1)] := by
  rw [v_eq_iff, pow_succ']
  exact dvd_not_dvd_iff_modEq (pow_pos (by norm_num) j)

/-- **One residue class per period.** For each `j` there is a residue `N₀` such that
`v N = j` happens precisely when `N ≡ N₀ (mod 2^(j+1))`.  Existence and uniqueness of the
class come from `3` being a unit modulo `2^(j+1)`. -/
theorem exists_residue (j : ℕ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, v N = j ↔ N ≡ N₀ [MOD 2 ^ (j + 1)] := by
  set m := 2 ^ (j + 1) with hm
  haveI : NeZero m := ⟨by rw [hm]; exact (pow_pos (by norm_num) (j + 1)).ne'⟩
  have hcop : Nat.Coprime 3 m := by
    rw [hm]; exact (show Nat.Coprime 3 2 by decide).pow_right (j + 1)
  have hcopgcd : Nat.gcd m 3 = 1 := by rw [Nat.gcd_comm]; exact hcop
  have hunit3 : IsUnit (3 : ZMod m) := by
    simpa using (ZMod.isUnit_iff_coprime 3 m).mpr hcop
  set t : ZMod m := (3 : ZMod m)⁻¹ * ((2 : ZMod m) ^ j - 1) with ht
  have hsol : (3 : ZMod m) * t + 1 = (2 : ZMod m) ^ j := by
    rw [ht, ← mul_assoc, ZMod.mul_inv_of_unit (3 : ZMod m) hunit3]
    ring
  have hN0 : 3 * t.val + 1 ≡ 2 ^ j [MOD m] := by
    rw [← ZMod.natCast_eq_natCast_iff]
    push_cast
    rw [ZMod.natCast_zmod_val t]
    exact hsol
  refine ⟨t.val, fun N => ?_⟩
  rw [v_eq_iff_modEq, ← hm]
  constructor
  · intro h
    have h2 : 3 * N + 1 ≡ 3 * t.val + 1 [MOD m] := h.trans hN0.symm
    have h3 : 3 * N ≡ 3 * t.val [MOD m] := Nat.ModEq.add_right_cancel' 1 h2
    exact Nat.ModEq.cancel_left_of_coprime hcopgcd h3
  · intro h
    exact ((h.mul_left 3).add_right 1).trans hN0

/-- **HEADLINE — the geometric count.** For `1 ≤ j` and `j + 1 ≤ K`, the number of
`N < 2^K` with `v₂(3N+1) = j` is exactly `2^(K-j-1)`.  This is the genuine
distributional statement: dividing by `2^K` yields the geometric mass `2^{-(j+1)}`. -/
theorem card_valuation_eq (K j : ℕ) (hj : 1 ≤ j) (hjK : j + 1 ≤ K) :
    ((Finset.range (2 ^ K)).filter (fun N => v N = j)).card = 2 ^ (K - j - 1) := by
  obtain ⟨N₀, hN₀⟩ := exists_residue j
  have hfilter : (Finset.range (2 ^ K)).filter (fun N => v N = j)
      = (Finset.range (2 ^ K)).filter (fun N => N ≡ N₀ [MOD 2 ^ (j + 1)]) :=
    Finset.filter_congr (fun N _ => hN₀ N)
  rw [hfilter, ← Nat.count_eq_card_filter_range,
    Nat.count_modEq_card (2 ^ K) (pow_pos (by norm_num) (j + 1)) N₀]
  have hsplit : 2 ^ K = 2 ^ (j + 1) * 2 ^ (K - j - 1) := by
    rw [← pow_add]; congr 1; omega
  have hmod : 2 ^ K % 2 ^ (j + 1) = 0 := by rw [hsplit, Nat.mul_mod_right]
  have hdiv : 2 ^ K / 2 ^ (j + 1) = 2 ^ (K - j - 1) := by
    rw [hsplit, Nat.mul_div_cancel_left _ (pow_pos (by norm_num) (j + 1))]
  rw [hmod, hdiv, if_neg (Nat.not_lt_zero (N₀ % 2 ^ (j + 1))), add_zero]

/-- **PRIMARY headline — exactly one residue per period.** Over one full period
`[0, 2^(j+1))` there is exactly one `N` with `v₂(3N+1) = j` (for `j ≥ 1`). -/
theorem card_valuation_eq_one_per_period (j : ℕ) (hj : 1 ≤ j) :
    ((Finset.range (2 ^ (j + 1))).filter (fun N => v N = j)).card = 1 := by
  have h := card_valuation_eq (j + 1) j hj le_rfl
  rwa [show (j + 1) - j - 1 = 0 from by omega, pow_zero] at h

/-- **Density corollary.** The proportion of `N < 2^K` with `v₂(3N+1) = j` equals
`2^{-(j+1)}`, exhibiting the geometric law `P(v = j) = 2^{-j}` over the odds. -/
theorem density_valuation_eq (K j : ℕ) (hj : 1 ≤ j) (hjK : j + 1 ≤ K) :
    (((Finset.range (2 ^ K)).filter (fun N => v N = j)).card : ℝ) / (2 : ℝ) ^ K
      = 1 / (2 : ℝ) ^ (j + 1) := by
  rw [card_valuation_eq K j hj hjK]
  push_cast
  rw [div_eq_div_iff (by positivity) (by positivity), one_mul, ← pow_add]
  congr 1
  omega

end SyracuseValuationDistribution
