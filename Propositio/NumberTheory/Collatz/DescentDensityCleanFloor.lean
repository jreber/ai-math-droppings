import Propositio.NumberTheory.Collatz.Basic
import Propositio.NumberTheory.Collatz.DensityCount
import Propositio.NumberTheory.Collatz.DescentDensityGeneral
import Propositio.NumberTheory.Collatz.AlmostAllDescendUncond
import Propositio.NumberTheory.Collatz.NonDescentWeight
import Propositio.NumberTheory.Collatz.BinomialTail
import Mathlib.Tactic

/-!
# Collatz descent density — a **native_decide-FREE** floor above `61/64`, and the limit `= 1`

This file delivers two axiom-clean results about the descending-residue density
`F(k) = D(k) / 2^k` (`D k` = number of residues mod `2^k` whose canonical lift
descends within `k` Terras steps, from `CollatzDensityCount`):

* **`collatz_descent_density_tendsto_one`** — `F(k) → 1`.  Immediate from
  `D k + β k = 2^k` (`bad_count_eq`) and the unconditional Everett–Terras decay
  `β k / 2^k → 0` (`collatz_almost_all_descend_uncond`), via `F = 1 − β/2^k`.

* **`descBy_density_ge_63_64`** — for every `k ≥ 78`, the lower natural density of
  integers descending within `k` Terras steps is `≥ 63/64`.  This **strictly
  improves** the previously-formalised clean floor `61/64`
  (`CollatzDescentDensityGeneral.descBy_density_ge_61_64`) **and supersedes** the
  `245/256` floor (`descBy_density_ge_245_256`), which relied on `native_decide`
  (carrying `Lean.ofReduceBool`).  The proof here is **kernel-`decide` only**:

  - `β(78) ≤ upperTail 78 (minOdd 78 − 1)` is the unconditional bound
    `beta_le_tail_pred` (no `2^k`-enumeration).
  - `minOdd 78 = 50` (the least `a` with `2^78 ≤ 3^a`) is pinned by two `norm_num`
    power comparisons.
  - `upperTail 78 49 = ∑_{i=34… no, i=49}^{78} C(78, i) = 4652323711743534623052`
    is a sum of **30 binomial coefficients**, each kernel-computable; this is NOT
    a `2^78`-residue census, so `decide` handles it in a few seconds.

  Hence `D(78) ≥ 2^78 − 4652323711743534623052 = 297579131191913759053492`, and
  `297579131191913759053492 / 2^78 ≈ 0.984616 > 63/64 = 0.984375`.  Propagating
  through the monotone density ladder `D_ratio_ge` carries the floor to all
  `k ≥ 78` with no further computation.

## Why `78`, and why this is the right clean target
The unconditional binomial-tail bound `β(k) ≤ ∑_{i ≥ minOdd k − 1} C(k,i)` is
much looser than the exact residue count `D(k)`, but it is computable from a
*handful* of binomials rather than a `2^k` census — so it survives kernel
`decide` at levels where the exact census (`D(14)` already overflows the kernel
evaluator stack) cannot.  `k = 78` is the first level at which this loose-but-clean
bound clears `63/64`.

## Axiom hygiene
Both headline theorems reduce to `[propext, Classical.choice, Quot.sound]`.
No `sorry`, no project `axiom`, **no `native_decide`**.
-/

namespace CollatzDescentDensityCleanFloor

open Filter Topology
open TerrasDensity
open CollatzStoppingF3
open CollatzDensityCount
open CollatzDescentDensityGeneral
open CollatzAlmostAllDescendUncond
open CollatzNonDescentWeight (minOdd minOdd_le_of_two_pow_le two_pow_le_three_pow_minOdd)

/-! ## §1  The descent density tends to `1` -/

/-- **`collatz_descent_density_tendsto_one`.**  The descending-residue density
`F(k) = D(k)/2^k` tends to `1`: almost every integer descends within its first
`k` Terras steps as `k → ∞`.  Proof: `F(k) = 1 − β(k)/2^k` (from
`β(k) + D(k) = 2^k`), and `β(k)/2^k → 0` is the unconditional Everett–Terras
theorem `collatz_almost_all_descend_uncond`. -/
theorem collatz_descent_density_tendsto_one :
    Tendsto (fun k => (D k : ℝ) / 2 ^ k) atTop (𝓝 1) := by
  have hbeta := collatz_almost_all_descend_uncond
  -- `F(k) = 1 − β(k)/2^k`
  have key : ∀ k, (D k : ℝ) / 2 ^ k = 1 - (beta k : ℝ) / 2 ^ k := by
    intro k
    have hbc : beta k + D k = 2 ^ k := bad_count_eq k
    have hcast : (D k : ℝ) = (2 : ℝ) ^ k - (beta k : ℝ) := by
      have := congrArg (Nat.cast : Nat → ℝ) hbc
      push_cast at this
      linarith
    have hpow : (2 : ℝ) ^ k ≠ 0 := by positivity
    rw [hcast]
    field_simp
  have hlim : Tendsto (fun k => 1 - (beta k : ℝ) / 2 ^ k) atTop (𝓝 (1 - 0)) :=
    (tendsto_const_nhds).sub hbeta
  rw [sub_zero] at hlim
  exact hlim.congr (fun k => (key k).symm)

/-! ## §2  A clean (`native_decide`-free) density floor `≥ 63/64` for all `k ≥ 78` -/

/-- `minOdd 78 = 50`: the least exponent `a` with `2^78 ≤ 3^a`.  Pinned by
`2^78 ≤ 3^50` (gives `minOdd 78 ≤ 50`) and `3^49 < 2^78` (gives `minOdd 78 ≥ 50`),
both `norm_num` comparisons of explicit integers. -/
theorem minOdd_78 : minOdd 78 = 50 := by
  apply le_antisymm
  · exact minOdd_le_of_two_pow_le 78 50 (by norm_num)
  · by_contra hlt
    have hsp : (2 : Nat) ^ 78 ≤ 3 ^ (minOdd 78) := two_pow_le_three_pow_minOdd 78
    have hmono : (3 : Nat) ^ (minOdd 78) ≤ 3 ^ 49 :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hle : (2 : Nat) ^ 78 ≤ 3 ^ 49 := le_trans hsp hmono
    have hcontra : (3 : Nat) ^ 49 < 2 ^ 78 := by norm_num
    omega

set_option maxRecDepth 10000 in
/-- `β(78) ≤ 4652323711743534623052` — the unconditional binomial-tail bound
`beta_le_tail_pred` at `k = 78`, evaluated with `minOdd 78 = 50`:
`β(78) ≤ upperTail 78 49 = ∑_{i=49}^{78} C(78,i) = 4652323711743534623052`.
This is a sum of `30` binomial coefficients, **kernel-`decide`-computable** (it is
NOT a `2^78`-residue census). -/
theorem beta_78_le : beta 78 ≤ 4652323711743534623052 := by
  have h := beta_le_tail_pred 78 (by norm_num)
  have htv : CollatzBinomialTail.upperTail 78 (minOdd 78 - 1) = 4652323711743534623052 := by
    rw [minOdd_78]; decide
  rw [htv] at h
  exact h

/-- `D(78) ≥ 297579131191913759053492 = 2^78 − 4652323711743534623052`.  From
`β(78) + D(78) = 2^78` (`bad_count_eq`) and the tail bound `beta_78_le`. -/
theorem D_78_ge : 297579131191913759053492 ≤ D 78 := by
  have hbc : beta 78 + D 78 = 2 ^ 78 := bad_count_eq 78
  have h2 : (2 : Nat) ^ 78 = 302231454903657293676544 := by norm_num
  rw [h2] at hbc
  have hb := beta_78_le
  omega

/-- **Lower natural density of integers descending within `k` Terras steps `≥ 63/64`
for EVERY `k ≥ 78`** — a clean (kernel-`decide`-only, `native_decide`-FREE) floor
strictly above the previous clean floor `61/64`, superseding the `native_decide`
`245/256` result.  Combines the tail-derived bound `D(78) ≥ 297579131191913759053492`
(`297579131191913759053492 / 2^78 ≈ 0.984616 > 63/64 = 0.984375`) with the monotone
density ladder `D_ratio_ge`, so the floor propagates to all larger step-budgets with
no further computation. -/
theorem descBy_density_ge_63_64 (k : Nat) (hk : 78 ≤ k) (p q : Nat)
    (hpq : 64 * p < 63 * q) : density_bounded_below (fun n => DescBy n k) p q := by
  apply descBy_density_general k p q
  rw [goodK_card_eq_D]
  have hD78 : 297579131191913759053492 ≤ D 78 := D_78_ge
  have hstep : p * 302231454903657293676544 < 297579131191913759053492 * q := by omega
  have hr : D 78 * 2 ^ k ≤ D k * 2 ^ 78 := D_ratio_ge 78 k hk
  have h2 : (2 : Nat) ^ 78 = 302231454903657293676544 := by norm_num
  rw [h2] at hr
  have hrr : 297579131191913759053492 * 2 ^ k ≤ D k * 302231454903657293676544 :=
    le_trans (Nat.mul_le_mul_right _ hD78) hr
  have hkey : p * 2 ^ k * 302231454903657293676544 < D k * q * 302231454903657293676544 := by
    calc p * 2 ^ k * 302231454903657293676544
        = (p * 302231454903657293676544) * 2 ^ k := by ring
      _ < (297579131191913759053492 * q) * 2 ^ k := by gcongr
      _ = (297579131191913759053492 * 2 ^ k) * q := by ring
      _ ≤ (D k * 302231454903657293676544) * q := Nat.mul_le_mul_right _ hrr
      _ = D k * q * 302231454903657293676544 := by ring
  exact lt_of_mul_lt_mul_right hkey (Nat.zero_le _)

/-! ## §3  The clean floor can be pushed arbitrarily close to `1` -/

/-- **Bridge lemma.**  A lower bound `p · 2^k < D(k) · q` on the integer count `D k`
(the number of residues mod `2^k` descending within `k` Terras steps) is exactly what
`descBy_density_general` needs: it yields `density_bounded_below (DescBy · k) p q`.  This
factors out the core step used in `descBy_density_ge_63_64`, stated for an arbitrary
target ratio `p/q`. -/
theorem descBy_density_of_D_bound (k p q : Nat) (h : p * 2 ^ k < D k * q) :
    density_bounded_below (fun n => DescBy n k) p q := by
  apply descBy_density_general k p q
  rw [goodK_card_eq_D]
  exact h

/-- **`descBy_density_approaches_one`.**  For ANY target ratio `p/q < 1`, there is a level
`K` beyond which the lower natural density of integers with Terras stopping time `≤ k` is
`≥ p/q`.  This is the honest "density limit `= 1`" in `density_bounded_below` form: it
generalizes both the `61/64` and `63/64` clean floors into a single statement asserting the
floor can be pushed arbitrarily close to `1`.

Proof: the real sequence `D(k)/2^k → 1` (`collatz_descent_density_tendsto_one`); since
`(p:ℝ)/q < 1`, eventually `(p:ℝ)/q < D(k)/2^k`, which clears denominators to the integer
inequality `p · 2^k < D(k) · q`; feed that to the bridge `descBy_density_of_D_bound`. -/
theorem descBy_density_approaches_one (p q : ℕ) (hq : 0 < q) (hpq : p < q) :
    ∃ K, ∀ k, K ≤ k → density_bounded_below (fun n => DescBy n k) p q := by
  -- `p/q < 1` as reals
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  have hlt1 : (p : ℝ) / q < 1 := by
    rw [div_lt_one hqpos]; exact_mod_cast hpq
  -- since `D k / 2^k → 1`, eventually `p/q < D k / 2^k`
  have hev : ∀ᶠ k in atTop, (p : ℝ) / q < (D k : ℝ) / 2 ^ k :=
    collatz_descent_density_tendsto_one.eventually (eventually_gt_nhds hlt1)
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.mp hev
  refine ⟨K, fun k hk => ?_⟩
  -- clear denominators at this `k`
  have hpow : (0 : ℝ) < 2 ^ k := by positivity
  have hreal : (p : ℝ) * 2 ^ k < (D k : ℝ) * q := (div_lt_div_iff₀ hqpos hpow).mp (hK k hk)
  have hnat : p * 2 ^ k < D k * q := by exact_mod_cast hreal
  exact descBy_density_of_D_bound k p q hnat

end CollatzDescentDensityCleanFloor
