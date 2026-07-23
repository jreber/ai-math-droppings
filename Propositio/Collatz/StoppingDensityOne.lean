import Propositio.Collatz.Basic
import Propositio.Collatz.StoppingF3
import Propositio.Collatz.DescentDensityCleanFloor
import Mathlib.Tactic

/-!
# Collatz: the natural density of integers with finite Terras stopping time is `1`

This file packages the unconditional Everett–Terras descent-density results into the
single-set statement of the Terras (1976) theorem: **almost every natural number has a
finite Terras stopping time.**

`StopFinite n` says the Terras orbit of `n` eventually drops strictly below `n`
(`∃ j ≥ 1, T^j(n) < n`).  This is exactly `∃ k, DescBy n k`, the union over all
step-budgets `k` of the "descends within `k` steps" predicate.

* `stopFinite_density_bounded_below` — for any ratio `p/q < 1`, the lower natural
  density of `StopFinite` is `≥ p/q`.  (The project's `density_bounded_below` form of
  "density `≥ p/q`.")  Obtained from `descBy_density_approaches_one` at the single level
  `k = K` plus monotonicity of `count_upto` under the predicate inclusion
  `DescBy n K → StopFinite n`.

* `stopFinite_density_tendsto_one` — **HEADLINE.** The real counting ratio
  `count_upto StopFinite N / N → 1`.  A squeeze: the upper bound `count ≤ N+1` gives
  `count/N ≤ (N+1)/N → 1`; the lower bound for each `a < 1` comes from
  `stopFinite_density_bounded_below n (n+1)` with `n/(n+1) > a`.  Assembled via
  `tendsto_order`.

Both headline theorems reduce to `[propext, Classical.choice, Quot.sound]`.
-/

namespace CollatzStoppingDensityOne

open Filter Topology
open TerrasDensity
open CollatzStoppingF3
open CollatzDescentDensityCleanFloor

attribute [local instance] Classical.propDecidable

/-- **Integers with finite Terras stopping time.**  The orbit of `n` under the Terras
half-step map `T` eventually drops strictly below the starting value. -/
def StopFinite (n : ℕ) : Prop := ∃ j : ℕ, 1 ≤ j ∧ T_iter n j < n

/-- **Bridge.**  Descending within `k` Terras steps implies a finite stopping time.
Immediate: drop the upper bound `j ≤ k` from the `DescBy` witness. -/
theorem descBy_imp_stopFinite {n k : ℕ} (h : DescBy n k) : StopFinite n := by
  obtain ⟨j, hj1, _, hlt⟩ := h
  exact ⟨j, hj1, hlt⟩

/-- `StopFinite n ↔ ∃ k, DescBy n k`:  `StopFinite` is the union over all step
budgets of the bounded-descent predicates. -/
theorem stopFinite_iff_exists_descBy (n : ℕ) : StopFinite n ↔ ∃ k, DescBy n k := by
  constructor
  · rintro ⟨j, hj1, hlt⟩; exact ⟨j, j, hj1, le_refl j, hlt⟩
  · rintro ⟨k, h⟩; exact descBy_imp_stopFinite h

/-! ## Counting bridge -/

/-- Instance-bridging for `Nat.count` (all `DecidablePred` instances agree). -/
private theorem count_inst_eq {P : ℕ → Prop} (i₁ i₂ : DecidablePred P) (n : ℕ) :
    @Nat.count P i₁ n = @Nat.count P i₂ n := by
  cases Subsingleton.elim i₁ i₂; rfl

/-- `count_upto` monotonicity under predicate inclusion, phrased through the classical
`count_upto`.  Mirror of the same private helper in `CollatzStoppingF3`. -/
private theorem count_upto_mono {N : ℕ} (A B : ℕ → Prop)
    (h : ∀ k, k < N + 1 → A k → B k) :
    count_upto A N ≤ count_upto B N := by
  unfold count_upto
  rw [count_inst_eq (fun a => Classical.propDecidable _) (Classical.decPred _) (N + 1),
      count_inst_eq (fun a => Classical.propDecidable _) (Classical.decPred _) (N + 1)]
  exact Nat.count_mono_left h

/-- `count_upto A N ≤ N + 1`:  at most `N + 1` of the integers `0, …, N` satisfy `A`. -/
private theorem count_upto_le (A : ℕ → Prop) (N : ℕ) : count_upto A N ≤ N + 1 := by
  unfold count_upto; exact Nat.count_le _

/-! ## §1  Lower density bound -/

/-- **`stopFinite_density_bounded_below`.**  For ANY ratio `p/q < 1`, the lower natural
density of the integers with finite Terras stopping time is `≥ p/q`.

Proof: `descBy_density_approaches_one` gives a level `K` whose bounded-descent set already
has lower density `≥ p/q`; since `DescBy n K → StopFinite n`, the count of `StopFinite`
dominates, so the same lower bound transfers. -/
theorem stopFinite_density_bounded_below (p q : ℕ) (hq : 0 < q) (hpq : p < q) :
    density_bounded_below StopFinite p q := by
  obtain ⟨K, hK⟩ := descBy_density_approaches_one p q hq hpq
  obtain ⟨N₀, hN₀⟩ := hK K (le_refl K)
  refine ⟨N₀, fun N hN => ?_⟩
  have h1 : p * N ≤ q * count_upto (fun n => DescBy n K) N := hN₀ N hN
  have h2 : count_upto (fun n => DescBy n K) N ≤ count_upto StopFinite N :=
    count_upto_mono _ _ (fun k _ hk => descBy_imp_stopFinite hk)
  calc p * N ≤ q * count_upto (fun n => DescBy n K) N := h1
    _ ≤ q * count_upto StopFinite N := by gcongr

/-! ## §2  The counting ratio tends to `1` -/

/-- **`stopFinite_density_tendsto_one` (HEADLINE).**  The natural density of integers with
finite Terras stopping time is `1`:  the counting ratio
`#{ m ≤ N : StopFinite m } / N → 1` as `N → ∞`.  This is the formal Terras-1976 statement
"almost all integers have a finite stopping time", in single-set density form.

Proof = squeeze via `tendsto_order`:
* upper:  `count ≤ N+1` gives `count/N ≤ (N+1)/N → 1`, so for any `b > 1` eventually
  `count/N < b`;
* lower:  for any `a < 1`, pick `n` with `1/(n+1) < 1-a` so that `a < n/(n+1)`; then
  `stopFinite_density_bounded_below n (n+1)` yields `n·N ≤ (n+1)·count` eventually,
  i.e. `a < n/(n+1) ≤ count/N`. -/
theorem stopFinite_density_tendsto_one :
    Tendsto (fun N => (count_upto StopFinite N : ℝ) / N) atTop (𝓝 1) := by
  rw [tendsto_order]
  refine ⟨?lower, ?upper⟩
  case lower =>
    -- For every `a < 1`, eventually `a < count/N`.
    intro a ha
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show (0 : ℝ) < 1 - a by linarith)
    -- `hn : 1 / (n + 1) < 1 - a`.  Set `q = n + 1`, target ratio `n/q`.
    set q := n + 1 with hq_def
    have hqpos : 0 < q := Nat.succ_pos n
    have hpq : n < q := Nat.lt_succ_self n
    have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hqpos
    have hcast : (q : ℝ) = (n : ℝ) + 1 := by rw [hq_def]; push_cast; ring
    have ha_lt : a < (n : ℝ) / (q : ℝ) := by
      rw [lt_div_iff₀ hqR, hcast]
      have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      have hk := (div_lt_iff₀ hpos).mp hn
      nlinarith [hk]
    obtain ⟨N₀, hN₀⟩ := stopFinite_density_bounded_below n q hqpos hpq
    filter_upwards [eventually_ge_atTop (max N₀ 1)] with N hN
    have hN0 : N₀ ≤ N := le_trans (le_max_left _ _) hN
    have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
    have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
    have hb : n * N ≤ q * count_upto StopFinite N := hN₀ N hN0
    have hbR : (n : ℝ) * N ≤ (q : ℝ) * (count_upto StopFinite N : ℝ) := by exact_mod_cast hb
    have hge : (n : ℝ) / (q : ℝ) ≤ (count_upto StopFinite N : ℝ) / (N : ℝ) := by
      rw [div_le_div_iff₀ hqR hNR]
      nlinarith [hbR]
    linarith [ha_lt, hge]
  case upper =>
    -- For every `b > 1`, eventually `count/N < b`.
    intro b hb1
    have hupper : Tendsto (fun N : ℕ => ((N : ℝ) + 1) / (N : ℝ)) atTop (𝓝 1) := by
      have h1 : Tendsto (fun N : ℕ => 1 + 1 / (N : ℝ)) atTop (𝓝 (1 + 0)) :=
        tendsto_const_nhds.add tendsto_one_div_atTop_nhds_zero_nat
      rw [add_zero] at h1
      refine h1.congr' ?_
      filter_upwards [eventually_ge_atTop 1] with N hN
      have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
      field_simp
    have hev := hupper.eventually (eventually_lt_nhds hb1)
    filter_upwards [hev, eventually_ge_atTop 1] with N hNb hN1
    have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
    have hcle : (count_upto StopFinite N : ℝ) ≤ (N : ℝ) + 1 := by
      have := count_upto_le StopFinite N
      exact_mod_cast this
    have hle : (count_upto StopFinite N : ℝ) / (N : ℝ) ≤ ((N : ℝ) + 1) / (N : ℝ) := by
      gcongr
    linarith [hNb, hle]

end CollatzStoppingDensityOne
