import Propositio.Collatz.StoppingDensityOne
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Natural density 1 ⇒ logarithmic density 1

Tao's 2019 work on Collatz (arXiv:1909.03562) is phrased in terms of **logarithmic
density**.  Our repository already proves, axiom-clean, that the **natural** density of
the set of integers with a finite Terras stopping time is `1`
(`CollatzStoppingDensityOne.stopFinite_density_tendsto_one`).  Since natural density `1`
implies logarithmic density `1`, this file proves that general transfer and then upgrades
the Terras headline to the log-density notion that Tao uses.

## Main results

* `weighted_avg_tendsto` — a reusable **weighted-average (Toeplitz/regular-summation)**
  convergence lemma: if `x n → L`, the weights `w n ≥ 0`, and `∑_{i<n} w i → ∞`, then
  `(∑_{i<n} w i * x i) / (∑_{i<n} w i) → L`.

* `natDensity_one_imp_logDensity_one` — **HEADLINE (A).**  For any decidable predicate `P`,
  if `#{k ≤ N : P k} / N → 1` then `(∑_{1 ≤ n ≤ N} [P n]/n) / log N → 1`.

* `stopFinite_logDensity_tendsto_one` — **HEADLINE (B).**  The log-density of the set of
  integers with a finite Terras stopping time is `1`.

## Proof route

Abel summation (proved here by a direct `Nat.le_induction`) turns the weighted sum
`∑_{1≤n≤N} [P n]/n` into `C(N)/N − C(0) + ∑_{i<N} (C(i)/i)·(1/(i+1))`, where
`C(n) = #{k ≤ n : P k}`.  The tail is a weighted average of `C(i)/i → 1` with weights
`1/(i+1)` whose partial sums are the harmonic numbers `harmonic N`.  The weighted-average
lemma gives `(tail)/harmonic N → 1`, and `harmonic N / log N → 1` (from the mathlib bounds
`log (N+1) ≤ harmonic N ≤ 1 + log N`) finishes the job, the two boundary terms being
`o(log N)`.
-/

open Filter Topology Asymptotics Finset

namespace LogDensityTransfer

/-- **Weighted-average (Toeplitz / regular-summation) convergence.**

If `x n → L`, the weights `w` are nonnegative, and the partial weight sums
`∑_{i < n} w i` diverge to `+∞`, then the weighted averages converge to the same limit:
`(∑_{i<n} w i * x i) / (∑_{i<n} w i) → L`.

This is the standard "Cesàro with weights" statement.  Mathlib has the unweighted
`Filter.Tendsto.cesaro`; this is the broadly-useful weighted generalization. -/
theorem weighted_avg_tendsto {x w : ℕ → ℝ} {L : ℝ}
    (hx : Tendsto x atTop (𝓝 L)) (hw : ∀ i, 0 ≤ w i)
    (hW : Tendsto (fun n => ∑ i ∈ Finset.range n, w i) atTop atTop) :
    Tendsto (fun n => (∑ i ∈ Finset.range n, w i * x i) / (∑ i ∈ Finset.range n, w i))
      atTop (𝓝 L) := by
  -- `w · (x · - L) = o(w)`, since `x · - L → 0`.
  have hfo : (fun i => w i * (x i - L)) =o[atTop] w := by
    have h1 : (fun i => x i - L) =o[atTop] (fun _ : ℕ => (1 : ℝ)) :=
      (Asymptotics.isLittleO_one_iff ℝ).2 (by simpa using hx.sub_const L)
    have h2 := (Asymptotics.isBigO_refl w atTop).mul_isLittleO h1
    simpa using h2
  -- Summing preserves little-o (mathlib `IsLittleO.sum_range`).
  have hsum := hfo.sum_range (fun i => hw i) hW
  have hratio := hsum.tendsto_div_nhds_zero
  -- Re-add `L`: the divergence of the weights turns the `o(1)` into the claim.
  have key := hratio.add_const L
  rw [zero_add] at key
  apply key.congr'
  filter_upwards [hW.eventually_gt_atTop 0] with n hn
  have hb : (∑ i ∈ Finset.range n, w i) ≠ 0 := ne_of_gt hn
  have hsumx : (∑ i ∈ Finset.range n, w i * x i)
      = (∑ i ∈ Finset.range n, w i * (x i - L)) + L * (∑ i ∈ Finset.range n, w i) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [hsumx, add_div, mul_div_assoc, div_self hb, mul_one]

/-- The harmonic numbers tend to `+∞` (they dominate `log (n+1) → ∞`). -/
theorem harmonic_tendsto_atTop : Tendsto (fun n : ℕ => (harmonic n : ℝ)) atTop atTop := by
  have hlogp : Tendsto (fun n : ℕ => Real.log (↑(n + 1))) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
  exact tendsto_atTop_mono (fun n => log_add_one_le_harmonic n) hlogp

/-- `harmonic N / log N → 1`, from `log (N+1) ≤ harmonic N ≤ 1 + log N`. -/
theorem harmonic_div_log_tendsto_one :
    Tendsto (fun n : ℕ => (harmonic n : ℝ) / Real.log n) atTop (𝓝 1) := by
  have hlog : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hloginv : Tendsto (fun n : ℕ => (Real.log n)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hlog
  -- upper envelope `1/log n + 1 → 1`
  have hupper : Tendsto (fun n : ℕ => (Real.log n)⁻¹ + 1) atTop (𝓝 1) := by
    simpa using hloginv.add_const (1 : ℝ)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (g := fun _ : ℕ => (1 : ℝ))
    (h := fun n : ℕ => (Real.log n)⁻¹ + 1) tendsto_const_nhds hupper ?_ ?_
  · -- `1 ≤ harmonic n / log n` eventually
    filter_upwards [eventually_ge_atTop 2] with n hn
    have hn1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 1 < n)
    have hlogpos : 0 < Real.log n := Real.log_pos hn1
    have hle : Real.log n ≤ (harmonic n : ℝ) := by
      have h1 : Real.log (n : ℝ) ≤ Real.log (↑(n + 1)) := by
        apply Real.log_le_log (by positivity)
        push_cast; linarith
      exact le_trans h1 (log_add_one_le_harmonic n)
    exact (one_le_div hlogpos).2 hle
  · -- `harmonic n / log n ≤ 1/log n + 1` eventually
    filter_upwards [eventually_ge_atTop 2] with n hn
    have hn1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 1 < n)
    have hlogpos : 0 < Real.log n := Real.log_pos hn1
    have hstep : (harmonic n : ℝ) / Real.log n ≤ (1 + Real.log n) / Real.log n := by
      gcongr
      exact harmonic_le_one_add_log n
    calc (harmonic n : ℝ) / Real.log n
        ≤ (1 + Real.log n) / Real.log n := hstep
      _ = (Real.log n)⁻¹ + 1 := by
          rw [add_div, div_self (ne_of_gt hlogpos), one_div]

variable (P : ℕ → Prop) [DecidablePred P]

/-- **Natural density `1` ⇒ logarithmic density `1`.**  If the natural counting ratio
`#{k ≤ N : P k} / N → 1`, then the logarithmically-weighted ratio
`(∑_{1 ≤ n ≤ N} [P n]/n) / log N → 1`. -/
theorem natDensity_one_imp_logDensity_one
    (h : Tendsto (fun N => (TerrasDensity.count_upto P N : ℝ) / N) atTop (𝓝 1)) :
    Tendsto (fun N => (∑ n ∈ Finset.Icc 1 N, (if P n then (1 : ℝ) / n else 0)) / Real.log N)
      atTop (𝓝 1) := by
  -- Notation: `C n = #{k ≤ n : P k}`.
  -- Counting recurrence (cast to ℝ).
  have hCrec : ∀ m : ℕ, (TerrasDensity.count_upto P (m + 1) : ℝ)
      = (TerrasDensity.count_upto P m : ℝ) + (if P (m + 1) then (1 : ℝ) else 0) := by
    intro m
    by_cases hP : P (m + 1)
    · have hn : TerrasDensity.count_upto P (m + 1) = TerrasDensity.count_upto P m + 1 := by
        unfold TerrasDensity.count_upto; rw [Nat.count_succ, if_pos hP]
      rw [hn]; push_cast; simp [hP]
    · have hn : TerrasDensity.count_upto P (m + 1) = TerrasDensity.count_upto P m := by
        unfold TerrasDensity.count_upto; rw [Nat.count_succ, if_neg hP, add_zero]
      rw [hn]; simp [hP]
  -- Abel-summation identity (proved by induction from `N = 1`).
  have hstar : ∀ N : ℕ, 1 ≤ N →
      (∑ n ∈ Finset.Icc 1 N, (if P n then (1 : ℝ) / n else 0))
        = (TerrasDensity.count_upto P N : ℝ) / N - (TerrasDensity.count_upto P 0 : ℝ)
          + ∑ i ∈ Finset.range N,
              ((i : ℝ) + 1)⁻¹ * ((TerrasDensity.count_upto P i : ℝ) / (i : ℝ)) := by
    intro N hN
    induction N, hN using Nat.le_induction with
    | base =>
      simp only [Finset.Icc_self, Finset.sum_singleton, Finset.range_one]
      rw [hCrec 0]
      by_cases hP : P 1 <;> simp [hP]
    | succ N hN ih =>
      rw [Finset.sum_Icc_succ_top (by omega : (1 : ℕ) ≤ N + 1), ih,
          Finset.sum_range_succ, hCrec N]
      have hN0 : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
      have hN1 : (N : ℝ) + 1 ≠ 0 := by positivity
      push_cast
      by_cases hP : P (N + 1)
      · simp only [hP, if_true]
        have key : (TerrasDensity.count_upto P N : ℝ) / N + (1 : ℝ) / ((N : ℝ) + 1)
            = ((TerrasDensity.count_upto P N : ℝ) + 1) / ((N : ℝ) + 1)
              + ((N : ℝ) + 1)⁻¹ * ((TerrasDensity.count_upto P N : ℝ) / N) := by
          field_simp; ring
        linarith [key]
      · simp only [hP, if_false]
        have key : (TerrasDensity.count_upto P N : ℝ) / N + (0 : ℝ)
            = ((TerrasDensity.count_upto P N : ℝ) + 0) / ((N : ℝ) + 1)
              + ((N : ℝ) + 1)⁻¹ * ((TerrasDensity.count_upto P N : ℝ) / N) := by
          field_simp; ring
        linarith [key]
  -- Limit ingredients.
  have hlog : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hloginv : Tendsto (fun n : ℕ => (Real.log n)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hlog
  have hWsum : ∀ n : ℕ, (∑ i ∈ Finset.range n, ((i : ℝ) + 1)⁻¹) = (harmonic n : ℝ) := by
    intro n
    simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    push_cast
    rfl
  have hWtop : Tendsto (fun n => ∑ i ∈ Finset.range n, ((i : ℝ) + 1)⁻¹) atTop atTop :=
    harmonic_tendsto_atTop.congr (fun n => (hWsum n).symm)
  have hwpos : ∀ i : ℕ, (0 : ℝ) ≤ ((i : ℝ) + 1)⁻¹ := fun i => by positivity
  -- Weighted average of `C(i)/i → 1` with weights `1/(i+1)`.
  have hWA := weighted_avg_tendsto (x := fun n => (TerrasDensity.count_upto P n : ℝ) / (n : ℝ))
      (w := fun i => ((i : ℝ) + 1)⁻¹) (L := 1) h hwpos hWtop
  have hWA' : Tendsto (fun n => (∑ i ∈ Finset.range n,
      ((i : ℝ) + 1)⁻¹ * ((TerrasDensity.count_upto P i : ℝ) / (i : ℝ))) / (harmonic n : ℝ))
      atTop (𝓝 1) := by
    refine hWA.congr (fun n => ?_)
    rw [hWsum n]
  -- Tail `/ log → 1`.
  have hD : Tendsto (fun n => (∑ i ∈ Finset.range n,
      ((i : ℝ) + 1)⁻¹ * ((TerrasDensity.count_upto P i : ℝ) / (i : ℝ))) / Real.log n)
      atTop (𝓝 1) := by
    have hprod := hWA'.mul harmonic_div_log_tendsto_one
    rw [one_mul] at hprod
    apply hprod.congr'
    filter_upwards [harmonic_tendsto_atTop.eventually_gt_atTop 0,
      hlog.eventually_gt_atTop 0] with n hn hln
    have hne : (harmonic n : ℝ) ≠ 0 := ne_of_gt hn
    have hlne : Real.log n ≠ 0 := ne_of_gt hln
    field_simp
  -- Boundary terms `o(log N)`.
  have hA : Tendsto (fun n : ℕ =>
      ((TerrasDensity.count_upto P n : ℝ) / (n : ℝ)) * (Real.log n)⁻¹) atTop (𝓝 0) := by
    simpa using h.mul hloginv
  have hB : Tendsto (fun n : ℕ =>
      (TerrasDensity.count_upto P 0 : ℝ) * (Real.log n)⁻¹) atTop (𝓝 0) := by
    simpa using hloginv.const_mul (TerrasDensity.count_upto P 0 : ℝ)
  -- Assemble and transfer through the Abel identity.
  have hlim : Tendsto (fun n : ℕ =>
      ((TerrasDensity.count_upto P n : ℝ) / (n : ℝ)) * (Real.log n)⁻¹
        - (TerrasDensity.count_upto P 0 : ℝ) * (Real.log n)⁻¹
        + (∑ i ∈ Finset.range n,
            ((i : ℝ) + 1)⁻¹ * ((TerrasDensity.count_upto P i : ℝ) / (i : ℝ))) / Real.log n)
      atTop (𝓝 1) := by
    simpa using (hA.sub hB).add hD
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  rw [hstar N hN]
  ring

end LogDensityTransfer

namespace CollatzStoppingDensityOne

open Filter Topology

attribute [local instance] Classical.propDecidable

/-- **Log-density Collatz brick (HEADLINE B).**  The *logarithmic* density of the set of
integers with a finite Terras stopping time is `1` — the upgrade of the natural-density
headline `stopFinite_density_tendsto_one` to the density notion used in Tao's framing. -/
theorem stopFinite_logDensity_tendsto_one :
    Tendsto (fun N => (∑ n ∈ Finset.Icc 1 N,
      (if StopFinite n then (1 : ℝ) / n else 0)) / Real.log N) atTop (𝓝 1) :=
  LogDensityTransfer.natDensity_one_imp_logDensity_one StopFinite
    stopFinite_density_tendsto_one

end CollatzStoppingDensityOne
