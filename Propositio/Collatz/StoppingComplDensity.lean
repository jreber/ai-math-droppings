import Propositio.Collatz.StoppingDensityOne

/-!
# Collatz: the natural density of integers WITHOUT finite Terras stopping time is `0`

This is the complement of the Terras (1976) headline
`CollatzStoppingDensityOne.stopFinite_density_tendsto_one`
(`count_upto StopFinite N / N → 1`).  Since the descending count and its complement
sum to `N + 1`, the counting ratio for the non-stopping integers satisfies

```
count_upto (¬StopFinite) N / N = (N+1)/N − count_upto StopFinite N / N
```

for `N ≥ 1`.  As `N → ∞` the right side tends to `1 − 1 = 0`.

`stopFinite_compl_density_tendsto_zero` reduces to `[propext, Classical.choice, Quot.sound]`.
-/

namespace CollatzStoppingComplDensity

open Filter Topology
open TerrasDensity
open CollatzStoppingDensityOne

attribute [local instance] Classical.propDecidable

/-- Complement identity through `count_upto`.  Reproved inline (mirror of the private
`count_upto_compl` in `CollatzBadDensity.lean`). -/
private theorem count_upto_compl (A : Nat → Prop) (N : Nat) :
    count_upto (fun k => ¬ A k) N + count_upto A N = N + 1 := by
  unfold count_upto
  generalize N + 1 = m
  induction m with
  | zero => simp [Nat.count_zero]
  | succ k ih =>
    rw [Nat.count_succ, Nat.count_succ]
    by_cases h : A k <;> simp [h] <;> omega

/-- **HEADLINE.**  The natural density of integers WITHOUT a finite Terras stopping time
is `0`:  `#{ m ≤ N : ¬StopFinite m } / N → 0` as `N → ∞`.  Complement of the Terras
density-one theorem. -/
theorem stopFinite_compl_density_tendsto_zero :
    Tendsto
      (fun N : ℕ => (count_upto (fun n => ¬ StopFinite n) N : ℝ) / (N : ℝ))
      atTop (𝓝 0) := by
  -- The arithmetic form `(N+1)/N − count_upto StopFinite N / N`.
  have hone : Tendsto (fun N : ℕ => ((N : ℝ) + 1) / (N : ℝ)) atTop (𝓝 1) := by
    have h1 : Tendsto (fun N : ℕ => 1 + 1 / (N : ℝ)) atTop (𝓝 (1 + 0)) :=
      tendsto_const_nhds.add tendsto_one_div_atTop_nhds_zero_nat
    rw [add_zero] at h1
    refine h1.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    field_simp
  -- The difference tends to `1 - 1 = 0`.
  have hdiff :
      Tendsto
        (fun N : ℕ => ((N : ℝ) + 1) / (N : ℝ)
          - (count_upto StopFinite N : ℝ) / (N : ℝ))
        atTop (𝓝 (1 - 1)) :=
    hone.sub stopFinite_density_tendsto_one
  rw [sub_self] at hdiff
  -- Replace the difference with the literal complement ratio for `N ≥ 1`.
  refine hdiff.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hsum :
      (count_upto (fun n => ¬ StopFinite n) N : ℝ) + (count_upto StopFinite N : ℝ)
        = (N : ℝ) + 1 := by
    have h := count_upto_compl StopFinite N
    exact_mod_cast h
  field_simp
  linarith [hsum]

end CollatzStoppingComplDensity
