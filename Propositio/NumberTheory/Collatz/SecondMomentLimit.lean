import Propositio.NumberTheory.Collatz.Drift
import Propositio.NumberTheory.Collatz.DriftLimit
import Propositio.NumberTheory.Collatz.ValuationSecondMoment
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# The second-moment limit: `E[a²](M) → 6` as `M → ∞`

`CollatzValuationSecondMoment.second_moment_sum` proves the exact identity

  `Σ_{a=1}^{M-1} a² · 2^(M-a-1) = 3·2^M − (M² + 2M + 3)`   (over ℕ, for `M ≥ 1`),

i.e. the second-moment total division count. Dividing by the odd-residue count
`2^(M-1)` gives the second moment

  `E[a²](M) = (3·2^M − (M²+2M+3)) / 2^(M-1) = 6 − (M²+2M+3)/2^(M-1)`,

which the file's own docstring claims "gives `E[a²] → 6`" — a limit statement
that was never actually formalized. This file completes it, as the direct
structural twin of `CollatzDrift.mean_valuation_tendsto_two`
(`CollatzDriftLimit.lean`): same reindexing `M = n + 1` trick, same Mathlib
tool `tendsto_pow_const_div_const_pow_of_one_lt`, now used at `k = 0, 1, 2`
(instead of just `k = 0, 1`) since the defect numerator is now quadratic in
`M`.

Combined with `CollatzDrift.mean_valuation_tendsto_two` (`E[a] → 2`), this
gives `Var[a] = E[a²] − E[a]² → 6 − 4 = 2` (`collatz_variance_tendsto_two`
below), the exact limit statement `CollatzValuationSecondMoment`'s docstring
promises.

Axiom-clean: no `sorry`, no `native_decide`, no new axioms.
-/

namespace CollatzValuationSecondMoment

open Filter Topology CollatzDrift

/-! ## 1. The closed form, cast to ℝ -/

/-- The second-moment total division count `3·2^M − (M²+2M+3)`, divided by the
odd-residue count `2^(M-1)`, cast to `ℝ` and rewritten in closed form
`6 − (M²+2M+3)/2^(M-1)` (mirroring `CollatzDrift.mean_valuation_closed_form`,
using the same `2^M = 2 · 2^(M-1)` split and the growth bound `sq_add_bound`
that keeps the `Nat` subtraction well-defined). -/
theorem second_moment_closed_form_real (M : Nat) (hM : 1 ≤ M) :
    ((3 * 2 ^ M - (M ^ 2 + 2 * M + 3) : Nat) : ℝ) / (2 : ℝ) ^ (M - 1)
      = 6 - ((M : ℝ) ^ 2 + 2 * (M : ℝ) + 3) / (2 : ℝ) ^ (M - 1) := by
  have hbound : M ^ 2 + 2 * M + 3 ≤ 3 * 2 ^ M := sq_add_bound M hM
  have hsplit : (2 : Nat) ^ M = 2 * 2 ^ (M - 1) := two_pow_split M hM
  have hcast : ((3 * 2 ^ M - (M ^ 2 + 2 * M + 3) : Nat) : ℝ)
      = 3 * (2 : ℝ) ^ M - ((M : ℝ) ^ 2 + 2 * (M : ℝ) + 3) := by
    rw [Nat.cast_sub hbound]
    push_cast
    ring
  rw [hcast]
  have hsplitR : (2 : ℝ) ^ M = 2 * (2 : ℝ) ^ (M - 1) := by
    have := congrArg (Nat.cast : Nat → ℝ) hsplit
    push_cast at this
    exact this
  rw [hsplitR]
  have hpow : (2 : ℝ) ^ (M - 1) ≠ 0 := by positivity
  field_simp
  ring

/-! ## 2. The defect term `(M²+2M+3)/2^(M-1) → 0` -/

/-- `n² / 2^n → 0` (the `k = 2` case of the Mathlib geometric-dominance lemma,
with `n^2` matching the goal directly). -/
theorem tendsto_n_sq_div_two_pow :
    Tendsto (fun n : ℕ => (n : ℝ) ^ 2 / (2 : ℝ) ^ n) atTop (𝓝 0) :=
  tendsto_pow_const_div_const_pow_of_one_lt 2 (r := (2 : ℝ)) (by norm_num)

/-- `(n² + 4n + 6) / 2^n → 0`: the reindexed second-moment defect
(`M = n + 1` shifts `M² + 2M + 3` to `n² + 4n + 6` and `M - 1` to `n`). -/
theorem tendsto_defect2_shifted :
    Tendsto (fun n : ℕ => ((n : ℝ) ^ 2 + 4 * (n : ℝ) + 6) / (2 : ℝ) ^ n) atTop (𝓝 0) := by
  have hsum := (tendsto_n_sq_div_two_pow.add (tendsto_n_div_two_pow.const_mul 4)).add
      (tendsto_one_div_two_pow.const_mul 6)
  rw [show (0 : ℝ) + 4 * 0 + 6 * 0 = 0 by ring] at hsum
  refine hsum.congr (fun n => ?_)
  have hpow : (2 : ℝ) ^ n ≠ 0 := by positivity
  field_simp

/-- The (unshifted) second-moment defect `(M²+2M+3)/2^(M-1) → 0` along the
reindexing `M = n+1`. -/
theorem tendsto_defect2 :
    Tendsto (fun n : ℕ => (((n + 1 : ℕ) : ℝ) ^ 2 + 2 * ((n + 1 : ℕ) : ℝ) + 3)
      / (2 : ℝ) ^ ((n + 1) - 1)) atTop (𝓝 0) := by
  refine tendsto_defect2_shifted.congr (fun n => ?_)
  have h1 : (n + 1) - 1 = n := by omega
  rw [h1]
  push_cast
  ring_nf

/-! ## 3. The headline: `E[a²](M) → 6` -/

/-- **`second_moment_tendsto_six` — REAL (headline).**
The second moment of the `v₂(3n+1)` valuation distribution,
`(3·2^M − (M²+2M+3)) / 2^(M-1)`, tends to `6` as `M → ∞`. This completes the
limit statement asserted (but never formalized) in
`CollatzValuationSecondMoment`'s own docstring, matching the structure of
`CollatzDrift.mean_valuation_tendsto_two` (`E[a] → 2`). -/
theorem second_moment_tendsto_six :
    Tendsto (fun M : Nat => ((3 * 2 ^ M - (M ^ 2 + 2 * M + 3) : Nat) : ℝ) / (2 : ℝ) ^ (M - 1))
      atTop (𝓝 6) := by
  rw [← tendsto_add_atTop_iff_nat 1]
  have hlim : Tendsto (fun n : ℕ => (6 : ℝ)
      - (((n + 1 : ℕ) : ℝ) ^ 2 + 2 * ((n + 1 : ℕ) : ℝ) + 3) / (2 : ℝ) ^ ((n + 1) - 1))
      atTop (𝓝 (6 - 0)) :=
    tendsto_const_nhds.sub tendsto_defect2
  rw [show (6 : ℝ) - 0 = 6 by ring] at hlim
  refine hlim.congr (fun n => ?_)
  exact (second_moment_closed_form_real (n + 1) (by omega)).symm

/-! ## 4. The variance limit: `Var[a](M) → 2` -/

/-- **`variance_tendsto_two` — REAL.**
Combining `second_moment_tendsto_six` (`E[a²] → 6`) with
`CollatzDrift.mean_valuation_tendsto_two` (`E[a] → 2`), the variance
`Var[a](M) := E[a²](M) − E[a](M)²` tends to `6 − 2² = 2` — the exact limit
statement `CollatzValuationSecondMoment`'s docstring promises. -/
theorem variance_tendsto_two :
    Tendsto (fun M : Nat =>
        ((3 * 2 ^ M - (M ^ 2 + 2 * M + 3) : Nat) : ℝ) / (2 : ℝ) ^ (M - 1)
          - ((CollatzDrift.meanValuation M : ℚ) : ℝ) ^ 2)
      atTop (𝓝 2) := by
  have h : Tendsto (fun M : Nat =>
      ((3 * 2 ^ M - (M ^ 2 + 2 * M + 3) : Nat) : ℝ) / (2 : ℝ) ^ (M - 1)
        - ((CollatzDrift.meanValuation M : ℚ) : ℝ) ^ 2)
      atTop (𝓝 (6 - (2 : ℝ) ^ 2)) :=
    second_moment_tendsto_six.sub (CollatzDrift.mean_valuation_tendsto_two.pow 2)
  norm_num at h
  exact h

end CollatzValuationSecondMoment
