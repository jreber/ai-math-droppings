import Propositio.Collatz.Drift
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# The mean valuation limit: `meanValuation M → 2` as `M → ∞`

`CollatzDrift.lean` proves the closed form

  `meanValuation M = 2 − (M+1)/2^(M−1)`   (over ℚ, for `M ≥ 1`)

and the two one-sided bounds `mean_valuation_lt_two` (`< 2`, all `M ≥ 1`) and
`mean_valuation_ge_eight_fifths` (`≥ 8/5`, `M ≥ 5`), but its own docstring
claims the mean "increases to 2 as `M → ∞`" — a limit statement that was never
actually formalized. This file completes it.

The proof casts the closed form to `ℝ` and shows the defect
`(M+1)/2^(M−1) → 0`, using Mathlib's `tendsto_pow_const_div_const_pow_of_one_lt`
(`n^k / r^n → 0` for `r > 1`, any `k : ℕ`) with `k = 1` (for the `M` term) and
`k = 0` (for the constant term), combined via `Tendsto.add`. A reindexing
`M = n + 1` (via `Filter.tendsto_add_atTop_iff_nat`) sidesteps the `Nat`
subtraction `M - 1` at `M = 0`, where the closed form doesn't hold.

Axiom-clean: no `sorry`, no `native_decide`, no new axioms.
-/

namespace CollatzDrift

open Filter Topology

/-! ## 1. The closed form, cast to ℝ -/

/-- The closed form `mean_valuation_closed_form`, cast from ℚ to ℝ, with the
`2^(M-1)` denominator written as a real power (rather than a cast natural
power), ready for the real-analysis limit argument. -/
theorem mean_valuation_closed_form_real (M : Nat) (hM : 1 ≤ M) :
    ((meanValuation M : ℚ) : ℝ) = 2 - ((M : ℝ) + 1) / (2 : ℝ) ^ (M - 1) := by
  have h := mean_valuation_closed_form M hM
  have hcast : (((meanValuation M : ℚ) : ℝ)) =
      ((2 - ((M : ℚ) + 1) / ((2 ^ (M - 1) : Nat) : ℚ) : ℚ) : ℝ) := by
    exact_mod_cast congrArg (fun q : ℚ => q) h
  rw [hcast]
  push_cast
  ring

/-! ## 2. The defect term `(M+1)/2^(M-1) → 0` -/

/-- `n / 2^n → 0` (the `k = 1` case of the Mathlib geometric-dominance lemma,
with `n^1` simplified to `n`). -/
theorem tendsto_n_div_two_pow : Tendsto (fun n : ℕ => (n : ℝ) / (2 : ℝ) ^ n) atTop (𝓝 0) := by
  have := tendsto_pow_const_div_const_pow_of_one_lt 1 (r := (2 : ℝ)) (by norm_num)
  simpa using this

/-- `1 / 2^n → 0` (the `k = 0` case). -/
theorem tendsto_one_div_two_pow : Tendsto (fun n : ℕ => (1 : ℝ) / (2 : ℝ) ^ n) atTop (𝓝 0) := by
  have := tendsto_pow_const_div_const_pow_of_one_lt 0 (r := (2 : ℝ)) (by norm_num)
  simpa using this

/-- `(n + 2) / 2^n → 0`: the reindexed defect (`M = n + 1` shifts `M + 1` to
`n + 2` and `M - 1` to `n`). -/
theorem tendsto_defect_shifted :
    Tendsto (fun n : ℕ => ((n : ℝ) + 2) / (2 : ℝ) ^ n) atTop (𝓝 0) := by
  have hsum := tendsto_n_div_two_pow.add (tendsto_one_div_two_pow.const_mul 2)
  rw [show (0 : ℝ) + 2 * 0 = 0 by ring] at hsum
  refine hsum.congr (fun n => ?_)
  have hpow : (2 : ℝ) ^ n ≠ 0 := by positivity
  field_simp

/-- The (unshifted) defect `(M+1)/2^(M-1) → 0` along the reindexing `M = n+1`. -/
theorem tendsto_defect :
    Tendsto (fun n : ℕ => (((n + 1 : ℕ) : ℝ) + 1) / (2 : ℝ) ^ ((n + 1) - 1)) atTop (𝓝 0) := by
  refine tendsto_defect_shifted.congr (fun n => ?_)
  have : (n + 1) - 1 = n := by omega
  rw [this]
  push_cast
  ring_nf

/-! ## 3. The headline: `meanValuation M → 2` -/

/-- **`mean_valuation_tendsto_two` — REAL (headline).**
The mean number of 2-adic divisions per compressed step, `meanValuation M`,
tends to `2` as `M → ∞`. This completes the limit statement asserted (but
never formalized) in `CollatzDrift`'s own docstring, alongside the two
one-sided bounds `mean_valuation_lt_two` and `mean_valuation_ge_eight_fifths`
already proved there. -/
theorem mean_valuation_tendsto_two :
    Tendsto (fun M : Nat => ((meanValuation M : ℚ) : ℝ)) atTop (𝓝 2) := by
  rw [← tendsto_add_atTop_iff_nat 1]
  have heq : ∀ n : ℕ, ((meanValuation (n + 1) : ℚ) : ℝ)
      = 2 - (((n + 1 : ℕ) : ℝ) + 1) / (2 : ℝ) ^ ((n + 1) - 1) := by
    intro n
    exact mean_valuation_closed_form_real (n + 1) (by omega)
  have hlim : Tendsto (fun n : ℕ => (2 : ℝ)
      - (((n + 1 : ℕ) : ℝ) + 1) / (2 : ℝ) ^ ((n + 1) - 1)) atTop (𝓝 (2 - 0)) :=
    tendsto_const_nhds.sub tendsto_defect
  simpa [heq] using hlim

end CollatzDrift
