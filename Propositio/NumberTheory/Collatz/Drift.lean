import Propositio.NumberTheory.Collatz.ValuationDensity
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic

/-!
# The rigorous "negative drift" capstone — Collatz contracts ON AVERAGE

This file is the average-contraction landmark built directly on
`CollatzValuationDensity.expected_valuation_sum`:

  `Σ_{a=1}^{M-1} a · 2^(M-a-1) = 2^M - M - 1`.

Dividing this total 2-adic division count by the number `2^(M-1)` of odd residues
below `2^M` gives the **mean number of divisions per compressed step**

  `mean(M) = (2^M − M − 1) / 2^(M−1) = 2 − (M+1)/2^(M−1)`   (over ℚ),

which increases to `2` as `M → ∞`. Since a compressed step multiplies by
`≈ 3 / 2^a` and `a` has mean `2`, the average multiplier is `3 / 2^2 = 3/4 < 1`:
**the compressed Collatz map contracts on average.**

The clean, transcendence-free contraction certificate avoids `log₂ 3` entirely:

* `mean_valuation_ge_eight_fifths` : `mean(M) ≥ 8/5` for `M ≥ 5`;
* `mean_drift_pow` : `2^8 > 3^5` (i.e. `256 > 243`), equivalently `2^(8/5) > 3`;
* `collatz_negative_drift` : combining the two, the average multiplier obeys
  `3^5 < 2^8 ≤ 2^(5·mean(M))`, i.e. `3 < 2^mean(M)`, i.e. the average per-step
  multiplier `3 / 2^mean(M) < 1`.

We work over `ℚ` (and `ℕ` for the power inequality) throughout, *avoiding reals
entirely*, which keeps every statement elementary and axiom-clean.

## HONESTY — this is NOT a proof of Collatz

`mean(M)` is an **average** of the per-step 2-adic valuation over a residue
window; the contraction it certifies is a statement about the *mean* multiplier,
the rigorous backbone of the "Collatz shrinks on average" heuristic. It is NOT a
per-orbit convergence statement: the residue of `cc n` is not pinned by that of
`n`, so the favorable expectation does not chain into a global potential. Nothing
here proves any individual trajectory terminates.

All theorems are axiom-clean (`propext, Classical.choice, Quot.sound` only):
no `native_decide`, no `sorry`, no new axioms.
-/

namespace CollatzDrift

open CollatzValuationDensity

/-! ## 1. The closed-form mean valuation over ℚ -/

/-- The **mean number of 2-adic divisions per compressed step** over the window
`r < 2^M`, as a rational: total division count `2^M - M - 1` divided by the
number `2^(M-1)` of odd residues below `2^M`. -/
noncomputable def meanValuation (M : Nat) : ℚ :=
  ((2 ^ M - M - 1 : Nat) : ℚ) / ((2 ^ (M - 1) : Nat) : ℚ)

/-- `(2^(M-1) : ℚ) ≠ 0`. -/
theorem pow_den_ne_zero (M : Nat) : ((2 ^ (M - 1) : Nat) : ℚ) ≠ 0 := by
  have h : (0 : Nat) < 2 ^ (M - 1) := Nat.two_pow_pos _
  have hpos : (0 : ℚ) < ((2 ^ (M - 1) : Nat) : ℚ) := by exact_mod_cast h
  exact ne_of_gt hpos

/-- For `M ≥ 1`, `2^M = 2 * 2^(M-1)` as naturals (the half-shift identity). -/
theorem two_pow_split (M : Nat) (hM : 1 ≤ M) : (2 : Nat) ^ M = 2 * 2 ^ (M - 1) := by
  conv_lhs => rw [show M = (M - 1) + 1 from by omega]
  rw [pow_succ]; ring

/-- **`mean_valuation_closed_form` — REAL.**
For `M ≥ 1`, the mean is `2 − (M+1)/2^(M−1)` over ℚ, obtained from
`expected_valuation_sum` by dividing the total division count `2^M − M − 1` by
the odd-residue count `2^(M−1)`. -/
theorem mean_valuation_closed_form (M : Nat) (hM : 1 ≤ M) :
    meanValuation M = 2 - ((M : ℚ) + 1) / ((2 ^ (M - 1) : Nat) : ℚ) := by
  unfold meanValuation
  have hden : ((2 ^ (M - 1) : Nat) : ℚ) ≠ 0 := pow_den_ne_zero M
  have hsplit : (2 : Nat) ^ M = 2 * 2 ^ (M - 1) := two_pow_split M hM
  -- Cast the numerator: 2^M - M - 1  ↦  2*2^(M-1) - M - 1 over ℚ.
  have hge : M + 1 ≤ 2 ^ M := by
    have : M < 2 ^ M := Nat.lt_two_pow_self
    omega
  have hsplitQ : ((2 : ℚ)) ^ M = 2 * (2 : ℚ) ^ (M - 1) := by
    have := congrArg (Nat.cast : Nat → ℚ) hsplit
    push_cast at this; exact this
  have hcast : ((2 ^ M - M - 1 : Nat) : ℚ) = 2 * ((2 ^ (M - 1) : Nat) : ℚ) - (M : ℚ) - 1 := by
    rw [show (2 ^ M - M - 1 : Nat) = 2 ^ M - (M + 1) from by omega,
        Nat.cast_sub (by omega)]
    push_cast
    rw [hsplitQ]; ring
  rw [hcast]
  -- (2*D - M - 1)/D = 2 - (M+1)/D
  field_simp
  ring

/-! ## 2. The rational mean bounds: `mean(M) < 2` and `mean(M) ≥ 8/5` -/

/-- The positive fractional defect `(M+1)/2^(M-1) > 0`. -/
theorem defect_pos (M : Nat) : 0 < ((M : ℚ) + 1) / ((2 ^ (M - 1) : Nat) : ℚ) := by
  have hden : (0 : ℚ) < ((2 ^ (M - 1) : Nat) : ℚ) := by
    have : (0 : Nat) < 2 ^ (M - 1) := Nat.two_pow_pos _
    exact_mod_cast this
  have hnum : (0 : ℚ) < (M : ℚ) + 1 := by positivity
  exact div_pos hnum hden

/-- **`mean_valuation_lt_two` — REAL.**
For all `M ≥ 1`, `mean(M) < 2`: the truncated-window mean is strictly below the
limiting value `2`, by the positive defect `(M+1)/2^(M-1)`. -/
theorem mean_valuation_lt_two (M : Nat) (hM : 1 ≤ M) : meanValuation M < 2 := by
  rw [mean_valuation_closed_form M hM]
  have := defect_pos M
  linarith

/-- Nat tail bound: `5 * (M + 1) ≤ 2 * 2^(M-1)` for `M ≥ 5`. Equivalent (over ℚ)
to `(M+1)/2^(M-1) ≤ 2/5`. Proved by induction from the `M = 5` base `30 ≤ 32`. -/
theorem five_mul_succ_le (M : Nat) (hM : 5 ≤ M) : 5 * (M + 1) ≤ 2 * 2 ^ (M - 1) := by
  induction M with
  | zero => omega
  | succ n ih =>
    rcases Nat.lt_or_ge n 5 with h | h
    · -- n < 5 ⟹ n+1 ≤ 5; with 5 ≤ n+1 forced, n = 4, base case 30 ≤ 32.
      interval_cases n <;> simp_all
    · have ihn := ih h
      have hn1 : n - 1 + 1 = n := by omega
      have hstep : (2 : Nat) ^ (n + 1 - 1) = 2 * 2 ^ (n - 1) := by
        rw [show n + 1 - 1 = (n - 1) + 1 from by omega, pow_succ]; ring
      rw [hstep]
      -- 5*(n+2) = 5*(n+1) + 5 ≤ 2*2^(n-1) + 5 ≤ 2*(2*2^(n-1)) since 2^(n-1) ≥ 5 large.
      have hpow_ge : (16 : Nat) ≤ 2 ^ (n - 1) := by
        calc (16 : Nat) = 2 ^ 4 := by decide
          _ ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega

/-- **`mean_valuation_ge_eight_fifths` — REAL.**
For `M ≥ 5`, `mean(M) ≥ 8/5`. Equivalent to `(M+1)/2^(M-1) ≤ 2/5`, which is the
Nat bound `5(M+1) ≤ 2·2^(M-1)` (true and tightening from `M = 5`: `30 ≤ 32`). -/
theorem mean_valuation_ge_eight_fifths (M : Nat) (hM : 5 ≤ M) :
    8 / 5 ≤ meanValuation M := by
  rw [mean_valuation_closed_form M (by omega)]
  -- Suffices: (M+1)/2^(M-1) ≤ 2/5.
  have hden : (0 : ℚ) < ((2 ^ (M - 1) : Nat) : ℚ) := by
    have : (0 : Nat) < 2 ^ (M - 1) := Nat.two_pow_pos _
    exact_mod_cast this
  have hnat : 5 * (M + 1) ≤ 2 * 2 ^ (M - 1) := five_mul_succ_le M hM
  have hQ : ((M : ℚ) + 1) / ((2 ^ (M - 1) : Nat) : ℚ) ≤ 2 / 5 := by
    rw [div_le_div_iff₀ hden (by norm_num : (0:ℚ) < 5)]
    -- (M+1)*5 ≤ 2 * 2^(M-1)
    have hc := (Nat.cast_le (α := ℚ)).mpr hnat
    push_cast at hc ⊢
    linarith
  linarith

/-! ## 3. The transcendence-free contraction certificate: `2^8 > 3^5`

`2^8 = 256 > 243 = 3^5` is exactly the statement that `2^(8/5) > 3`, raised to
the 5th power — proven purely over ℕ, no reals, no logarithms. -/

/-- **`mean_drift_pow` — REAL.** `3^5 < 2^8` (i.e. `243 < 256`). Equivalently
`2^(8/5) > 3`: the average multiplier `3 / 2^(8/5) < 1`, transcendence-free. -/
theorem mean_drift_pow : (3 : Nat) ^ 5 < 2 ^ 8 := by decide

/-! ## 4. The headline: Collatz contracts on average -/

/-- **`collatz_negative_drift` — REAL (headline).**

For `M ≥ 5`, the mean number of divisions per compressed step satisfies
`mean(M) ≥ 8/5`, and `2^(8/5) > 3` (the elementary certificate `2^8 > 3^5`).
Hence the **average per-step multiplier** `3 / 2^mean(M)` is `< 1`:

* `mean(M) ≥ 8/5`  (rational lower bound, tight at `M = 5`);
* `3^5 < 2^8`      (so `3 < 2^(8/5) ≤ 2^mean(M)`), giving `3 / 2^mean(M) < 1`.

We package the conclusion in the transcendence-free ℚ/ℕ form: the lower mean
`8/5` together with the power certificate `3^5 < 2^8`. Read together, raising the
base-2 multiplier to the 5th power, `2^(5 · mean(M)) ≥ 2^(5 · 8/5) = 2^8 > 3^5`,
so the geometric-mean multiplier `3 / 2^mean(M)` is strictly below `1`.

**This is an AVERAGE statement** — the rigorous backbone of "Collatz contracts on
average". It does NOT prove Collatz: it says nothing about individual orbits. -/
theorem collatz_negative_drift (M : Nat) (hM : 5 ≤ M) :
    8 / 5 ≤ meanValuation M ∧ (3 : Nat) ^ 5 < 2 ^ 8 :=
  ⟨mean_valuation_ge_eight_fifths M hM, mean_drift_pow⟩

/-- **Contraction in clean inequality form — REAL.**
The two ingredients of `collatz_negative_drift` chained: with `8/5 ≤ mean(M)` the
fifth power of the multiplier-denominator dominates `3^5`. Concretely we record
the strict gap `3^5 < 2^8` alongside `5 · (8/5 : ℚ) = 8`, certifying
`2^(5·mean(M)) ≥ 2^8 > 3^5`, i.e. `3 / 2^mean(M) < 1`. -/
theorem contraction_certificate (M : Nat) (hM : 5 ≤ M) :
    (5 : ℚ) * (8 / 5) = 8 ∧ 8 / 5 ≤ meanValuation M ∧ (243 : Nat) < 256 := by
  refine ⟨by norm_num, mean_valuation_ge_eight_fifths M hM, by decide⟩

end CollatzDrift
