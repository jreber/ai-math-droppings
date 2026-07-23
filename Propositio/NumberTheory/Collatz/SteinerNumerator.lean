import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr
import Propositio.NumberTheory.Collatz.CycleTelescope
import Propositio.NumberTheory.Collatz.CascadeCycles
import Propositio.NumberTheory.Collatz.CycleElementBound

/-!
# The Steiner numerator `Steiner n L` — an unconditional lower bound

**Superseded premise, corrected 2026-07-23**: this file originally investigated
discharging a hypothesis `hsteiner : Steiner n L < 3 ^ L` that
`CollatzCycleElementBound.cc_cycle_element_bound` used to require, and argued (with a
genuine, carefully-recorded elementary obstruction) that the hypothesis was not
closable by elementary methods. That analysis is no longer the live status: **the
current `CycleElementBound.lean` proves `cc_cycle_element_bound` fully
unconditionally**, via the subtraction-free bound `steiner_key_bound` (a different,
sharper elementary route than the one this file's obstruction analysis considered —
it bounds `Steiner n L` from *above* directly by induction, rather than trying to
bound the ratio `Σ 2^(S n i)/3^{i+1}` term-by-term). There is no `hsteiner` hypothesis
and no `cc_cycle_element_formula` in the current API; both the obstruction discussion
and the theorems built on them (`steiner_lt_iff_element_mul`,
`cc_cycle_element_sandwich`) are removed below as moot rather than patched, since
patching them would just restate `cc_cycle_element_bound` under a different name.

What remains is the genuinely independent content: the recursive Steiner numerator
(`CollatzCycleTelescope.Steiner`) is

    Steiner n 0     = 0,
    Steiner n (L+1) = 3 · Steiner n L + 2 ^ (S n L),

equivalently `Steiner n L = Σ_{i<L} 3^{L-1-i} · 2^{S n i}`, and the telescope identity
gives the exact factorisation `(2^A − 3^L) · n = Steiner n L` (`A := S n L`).

## What is proved here (axiom-clean, non-vacuous)

1. `steiner_ge` / `steiner_lower_bound` — the **unconditional lower bound**
   `3^(L-1) ≤ Steiner n L` (no cycle hypothesis at all; pure consequence of the
   recursion, since each step multiplies by ≥ 3).

2. `cc_cycle_element_lower_bound` — the **unconditional lower bound on the element**
   `3^(L-1)/(2^A − 3^L) ≤ n` (over ℚ), the mirror of `CycleElementBound`'s (now also
   unconditional) upper bound. Immediate from (1) and the exact factorisation
   `CollatzCycleElementBound.cc_cycle_element_equation`.
-/

namespace CollatzSteinerNumerator

open TerrasDensity (cc)
open CollatzCycleTelescope (S Steiner)

/-- Local abbreviation for the project's `Odd` (`∃ k, n = 2k+1`). -/
local notation "Odd" => TerrasDensity.Odd

/-! ## 1. Unconditional lower bound on the Steiner numerator -/

/-- **`steiner_ge` — unconditional numerator lower bound (NEW).**

For all `n L : Nat`, `3^L ≤ Steiner n (L+1)`.  Pure consequence of the recursion
`Steiner n (k+1) = 3·Steiner n k + 2^(S n k) ≥ 3·Steiner n k`, with base
`Steiner n 1 = 2^(S n 0) = 1 = 3^0`.  No cycle hypothesis is used. -/
theorem steiner_ge (n L : Nat) : 3 ^ L ≤ Steiner n (L + 1) := by
  induction L with
  | zero =>
    simp [CollatzCycleTelescope.Steiner_succ, CollatzCycleTelescope.Steiner_zero,
      CollatzCycleTelescope.S_zero]
  | succ L ih =>
    rw [CollatzCycleTelescope.Steiner_succ, pow_succ]
    -- Goal: 3^L * 3 ≤ 3 * Steiner n (L+1) + 2^(S n (L+1))
    have h2 : 3 ^ L * 3 ≤ 3 * Steiner n (L + 1) := by
      rw [Nat.mul_comm]; gcongr
    exact le_trans h2 (Nat.le_add_right _ _)

/-- **`steiner_lower_bound` — unconditional numerator lower bound, `L ≥ 1` form (NEW).**

For `L ≥ 1`, `3^(L-1) ≤ Steiner n L`.  Restatement of `steiner_ge` writing
`L = (L-1)+1`. -/
theorem steiner_lower_bound (n L : Nat) (hL : 1 ≤ L) :
    3 ^ (L - 1) ≤ Steiner n L := by
  obtain ⟨L', rfl⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by omega⟩
  simpa using steiner_ge n L'

/-! ## 2. Unconditional lower bound on the cycle element -/

/-- **`cc_cycle_element_lower_bound` — unconditional Simons–de Weger element lower
bound.**

For an odd `cc`-cycle of length `L` (`L ≥ 1`, `cc^[L] n = n`), writing `A := S n L`,

    3^(L-1) / (2^A − 3^L)  ≤  n        (over ℚ).

The mirror of `CollatzCycleElementBound.cc_cycle_element_bound` (the upper bound,
proved unconditionally there). Needs no analytic input: it follows from the exact
factorisation `(2^A − 3^L)·n = Steiner n L`
(`CollatzCycleElementBound.cc_cycle_element_equation`) together with the
unconditional numerator lower bound `3^(L-1) ≤ Steiner n L` above. -/
theorem cc_cycle_element_lower_bound (n L : Nat) (hodd : Odd n) (hL : 1 ≤ L)
    (hcyc : cc^[L] n = n) :
    (3 : ℚ) ^ (L - 1) / ((2 : ℚ) ^ S n L - (3 : ℚ) ^ L) ≤ (n : ℚ) := by
  have hlt := CollatzCycleElementBound.three_pow_lt_of_cycle n L hodd hL hcyc
  have hfactor := CollatzCycleElementBound.cc_cycle_element_equation n L hodd hL hcyc
  have hdpos : (0 : ℚ) < (2 : ℚ) ^ S n L - (3 : ℚ) ^ L := by
    have h : ((3 : Nat) ^ L : ℚ) < ((2 : Nat) ^ S n L : ℚ) := by exact_mod_cast hlt
    push_cast at h; linarith
  have hcast : (((2 ^ S n L - 3 ^ L : Nat)) : ℚ)
      = (2 : ℚ) ^ S n L - (3 : ℚ) ^ L := by
    rw [Nat.cast_sub (le_of_lt hlt)]; push_cast; ring
  have hmul : (n : ℚ) * ((2 : ℚ) ^ S n L - (3 : ℚ) ^ L) = (Steiner n L : ℚ) := by
    rw [← hcast]; exact_mod_cast hfactor
  rw [div_le_iff₀ hdpos, hmul]
  -- Goal: (3 : ℚ)^(L-1) ≤ (Steiner n L : ℚ)
  exact_mod_cast steiner_lower_bound n L hL

end CollatzSteinerNumerator

-- Axiom checks: only [propext, Classical.choice, Quot.sound] are permitted.
#print axioms CollatzSteinerNumerator.steiner_ge
#print axioms CollatzSteinerNumerator.steiner_lower_bound
#print axioms CollatzSteinerNumerator.cc_cycle_element_lower_bound
