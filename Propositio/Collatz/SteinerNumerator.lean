import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr
import Propositio.Collatz.CycleTelescope
import Propositio.Collatz.CascadeCycles
import Propositio.Collatz.CycleElementBound

/-!
# The Steiner numerator `Steiner n L` — bounds and the obstruction to unconditionality

`CollatzCycleElementBound.cc_cycle_element_bound` proves the sharp Simons–de Weger
element bound `n < 3^L/(2^A − 3^L)` for a nontrivial cc-cycle, **conditional** on the
single hypothesis

    hsteiner :  Steiner n L < 3 ^ L                                   (numerator estimate)

This file investigates discharging that hypothesis.  The recursive Steiner numerator
(`CollatzCycleTelescope.Steiner`) is

    Steiner n 0     = 0,
    Steiner n (L+1) = 3 · Steiner n L + 2 ^ (S n L),

equivalently `Steiner n L = Σ_{i<L} 3^{L-1-i} · 2^{S n i}`, and the telescope identity
gives the exact factorisation `(2^A − 3^L) · n = Steiner n L` (`A := S n L`).

## What is proved here (all axiom-clean, all non-vacuous)

1. `steiner_ge` / `steiner_lower_bound` — the **unconditional lower bound**
   `3^(L-1) ≤ Steiner n L` (no cycle hypothesis at all; pure consequence of the
   recursion, since each step multiplies by ≥ 3).  Together with the *target*
   `Steiner n L < 3^L` this would sandwich `Steiner n L ∈ [3^(L-1), 3^L)` — i.e. the
   numerator estimate is a "within one factor of 3" statement, and the lower half is
   free.

2. `cc_cycle_element_lower_bound` — the **unconditional lower bound on the element**
   `3^(L-1)/(2^A − 3^L) ≤ n` (over ℚ), the mirror of the conditional upper bound.
   This is the Simons–de Weger minimal-element *lower* estimate and needs no analytic
   input: it is immediate from (1) and the exact factorisation.

3. `steiner_lt_iff_element_mul` — the **obstruction, made explicit**: for a cc-cycle,
   `Steiner n L < 3^L  ↔  n · (2^A − 3^L) < 3^L`.  The hypothesis `hsteiner` consumed
   by `cc_cycle_element_bound` is therefore *logically identical* (recast through the
   exact factorisation) to that theorem's own conclusion `n·(2^A−3^L) < 3^L`.  Hence
   "discharging `hsteiner`" is **not** the discharge of an independent lemma — it *is*
   the full Simons–de Weger element bound.  This is recorded so future work does not
   treat the numerator estimate as a cheaper side-condition.

4. `cc_cycle_element_sandwich` — the two-sided element bound, conditional only on
   `hsteiner` (carrying the upper half through to `cc_cycle_element_bound`).

## Honest status: `cc_cycle_element_bound` remains CONDITIONAL

`Steiner n L < 3^L` is **not** proved here, and the obstruction is genuine, not a gap
in effort:

* The recursion `Steiner n (L+1) = 3·Steiner n L + 2^(S n L)` multiplies the running
  numerator by exactly 3 and adds `2^(S n L)`.  Dividing by `3^L`, the target is
  `Σ_{i<L} 2^(S n i)/3^{i+1} < 1`.  Writing `r_i := 2^(S n i)/3^{i+1}` and using the
  partial telescope `2^(S n i)·(cc^[i] n) = 3^i·n + Steiner n i`, even with full
  minimality `n ≤ cc^[i] n` the sharpest elementary estimate gives only
  `Σ r_i ≤ L/3`, which exceeds 1 once `L ≥ 3`.  (Recorded independently in
  `docs/kb/failed/2026-06-29__conj-2026-06-29-002__steiner-numerator.json`.)
* Getting below 1 requires that the cycle elements **grow** away from the minimum
  (Steiner's 1977 descent), not merely `cc^[i] n ≥ n`; equivalently a lower bound on
  `2^A − 3^L` of Baker / linear-forms-in-logarithms type.  Neither is an elementary
  ℕ-arithmetic fact and neither is available cheaply at this layer.

So this brick is **not closable by elementary methods**; `cc_cycle_element_bound`
stays conditional on the numerator estimate, and the strongest honest deliverables are
the unconditional lower bounds (1)–(2) plus the obstruction equivalence (3).
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
bound (NEW).**

For a nontrivial cc-cycle of length `L` (odd `n`, `L ≥ 1`, `cc^[L] n = n`, some
element `> 1`), writing `A := S n L`,

    3^(L-1) / (2^A − 3^L)  ≤  n        (over ℚ).

This is the mirror of the conditional upper bound `cc_cycle_element_bound` and needs
**no** analytic input: it follows from the exact factorisation
`(2^A − 3^L)·n = Steiner n L` together with the unconditional numerator lower bound
`3^(L-1) ≤ Steiner n L`. -/
theorem cc_cycle_element_lower_bound (n L : Nat) (hodd : Odd n) (hL : 1 ≤ L)
    (hcyc : cc^[L] n = n) (hnontriv : ∃ j ∈ Finset.range L, 1 < cc^[j] n) :
    (3 : ℚ) ^ (L - 1) / ((2 : ℚ) ^ S n L - (3 : ℚ) ^ L) ≤ (n : ℚ) := by
  obtain ⟨hlt, _hub, hfactor, _hval⟩ :=
    CollatzCycleElementBound.cc_cycle_element_formula n L hodd hL hcyc hnontriv
  have hdpos : (0 : ℚ) < (2 : ℚ) ^ S n L - (3 : ℚ) ^ L := by
    have h : ((3 : Nat) ^ L : ℚ) < ((2 : Nat) ^ S n L : ℚ) := by exact_mod_cast hlt
    push_cast at h; linarith
  have hcast : (((2 ^ S n L - 3 ^ L : Nat)) : ℚ)
      = (2 : ℚ) ^ S n L - (3 : ℚ) ^ L := by
    rw [Nat.cast_sub (le_of_lt hlt)]; push_cast; ring
  have hmul : (n : ℚ) * ((2 : ℚ) ^ S n L - (3 : ℚ) ^ L) = (Steiner n L : ℚ) := by
    rw [← hcast, mul_comm]; exact_mod_cast hfactor
  rw [div_le_iff₀ hdpos, hmul]
  -- Goal: (3 : ℚ)^(L-1) ≤ (Steiner n L : ℚ)
  exact_mod_cast steiner_lower_bound n L hL

/-! ## 3. The obstruction, made explicit -/

/-- **`steiner_lt_iff_element_mul` — the numerator estimate *is* the element bound (NEW).**

For a nontrivial cc-cycle of length `L`,

    Steiner n L < 3^L   ↔   n · (2^A − 3^L) < 3^L,        A := S n L.

The two are interchanged by the exact factorisation `(2^A − 3^L)·n = Steiner n L`.
Consequently the hypothesis `hsteiner : Steiner n L < 3^L` consumed by
`CollatzCycleElementBound.cc_cycle_element_bound` is logically identical to that
theorem's *conclusion* `n·(2^A − 3^L) < 3^L`; the numerator estimate is **not** an
independent, cheaper side-condition — discharging it is the full element bound. -/
theorem steiner_lt_iff_element_mul (n L : Nat) (hodd : Odd n) (hL : 1 ≤ L)
    (hcyc : cc^[L] n = n) (hnontriv : ∃ j ∈ Finset.range L, 1 < cc^[j] n) :
    Steiner n L < 3 ^ L ↔ n * (2 ^ S n L - 3 ^ L) < 3 ^ L := by
  obtain ⟨_hlt, _hub, hfactor, _hval⟩ :=
    CollatzCycleElementBound.cc_cycle_element_formula n L hodd hL hcyc hnontriv
  have hfac' : n * (2 ^ S n L - 3 ^ L) = Steiner n L := by
    rw [mul_comm]; exact hfactor
  rw [hfac']

/-! ## 4. The two-sided element bound (upper half still conditional) -/

/-- **`cc_cycle_element_sandwich` — two-sided element bound (NEW).**

For a nontrivial cc-cycle of length `L`, with the numerator estimate
`hsteiner : Steiner n L < 3^L` (the single analytic input, supplying *only* the upper
half), the element is pinned to a factor-3 window:

    3^(L-1)/(2^A − 3^L)  ≤  n  <  3^L/(2^A − 3^L),        A := S n L.

The lower bound is unconditional (`cc_cycle_element_lower_bound`); the upper bound is
`CollatzCycleElementBound.cc_cycle_element_bound`, which is what consumes `hsteiner`. -/
theorem cc_cycle_element_sandwich (n L : Nat) (hodd : Odd n) (hL : 1 ≤ L)
    (hcyc : cc^[L] n = n) (hnontriv : ∃ j ∈ Finset.range L, 1 < cc^[j] n)
    (hsteiner : Steiner n L < 3 ^ L) :
    (3 : ℚ) ^ (L - 1) / ((2 : ℚ) ^ S n L - (3 : ℚ) ^ L) ≤ (n : ℚ) ∧
    (n : ℚ) < (3 : ℚ) ^ L / ((2 : ℚ) ^ S n L - (3 : ℚ) ^ L) :=
  ⟨cc_cycle_element_lower_bound n L hodd hL hcyc hnontriv,
   CollatzCycleElementBound.cc_cycle_element_bound n L hodd hL hcyc hnontriv hsteiner⟩

end CollatzSteinerNumerator

-- Axiom checks: only [propext, Classical.choice, Quot.sound] are permitted.
#print axioms CollatzSteinerNumerator.steiner_ge
#print axioms CollatzSteinerNumerator.steiner_lower_bound
#print axioms CollatzSteinerNumerator.cc_cycle_element_lower_bound
#print axioms CollatzSteinerNumerator.steiner_lt_iff_element_mul
#print axioms CollatzSteinerNumerator.cc_cycle_element_sandwich
