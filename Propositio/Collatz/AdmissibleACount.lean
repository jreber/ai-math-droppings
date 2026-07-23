import Mathlib.Data.Nat.Log
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Exact closed-form count of admissible total-valuations `A` per cycle length `L`

## Background

`CollatzCascadeCycles.cc_cycle_constraint` shows that any nontrivial `cc`-cycle of
length `L ≥ 1` has its total 2-adic valuation `A` pinned to the open window

    3 ^ L < 2 ^ A < 4 ^ L.

`CollatzCycleUniform.cycleExcludedB` enumerates exactly the `A ∈ List.range (2 * L)`
satisfying `3 ^ L < 2 ^ A ∧ 2 ^ A < 4 ^ L` (the second conjunct is automatic once
`A < 2 * L`, since `4 ^ L = 2 ^ (2 * L)` and `2 ^ ·` is strictly monotone). This
file computes the **exact count** of such admissible `A`, in closed form, as a
function of `L` alone — the "first half" of proof-queue card `conj-2026-06-29-003`.

## The queue card had an off-by-one error

The queue statement conjectures the count is

    ⌊L · log₂ 4⌋ − ⌈L · log₂ 3⌉ + 1        (†)

Since `log₂ 4 = 2`, `⌊L · log₂ 4⌋ = 2 * L`, so (†) reads `2*L − ⌈L·log₂3⌉ + 1`.
Checking this against the concrete admissible-`A` sets already recorded in
`CollatzCycleUniform`/`CollatzThirteenCycle` shows (†) **overcounts by exactly
one**:

  * `L = 11`: admissible `A ∈ {18,19,20,21}`, actual count `4`.
    `⌈11·log₂3⌉ = 18`, so (†) gives `22 − 18 + 1 = 5 ≠ 4`.
  * `L = 12`: admissible `A ∈ {20,21,22,23}`, actual count `4`.
    `⌈12·log₂3⌉ = 20`, so (†) gives `24 − 20 + 1 = 5 ≠ 4`.
  * `L = 13`: admissible `A ∈ {21,22,23,24,25}`, actual count `5`.
    `⌈13·log₂3⌉ = 21`, so (†) gives `26 − 21 + 1 = 6 ≠ 5`.

The bug: the window is `3^L < 2^A < 4^L` with the **upper end strict**, and
`4^L = 2^(2L)` is exactly a power of two, so the largest admissible `A` is
`2*L − 1`, not `2*L`. The standard "count of integers in `(a,b)`" formula
`⌊b⌋ − ⌈a⌉ + 1` is only correct when `b` itself is *not* attained (i.e. really
counts `[⌈a⌉, ⌊b⌋]`); here the true upper endpoint of the *closed* range of
admissible integers is `⌊L·log₂4⌋ − 1`, not `⌊L·log₂4⌋`. The corrected formula
drops the `+1`:

    2*L − ⌈L · log₂ 3⌉                      (corrected)

which does match all three data points above (`22−18=4`, `24−20=4`, `26−21=5`).

## What this file proves

Rather than fight `Real.logb`/`Int.ceil` conversions, we give the **exact,
purely-`Nat` closed form**, using `Nat.log` (floor of the base-2 log) instead of
a real-number ceiling of `log₂ 3`:

    admissibleACount L = 2 * L − 1 − Nat.log 2 (3 ^ L)        (for L ≥ 1)

This is provably equal to the corrected real-log formula above (since
`Nat.log 2 (3^L) = ⌈L·log₂3⌉ − 1`, `3^L` never being an exact power of `2`), but
avoids importing real-analysis machinery entirely — `Nat.log` is exactly "the
integer straddling `L log₂ 3` from below", which is the only fact this count
needs.
-/

namespace CollatzAdmissibleACount

/-- The set of admissible total valuations `A` for cycle length `L`: those with
`3 ^ L < 2 ^ A` and `A` in the ambient window `range (2 * L)` (equivalently,
together with `A < 2 * L`, exactly `3 ^ L < 2 ^ A < 4 ^ L` — see
`admissibleA_iff` below). This is definitionally the set `cycleExcludedB`
ranges over. -/
def admissibleA (L : ℕ) : Finset ℕ :=
  (Finset.range (2 * L)).filter (fun A => 3 ^ L < 2 ^ A)

/-- Membership in `admissibleA L` is exactly the fundamental cycle window
`3 ^ L < 2 ^ A < 4 ^ L` (matching `CollatzCascadeCycles.cc_cycle_constraint`). -/
theorem mem_admissibleA_iff (L A : ℕ) :
    A ∈ admissibleA L ↔ 3 ^ L < 2 ^ A ∧ 2 ^ A < 4 ^ L := by
  have h22 : (4 : ℕ) = 2 ^ 2 := by norm_num
  have h4L : (4 : ℕ) ^ L = 2 ^ (2 * L) := by rw [h22, ← pow_mul]
  simp only [admissibleA, Finset.mem_filter, Finset.mem_range, h4L]
  constructor
  · rintro ⟨hA, h3⟩
    exact ⟨h3, Nat.pow_lt_pow_right (by norm_num) hA⟩
  · rintro ⟨h3, h2⟩
    refine ⟨?_, h3⟩
    exact (Nat.pow_lt_pow_iff_right (by norm_num)).mp h2

/-- **The exact closed-form count of admissible `A`.**

For every cycle length `L ≥ 1`,

    (admissibleA L).card = 2 * L − 1 − Nat.log 2 (3 ^ L).

This is the corrected, purely-elementary form of the queue card's conjectured
count formula (see the file docstring for the off-by-one correction). -/
theorem admissibleA_card (L : ℕ) (hL : 1 ≤ L) :
    (admissibleA L).card = 2 * L - 1 - Nat.log 2 (3 ^ L) := by
  set k := Nat.log 2 (3 ^ L) with hk
  have h3pos : (3 : ℕ) ^ L ≠ 0 := by positivity
  -- Pointwise: `3^L < 2^A ↔ k < A` (Nat.log_lt_iff_lt_pow).
  have hiff : ∀ A, (3 : ℕ) ^ L < 2 ^ A ↔ k < A := by
    intro A
    exact (Nat.log_lt_iff_lt_pow (by norm_num) h3pos).symm
  -- `k < 2 * L` (from `3^L < 4^L = 2^(2L)`, the strict cycle upper bound).
  have h34 : (3 : ℕ) ^ L < 4 ^ L := Nat.pow_lt_pow_left (by norm_num) (by omega)
  have h22 : (4 : ℕ) = 2 ^ 2 := by norm_num
  have h4L : (4 : ℕ) ^ L = 2 ^ (2 * L) := by rw [h22, ← pow_mul]
  have hk2L : k < 2 * L := (hiff (2 * L)).mp (by rw [← h4L]; exact h34)
  -- Rewrite `admissibleA L` as `Finset.Ico (k+1) (2*L)`.
  have hset : admissibleA L = Finset.Ico (k + 1) (2 * L) := by
    ext A
    simp only [admissibleA, Finset.mem_filter, Finset.mem_range, Finset.mem_Ico, hiff]
    omega
  rw [hset, Nat.card_Ico]
  omega

/-- Sanity check reproducing the concrete data recorded in `CollatzCycleUniform`
(`L=8: {13,14,15}`) and `CollatzThirteenCycle` (`L=13: {21,...,25}`), confirming
the corrected formula against the actual admissible sets used in the cycle-ladder
proofs. Evaluated by `decide` on small, honest `Nat` arithmetic — not a stand-in
for `admissibleA_card`, which is the real theorem. -/
example : (admissibleA 8).card = 3 := by decide
example : (admissibleA 11).card = 4 := by decide
example : (admissibleA 12).card = 4 := by decide

end CollatzAdmissibleACount
