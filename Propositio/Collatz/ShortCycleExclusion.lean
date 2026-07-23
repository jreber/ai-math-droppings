import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Propositio.Collatz.Basic
import Propositio.Collatz.CascadeCycles

/-!
# Exclusion of short `cc`-cycles (length 1 and 2) — Lean 4 (NEW extension)

This file derives a genuine, **unconditional**, axiom-clean consequence of the
already-proved fundamental cycle constraint `cc_cycle_constraint`
(`CollatzCascadeCycles.lean`): the fully-compressed odd Collatz map

    cc n = (3n+1)/2^{v₂(3n+1)}

has **no nontrivial cycle of length 1 or 2**.

## The arithmetic, in one line

For a nontrivial `L`-cycle, `cc_cycle_constraint` gives `3^L < 2^A < 4^L` where
`A := Σ_{i<L} v₂(3·cc^[i] n + 1)`.

  * `L = 1`:  `3 < 2^A < 4`.  No power of `2` lies in the open interval `(3,4)`:
    `A ≤ 1 ⟹ 2^A ≤ 2 < 3`, and `A ≥ 2 ⟹ 2^A ≥ 4`.  Contradiction.
  * `L = 2`:  `9 < 2^A < 16`.  No power of `2` lies in `(9,16)`:
    `A ≤ 3 ⟹ 2^A ≤ 8 < 9`, and `A ≥ 4 ⟹ 2^A ≥ 16`.  Contradiction.

## What is new

  1. `cc_no_nontrivial_one_cycle` — no nontrivial `cc` 1-cycle: for odd `n` with
     `cc n = n` and `1 < n`, `False`.
  2. `cc_fixed_point_eq_one` — every odd fixed point of `cc` is `1`.
  3. `cc_no_nontrivial_two_cycle` — no nontrivial `cc` 2-cycle: for odd `n` with
     `cc (cc n) = n` and a nontriviality witness, `False`.

## Honesty caveat — why only `L = 1, 2`

This method excludes **exactly** the lengths for which the open interval
`(3^L, 4^L)` contains no power of `2`.  That fails already at `L = 3`:
`(27, 64)` contains `2^5 = 32`, so the constraint `27 < 2^A < 64` is satisfiable
(`A = 5`) and does **not** force a contradiction.  Hence this is a genuine
length-1-and-2 result, not a general cycle exclusion. Ruling out all `L`
(Steiner 1977, Simons–de Weger 2005) needs transcendence theory and is far
beyond this file.
-/

namespace CollatzShortCycleExclusion

open TerrasDensity (cc)
open scoped BigOperators

local notation "Odd" => TerrasDensity.Odd

/-! ## Lemma: a power of `2` cannot lie strictly between consecutive powers used here. -/

/-- No power of `2` lies in the open interval `(3, 4)`: if `3 < 2^A < 4` then
`False`.  (`A ≤ 1 ⟹ 2^A ≤ 2`; `A ≥ 2 ⟹ 2^A ≥ 4`.) -/
theorem no_pow_two_in_three_four (A : Nat) (hlo : 3 < 2 ^ A) (hhi : 2 ^ A < 4) :
    False := by
  rcases Nat.lt_or_ge A 2 with hA | hA
  · -- A ≤ 1 ⟹ 2^A ≤ 2 < 3, contradicting 3 < 2^A.
    interval_cases A <;> simp_all
  · -- A ≥ 2 ⟹ 2^A ≥ 2^2 = 4, contradicting 2^A < 4.
    have : (2 : Nat) ^ 2 ≤ 2 ^ A := Nat.pow_le_pow_right (by norm_num) hA
    omega

/-- No power of `2` lies in the open interval `(9, 16)`: if `9 < 2^A < 16` then
`False`.  (`A ≤ 3 ⟹ 2^A ≤ 8`; `A ≥ 4 ⟹ 2^A ≥ 16`.) -/
theorem no_pow_two_in_nine_sixteen (A : Nat) (hlo : 9 < 2 ^ A) (hhi : 2 ^ A < 16) :
    False := by
  rcases Nat.lt_or_ge A 4 with hA | hA
  · -- A ≤ 3 ⟹ 2^A ≤ 8 < 9, contradicting 9 < 2^A.
    interval_cases A <;> simp_all
  · -- A ≥ 4 ⟹ 2^A ≥ 2^4 = 16, contradicting 2^A < 16.
    have : (2 : Nat) ^ 4 ≤ 2 ^ A := Nat.pow_le_pow_right (by norm_num) hA
    omega

/-! ## 1. No nontrivial 1-cycle. -/

/-- **`cc_no_nontrivial_one_cycle` (NEW).**

There is no nontrivial `cc` 1-cycle: for odd `n` with `cc n = n` and `1 < n`,
`False`.

Proof. Instantiate `cc_cycle_constraint` at `L = 1`.  The hypothesis
`cc^[1] n = n` is `cc n = n`; the nontriviality witness is `j = 0` with
`cc^[0] n = n > 1`.  We obtain `3^1 < 2^A < 4^1`, i.e. `3 < 2^A < 4`, which is
impossible by `no_pow_two_in_three_four`. -/
theorem cc_no_nontrivial_one_cycle (n : Nat) (hodd : Odd n) (hfix : cc n = n)
    (hn : 1 < n) : False := by
  have hcyc : cc^[1] n = n := by simpa using hfix
  have hnontriv : ∃ j ∈ Finset.range 1, 1 < cc^[j] n :=
    ⟨0, by simp, by simpa using hn⟩
  have hcon := CollatzCascadeCycles.cc_cycle_constraint n 1 hodd hcyc (le_refl 1) hnontriv
  set A := ∑ i ∈ Finset.range 1, padicValNat 2 (3 * cc^[i] n + 1) with hA
  obtain ⟨hlo, hhi⟩ := hcon
  -- 3^1 = 3, 4^1 = 4.
  rw [pow_one] at hlo
  rw [pow_one] at hhi
  exact no_pow_two_in_three_four A hlo hhi

/-! ## 2. Odd fixed points of `cc` are exactly `1`. -/

/-- **`cc_fixed_point_eq_one` (NEW).**

Every odd fixed point of `cc` equals `1`: for odd `n` with `cc n = n`, `n = 1`.

Proof. `n` is odd hence `n ≥ 1`. If `1 < n`, `cc_no_nontrivial_one_cycle` gives a
contradiction; so `n = 1`. (And indeed `cc 1 = 1`, so `1` genuinely is the unique
odd fixed point.) -/
theorem cc_fixed_point_eq_one (n : Nat) (hodd : Odd n) (hfix : cc n = n) : n = 1 := by
  obtain ⟨k, hk⟩ := hodd
  rcases Nat.lt_or_ge 1 n with hn | hn
  · exact absurd (cc_no_nontrivial_one_cycle n ⟨k, hk⟩ hfix hn) (by simp)
  · -- n ≤ 1 and n odd (n = 2k+1 ≥ 1) ⟹ n = 1.
    omega

/-! ## 3. No nontrivial 2-cycle. -/

/-- **`cc_no_nontrivial_two_cycle` (NEW).**

There is no nontrivial `cc` 2-cycle: for odd `n` with `cc (cc n) = n` and a
nontriviality witness `∃ j ∈ Finset.range 2, 1 < cc^[j] n`, `False`.

Proof. Instantiate `cc_cycle_constraint` at `L = 2`.  The hypothesis
`cc^[2] n = n` is `cc (cc n) = n`.  We obtain `3^2 < 2^A < 4^2`, i.e.
`9 < 2^A < 16`, which is impossible by `no_pow_two_in_nine_sixteen`. -/
theorem cc_no_nontrivial_two_cycle (n : Nat) (hodd : Odd n)
    (hcyc2 : cc (cc n) = n) (hnontriv : ∃ j ∈ Finset.range 2, 1 < cc^[j] n) :
    False := by
  have hcyc : cc^[2] n = n := by
    rw [show (2 : Nat) = 1 + 1 from rfl, Function.iterate_add_apply]
    simpa using hcyc2
  have hcon := CollatzCascadeCycles.cc_cycle_constraint n 2 hodd hcyc (by omega) hnontriv
  set A := ∑ i ∈ Finset.range 2, padicValNat 2 (3 * cc^[i] n + 1) with hA
  obtain ⟨hlo, hhi⟩ := hcon
  -- 3^2 = 9, 4^2 = 16.
  norm_num at hlo hhi
  exact no_pow_two_in_nine_sixteen A hlo hhi

end CollatzShortCycleExclusion
