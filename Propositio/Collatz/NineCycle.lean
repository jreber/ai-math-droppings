import Propositio.Collatz.CycleUniform
import Propositio.Collatz.CycleEnum

/-!
# No nontrivial `cc`-cycle of length 9 (`L = 9`)

This file discharges `cycleExcludedB 9 = true` and hence proves `cc` has no
nontrivial 9-step cycle, extending the `L ≤ 8` result of
`CollatzCycleCapstone`/`CollatzCycleUniform` by one.

## Why this needed a new idea (the OOM that blocked `L = 9`)

`CollatzCycleUniform` discharges `cycleExcludedB L = true` for `L ≤ 8` with a
*single* kernel `decide` over **all** admissible `(A, composition)` pairs at once.
For `L = 9` the admissible totals are `A ∈ {15, 16, 17}` (those with
`3⁹ = 19683 < 2^A < 4⁹ = 262144`), with composition counts

  `C(14,8) = 3003`,  `C(15,8) = 6435`,  `C(16,8) = 12870`   (total ≈ 22308).

A single `decide` over all ≈22k compositions exhausts memory (the OOM that
crashed an earlier session). `native_decide` is banned (it would inject
`Lean.ofReduceBool`).

## The fix: split the kernel `decide` per total `A`

Each admissible `A` is checked by its **own** `decide` (`check9_15/16/17`), so the
kernel only ever holds one `A`'s compositions at a time; memory is freed between
declarations. `cycleExcludedB9` then assembles the three per-`A` facts. The one subtlety: the
guard `A ∈ {15,16,17}` must be derived in a **separate** subgoal, *before* the big
body `(compositions 9 A).all …` is in view — otherwise `interval_cases` eagerly
evaluates that 12870-element body and overflows the kernel stack. So the proof
splits on the guard, pins `A = 15 ∨ 16 ∨ 17` from the power bounds alone, then
`rcases` + `exact check9_*` references each body without ever evaluating it.
No single `decide` exceeds ~12870 compositions.

The marquee theorem `cc_no_nontrivial_nine_cycle` is then immediate from the
reusable uniform theorem `cc_no_nontrivial_cycle_of_excluded`.

## Resource note

Each `check9_*` is discharged through `CollatzCycleEnum.noStDvd`, a recursive
enumerator that carries the `steinerVal` accumulator down the composition tree
instead of materializing `compositions 9 A`. This keeps the live kernel term `O(L)`
deep; `check9_17` (12870 compositions) peaks ~3.6 GB / ~1 min (vs ~6 GB / ~2 min for
the list-materializing `decide`). **Build this file through `scripts/safe-lean.sh`**
(cgroup-bounded), never a bare `lake build`. All theorems are axiom-clean:
`#print axioms` reports only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`,
no `Lean.ofReduceBool`).
-/

namespace CollatzNineCycle

open CollatzCycleDecide (steinerVal compositions)
open CollatzCycleEnum (noStDvd noStDvd_top)
open CollatzCycleUniform (cycleExcludedB cc_no_nontrivial_cycle_of_excluded)
open TerrasDensity (cc)

local notation "Odd" => TerrasDensity.Odd

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000000

/-! ## §1  Per-total kernel `decide`s

Each checks that for the given admissible total `A`, no length-9 composition `as`
of `A` satisfies `(2^A − 3⁹) ∣ steinerVal as` — exactly the body of
`cycleExcludedB 9` at that `A`. -/

/-- `A = 15`: 3003 compositions. Discharged through the recursive enumerator
`noStDvd` (`noStDvd_top` bridge) rather than a `decide` over the materialized list. -/
theorem check9_15 :
    (compositions 9 15).all (fun as => !decide ((2 ^ 15 - 3 ^ 9) ∣ steinerVal as)) = true := by
  rw [← noStDvd_top]; decide

/-- `A = 16`: 6435 compositions. -/
theorem check9_16 :
    (compositions 9 16).all (fun as => !decide ((2 ^ 16 - 3 ^ 9) ∣ steinerVal as)) = true := by
  rw [← noStDvd_top]; decide

/-- `A = 17`: 12870 compositions (the heavy one). Via `noStDvd` this peaks ~3.6 GB
/ ~1 min instead of ~6 GB / ~2 min for the list-materializing `decide`. -/
theorem check9_17 :
    (compositions 9 17).all (fun as => !decide ((2 ^ 17 - 3 ^ 9) ∣ steinerVal as)) = true := by
  rw [← noStDvd_top]; decide

/-! ## §2  Assembling `cycleExcludedB 9 = true` from the three per-`A` facts -/

/-- The decidable exclusion predicate holds at `L = 9`.

We unfold `cycleExcludedB 9` to `(range 18).all (fun A => if guard A then body A else true)`
and check each `A < 18`. The `if`-guard `3⁹ < 2^A ∧ 2^A < 4⁹` is a cheap `decide`; it
is true exactly for `A ∈ {15, 16, 17}`, where the body is the matching `check9_*`. -/
theorem cycleExcludedB9 : cycleExcludedB 9 = true := by
  rw [cycleExcludedB]
  apply List.all_eq_true.mpr
  intro A hA
  rw [List.mem_range] at hA
  by_cases hg : (3 : Nat) ^ 9 < 2 ^ A ∧ 2 ^ A < 4 ^ 9
  · -- Live guard: pin `A ∈ {15,16,17}` in a *separate* subgoal (no big body present,
    -- so `interval_cases` never evaluates `(compositions 9 A).all …`), then discharge.
    rw [if_pos hg]
    have hval : A = 15 ∨ A = 16 ∨ A = 17 := by
      obtain ⟨h1, h2⟩ := hg
      interval_cases A <;>
        first
          | (left; rfl) | (right; left; rfl) | (right; right; rfl)
          | (exfalso; revert h1; decide)
    rcases hval with rfl | rfl | rfl
    · exact check9_15
    · exact check9_16
    · exact check9_17
  · rw [if_neg hg]

/-! ## §3  The marquee theorem -/

/-- **No nontrivial `cc`-cycle of length 9.**

If `n` is odd, `cc^[9] n = n`, and some iterate in the cycle exceeds `1`, this is a
contradiction. Immediate from the uniform exclusion theorem and `cycleExcludedB9`. -/
theorem cc_no_nontrivial_nine_cycle
    (n : Nat) (hodd : Odd n) (hcyc : cc^[9] n = n)
    (hnt : ∃ j ∈ Finset.range 9, 1 < cc^[j] n) : False :=
  cc_no_nontrivial_cycle_of_excluded 9 (by norm_num) cycleExcludedB9 n hodd hcyc hnt

/-! ## §4  Axiom checks -/

#print axioms cycleExcludedB9
#print axioms cc_no_nontrivial_nine_cycle

end CollatzNineCycle
