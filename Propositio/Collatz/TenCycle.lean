import Propositio.Collatz.CycleUniform
import Propositio.Collatz.CycleEnum

/-!
# No nontrivial `cc`-cycle of length 10 (`L = 10`)

Discharges `cycleExcludedB 10 = true` and hence proves `cc` has no nontrivial
10-step cycle, extending the `L ≤ 9` result by one.

## Admissible totals at `L = 10`

  `3^10 = 59049`, `4^10 = 2^20 = 1048576`

  The admissible condition `3^10 < 2^A < 4^10` holds exactly for `A ∈ {16, 17, 18, 19}`:

    A = 16: 2^16 = 65536,  C(15,9) =  5005 compositions
    A = 17: 2^17 = 131072, C(16,9) = 11440 compositions
    A = 18: 2^18 = 262144, C(17,9) = 24310 compositions
    A = 19: 2^19 = 524288, C(18,9) = 48620 compositions   ← heaviest

## Strategy (inherited from `CollatzNineCycle`)

Each admissible `A` is discharged by its own `decide` via the `noStDvd` recursive
enumerator (which carries the `steinerVal` accumulator through the composition tree
rather than materialising the list).  The `noStDvd_top` bridge converts the
`decide` result to the `(compositions L A).all …` form that `cycleExcludedB` needs.

## Resource note

`check10_19` (48620 compositions) is the heaviest call — empirically ~4× the cost of
`check9_17` (12870 compositions, ≈1 min at `noStDvd`).  Estimated wall-clock
~4 minutes; well within the 15-min cgroup limit of `scripts/safe-lean.sh`.
Build only through `safe-lean.sh`, never bare `lake build`.
`set_option maxHeartbeats 0` disables the heartbeat ceiling; the OS-level
`timeout 900s` in `safe-lean.sh` is the safety net.

All theorems are axiom-clean: `#print axioms` reports only
`[propext, Classical.choice, Quot.sound]`.
-/

namespace CollatzTenCycle

open CollatzCycleDecide (steinerVal compositions)
open CollatzCycleEnum (noStDvd noStDvd_top)
open CollatzCycleUniform (cycleExcludedB cc_no_nontrivial_cycle_of_excluded)
open TerrasDensity (cc)

local notation "Odd" => TerrasDensity.Odd

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-! ## §1  Per-total kernel `decide`s -/

/-- `A = 16`: 5005 compositions. -/
theorem check10_16 :
    (compositions 10 16).all (fun as => !decide ((2 ^ 16 - 3 ^ 10) ∣ steinerVal as)) = true := by
  rw [← noStDvd_top]; decide

/-- `A = 17`: 11440 compositions. -/
theorem check10_17 :
    (compositions 10 17).all (fun as => !decide ((2 ^ 17 - 3 ^ 10) ∣ steinerVal as)) = true := by
  rw [← noStDvd_top]; decide

/-- `A = 18`: 24310 compositions. -/
theorem check10_18 :
    (compositions 10 18).all (fun as => !decide ((2 ^ 18 - 3 ^ 10) ∣ steinerVal as)) = true := by
  rw [← noStDvd_top]; decide

/-- `A = 19`: 48620 compositions (the heavy one). -/
theorem check10_19 :
    (compositions 10 19).all (fun as => !decide ((2 ^ 19 - 3 ^ 10) ∣ steinerVal as)) = true := by
  rw [← noStDvd_top]; decide

/-! ## §2  Assembling `cycleExcludedB 10 = true` -/

theorem cycleExcludedB10 : cycleExcludedB 10 = true := by
  rw [cycleExcludedB]
  apply List.all_eq_true.mpr
  intro A hA
  rw [List.mem_range] at hA
  by_cases hg : (3 : Nat) ^ 10 < 2 ^ A ∧ 2 ^ A < 4 ^ 10
  · rw [if_pos hg]
    have hval : A = 16 ∨ A = 17 ∨ A = 18 ∨ A = 19 := by
      obtain ⟨h1, h2⟩ := hg
      interval_cases A <;>
        first
          | (left; rfl) | (right; left; rfl) | (right; right; left; rfl)
          | (right; right; right; rfl) | (exfalso; revert h1; decide)
    rcases hval with rfl | rfl | rfl | rfl
    · exact check10_16
    · exact check10_17
    · exact check10_18
    · exact check10_19
  · rw [if_neg hg]

/-! ## §3  Marquee theorem -/

/-- **No nontrivial `cc`-cycle of length 10.** -/
theorem cc_no_nontrivial_ten_cycle
    (n : Nat) (hodd : Odd n) (hcyc : cc^[10] n = n)
    (hnt : ∃ j ∈ Finset.range 10, 1 < cc^[j] n) : False :=
  cc_no_nontrivial_cycle_of_excluded 10 (by norm_num) cycleExcludedB10 n hodd hcyc hnt

/-! ## §4  Axiom checks -/

#print axioms cycleExcludedB10
#print axioms cc_no_nontrivial_ten_cycle

end CollatzTenCycle
