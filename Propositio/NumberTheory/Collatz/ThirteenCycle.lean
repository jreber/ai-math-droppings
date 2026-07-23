import Propositio.NumberTheory.Collatz.ThirteenAsm21
import Propositio.NumberTheory.Collatz.ThirteenAsm22
import Propositio.NumberTheory.Collatz.ThirteenAsm23
import Propositio.NumberTheory.Collatz.ThirteenAsm24
import Propositio.NumberTheory.Collatz.ThirteenAsm25
import Propositio.NumberTheory.Collatz.CycleUniform

namespace CollatzThirteenCycle
open CollatzCycleDecide (steinerVal compositions)
open CollatzCycleEnum (noStDvd noStDvd_top)
open CollatzCycleUniform (cycleExcludedB cc_no_nontrivial_cycle_of_excluded)
open TerrasDensity (cc)
local notation "Odd" => TerrasDensity.Odd
set_option maxRecDepth 100000

theorem cycleExcludedB13 : cycleExcludedB 13 = true := by
  rw [cycleExcludedB]
  apply List.all_eq_true.mpr
  intro A hA
  rw [List.mem_range] at hA
  by_cases hg : (3 : Nat) ^ 13 < 2 ^ A ∧ 2 ^ A < 4 ^ 13
  · rw [if_pos hg]
    have hval : A = 21 ∨ A = 22 ∨ A = 23 ∨ A = 24 ∨ A = 25 := by
      obtain ⟨h1, h2⟩ := hg
      interval_cases A <;>
        first
          | (left; rfl)
          | (right; left; rfl)
          | (right; right; left; rfl)
          | (right; right; right; left; rfl)
          | (right; right; right; right; rfl)
          | (exfalso; revert h1; decide)
    rcases hval with rfl | rfl | rfl | rfl | rfl
    · exact check13_21
    · exact check13_22
    · exact check13_23
    · exact check13_24
    · exact check13_25
  · rw [if_neg hg]

/-- **No nontrivial `cc`-cycle of length 13.** -/
theorem cc_no_nontrivial_thirteen_cycle
    (n : Nat) (hodd : Odd n) (hcyc : cc^[13] n = n)
    (hnt : ∃ j ∈ Finset.range 13, 1 < cc^[j] n) : False :=
  cc_no_nontrivial_cycle_of_excluded 13 (by norm_num) cycleExcludedB13 n hodd hcyc hnt

#print axioms cc_no_nontrivial_thirteen_cycle

end CollatzThirteenCycle
