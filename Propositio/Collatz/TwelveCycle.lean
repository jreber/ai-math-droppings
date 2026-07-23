import Propositio.Collatz.TwelveAsm20
import Propositio.Collatz.TwelveAsm21
import Propositio.Collatz.TwelveAsm22
import Propositio.Collatz.TwelveAsm23
import Propositio.Collatz.CycleUniform

namespace CollatzTwelveCycle
open CollatzCycleDecide (steinerVal compositions)
open CollatzCycleEnum (noStDvd noStDvd_top)
open CollatzCycleUniform (cycleExcludedB cc_no_nontrivial_cycle_of_excluded)
open TerrasDensity (cc)
local notation "Odd" => TerrasDensity.Odd
set_option maxRecDepth 100000

theorem cycleExcludedB12 : cycleExcludedB 12 = true := by
  rw [cycleExcludedB]
  apply List.all_eq_true.mpr
  intro A hA
  rw [List.mem_range] at hA
  by_cases hg : (3 : Nat) ^ 12 < 2 ^ A ∧ 2 ^ A < 4 ^ 12
  · rw [if_pos hg]
    have hval : A = 20 ∨ A = 21 ∨ A = 22 ∨ A = 23 := by
      obtain ⟨h1, h2⟩ := hg
      interval_cases A <;>
        first
          | (left; rfl) | (right; left; rfl) | (right; right; left; rfl)
          | (right; right; right; rfl)
          | (exfalso; revert h1; decide)
    rcases hval with rfl | rfl | rfl | rfl
    · exact check12_20
    · exact check12_21
    · exact check12_22
    · exact check12_23
  · rw [if_neg hg]

/-- **No nontrivial `cc`-cycle of length 12.** -/
theorem cc_no_nontrivial_twelve_cycle
    (n : Nat) (hodd : Odd n) (hcyc : cc^[12] n = n)
    (hnt : ∃ j ∈ Finset.range 12, 1 < cc^[j] n) : False :=
  cc_no_nontrivial_cycle_of_excluded 12 (by norm_num) cycleExcludedB12 n hodd hcyc hnt

#print axioms cc_no_nontrivial_twelve_cycle

end CollatzTwelveCycle
