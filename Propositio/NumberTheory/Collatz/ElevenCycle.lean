import Propositio.NumberTheory.Collatz.ElevenA
import Propositio.NumberTheory.Collatz.ElevenE
import Propositio.NumberTheory.Collatz.ElevenG

namespace CollatzElevenCycle
open CollatzCycleDecide (steinerVal compositions)
open CollatzCycleEnum (noStDvd noStDvd_top)
open CollatzCycleUniform (cycleExcludedB cc_no_nontrivial_cycle_of_excluded)
open TerrasDensity (cc)
local notation "Odd" => TerrasDensity.Odd
set_option maxRecDepth 100000

theorem cycleExcludedB11 : cycleExcludedB 11 = true := by
  rw [cycleExcludedB]
  apply List.all_eq_true.mpr
  intro A hA
  rw [List.mem_range] at hA
  by_cases hg : (3 : Nat) ^ 11 < 2 ^ A ∧ 2 ^ A < 4 ^ 11
  · rw [if_pos hg]
    have hval : A = 18 ∨ A = 19 ∨ A = 20 ∨ A = 21 := by
      obtain ⟨h1, h2⟩ := hg
      interval_cases A <;>
        first
          | (left; rfl) | (right; left; rfl) | (right; right; left; rfl)
          | (right; right; right; rfl)
          | (exfalso; revert h1; decide)
    rcases hval with rfl | rfl | rfl | rfl
    · exact check11_18
    · exact check11_19
    · exact check11_20
    · exact check11_21
  · rw [if_neg hg]

/-- **No nontrivial `cc`-cycle of length 11.** -/
theorem cc_no_nontrivial_eleven_cycle
    (n : Nat) (hodd : Odd n) (hcyc : cc^[11] n = n)
    (hnt : ∃ j ∈ Finset.range 11, 1 < cc^[j] n) : False :=
  cc_no_nontrivial_cycle_of_excluded 11 (by norm_num) cycleExcludedB11 n hodd hcyc hnt

#print axioms cc_no_nontrivial_eleven_cycle

end CollatzElevenCycle
