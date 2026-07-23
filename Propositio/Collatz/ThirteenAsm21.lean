import Propositio.Collatz.CycleUniform
import Propositio.Collatz.CycleEnum
import Propositio.Collatz.ThirteenL21_0
import Propositio.Collatz.ThirteenL21_1
namespace CollatzThirteenCycle
open CollatzCycleDecide (steinerVal compositions)
open CollatzCycleEnum (noStDvd noStDvd_top)
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000000

theorem a21_0 : noStDvd (2 ^ 21 - 3 ^ 13) 12 20 1 1 = true := by
  rw [show (12 : Nat) = 11 + 1 from rfl, noStDvd]
  apply List.all_eq_true.mpr
  intro i hi
  rw [List.mem_range] at hi
  interval_cases i
  · exact b21_0_0
  · exact b21_0_1
  · exact b21_0_2
  · exact b21_0_3
  · exact b21_0_4
  · exact b21_0_5
  · exact b21_0_6
  · exact b21_0_7
  · exact b21_0_8
  all_goals decide

theorem check13_21 : (compositions 13 21).all (fun as => !decide ((2 ^ 21 - 3 ^ 13) ∣ steinerVal as)) = true := by
  rw [← noStDvd_top, show (13 : Nat) = 12 + 1 from rfl, noStDvd]
  apply List.all_eq_true.mpr
  intro i hi
  rw [List.mem_range] at hi
  interval_cases i
  · exact a21_0
  · exact b21_1
  · exact b21_2
  · exact b21_3
  · exact b21_4
  · exact b21_5
  · exact b21_6
  · exact b21_7
  · exact b21_8
  all_goals decide

end CollatzThirteenCycle
