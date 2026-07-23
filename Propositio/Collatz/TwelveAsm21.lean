import Propositio.Collatz.CycleUniform
import Propositio.Collatz.CycleEnum
import Propositio.Collatz.TwelveL21_0
import Propositio.Collatz.TwelveL21_1
import Propositio.Collatz.TwelveL21_2
namespace CollatzTwelveCycle
open CollatzCycleDecide (steinerVal compositions)
open CollatzCycleEnum (noStDvd noStDvd_top)
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000000

theorem a21_0_0 : noStDvd (2 ^ 21 - 3 ^ 12) 10 19 5 2 = true := by
  rw [show (10 : Nat) = 9 + 1 from rfl, noStDvd]
  apply List.all_eq_true.mpr
  intro i hi
  rw [List.mem_range] at hi
  interval_cases i
  · exact b21_0_0_0
  · exact b21_0_0_1
  · exact b21_0_0_2
  · exact b21_0_0_3
  · exact b21_0_0_4
  · exact b21_0_0_5
  · exact b21_0_0_6
  · exact b21_0_0_7
  · exact b21_0_0_8
  · exact b21_0_0_9
  all_goals decide

theorem a21_0 : noStDvd (2 ^ 21 - 3 ^ 12) 11 20 1 1 = true := by
  rw [show (11 : Nat) = 10 + 1 from rfl, noStDvd]
  apply List.all_eq_true.mpr
  intro i hi
  rw [List.mem_range] at hi
  interval_cases i
  · exact a21_0_0
  · exact b21_0_1
  · exact b21_0_2
  · exact b21_0_3
  · exact b21_0_4
  · exact b21_0_5
  · exact b21_0_6
  · exact b21_0_7
  · exact b21_0_8
  · exact b21_0_9
  all_goals decide

theorem check12_21 : (compositions 12 21).all (fun as => !decide ((2 ^ 21 - 3 ^ 12) ∣ steinerVal as)) = true := by
  rw [← noStDvd_top, show (12 : Nat) = 11 + 1 from rfl, noStDvd]
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
  · exact b21_9
  all_goals decide

end CollatzTwelveCycle
