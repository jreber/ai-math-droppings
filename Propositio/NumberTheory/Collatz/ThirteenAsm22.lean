import Propositio.NumberTheory.Collatz.CycleUniform
import Propositio.NumberTheory.Collatz.CycleEnum
import Propositio.NumberTheory.Collatz.ThirteenL22_0
import Propositio.NumberTheory.Collatz.ThirteenL22_1
import Propositio.NumberTheory.Collatz.ThirteenL22_2
import Propositio.NumberTheory.Collatz.ThirteenL22_3
import Propositio.NumberTheory.Collatz.ThirteenL22_4
namespace CollatzThirteenCycle
open CollatzCycleDecide (steinerVal compositions)
open CollatzCycleEnum (noStDvd noStDvd_top)
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000000

theorem a22_0_0_0 : noStDvd (2 ^ 22 - 3 ^ 13) 10 19 19 3 = true := by
  rw [show (10 : Nat) = 9 + 1 from rfl, noStDvd]
  apply List.all_eq_true.mpr
  intro i hi
  rw [List.mem_range] at hi
  interval_cases i
  · exact b22_0_0_0_0
  · exact b22_0_0_0_1
  · exact b22_0_0_0_2
  · exact b22_0_0_0_3
  · exact b22_0_0_0_4
  · exact b22_0_0_0_5
  · exact b22_0_0_0_6
  · exact b22_0_0_0_7
  · exact b22_0_0_0_8
  · exact b22_0_0_0_9
  all_goals decide

theorem a22_0_0 : noStDvd (2 ^ 22 - 3 ^ 13) 11 20 5 2 = true := by
  rw [show (11 : Nat) = 10 + 1 from rfl, noStDvd]
  apply List.all_eq_true.mpr
  intro i hi
  rw [List.mem_range] at hi
  interval_cases i
  · exact a22_0_0_0
  · exact b22_0_0_1
  · exact b22_0_0_2
  · exact b22_0_0_3
  · exact b22_0_0_4
  · exact b22_0_0_5
  · exact b22_0_0_6
  · exact b22_0_0_7
  · exact b22_0_0_8
  · exact b22_0_0_9
  all_goals decide

theorem a22_0 : noStDvd (2 ^ 22 - 3 ^ 13) 12 21 1 1 = true := by
  rw [show (12 : Nat) = 11 + 1 from rfl, noStDvd]
  apply List.all_eq_true.mpr
  intro i hi
  rw [List.mem_range] at hi
  interval_cases i
  · exact a22_0_0
  · exact b22_0_1
  · exact b22_0_2
  · exact b22_0_3
  · exact b22_0_4
  · exact b22_0_5
  · exact b22_0_6
  · exact b22_0_7
  · exact b22_0_8
  · exact b22_0_9
  all_goals decide

theorem a22_1 : noStDvd (2 ^ 22 - 3 ^ 13) 12 20 1 2 = true := by
  rw [show (12 : Nat) = 11 + 1 from rfl, noStDvd]
  apply List.all_eq_true.mpr
  intro i hi
  rw [List.mem_range] at hi
  interval_cases i
  · exact b22_1_0
  · exact b22_1_1
  · exact b22_1_2
  · exact b22_1_3
  · exact b22_1_4
  · exact b22_1_5
  · exact b22_1_6
  · exact b22_1_7
  · exact b22_1_8
  all_goals decide

theorem check13_22 : (compositions 13 22).all (fun as => !decide ((2 ^ 22 - 3 ^ 13) ∣ steinerVal as)) = true := by
  rw [← noStDvd_top, show (13 : Nat) = 12 + 1 from rfl, noStDvd]
  apply List.all_eq_true.mpr
  intro i hi
  rw [List.mem_range] at hi
  interval_cases i
  · exact a22_0
  · exact a22_1
  · exact b22_2
  · exact b22_3
  · exact b22_4
  · exact b22_5
  · exact b22_6
  · exact b22_7
  · exact b22_8
  · exact b22_9
  all_goals decide

end CollatzThirteenCycle
