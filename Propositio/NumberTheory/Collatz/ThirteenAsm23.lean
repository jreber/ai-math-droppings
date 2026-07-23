import Propositio.NumberTheory.Collatz.CycleUniform
import Propositio.NumberTheory.Collatz.CycleEnum
import Propositio.NumberTheory.Collatz.ThirteenL23_0
import Propositio.NumberTheory.Collatz.ThirteenL23_1
import Propositio.NumberTheory.Collatz.ThirteenL23_2
import Propositio.NumberTheory.Collatz.ThirteenL23_3
import Propositio.NumberTheory.Collatz.ThirteenL23_4
import Propositio.NumberTheory.Collatz.ThirteenL23_5
import Propositio.NumberTheory.Collatz.ThirteenL23_6
import Propositio.NumberTheory.Collatz.ThirteenL23_7
import Propositio.NumberTheory.Collatz.ThirteenL23_8
import Propositio.NumberTheory.Collatz.ThirteenL23_9
namespace CollatzThirteenCycle
open CollatzCycleDecide (steinerVal compositions)
open CollatzCycleEnum (noStDvd noStDvd_top)
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000000

theorem a23_0_0_0 : noStDvd (2 ^ 23 - 3 ^ 13) 10 20 19 3 = true := by
  rw [show (10 : Nat) = 9 + 1 from rfl, noStDvd]
  apply List.all_eq_true.mpr
  intro i hi
  rw [List.mem_range] at hi
  interval_cases i
  · exact b23_0_0_0_0
  · exact b23_0_0_0_1
  · exact b23_0_0_0_2
  · exact b23_0_0_0_3
  · exact b23_0_0_0_4
  · exact b23_0_0_0_5
  · exact b23_0_0_0_6
  · exact b23_0_0_0_7
  · exact b23_0_0_0_8
  · exact b23_0_0_0_9
  · exact b23_0_0_0_10
  all_goals decide

theorem a23_0_0_1 : noStDvd (2 ^ 23 - 3 ^ 13) 10 19 19 4 = true := by
  rw [show (10 : Nat) = 9 + 1 from rfl, noStDvd]
  apply List.all_eq_true.mpr
  intro i hi
  rw [List.mem_range] at hi
  interval_cases i
  · exact b23_0_0_1_0
  · exact b23_0_0_1_1
  · exact b23_0_0_1_2
  · exact b23_0_0_1_3
  · exact b23_0_0_1_4
  · exact b23_0_0_1_5
  · exact b23_0_0_1_6
  · exact b23_0_0_1_7
  · exact b23_0_0_1_8
  · exact b23_0_0_1_9
  all_goals decide

theorem a23_0_0 : noStDvd (2 ^ 23 - 3 ^ 13) 11 21 5 2 = true := by
  rw [show (11 : Nat) = 10 + 1 from rfl, noStDvd]
  apply List.all_eq_true.mpr
  intro i hi
  rw [List.mem_range] at hi
  interval_cases i
  · exact a23_0_0_0
  · exact a23_0_0_1
  · exact b23_0_0_2
  · exact b23_0_0_3
  · exact b23_0_0_4
  · exact b23_0_0_5
  · exact b23_0_0_6
  · exact b23_0_0_7
  · exact b23_0_0_8
  · exact b23_0_0_9
  · exact b23_0_0_10
  all_goals decide

theorem a23_0_1_0 : noStDvd (2 ^ 23 - 3 ^ 13) 10 19 23 4 = true := by
  rw [show (10 : Nat) = 9 + 1 from rfl, noStDvd]
  apply List.all_eq_true.mpr
  intro i hi
  rw [List.mem_range] at hi
  interval_cases i
  · exact b23_0_1_0_0
  · exact b23_0_1_0_1
  · exact b23_0_1_0_2
  · exact b23_0_1_0_3
  · exact b23_0_1_0_4
  · exact b23_0_1_0_5
  · exact b23_0_1_0_6
  · exact b23_0_1_0_7
  · exact b23_0_1_0_8
  · exact b23_0_1_0_9
  all_goals decide

theorem a23_0_1 : noStDvd (2 ^ 23 - 3 ^ 13) 11 20 5 3 = true := by
  rw [show (11 : Nat) = 10 + 1 from rfl, noStDvd]
  apply List.all_eq_true.mpr
  intro i hi
  rw [List.mem_range] at hi
  interval_cases i
  · exact a23_0_1_0
  · exact b23_0_1_1
  · exact b23_0_1_2
  · exact b23_0_1_3
  · exact b23_0_1_4
  · exact b23_0_1_5
  · exact b23_0_1_6
  · exact b23_0_1_7
  · exact b23_0_1_8
  · exact b23_0_1_9
  all_goals decide

theorem a23_0 : noStDvd (2 ^ 23 - 3 ^ 13) 12 22 1 1 = true := by
  rw [show (12 : Nat) = 11 + 1 from rfl, noStDvd]
  apply List.all_eq_true.mpr
  intro i hi
  rw [List.mem_range] at hi
  interval_cases i
  · exact a23_0_0
  · exact a23_0_1
  · exact b23_0_2
  · exact b23_0_3
  · exact b23_0_4
  · exact b23_0_5
  · exact b23_0_6
  · exact b23_0_7
  · exact b23_0_8
  · exact b23_0_9
  · exact b23_0_10
  all_goals decide

theorem a23_1_0_0 : noStDvd (2 ^ 23 - 3 ^ 13) 10 19 29 4 = true := by
  rw [show (10 : Nat) = 9 + 1 from rfl, noStDvd]
  apply List.all_eq_true.mpr
  intro i hi
  rw [List.mem_range] at hi
  interval_cases i
  · exact b23_1_0_0_0
  · exact b23_1_0_0_1
  · exact b23_1_0_0_2
  · exact b23_1_0_0_3
  · exact b23_1_0_0_4
  · exact b23_1_0_0_5
  · exact b23_1_0_0_6
  · exact b23_1_0_0_7
  · exact b23_1_0_0_8
  · exact b23_1_0_0_9
  all_goals decide

theorem a23_1_0 : noStDvd (2 ^ 23 - 3 ^ 13) 11 20 7 3 = true := by
  rw [show (11 : Nat) = 10 + 1 from rfl, noStDvd]
  apply List.all_eq_true.mpr
  intro i hi
  rw [List.mem_range] at hi
  interval_cases i
  · exact a23_1_0_0
  · exact b23_1_0_1
  · exact b23_1_0_2
  · exact b23_1_0_3
  · exact b23_1_0_4
  · exact b23_1_0_5
  · exact b23_1_0_6
  · exact b23_1_0_7
  · exact b23_1_0_8
  · exact b23_1_0_9
  all_goals decide

theorem a23_1 : noStDvd (2 ^ 23 - 3 ^ 13) 12 21 1 2 = true := by
  rw [show (12 : Nat) = 11 + 1 from rfl, noStDvd]
  apply List.all_eq_true.mpr
  intro i hi
  rw [List.mem_range] at hi
  interval_cases i
  · exact a23_1_0
  · exact b23_1_1
  · exact b23_1_2
  · exact b23_1_3
  · exact b23_1_4
  · exact b23_1_5
  · exact b23_1_6
  · exact b23_1_7
  · exact b23_1_8
  · exact b23_1_9
  all_goals decide

theorem a23_2 : noStDvd (2 ^ 23 - 3 ^ 13) 12 20 1 3 = true := by
  rw [show (12 : Nat) = 11 + 1 from rfl, noStDvd]
  apply List.all_eq_true.mpr
  intro i hi
  rw [List.mem_range] at hi
  interval_cases i
  · exact b23_2_0
  · exact b23_2_1
  · exact b23_2_2
  · exact b23_2_3
  · exact b23_2_4
  · exact b23_2_5
  · exact b23_2_6
  · exact b23_2_7
  · exact b23_2_8
  all_goals decide

theorem check13_23 : (compositions 13 23).all (fun as => !decide ((2 ^ 23 - 3 ^ 13) ∣ steinerVal as)) = true := by
  rw [← noStDvd_top, show (13 : Nat) = 12 + 1 from rfl, noStDvd]
  apply List.all_eq_true.mpr
  intro i hi
  rw [List.mem_range] at hi
  interval_cases i
  · exact a23_0
  · exact a23_1
  · exact a23_2
  · exact b23_3
  · exact b23_4
  · exact b23_5
  · exact b23_6
  · exact b23_7
  · exact b23_8
  · exact b23_9
  · exact b23_10
  all_goals decide

end CollatzThirteenCycle
