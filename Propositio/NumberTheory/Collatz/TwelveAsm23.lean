import Propositio.NumberTheory.Collatz.CycleUniform
import Propositio.NumberTheory.Collatz.CycleEnum
import Propositio.NumberTheory.Collatz.TwelveL23_0
import Propositio.NumberTheory.Collatz.TwelveL23_1
import Propositio.NumberTheory.Collatz.TwelveL23_2
import Propositio.NumberTheory.Collatz.TwelveL23_3
import Propositio.NumberTheory.Collatz.TwelveL23_4
import Propositio.NumberTheory.Collatz.TwelveL23_5
import Propositio.NumberTheory.Collatz.TwelveL23_6
import Propositio.NumberTheory.Collatz.TwelveL23_7
import Propositio.NumberTheory.Collatz.TwelveL23_8
import Propositio.NumberTheory.Collatz.TwelveL23_9
namespace CollatzTwelveCycle
open CollatzCycleDecide (steinerVal compositions)
open CollatzCycleEnum (noStDvd noStDvd_top)
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000000

theorem a23_0_0_0 : noStDvd (2 ^ 23 - 3 ^ 12) 9 20 19 3 = true := by
  rw [show (9 : Nat) = 8 + 1 from rfl, noStDvd]
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
  · exact b23_0_0_0_11
  all_goals decide

theorem a23_0_0 : noStDvd (2 ^ 23 - 3 ^ 12) 10 21 5 2 = true := by
  rw [show (10 : Nat) = 9 + 1 from rfl, noStDvd]
  apply List.all_eq_true.mpr
  intro i hi
  rw [List.mem_range] at hi
  interval_cases i
  · exact a23_0_0_0
  · exact b23_0_0_1
  · exact b23_0_0_2
  · exact b23_0_0_3
  · exact b23_0_0_4
  · exact b23_0_0_5
  · exact b23_0_0_6
  · exact b23_0_0_7
  · exact b23_0_0_8
  · exact b23_0_0_9
  · exact b23_0_0_10
  · exact b23_0_0_11
  all_goals decide

theorem a23_0_1 : noStDvd (2 ^ 23 - 3 ^ 12) 10 20 5 3 = true := by
  rw [show (10 : Nat) = 9 + 1 from rfl, noStDvd]
  apply List.all_eq_true.mpr
  intro i hi
  rw [List.mem_range] at hi
  interval_cases i
  · exact b23_0_1_0
  · exact b23_0_1_1
  · exact b23_0_1_2
  · exact b23_0_1_3
  · exact b23_0_1_4
  · exact b23_0_1_5
  · exact b23_0_1_6
  · exact b23_0_1_7
  · exact b23_0_1_8
  · exact b23_0_1_9
  · exact b23_0_1_10
  all_goals decide

theorem a23_0_2 : noStDvd (2 ^ 23 - 3 ^ 12) 10 19 5 4 = true := by
  rw [show (10 : Nat) = 9 + 1 from rfl, noStDvd]
  apply List.all_eq_true.mpr
  intro i hi
  rw [List.mem_range] at hi
  interval_cases i
  · exact b23_0_2_0
  · exact b23_0_2_1
  · exact b23_0_2_2
  · exact b23_0_2_3
  · exact b23_0_2_4
  · exact b23_0_2_5
  · exact b23_0_2_6
  · exact b23_0_2_7
  · exact b23_0_2_8
  · exact b23_0_2_9
  all_goals decide

theorem a23_0 : noStDvd (2 ^ 23 - 3 ^ 12) 11 22 1 1 = true := by
  rw [show (11 : Nat) = 10 + 1 from rfl, noStDvd]
  apply List.all_eq_true.mpr
  intro i hi
  rw [List.mem_range] at hi
  interval_cases i
  · exact a23_0_0
  · exact a23_0_1
  · exact a23_0_2
  · exact b23_0_3
  · exact b23_0_4
  · exact b23_0_5
  · exact b23_0_6
  · exact b23_0_7
  · exact b23_0_8
  · exact b23_0_9
  · exact b23_0_10
  · exact b23_0_11
  all_goals decide

theorem a23_1_0 : noStDvd (2 ^ 23 - 3 ^ 12) 10 20 7 3 = true := by
  rw [show (10 : Nat) = 9 + 1 from rfl, noStDvd]
  apply List.all_eq_true.mpr
  intro i hi
  rw [List.mem_range] at hi
  interval_cases i
  · exact b23_1_0_0
  · exact b23_1_0_1
  · exact b23_1_0_2
  · exact b23_1_0_3
  · exact b23_1_0_4
  · exact b23_1_0_5
  · exact b23_1_0_6
  · exact b23_1_0_7
  · exact b23_1_0_8
  · exact b23_1_0_9
  · exact b23_1_0_10
  all_goals decide

theorem a23_1_1 : noStDvd (2 ^ 23 - 3 ^ 12) 10 19 7 4 = true := by
  rw [show (10 : Nat) = 9 + 1 from rfl, noStDvd]
  apply List.all_eq_true.mpr
  intro i hi
  rw [List.mem_range] at hi
  interval_cases i
  · exact b23_1_1_0
  · exact b23_1_1_1
  · exact b23_1_1_2
  · exact b23_1_1_3
  · exact b23_1_1_4
  · exact b23_1_1_5
  · exact b23_1_1_6
  · exact b23_1_1_7
  · exact b23_1_1_8
  · exact b23_1_1_9
  all_goals decide

theorem a23_1 : noStDvd (2 ^ 23 - 3 ^ 12) 11 21 1 2 = true := by
  rw [show (11 : Nat) = 10 + 1 from rfl, noStDvd]
  apply List.all_eq_true.mpr
  intro i hi
  rw [List.mem_range] at hi
  interval_cases i
  · exact a23_1_0
  · exact a23_1_1
  · exact b23_1_2
  · exact b23_1_3
  · exact b23_1_4
  · exact b23_1_5
  · exact b23_1_6
  · exact b23_1_7
  · exact b23_1_8
  · exact b23_1_9
  · exact b23_1_10
  all_goals decide

theorem a23_2_0 : noStDvd (2 ^ 23 - 3 ^ 12) 10 19 11 4 = true := by
  rw [show (10 : Nat) = 9 + 1 from rfl, noStDvd]
  apply List.all_eq_true.mpr
  intro i hi
  rw [List.mem_range] at hi
  interval_cases i
  · exact b23_2_0_0
  · exact b23_2_0_1
  · exact b23_2_0_2
  · exact b23_2_0_3
  · exact b23_2_0_4
  · exact b23_2_0_5
  · exact b23_2_0_6
  · exact b23_2_0_7
  · exact b23_2_0_8
  · exact b23_2_0_9
  all_goals decide

theorem a23_2 : noStDvd (2 ^ 23 - 3 ^ 12) 11 20 1 3 = true := by
  rw [show (11 : Nat) = 10 + 1 from rfl, noStDvd]
  apply List.all_eq_true.mpr
  intro i hi
  rw [List.mem_range] at hi
  interval_cases i
  · exact a23_2_0
  · exact b23_2_1
  · exact b23_2_2
  · exact b23_2_3
  · exact b23_2_4
  · exact b23_2_5
  · exact b23_2_6
  · exact b23_2_7
  · exact b23_2_8
  · exact b23_2_9
  all_goals decide

theorem check12_23 : (compositions 12 23).all (fun as => !decide ((2 ^ 23 - 3 ^ 12) ∣ steinerVal as)) = true := by
  rw [← noStDvd_top, show (12 : Nat) = 11 + 1 from rfl, noStDvd]
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
  · exact b23_11
  all_goals decide

end CollatzTwelveCycle
