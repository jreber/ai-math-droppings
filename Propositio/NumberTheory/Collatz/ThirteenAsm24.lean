import Propositio.NumberTheory.Collatz.CycleUniform
import Propositio.NumberTheory.Collatz.CycleEnum
import Propositio.NumberTheory.Collatz.ThirteenL24_0
import Propositio.NumberTheory.Collatz.ThirteenL24_1
import Propositio.NumberTheory.Collatz.ThirteenL24_2
import Propositio.NumberTheory.Collatz.ThirteenL24_3
import Propositio.NumberTheory.Collatz.ThirteenL24_4
import Propositio.NumberTheory.Collatz.ThirteenL24_5
import Propositio.NumberTheory.Collatz.ThirteenL24_6
import Propositio.NumberTheory.Collatz.ThirteenL24_7
import Propositio.NumberTheory.Collatz.ThirteenL24_8
import Propositio.NumberTheory.Collatz.ThirteenL24_9
import Propositio.NumberTheory.Collatz.ThirteenL24_10
import Propositio.NumberTheory.Collatz.ThirteenL24_11
import Propositio.NumberTheory.Collatz.ThirteenL24_12
import Propositio.NumberTheory.Collatz.ThirteenL24_13
import Propositio.NumberTheory.Collatz.ThirteenL24_14
import Propositio.NumberTheory.Collatz.ThirteenL24_15
import Propositio.NumberTheory.Collatz.ThirteenL24_16
import Propositio.NumberTheory.Collatz.ThirteenL24_17
import Propositio.NumberTheory.Collatz.ThirteenL24_18
import Propositio.NumberTheory.Collatz.ThirteenL24_19
namespace CollatzThirteenCycle
open CollatzCycleDecide (steinerVal compositions)
open CollatzCycleEnum (noStDvd noStDvd_top)
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000000

theorem a24_0_0_0_0 : noStDvd (2 ^ 24 - 3 ^ 13) 9 20 65 4 = true := by
  rw [show (9 : Nat) = 8 + 1 from rfl, noStDvd]
  apply List.all_eq_true.mpr
  intro i hi
  rw [List.mem_range] at hi
  interval_cases i
  · exact b24_0_0_0_0_0
  · exact b24_0_0_0_0_1
  · exact b24_0_0_0_0_2
  · exact b24_0_0_0_0_3
  · exact b24_0_0_0_0_4
  · exact b24_0_0_0_0_5
  · exact b24_0_0_0_0_6
  · exact b24_0_0_0_0_7
  · exact b24_0_0_0_0_8
  · exact b24_0_0_0_0_9
  · exact b24_0_0_0_0_10
  · exact b24_0_0_0_0_11
  all_goals decide

theorem a24_0_0_0 : noStDvd (2 ^ 24 - 3 ^ 13) 10 21 19 3 = true := by
  rw [show (10 : Nat) = 9 + 1 from rfl, noStDvd]
  apply List.all_eq_true.mpr
  intro i hi
  rw [List.mem_range] at hi
  interval_cases i
  · exact a24_0_0_0_0
  · exact b24_0_0_0_1
  · exact b24_0_0_0_2
  · exact b24_0_0_0_3
  · exact b24_0_0_0_4
  · exact b24_0_0_0_5
  · exact b24_0_0_0_6
  · exact b24_0_0_0_7
  · exact b24_0_0_0_8
  · exact b24_0_0_0_9
  · exact b24_0_0_0_10
  · exact b24_0_0_0_11
  all_goals decide

theorem a24_0_0_1 : noStDvd (2 ^ 24 - 3 ^ 13) 10 20 19 4 = true := by
  rw [show (10 : Nat) = 9 + 1 from rfl, noStDvd]
  apply List.all_eq_true.mpr
  intro i hi
  rw [List.mem_range] at hi
  interval_cases i
  · exact b24_0_0_1_0
  · exact b24_0_0_1_1
  · exact b24_0_0_1_2
  · exact b24_0_0_1_3
  · exact b24_0_0_1_4
  · exact b24_0_0_1_5
  · exact b24_0_0_1_6
  · exact b24_0_0_1_7
  · exact b24_0_0_1_8
  · exact b24_0_0_1_9
  · exact b24_0_0_1_10
  all_goals decide

theorem a24_0_0_2 : noStDvd (2 ^ 24 - 3 ^ 13) 10 19 19 5 = true := by
  rw [show (10 : Nat) = 9 + 1 from rfl, noStDvd]
  apply List.all_eq_true.mpr
  intro i hi
  rw [List.mem_range] at hi
  interval_cases i
  · exact b24_0_0_2_0
  · exact b24_0_0_2_1
  · exact b24_0_0_2_2
  · exact b24_0_0_2_3
  · exact b24_0_0_2_4
  · exact b24_0_0_2_5
  · exact b24_0_0_2_6
  · exact b24_0_0_2_7
  · exact b24_0_0_2_8
  · exact b24_0_0_2_9
  all_goals decide

theorem a24_0_0 : noStDvd (2 ^ 24 - 3 ^ 13) 11 22 5 2 = true := by
  rw [show (11 : Nat) = 10 + 1 from rfl, noStDvd]
  apply List.all_eq_true.mpr
  intro i hi
  rw [List.mem_range] at hi
  interval_cases i
  · exact a24_0_0_0
  · exact a24_0_0_1
  · exact a24_0_0_2
  · exact b24_0_0_3
  · exact b24_0_0_4
  · exact b24_0_0_5
  · exact b24_0_0_6
  · exact b24_0_0_7
  · exact b24_0_0_8
  · exact b24_0_0_9
  · exact b24_0_0_10
  · exact b24_0_0_11
  all_goals decide

theorem a24_0_1_0 : noStDvd (2 ^ 24 - 3 ^ 13) 10 20 23 4 = true := by
  rw [show (10 : Nat) = 9 + 1 from rfl, noStDvd]
  apply List.all_eq_true.mpr
  intro i hi
  rw [List.mem_range] at hi
  interval_cases i
  · exact b24_0_1_0_0
  · exact b24_0_1_0_1
  · exact b24_0_1_0_2
  · exact b24_0_1_0_3
  · exact b24_0_1_0_4
  · exact b24_0_1_0_5
  · exact b24_0_1_0_6
  · exact b24_0_1_0_7
  · exact b24_0_1_0_8
  · exact b24_0_1_0_9
  · exact b24_0_1_0_10
  all_goals decide

theorem a24_0_1_1 : noStDvd (2 ^ 24 - 3 ^ 13) 10 19 23 5 = true := by
  rw [show (10 : Nat) = 9 + 1 from rfl, noStDvd]
  apply List.all_eq_true.mpr
  intro i hi
  rw [List.mem_range] at hi
  interval_cases i
  · exact b24_0_1_1_0
  · exact b24_0_1_1_1
  · exact b24_0_1_1_2
  · exact b24_0_1_1_3
  · exact b24_0_1_1_4
  · exact b24_0_1_1_5
  · exact b24_0_1_1_6
  · exact b24_0_1_1_7
  · exact b24_0_1_1_8
  · exact b24_0_1_1_9
  all_goals decide

theorem a24_0_1 : noStDvd (2 ^ 24 - 3 ^ 13) 11 21 5 3 = true := by
  rw [show (11 : Nat) = 10 + 1 from rfl, noStDvd]
  apply List.all_eq_true.mpr
  intro i hi
  rw [List.mem_range] at hi
  interval_cases i
  · exact a24_0_1_0
  · exact a24_0_1_1
  · exact b24_0_1_2
  · exact b24_0_1_3
  · exact b24_0_1_4
  · exact b24_0_1_5
  · exact b24_0_1_6
  · exact b24_0_1_7
  · exact b24_0_1_8
  · exact b24_0_1_9
  · exact b24_0_1_10
  all_goals decide

theorem a24_0_2_0 : noStDvd (2 ^ 24 - 3 ^ 13) 10 19 31 5 = true := by
  rw [show (10 : Nat) = 9 + 1 from rfl, noStDvd]
  apply List.all_eq_true.mpr
  intro i hi
  rw [List.mem_range] at hi
  interval_cases i
  · exact b24_0_2_0_0
  · exact b24_0_2_0_1
  · exact b24_0_2_0_2
  · exact b24_0_2_0_3
  · exact b24_0_2_0_4
  · exact b24_0_2_0_5
  · exact b24_0_2_0_6
  · exact b24_0_2_0_7
  · exact b24_0_2_0_8
  · exact b24_0_2_0_9
  all_goals decide

theorem a24_0_2 : noStDvd (2 ^ 24 - 3 ^ 13) 11 20 5 4 = true := by
  rw [show (11 : Nat) = 10 + 1 from rfl, noStDvd]
  apply List.all_eq_true.mpr
  intro i hi
  rw [List.mem_range] at hi
  interval_cases i
  · exact a24_0_2_0
  · exact b24_0_2_1
  · exact b24_0_2_2
  · exact b24_0_2_3
  · exact b24_0_2_4
  · exact b24_0_2_5
  · exact b24_0_2_6
  · exact b24_0_2_7
  · exact b24_0_2_8
  · exact b24_0_2_9
  all_goals decide

theorem a24_0 : noStDvd (2 ^ 24 - 3 ^ 13) 12 23 1 1 = true := by
  rw [show (12 : Nat) = 11 + 1 from rfl, noStDvd]
  apply List.all_eq_true.mpr
  intro i hi
  rw [List.mem_range] at hi
  interval_cases i
  · exact a24_0_0
  · exact a24_0_1
  · exact a24_0_2
  · exact b24_0_3
  · exact b24_0_4
  · exact b24_0_5
  · exact b24_0_6
  · exact b24_0_7
  · exact b24_0_8
  · exact b24_0_9
  · exact b24_0_10
  · exact b24_0_11
  all_goals decide

theorem a24_1_0_0 : noStDvd (2 ^ 24 - 3 ^ 13) 10 20 29 4 = true := by
  rw [show (10 : Nat) = 9 + 1 from rfl, noStDvd]
  apply List.all_eq_true.mpr
  intro i hi
  rw [List.mem_range] at hi
  interval_cases i
  · exact b24_1_0_0_0
  · exact b24_1_0_0_1
  · exact b24_1_0_0_2
  · exact b24_1_0_0_3
  · exact b24_1_0_0_4
  · exact b24_1_0_0_5
  · exact b24_1_0_0_6
  · exact b24_1_0_0_7
  · exact b24_1_0_0_8
  · exact b24_1_0_0_9
  · exact b24_1_0_0_10
  all_goals decide

theorem a24_1_0_1 : noStDvd (2 ^ 24 - 3 ^ 13) 10 19 29 5 = true := by
  rw [show (10 : Nat) = 9 + 1 from rfl, noStDvd]
  apply List.all_eq_true.mpr
  intro i hi
  rw [List.mem_range] at hi
  interval_cases i
  · exact b24_1_0_1_0
  · exact b24_1_0_1_1
  · exact b24_1_0_1_2
  · exact b24_1_0_1_3
  · exact b24_1_0_1_4
  · exact b24_1_0_1_5
  · exact b24_1_0_1_6
  · exact b24_1_0_1_7
  · exact b24_1_0_1_8
  · exact b24_1_0_1_9
  all_goals decide

theorem a24_1_0 : noStDvd (2 ^ 24 - 3 ^ 13) 11 21 7 3 = true := by
  rw [show (11 : Nat) = 10 + 1 from rfl, noStDvd]
  apply List.all_eq_true.mpr
  intro i hi
  rw [List.mem_range] at hi
  interval_cases i
  · exact a24_1_0_0
  · exact a24_1_0_1
  · exact b24_1_0_2
  · exact b24_1_0_3
  · exact b24_1_0_4
  · exact b24_1_0_5
  · exact b24_1_0_6
  · exact b24_1_0_7
  · exact b24_1_0_8
  · exact b24_1_0_9
  · exact b24_1_0_10
  all_goals decide

theorem a24_1_1_0 : noStDvd (2 ^ 24 - 3 ^ 13) 10 19 37 5 = true := by
  rw [show (10 : Nat) = 9 + 1 from rfl, noStDvd]
  apply List.all_eq_true.mpr
  intro i hi
  rw [List.mem_range] at hi
  interval_cases i
  · exact b24_1_1_0_0
  · exact b24_1_1_0_1
  · exact b24_1_1_0_2
  · exact b24_1_1_0_3
  · exact b24_1_1_0_4
  · exact b24_1_1_0_5
  · exact b24_1_1_0_6
  · exact b24_1_1_0_7
  · exact b24_1_1_0_8
  · exact b24_1_1_0_9
  all_goals decide

theorem a24_1_1 : noStDvd (2 ^ 24 - 3 ^ 13) 11 20 7 4 = true := by
  rw [show (11 : Nat) = 10 + 1 from rfl, noStDvd]
  apply List.all_eq_true.mpr
  intro i hi
  rw [List.mem_range] at hi
  interval_cases i
  · exact a24_1_1_0
  · exact b24_1_1_1
  · exact b24_1_1_2
  · exact b24_1_1_3
  · exact b24_1_1_4
  · exact b24_1_1_5
  · exact b24_1_1_6
  · exact b24_1_1_7
  · exact b24_1_1_8
  · exact b24_1_1_9
  all_goals decide

theorem a24_1 : noStDvd (2 ^ 24 - 3 ^ 13) 12 22 1 2 = true := by
  rw [show (12 : Nat) = 11 + 1 from rfl, noStDvd]
  apply List.all_eq_true.mpr
  intro i hi
  rw [List.mem_range] at hi
  interval_cases i
  · exact a24_1_0
  · exact a24_1_1
  · exact b24_1_2
  · exact b24_1_3
  · exact b24_1_4
  · exact b24_1_5
  · exact b24_1_6
  · exact b24_1_7
  · exact b24_1_8
  · exact b24_1_9
  · exact b24_1_10
  all_goals decide

theorem a24_2_0_0 : noStDvd (2 ^ 24 - 3 ^ 13) 10 19 49 5 = true := by
  rw [show (10 : Nat) = 9 + 1 from rfl, noStDvd]
  apply List.all_eq_true.mpr
  intro i hi
  rw [List.mem_range] at hi
  interval_cases i
  · exact b24_2_0_0_0
  · exact b24_2_0_0_1
  · exact b24_2_0_0_2
  · exact b24_2_0_0_3
  · exact b24_2_0_0_4
  · exact b24_2_0_0_5
  · exact b24_2_0_0_6
  · exact b24_2_0_0_7
  · exact b24_2_0_0_8
  · exact b24_2_0_0_9
  all_goals decide

theorem a24_2_0 : noStDvd (2 ^ 24 - 3 ^ 13) 11 20 11 4 = true := by
  rw [show (11 : Nat) = 10 + 1 from rfl, noStDvd]
  apply List.all_eq_true.mpr
  intro i hi
  rw [List.mem_range] at hi
  interval_cases i
  · exact a24_2_0_0
  · exact b24_2_0_1
  · exact b24_2_0_2
  · exact b24_2_0_3
  · exact b24_2_0_4
  · exact b24_2_0_5
  · exact b24_2_0_6
  · exact b24_2_0_7
  · exact b24_2_0_8
  · exact b24_2_0_9
  all_goals decide

theorem a24_2 : noStDvd (2 ^ 24 - 3 ^ 13) 12 21 1 3 = true := by
  rw [show (12 : Nat) = 11 + 1 from rfl, noStDvd]
  apply List.all_eq_true.mpr
  intro i hi
  rw [List.mem_range] at hi
  interval_cases i
  · exact a24_2_0
  · exact b24_2_1
  · exact b24_2_2
  · exact b24_2_3
  · exact b24_2_4
  · exact b24_2_5
  · exact b24_2_6
  · exact b24_2_7
  · exact b24_2_8
  · exact b24_2_9
  all_goals decide

theorem a24_3 : noStDvd (2 ^ 24 - 3 ^ 13) 12 20 1 4 = true := by
  rw [show (12 : Nat) = 11 + 1 from rfl, noStDvd]
  apply List.all_eq_true.mpr
  intro i hi
  rw [List.mem_range] at hi
  interval_cases i
  · exact b24_3_0
  · exact b24_3_1
  · exact b24_3_2
  · exact b24_3_3
  · exact b24_3_4
  · exact b24_3_5
  · exact b24_3_6
  · exact b24_3_7
  · exact b24_3_8
  all_goals decide

theorem check13_24 : (compositions 13 24).all (fun as => !decide ((2 ^ 24 - 3 ^ 13) ∣ steinerVal as)) = true := by
  rw [← noStDvd_top, show (13 : Nat) = 12 + 1 from rfl, noStDvd]
  apply List.all_eq_true.mpr
  intro i hi
  rw [List.mem_range] at hi
  interval_cases i
  · exact a24_0
  · exact a24_1
  · exact a24_2
  · exact a24_3
  · exact b24_4
  · exact b24_5
  · exact b24_6
  · exact b24_7
  · exact b24_8
  · exact b24_9
  · exact b24_10
  · exact b24_11
  all_goals decide

end CollatzThirteenCycle
