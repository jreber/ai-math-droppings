import Propositio.Collatz.CycleUniform
import Propositio.Collatz.CycleEnum
import Propositio.Collatz.ThirteenL25_0
import Propositio.Collatz.ThirteenL25_1
import Propositio.Collatz.ThirteenL25_2
import Propositio.Collatz.ThirteenL25_3
import Propositio.Collatz.ThirteenL25_4
import Propositio.Collatz.ThirteenL25_5
import Propositio.Collatz.ThirteenL25_6
import Propositio.Collatz.ThirteenL25_7
import Propositio.Collatz.ThirteenL25_8
import Propositio.Collatz.ThirteenL25_9
import Propositio.Collatz.ThirteenL25_10
import Propositio.Collatz.ThirteenL25_11
import Propositio.Collatz.ThirteenL25_12
import Propositio.Collatz.ThirteenL25_13
import Propositio.Collatz.ThirteenL25_14
import Propositio.Collatz.ThirteenL25_15
import Propositio.Collatz.ThirteenL25_16
import Propositio.Collatz.ThirteenL25_17
import Propositio.Collatz.ThirteenL25_18
import Propositio.Collatz.ThirteenL25_19
import Propositio.Collatz.ThirteenL25_20
import Propositio.Collatz.ThirteenL25_21
import Propositio.Collatz.ThirteenL25_22
import Propositio.Collatz.ThirteenL25_23
import Propositio.Collatz.ThirteenL25_24
import Propositio.Collatz.ThirteenL25_25
import Propositio.Collatz.ThirteenL25_26
import Propositio.Collatz.ThirteenL25_27
import Propositio.Collatz.ThirteenL25_28
import Propositio.Collatz.ThirteenL25_29
import Propositio.Collatz.ThirteenL25_30
import Propositio.Collatz.ThirteenL25_31
import Propositio.Collatz.ThirteenL25_32
import Propositio.Collatz.ThirteenL25_33
import Propositio.Collatz.ThirteenL25_34
import Propositio.Collatz.ThirteenL25_35
import Propositio.Collatz.ThirteenL25_36
import Propositio.Collatz.ThirteenL25_37
import Propositio.Collatz.ThirteenL25_38
import Propositio.Collatz.ThirteenL25_39
namespace CollatzThirteenCycle
open CollatzCycleDecide (steinerVal compositions)
open CollatzCycleEnum (noStDvd noStDvd_top)
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000000

theorem a25_0_0_0_0_0 : noStDvd (2 ^ 25 - 3 ^ 13) 8 20 211 5 = true := by
  rw [show (8 : Nat) = 7 + 1 from rfl, noStDvd]
  apply List.all_eq_true.mpr
  intro i hi
  rw [List.mem_range] at hi
  interval_cases i
  · exact b25_0_0_0_0_0_0
  · exact b25_0_0_0_0_0_1
  · exact b25_0_0_0_0_0_2
  · exact b25_0_0_0_0_0_3
  · exact b25_0_0_0_0_0_4
  · exact b25_0_0_0_0_0_5
  · exact b25_0_0_0_0_0_6
  · exact b25_0_0_0_0_0_7
  · exact b25_0_0_0_0_0_8
  · exact b25_0_0_0_0_0_9
  · exact b25_0_0_0_0_0_10
  · exact b25_0_0_0_0_0_11
  · exact b25_0_0_0_0_0_12
  all_goals decide

theorem a25_0_0_0_0 : noStDvd (2 ^ 25 - 3 ^ 13) 9 21 65 4 = true := by
  rw [show (9 : Nat) = 8 + 1 from rfl, noStDvd]
  apply List.all_eq_true.mpr
  intro i hi
  rw [List.mem_range] at hi
  interval_cases i
  · exact a25_0_0_0_0_0
  · exact b25_0_0_0_0_1
  · exact b25_0_0_0_0_2
  · exact b25_0_0_0_0_3
  · exact b25_0_0_0_0_4
  · exact b25_0_0_0_0_5
  · exact b25_0_0_0_0_6
  · exact b25_0_0_0_0_7
  · exact b25_0_0_0_0_8
  · exact b25_0_0_0_0_9
  · exact b25_0_0_0_0_10
  · exact b25_0_0_0_0_11
  · exact b25_0_0_0_0_12
  all_goals decide

theorem a25_0_0_0_1 : noStDvd (2 ^ 25 - 3 ^ 13) 9 20 65 5 = true := by
  rw [show (9 : Nat) = 8 + 1 from rfl, noStDvd]
  apply List.all_eq_true.mpr
  intro i hi
  rw [List.mem_range] at hi
  interval_cases i
  · exact b25_0_0_0_1_0
  · exact b25_0_0_0_1_1
  · exact b25_0_0_0_1_2
  · exact b25_0_0_0_1_3
  · exact b25_0_0_0_1_4
  · exact b25_0_0_0_1_5
  · exact b25_0_0_0_1_6
  · exact b25_0_0_0_1_7
  · exact b25_0_0_0_1_8
  · exact b25_0_0_0_1_9
  · exact b25_0_0_0_1_10
  · exact b25_0_0_0_1_11
  all_goals decide

theorem a25_0_0_0 : noStDvd (2 ^ 25 - 3 ^ 13) 10 22 19 3 = true := by
  rw [show (10 : Nat) = 9 + 1 from rfl, noStDvd]
  apply List.all_eq_true.mpr
  intro i hi
  rw [List.mem_range] at hi
  interval_cases i
  · exact a25_0_0_0_0
  · exact a25_0_0_0_1
  · exact b25_0_0_0_2
  · exact b25_0_0_0_3
  · exact b25_0_0_0_4
  · exact b25_0_0_0_5
  · exact b25_0_0_0_6
  · exact b25_0_0_0_7
  · exact b25_0_0_0_8
  · exact b25_0_0_0_9
  · exact b25_0_0_0_10
  · exact b25_0_0_0_11
  · exact b25_0_0_0_12
  all_goals decide

theorem a25_0_0_1_0 : noStDvd (2 ^ 25 - 3 ^ 13) 9 20 73 5 = true := by
  rw [show (9 : Nat) = 8 + 1 from rfl, noStDvd]
  apply List.all_eq_true.mpr
  intro i hi
  rw [List.mem_range] at hi
  interval_cases i
  · exact b25_0_0_1_0_0
  · exact b25_0_0_1_0_1
  · exact b25_0_0_1_0_2
  · exact b25_0_0_1_0_3
  · exact b25_0_0_1_0_4
  · exact b25_0_0_1_0_5
  · exact b25_0_0_1_0_6
  · exact b25_0_0_1_0_7
  · exact b25_0_0_1_0_8
  · exact b25_0_0_1_0_9
  · exact b25_0_0_1_0_10
  · exact b25_0_0_1_0_11
  all_goals decide

theorem a25_0_0_1 : noStDvd (2 ^ 25 - 3 ^ 13) 10 21 19 4 = true := by
  rw [show (10 : Nat) = 9 + 1 from rfl, noStDvd]
  apply List.all_eq_true.mpr
  intro i hi
  rw [List.mem_range] at hi
  interval_cases i
  · exact a25_0_0_1_0
  · exact b25_0_0_1_1
  · exact b25_0_0_1_2
  · exact b25_0_0_1_3
  · exact b25_0_0_1_4
  · exact b25_0_0_1_5
  · exact b25_0_0_1_6
  · exact b25_0_0_1_7
  · exact b25_0_0_1_8
  · exact b25_0_0_1_9
  · exact b25_0_0_1_10
  · exact b25_0_0_1_11
  all_goals decide

theorem a25_0_0_2 : noStDvd (2 ^ 25 - 3 ^ 13) 10 20 19 5 = true := by
  rw [show (10 : Nat) = 9 + 1 from rfl, noStDvd]
  apply List.all_eq_true.mpr
  intro i hi
  rw [List.mem_range] at hi
  interval_cases i
  · exact b25_0_0_2_0
  · exact b25_0_0_2_1
  · exact b25_0_0_2_2
  · exact b25_0_0_2_3
  · exact b25_0_0_2_4
  · exact b25_0_0_2_5
  · exact b25_0_0_2_6
  · exact b25_0_0_2_7
  · exact b25_0_0_2_8
  · exact b25_0_0_2_9
  · exact b25_0_0_2_10
  all_goals decide

theorem a25_0_0_3 : noStDvd (2 ^ 25 - 3 ^ 13) 10 19 19 6 = true := by
  rw [show (10 : Nat) = 9 + 1 from rfl, noStDvd]
  apply List.all_eq_true.mpr
  intro i hi
  rw [List.mem_range] at hi
  interval_cases i
  · exact b25_0_0_3_0
  · exact b25_0_0_3_1
  · exact b25_0_0_3_2
  · exact b25_0_0_3_3
  · exact b25_0_0_3_4
  · exact b25_0_0_3_5
  · exact b25_0_0_3_6
  · exact b25_0_0_3_7
  · exact b25_0_0_3_8
  · exact b25_0_0_3_9
  all_goals decide

theorem a25_0_0 : noStDvd (2 ^ 25 - 3 ^ 13) 11 23 5 2 = true := by
  rw [show (11 : Nat) = 10 + 1 from rfl, noStDvd]
  apply List.all_eq_true.mpr
  intro i hi
  rw [List.mem_range] at hi
  interval_cases i
  · exact a25_0_0_0
  · exact a25_0_0_1
  · exact a25_0_0_2
  · exact a25_0_0_3
  · exact b25_0_0_4
  · exact b25_0_0_5
  · exact b25_0_0_6
  · exact b25_0_0_7
  · exact b25_0_0_8
  · exact b25_0_0_9
  · exact b25_0_0_10
  · exact b25_0_0_11
  · exact b25_0_0_12
  all_goals decide

theorem a25_0_1_0_0 : noStDvd (2 ^ 25 - 3 ^ 13) 9 20 85 5 = true := by
  rw [show (9 : Nat) = 8 + 1 from rfl, noStDvd]
  apply List.all_eq_true.mpr
  intro i hi
  rw [List.mem_range] at hi
  interval_cases i
  · exact b25_0_1_0_0_0
  · exact b25_0_1_0_0_1
  · exact b25_0_1_0_0_2
  · exact b25_0_1_0_0_3
  · exact b25_0_1_0_0_4
  · exact b25_0_1_0_0_5
  · exact b25_0_1_0_0_6
  · exact b25_0_1_0_0_7
  · exact b25_0_1_0_0_8
  · exact b25_0_1_0_0_9
  · exact b25_0_1_0_0_10
  · exact b25_0_1_0_0_11
  all_goals decide

theorem a25_0_1_0 : noStDvd (2 ^ 25 - 3 ^ 13) 10 21 23 4 = true := by
  rw [show (10 : Nat) = 9 + 1 from rfl, noStDvd]
  apply List.all_eq_true.mpr
  intro i hi
  rw [List.mem_range] at hi
  interval_cases i
  · exact a25_0_1_0_0
  · exact b25_0_1_0_1
  · exact b25_0_1_0_2
  · exact b25_0_1_0_3
  · exact b25_0_1_0_4
  · exact b25_0_1_0_5
  · exact b25_0_1_0_6
  · exact b25_0_1_0_7
  · exact b25_0_1_0_8
  · exact b25_0_1_0_9
  · exact b25_0_1_0_10
  · exact b25_0_1_0_11
  all_goals decide

theorem a25_0_1_1 : noStDvd (2 ^ 25 - 3 ^ 13) 10 20 23 5 = true := by
  rw [show (10 : Nat) = 9 + 1 from rfl, noStDvd]
  apply List.all_eq_true.mpr
  intro i hi
  rw [List.mem_range] at hi
  interval_cases i
  · exact b25_0_1_1_0
  · exact b25_0_1_1_1
  · exact b25_0_1_1_2
  · exact b25_0_1_1_3
  · exact b25_0_1_1_4
  · exact b25_0_1_1_5
  · exact b25_0_1_1_6
  · exact b25_0_1_1_7
  · exact b25_0_1_1_8
  · exact b25_0_1_1_9
  · exact b25_0_1_1_10
  all_goals decide

theorem a25_0_1_2 : noStDvd (2 ^ 25 - 3 ^ 13) 10 19 23 6 = true := by
  rw [show (10 : Nat) = 9 + 1 from rfl, noStDvd]
  apply List.all_eq_true.mpr
  intro i hi
  rw [List.mem_range] at hi
  interval_cases i
  · exact b25_0_1_2_0
  · exact b25_0_1_2_1
  · exact b25_0_1_2_2
  · exact b25_0_1_2_3
  · exact b25_0_1_2_4
  · exact b25_0_1_2_5
  · exact b25_0_1_2_6
  · exact b25_0_1_2_7
  · exact b25_0_1_2_8
  · exact b25_0_1_2_9
  all_goals decide

theorem a25_0_1 : noStDvd (2 ^ 25 - 3 ^ 13) 11 22 5 3 = true := by
  rw [show (11 : Nat) = 10 + 1 from rfl, noStDvd]
  apply List.all_eq_true.mpr
  intro i hi
  rw [List.mem_range] at hi
  interval_cases i
  · exact a25_0_1_0
  · exact a25_0_1_1
  · exact a25_0_1_2
  · exact b25_0_1_3
  · exact b25_0_1_4
  · exact b25_0_1_5
  · exact b25_0_1_6
  · exact b25_0_1_7
  · exact b25_0_1_8
  · exact b25_0_1_9
  · exact b25_0_1_10
  · exact b25_0_1_11
  all_goals decide

theorem a25_0_2_0 : noStDvd (2 ^ 25 - 3 ^ 13) 10 20 31 5 = true := by
  rw [show (10 : Nat) = 9 + 1 from rfl, noStDvd]
  apply List.all_eq_true.mpr
  intro i hi
  rw [List.mem_range] at hi
  interval_cases i
  · exact b25_0_2_0_0
  · exact b25_0_2_0_1
  · exact b25_0_2_0_2
  · exact b25_0_2_0_3
  · exact b25_0_2_0_4
  · exact b25_0_2_0_5
  · exact b25_0_2_0_6
  · exact b25_0_2_0_7
  · exact b25_0_2_0_8
  · exact b25_0_2_0_9
  · exact b25_0_2_0_10
  all_goals decide

theorem a25_0_2_1 : noStDvd (2 ^ 25 - 3 ^ 13) 10 19 31 6 = true := by
  rw [show (10 : Nat) = 9 + 1 from rfl, noStDvd]
  apply List.all_eq_true.mpr
  intro i hi
  rw [List.mem_range] at hi
  interval_cases i
  · exact b25_0_2_1_0
  · exact b25_0_2_1_1
  · exact b25_0_2_1_2
  · exact b25_0_2_1_3
  · exact b25_0_2_1_4
  · exact b25_0_2_1_5
  · exact b25_0_2_1_6
  · exact b25_0_2_1_7
  · exact b25_0_2_1_8
  · exact b25_0_2_1_9
  all_goals decide

theorem a25_0_2 : noStDvd (2 ^ 25 - 3 ^ 13) 11 21 5 4 = true := by
  rw [show (11 : Nat) = 10 + 1 from rfl, noStDvd]
  apply List.all_eq_true.mpr
  intro i hi
  rw [List.mem_range] at hi
  interval_cases i
  · exact a25_0_2_0
  · exact a25_0_2_1
  · exact b25_0_2_2
  · exact b25_0_2_3
  · exact b25_0_2_4
  · exact b25_0_2_5
  · exact b25_0_2_6
  · exact b25_0_2_7
  · exact b25_0_2_8
  · exact b25_0_2_9
  · exact b25_0_2_10
  all_goals decide

theorem a25_0_3_0 : noStDvd (2 ^ 25 - 3 ^ 13) 10 19 47 6 = true := by
  rw [show (10 : Nat) = 9 + 1 from rfl, noStDvd]
  apply List.all_eq_true.mpr
  intro i hi
  rw [List.mem_range] at hi
  interval_cases i
  · exact b25_0_3_0_0
  · exact b25_0_3_0_1
  · exact b25_0_3_0_2
  · exact b25_0_3_0_3
  · exact b25_0_3_0_4
  · exact b25_0_3_0_5
  · exact b25_0_3_0_6
  · exact b25_0_3_0_7
  · exact b25_0_3_0_8
  · exact b25_0_3_0_9
  all_goals decide

theorem a25_0_3 : noStDvd (2 ^ 25 - 3 ^ 13) 11 20 5 5 = true := by
  rw [show (11 : Nat) = 10 + 1 from rfl, noStDvd]
  apply List.all_eq_true.mpr
  intro i hi
  rw [List.mem_range] at hi
  interval_cases i
  · exact a25_0_3_0
  · exact b25_0_3_1
  · exact b25_0_3_2
  · exact b25_0_3_3
  · exact b25_0_3_4
  · exact b25_0_3_5
  · exact b25_0_3_6
  · exact b25_0_3_7
  · exact b25_0_3_8
  · exact b25_0_3_9
  all_goals decide

theorem a25_0 : noStDvd (2 ^ 25 - 3 ^ 13) 12 24 1 1 = true := by
  rw [show (12 : Nat) = 11 + 1 from rfl, noStDvd]
  apply List.all_eq_true.mpr
  intro i hi
  rw [List.mem_range] at hi
  interval_cases i
  · exact a25_0_0
  · exact a25_0_1
  · exact a25_0_2
  · exact a25_0_3
  · exact b25_0_4
  · exact b25_0_5
  · exact b25_0_6
  · exact b25_0_7
  · exact b25_0_8
  · exact b25_0_9
  · exact b25_0_10
  · exact b25_0_11
  · exact b25_0_12
  all_goals decide

theorem a25_1_0_0_0 : noStDvd (2 ^ 25 - 3 ^ 13) 9 20 103 5 = true := by
  rw [show (9 : Nat) = 8 + 1 from rfl, noStDvd]
  apply List.all_eq_true.mpr
  intro i hi
  rw [List.mem_range] at hi
  interval_cases i
  · exact b25_1_0_0_0_0
  · exact b25_1_0_0_0_1
  · exact b25_1_0_0_0_2
  · exact b25_1_0_0_0_3
  · exact b25_1_0_0_0_4
  · exact b25_1_0_0_0_5
  · exact b25_1_0_0_0_6
  · exact b25_1_0_0_0_7
  · exact b25_1_0_0_0_8
  · exact b25_1_0_0_0_9
  · exact b25_1_0_0_0_10
  · exact b25_1_0_0_0_11
  all_goals decide

theorem a25_1_0_0 : noStDvd (2 ^ 25 - 3 ^ 13) 10 21 29 4 = true := by
  rw [show (10 : Nat) = 9 + 1 from rfl, noStDvd]
  apply List.all_eq_true.mpr
  intro i hi
  rw [List.mem_range] at hi
  interval_cases i
  · exact a25_1_0_0_0
  · exact b25_1_0_0_1
  · exact b25_1_0_0_2
  · exact b25_1_0_0_3
  · exact b25_1_0_0_4
  · exact b25_1_0_0_5
  · exact b25_1_0_0_6
  · exact b25_1_0_0_7
  · exact b25_1_0_0_8
  · exact b25_1_0_0_9
  · exact b25_1_0_0_10
  · exact b25_1_0_0_11
  all_goals decide

theorem a25_1_0_1 : noStDvd (2 ^ 25 - 3 ^ 13) 10 20 29 5 = true := by
  rw [show (10 : Nat) = 9 + 1 from rfl, noStDvd]
  apply List.all_eq_true.mpr
  intro i hi
  rw [List.mem_range] at hi
  interval_cases i
  · exact b25_1_0_1_0
  · exact b25_1_0_1_1
  · exact b25_1_0_1_2
  · exact b25_1_0_1_3
  · exact b25_1_0_1_4
  · exact b25_1_0_1_5
  · exact b25_1_0_1_6
  · exact b25_1_0_1_7
  · exact b25_1_0_1_8
  · exact b25_1_0_1_9
  · exact b25_1_0_1_10
  all_goals decide

theorem a25_1_0_2 : noStDvd (2 ^ 25 - 3 ^ 13) 10 19 29 6 = true := by
  rw [show (10 : Nat) = 9 + 1 from rfl, noStDvd]
  apply List.all_eq_true.mpr
  intro i hi
  rw [List.mem_range] at hi
  interval_cases i
  · exact b25_1_0_2_0
  · exact b25_1_0_2_1
  · exact b25_1_0_2_2
  · exact b25_1_0_2_3
  · exact b25_1_0_2_4
  · exact b25_1_0_2_5
  · exact b25_1_0_2_6
  · exact b25_1_0_2_7
  · exact b25_1_0_2_8
  · exact b25_1_0_2_9
  all_goals decide

theorem a25_1_0 : noStDvd (2 ^ 25 - 3 ^ 13) 11 22 7 3 = true := by
  rw [show (11 : Nat) = 10 + 1 from rfl, noStDvd]
  apply List.all_eq_true.mpr
  intro i hi
  rw [List.mem_range] at hi
  interval_cases i
  · exact a25_1_0_0
  · exact a25_1_0_1
  · exact a25_1_0_2
  · exact b25_1_0_3
  · exact b25_1_0_4
  · exact b25_1_0_5
  · exact b25_1_0_6
  · exact b25_1_0_7
  · exact b25_1_0_8
  · exact b25_1_0_9
  · exact b25_1_0_10
  · exact b25_1_0_11
  all_goals decide

theorem a25_1_1_0 : noStDvd (2 ^ 25 - 3 ^ 13) 10 20 37 5 = true := by
  rw [show (10 : Nat) = 9 + 1 from rfl, noStDvd]
  apply List.all_eq_true.mpr
  intro i hi
  rw [List.mem_range] at hi
  interval_cases i
  · exact b25_1_1_0_0
  · exact b25_1_1_0_1
  · exact b25_1_1_0_2
  · exact b25_1_1_0_3
  · exact b25_1_1_0_4
  · exact b25_1_1_0_5
  · exact b25_1_1_0_6
  · exact b25_1_1_0_7
  · exact b25_1_1_0_8
  · exact b25_1_1_0_9
  · exact b25_1_1_0_10
  all_goals decide

theorem a25_1_1_1 : noStDvd (2 ^ 25 - 3 ^ 13) 10 19 37 6 = true := by
  rw [show (10 : Nat) = 9 + 1 from rfl, noStDvd]
  apply List.all_eq_true.mpr
  intro i hi
  rw [List.mem_range] at hi
  interval_cases i
  · exact b25_1_1_1_0
  · exact b25_1_1_1_1
  · exact b25_1_1_1_2
  · exact b25_1_1_1_3
  · exact b25_1_1_1_4
  · exact b25_1_1_1_5
  · exact b25_1_1_1_6
  · exact b25_1_1_1_7
  · exact b25_1_1_1_8
  · exact b25_1_1_1_9
  all_goals decide

theorem a25_1_1 : noStDvd (2 ^ 25 - 3 ^ 13) 11 21 7 4 = true := by
  rw [show (11 : Nat) = 10 + 1 from rfl, noStDvd]
  apply List.all_eq_true.mpr
  intro i hi
  rw [List.mem_range] at hi
  interval_cases i
  · exact a25_1_1_0
  · exact a25_1_1_1
  · exact b25_1_1_2
  · exact b25_1_1_3
  · exact b25_1_1_4
  · exact b25_1_1_5
  · exact b25_1_1_6
  · exact b25_1_1_7
  · exact b25_1_1_8
  · exact b25_1_1_9
  · exact b25_1_1_10
  all_goals decide

theorem a25_1_2_0 : noStDvd (2 ^ 25 - 3 ^ 13) 10 19 53 6 = true := by
  rw [show (10 : Nat) = 9 + 1 from rfl, noStDvd]
  apply List.all_eq_true.mpr
  intro i hi
  rw [List.mem_range] at hi
  interval_cases i
  · exact b25_1_2_0_0
  · exact b25_1_2_0_1
  · exact b25_1_2_0_2
  · exact b25_1_2_0_3
  · exact b25_1_2_0_4
  · exact b25_1_2_0_5
  · exact b25_1_2_0_6
  · exact b25_1_2_0_7
  · exact b25_1_2_0_8
  · exact b25_1_2_0_9
  all_goals decide

theorem a25_1_2 : noStDvd (2 ^ 25 - 3 ^ 13) 11 20 7 5 = true := by
  rw [show (11 : Nat) = 10 + 1 from rfl, noStDvd]
  apply List.all_eq_true.mpr
  intro i hi
  rw [List.mem_range] at hi
  interval_cases i
  · exact a25_1_2_0
  · exact b25_1_2_1
  · exact b25_1_2_2
  · exact b25_1_2_3
  · exact b25_1_2_4
  · exact b25_1_2_5
  · exact b25_1_2_6
  · exact b25_1_2_7
  · exact b25_1_2_8
  · exact b25_1_2_9
  all_goals decide

theorem a25_1 : noStDvd (2 ^ 25 - 3 ^ 13) 12 23 1 2 = true := by
  rw [show (12 : Nat) = 11 + 1 from rfl, noStDvd]
  apply List.all_eq_true.mpr
  intro i hi
  rw [List.mem_range] at hi
  interval_cases i
  · exact a25_1_0
  · exact a25_1_1
  · exact a25_1_2
  · exact b25_1_3
  · exact b25_1_4
  · exact b25_1_5
  · exact b25_1_6
  · exact b25_1_7
  · exact b25_1_8
  · exact b25_1_9
  · exact b25_1_10
  · exact b25_1_11
  all_goals decide

theorem a25_2_0_0 : noStDvd (2 ^ 25 - 3 ^ 13) 10 20 49 5 = true := by
  rw [show (10 : Nat) = 9 + 1 from rfl, noStDvd]
  apply List.all_eq_true.mpr
  intro i hi
  rw [List.mem_range] at hi
  interval_cases i
  · exact b25_2_0_0_0
  · exact b25_2_0_0_1
  · exact b25_2_0_0_2
  · exact b25_2_0_0_3
  · exact b25_2_0_0_4
  · exact b25_2_0_0_5
  · exact b25_2_0_0_6
  · exact b25_2_0_0_7
  · exact b25_2_0_0_8
  · exact b25_2_0_0_9
  · exact b25_2_0_0_10
  all_goals decide

theorem a25_2_0_1 : noStDvd (2 ^ 25 - 3 ^ 13) 10 19 49 6 = true := by
  rw [show (10 : Nat) = 9 + 1 from rfl, noStDvd]
  apply List.all_eq_true.mpr
  intro i hi
  rw [List.mem_range] at hi
  interval_cases i
  · exact b25_2_0_1_0
  · exact b25_2_0_1_1
  · exact b25_2_0_1_2
  · exact b25_2_0_1_3
  · exact b25_2_0_1_4
  · exact b25_2_0_1_5
  · exact b25_2_0_1_6
  · exact b25_2_0_1_7
  · exact b25_2_0_1_8
  · exact b25_2_0_1_9
  all_goals decide

theorem a25_2_0 : noStDvd (2 ^ 25 - 3 ^ 13) 11 21 11 4 = true := by
  rw [show (11 : Nat) = 10 + 1 from rfl, noStDvd]
  apply List.all_eq_true.mpr
  intro i hi
  rw [List.mem_range] at hi
  interval_cases i
  · exact a25_2_0_0
  · exact a25_2_0_1
  · exact b25_2_0_2
  · exact b25_2_0_3
  · exact b25_2_0_4
  · exact b25_2_0_5
  · exact b25_2_0_6
  · exact b25_2_0_7
  · exact b25_2_0_8
  · exact b25_2_0_9
  · exact b25_2_0_10
  all_goals decide

theorem a25_2_1_0 : noStDvd (2 ^ 25 - 3 ^ 13) 10 19 65 6 = true := by
  rw [show (10 : Nat) = 9 + 1 from rfl, noStDvd]
  apply List.all_eq_true.mpr
  intro i hi
  rw [List.mem_range] at hi
  interval_cases i
  · exact b25_2_1_0_0
  · exact b25_2_1_0_1
  · exact b25_2_1_0_2
  · exact b25_2_1_0_3
  · exact b25_2_1_0_4
  · exact b25_2_1_0_5
  · exact b25_2_1_0_6
  · exact b25_2_1_0_7
  · exact b25_2_1_0_8
  · exact b25_2_1_0_9
  all_goals decide

theorem a25_2_1 : noStDvd (2 ^ 25 - 3 ^ 13) 11 20 11 5 = true := by
  rw [show (11 : Nat) = 10 + 1 from rfl, noStDvd]
  apply List.all_eq_true.mpr
  intro i hi
  rw [List.mem_range] at hi
  interval_cases i
  · exact a25_2_1_0
  · exact b25_2_1_1
  · exact b25_2_1_2
  · exact b25_2_1_3
  · exact b25_2_1_4
  · exact b25_2_1_5
  · exact b25_2_1_6
  · exact b25_2_1_7
  · exact b25_2_1_8
  · exact b25_2_1_9
  all_goals decide

theorem a25_2 : noStDvd (2 ^ 25 - 3 ^ 13) 12 22 1 3 = true := by
  rw [show (12 : Nat) = 11 + 1 from rfl, noStDvd]
  apply List.all_eq_true.mpr
  intro i hi
  rw [List.mem_range] at hi
  interval_cases i
  · exact a25_2_0
  · exact a25_2_1
  · exact b25_2_2
  · exact b25_2_3
  · exact b25_2_4
  · exact b25_2_5
  · exact b25_2_6
  · exact b25_2_7
  · exact b25_2_8
  · exact b25_2_9
  · exact b25_2_10
  all_goals decide

theorem a25_3_0_0 : noStDvd (2 ^ 25 - 3 ^ 13) 10 19 89 6 = true := by
  rw [show (10 : Nat) = 9 + 1 from rfl, noStDvd]
  apply List.all_eq_true.mpr
  intro i hi
  rw [List.mem_range] at hi
  interval_cases i
  · exact b25_3_0_0_0
  · exact b25_3_0_0_1
  · exact b25_3_0_0_2
  · exact b25_3_0_0_3
  · exact b25_3_0_0_4
  · exact b25_3_0_0_5
  · exact b25_3_0_0_6
  · exact b25_3_0_0_7
  · exact b25_3_0_0_8
  · exact b25_3_0_0_9
  all_goals decide

theorem a25_3_0 : noStDvd (2 ^ 25 - 3 ^ 13) 11 20 19 5 = true := by
  rw [show (11 : Nat) = 10 + 1 from rfl, noStDvd]
  apply List.all_eq_true.mpr
  intro i hi
  rw [List.mem_range] at hi
  interval_cases i
  · exact a25_3_0_0
  · exact b25_3_0_1
  · exact b25_3_0_2
  · exact b25_3_0_3
  · exact b25_3_0_4
  · exact b25_3_0_5
  · exact b25_3_0_6
  · exact b25_3_0_7
  · exact b25_3_0_8
  · exact b25_3_0_9
  all_goals decide

theorem a25_3 : noStDvd (2 ^ 25 - 3 ^ 13) 12 21 1 4 = true := by
  rw [show (12 : Nat) = 11 + 1 from rfl, noStDvd]
  apply List.all_eq_true.mpr
  intro i hi
  rw [List.mem_range] at hi
  interval_cases i
  · exact a25_3_0
  · exact b25_3_1
  · exact b25_3_2
  · exact b25_3_3
  · exact b25_3_4
  · exact b25_3_5
  · exact b25_3_6
  · exact b25_3_7
  · exact b25_3_8
  · exact b25_3_9
  all_goals decide

theorem a25_4 : noStDvd (2 ^ 25 - 3 ^ 13) 12 20 1 5 = true := by
  rw [show (12 : Nat) = 11 + 1 from rfl, noStDvd]
  apply List.all_eq_true.mpr
  intro i hi
  rw [List.mem_range] at hi
  interval_cases i
  · exact b25_4_0
  · exact b25_4_1
  · exact b25_4_2
  · exact b25_4_3
  · exact b25_4_4
  · exact b25_4_5
  · exact b25_4_6
  · exact b25_4_7
  · exact b25_4_8
  all_goals decide

theorem check13_25 : (compositions 13 25).all (fun as => !decide ((2 ^ 25 - 3 ^ 13) ∣ steinerVal as)) = true := by
  rw [← noStDvd_top, show (13 : Nat) = 12 + 1 from rfl, noStDvd]
  apply List.all_eq_true.mpr
  intro i hi
  rw [List.mem_range] at hi
  interval_cases i
  · exact a25_0
  · exact a25_1
  · exact a25_2
  · exact a25_3
  · exact a25_4
  · exact b25_5
  · exact b25_6
  · exact b25_7
  · exact b25_8
  · exact b25_9
  · exact b25_10
  · exact b25_11
  · exact b25_12
  all_goals decide

end CollatzThirteenCycle
