import Propositio.NumberTheory.Collatz.CycleUniform
import Propositio.NumberTheory.Collatz.CycleEnum

namespace CollatzThirteenCycle
open CollatzCycleDecide (steinerVal compositions)
open CollatzCycleEnum (noStDvd noStDvd_top)
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000000

theorem b25_1_0_2_1 : noStDvd (2 ^ 25 - 3 ^ 13) 9 17 151 8 = true := by decide
theorem b25_1_0_2_2 : noStDvd (2 ^ 25 - 3 ^ 13) 9 16 151 9 = true := by decide
theorem b25_1_0_2_3 : noStDvd (2 ^ 25 - 3 ^ 13) 9 15 151 10 = true := by decide
theorem b25_1_0_2_4 : noStDvd (2 ^ 25 - 3 ^ 13) 9 14 151 11 = true := by decide
theorem b25_1_0_2_5 : noStDvd (2 ^ 25 - 3 ^ 13) 9 13 151 12 = true := by decide
theorem b25_1_0_2_6 : noStDvd (2 ^ 25 - 3 ^ 13) 9 12 151 13 = true := by decide
theorem b25_1_0_2_7 : noStDvd (2 ^ 25 - 3 ^ 13) 9 11 151 14 = true := by decide
theorem b25_1_0_2_8 : noStDvd (2 ^ 25 - 3 ^ 13) 9 10 151 15 = true := by decide
theorem b25_1_0_2_9 : noStDvd (2 ^ 25 - 3 ^ 13) 9 9 151 16 = true := by decide
theorem b25_1_0_3 : noStDvd (2 ^ 25 - 3 ^ 13) 10 18 29 7 = true := by decide
theorem b25_1_0_4 : noStDvd (2 ^ 25 - 3 ^ 13) 10 17 29 8 = true := by decide
theorem b25_1_0_5 : noStDvd (2 ^ 25 - 3 ^ 13) 10 16 29 9 = true := by decide
theorem b25_1_0_6 : noStDvd (2 ^ 25 - 3 ^ 13) 10 15 29 10 = true := by decide
theorem b25_1_0_7 : noStDvd (2 ^ 25 - 3 ^ 13) 10 14 29 11 = true := by decide
theorem b25_1_0_8 : noStDvd (2 ^ 25 - 3 ^ 13) 10 13 29 12 = true := by decide
theorem b25_1_0_9 : noStDvd (2 ^ 25 - 3 ^ 13) 10 12 29 13 = true := by decide
theorem b25_1_0_10 : noStDvd (2 ^ 25 - 3 ^ 13) 10 11 29 14 = true := by decide
theorem b25_1_0_11 : noStDvd (2 ^ 25 - 3 ^ 13) 10 10 29 15 = true := by decide

end CollatzThirteenCycle
