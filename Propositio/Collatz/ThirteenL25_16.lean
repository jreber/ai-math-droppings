import Propositio.Collatz.CycleUniform
import Propositio.Collatz.CycleEnum

namespace CollatzThirteenCycle
open CollatzCycleDecide (steinerVal compositions)
open CollatzCycleEnum (noStDvd noStDvd_top)
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000000

theorem b25_0_2_0_2 : noStDvd (2 ^ 25 - 3 ^ 13) 9 17 125 8 = true := by decide
theorem b25_0_2_0_3 : noStDvd (2 ^ 25 - 3 ^ 13) 9 16 125 9 = true := by decide
theorem b25_0_2_0_4 : noStDvd (2 ^ 25 - 3 ^ 13) 9 15 125 10 = true := by decide
theorem b25_0_2_0_5 : noStDvd (2 ^ 25 - 3 ^ 13) 9 14 125 11 = true := by decide
theorem b25_0_2_0_6 : noStDvd (2 ^ 25 - 3 ^ 13) 9 13 125 12 = true := by decide
theorem b25_0_2_0_7 : noStDvd (2 ^ 25 - 3 ^ 13) 9 12 125 13 = true := by decide
theorem b25_0_2_0_8 : noStDvd (2 ^ 25 - 3 ^ 13) 9 11 125 14 = true := by decide
theorem b25_0_2_0_9 : noStDvd (2 ^ 25 - 3 ^ 13) 9 10 125 15 = true := by decide
theorem b25_0_2_0_10 : noStDvd (2 ^ 25 - 3 ^ 13) 9 9 125 16 = true := by decide
theorem b25_0_2_1_0 : noStDvd (2 ^ 25 - 3 ^ 13) 9 18 157 7 = true := by decide
theorem b25_0_2_1_1 : noStDvd (2 ^ 25 - 3 ^ 13) 9 17 157 8 = true := by decide
theorem b25_0_2_1_2 : noStDvd (2 ^ 25 - 3 ^ 13) 9 16 157 9 = true := by decide
theorem b25_0_2_1_3 : noStDvd (2 ^ 25 - 3 ^ 13) 9 15 157 10 = true := by decide
theorem b25_0_2_1_4 : noStDvd (2 ^ 25 - 3 ^ 13) 9 14 157 11 = true := by decide
theorem b25_0_2_1_5 : noStDvd (2 ^ 25 - 3 ^ 13) 9 13 157 12 = true := by decide
theorem b25_0_2_1_6 : noStDvd (2 ^ 25 - 3 ^ 13) 9 12 157 13 = true := by decide
theorem b25_0_2_1_7 : noStDvd (2 ^ 25 - 3 ^ 13) 9 11 157 14 = true := by decide
theorem b25_0_2_1_8 : noStDvd (2 ^ 25 - 3 ^ 13) 9 10 157 15 = true := by decide
theorem b25_0_2_1_9 : noStDvd (2 ^ 25 - 3 ^ 13) 9 9 157 16 = true := by decide

end CollatzThirteenCycle
