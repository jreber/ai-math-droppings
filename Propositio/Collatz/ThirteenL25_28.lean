import Propositio.Collatz.CycleUniform
import Propositio.Collatz.CycleEnum

namespace CollatzThirteenCycle
open CollatzCycleDecide (steinerVal compositions)
open CollatzCycleEnum (noStDvd noStDvd_top)
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000000

theorem b25_1_2_0_1 : noStDvd (2 ^ 25 - 3 ^ 13) 9 17 223 8 = true := by decide
theorem b25_1_2_0_2 : noStDvd (2 ^ 25 - 3 ^ 13) 9 16 223 9 = true := by decide
theorem b25_1_2_0_3 : noStDvd (2 ^ 25 - 3 ^ 13) 9 15 223 10 = true := by decide
theorem b25_1_2_0_4 : noStDvd (2 ^ 25 - 3 ^ 13) 9 14 223 11 = true := by decide
theorem b25_1_2_0_5 : noStDvd (2 ^ 25 - 3 ^ 13) 9 13 223 12 = true := by decide
theorem b25_1_2_0_6 : noStDvd (2 ^ 25 - 3 ^ 13) 9 12 223 13 = true := by decide
theorem b25_1_2_0_7 : noStDvd (2 ^ 25 - 3 ^ 13) 9 11 223 14 = true := by decide
theorem b25_1_2_0_8 : noStDvd (2 ^ 25 - 3 ^ 13) 9 10 223 15 = true := by decide
theorem b25_1_2_0_9 : noStDvd (2 ^ 25 - 3 ^ 13) 9 9 223 16 = true := by decide
theorem b25_1_2_1 : noStDvd (2 ^ 25 - 3 ^ 13) 10 18 53 7 = true := by decide
theorem b25_1_2_2 : noStDvd (2 ^ 25 - 3 ^ 13) 10 17 53 8 = true := by decide
theorem b25_1_2_3 : noStDvd (2 ^ 25 - 3 ^ 13) 10 16 53 9 = true := by decide
theorem b25_1_2_4 : noStDvd (2 ^ 25 - 3 ^ 13) 10 15 53 10 = true := by decide
theorem b25_1_2_5 : noStDvd (2 ^ 25 - 3 ^ 13) 10 14 53 11 = true := by decide
theorem b25_1_2_6 : noStDvd (2 ^ 25 - 3 ^ 13) 10 13 53 12 = true := by decide
theorem b25_1_2_7 : noStDvd (2 ^ 25 - 3 ^ 13) 10 12 53 13 = true := by decide
theorem b25_1_2_8 : noStDvd (2 ^ 25 - 3 ^ 13) 10 11 53 14 = true := by decide
theorem b25_1_2_9 : noStDvd (2 ^ 25 - 3 ^ 13) 10 10 53 15 = true := by decide

end CollatzThirteenCycle
