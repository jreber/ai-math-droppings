import Propositio.Collatz.CycleUniform
import Propositio.Collatz.CycleEnum

namespace CollatzThirteenCycle
open CollatzCycleDecide (steinerVal compositions)
open CollatzCycleEnum (noStDvd noStDvd_top)
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000000

theorem b25_0_1_2_1 : noStDvd (2 ^ 25 - 3 ^ 13) 9 17 133 8 = true := by decide
theorem b25_0_1_2_2 : noStDvd (2 ^ 25 - 3 ^ 13) 9 16 133 9 = true := by decide
theorem b25_0_1_2_3 : noStDvd (2 ^ 25 - 3 ^ 13) 9 15 133 10 = true := by decide
theorem b25_0_1_2_4 : noStDvd (2 ^ 25 - 3 ^ 13) 9 14 133 11 = true := by decide
theorem b25_0_1_2_5 : noStDvd (2 ^ 25 - 3 ^ 13) 9 13 133 12 = true := by decide
theorem b25_0_1_2_6 : noStDvd (2 ^ 25 - 3 ^ 13) 9 12 133 13 = true := by decide
theorem b25_0_1_2_7 : noStDvd (2 ^ 25 - 3 ^ 13) 9 11 133 14 = true := by decide
theorem b25_0_1_2_8 : noStDvd (2 ^ 25 - 3 ^ 13) 9 10 133 15 = true := by decide
theorem b25_0_1_2_9 : noStDvd (2 ^ 25 - 3 ^ 13) 9 9 133 16 = true := by decide
theorem b25_0_1_3 : noStDvd (2 ^ 25 - 3 ^ 13) 10 18 23 7 = true := by decide
theorem b25_0_1_4 : noStDvd (2 ^ 25 - 3 ^ 13) 10 17 23 8 = true := by decide
theorem b25_0_1_5 : noStDvd (2 ^ 25 - 3 ^ 13) 10 16 23 9 = true := by decide
theorem b25_0_1_6 : noStDvd (2 ^ 25 - 3 ^ 13) 10 15 23 10 = true := by decide
theorem b25_0_1_7 : noStDvd (2 ^ 25 - 3 ^ 13) 10 14 23 11 = true := by decide
theorem b25_0_1_8 : noStDvd (2 ^ 25 - 3 ^ 13) 10 13 23 12 = true := by decide
theorem b25_0_1_9 : noStDvd (2 ^ 25 - 3 ^ 13) 10 12 23 13 = true := by decide
theorem b25_0_1_10 : noStDvd (2 ^ 25 - 3 ^ 13) 10 11 23 14 = true := by decide
theorem b25_0_1_11 : noStDvd (2 ^ 25 - 3 ^ 13) 10 10 23 15 = true := by decide

end CollatzThirteenCycle
