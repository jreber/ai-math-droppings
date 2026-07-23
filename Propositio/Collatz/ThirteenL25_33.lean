import Propositio.Collatz.CycleUniform
import Propositio.Collatz.CycleEnum

namespace CollatzThirteenCycle
open CollatzCycleDecide (steinerVal compositions)
open CollatzCycleEnum (noStDvd noStDvd_top)
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000000

theorem b25_2_1_0_1 : noStDvd (2 ^ 25 - 3 ^ 13) 9 17 259 8 = true := by decide
theorem b25_2_1_0_2 : noStDvd (2 ^ 25 - 3 ^ 13) 9 16 259 9 = true := by decide
theorem b25_2_1_0_3 : noStDvd (2 ^ 25 - 3 ^ 13) 9 15 259 10 = true := by decide
theorem b25_2_1_0_4 : noStDvd (2 ^ 25 - 3 ^ 13) 9 14 259 11 = true := by decide
theorem b25_2_1_0_5 : noStDvd (2 ^ 25 - 3 ^ 13) 9 13 259 12 = true := by decide
theorem b25_2_1_0_6 : noStDvd (2 ^ 25 - 3 ^ 13) 9 12 259 13 = true := by decide
theorem b25_2_1_0_7 : noStDvd (2 ^ 25 - 3 ^ 13) 9 11 259 14 = true := by decide
theorem b25_2_1_0_8 : noStDvd (2 ^ 25 - 3 ^ 13) 9 10 259 15 = true := by decide
theorem b25_2_1_0_9 : noStDvd (2 ^ 25 - 3 ^ 13) 9 9 259 16 = true := by decide
theorem b25_2_1_1 : noStDvd (2 ^ 25 - 3 ^ 13) 10 18 65 7 = true := by decide
theorem b25_2_1_2 : noStDvd (2 ^ 25 - 3 ^ 13) 10 17 65 8 = true := by decide
theorem b25_2_1_3 : noStDvd (2 ^ 25 - 3 ^ 13) 10 16 65 9 = true := by decide
theorem b25_2_1_4 : noStDvd (2 ^ 25 - 3 ^ 13) 10 15 65 10 = true := by decide
theorem b25_2_1_5 : noStDvd (2 ^ 25 - 3 ^ 13) 10 14 65 11 = true := by decide
theorem b25_2_1_6 : noStDvd (2 ^ 25 - 3 ^ 13) 10 13 65 12 = true := by decide
theorem b25_2_1_7 : noStDvd (2 ^ 25 - 3 ^ 13) 10 12 65 13 = true := by decide
theorem b25_2_1_8 : noStDvd (2 ^ 25 - 3 ^ 13) 10 11 65 14 = true := by decide
theorem b25_2_1_9 : noStDvd (2 ^ 25 - 3 ^ 13) 10 10 65 15 = true := by decide

end CollatzThirteenCycle
