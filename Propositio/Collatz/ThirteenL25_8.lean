import Propositio.Collatz.CycleUniform
import Propositio.Collatz.CycleEnum

namespace CollatzThirteenCycle
open CollatzCycleDecide (steinerVal compositions)
open CollatzCycleEnum (noStDvd noStDvd_top)
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000000

theorem b25_0_0_2_2 : noStDvd (2 ^ 25 - 3 ^ 13) 9 17 89 8 = true := by decide
theorem b25_0_0_2_3 : noStDvd (2 ^ 25 - 3 ^ 13) 9 16 89 9 = true := by decide
theorem b25_0_0_2_4 : noStDvd (2 ^ 25 - 3 ^ 13) 9 15 89 10 = true := by decide
theorem b25_0_0_2_5 : noStDvd (2 ^ 25 - 3 ^ 13) 9 14 89 11 = true := by decide
theorem b25_0_0_2_6 : noStDvd (2 ^ 25 - 3 ^ 13) 9 13 89 12 = true := by decide
theorem b25_0_0_2_7 : noStDvd (2 ^ 25 - 3 ^ 13) 9 12 89 13 = true := by decide
theorem b25_0_0_2_8 : noStDvd (2 ^ 25 - 3 ^ 13) 9 11 89 14 = true := by decide
theorem b25_0_0_2_9 : noStDvd (2 ^ 25 - 3 ^ 13) 9 10 89 15 = true := by decide
theorem b25_0_0_2_10 : noStDvd (2 ^ 25 - 3 ^ 13) 9 9 89 16 = true := by decide
theorem b25_0_0_3_0 : noStDvd (2 ^ 25 - 3 ^ 13) 9 18 121 7 = true := by decide
theorem b25_0_0_3_1 : noStDvd (2 ^ 25 - 3 ^ 13) 9 17 121 8 = true := by decide
theorem b25_0_0_3_2 : noStDvd (2 ^ 25 - 3 ^ 13) 9 16 121 9 = true := by decide
theorem b25_0_0_3_3 : noStDvd (2 ^ 25 - 3 ^ 13) 9 15 121 10 = true := by decide
theorem b25_0_0_3_4 : noStDvd (2 ^ 25 - 3 ^ 13) 9 14 121 11 = true := by decide
theorem b25_0_0_3_5 : noStDvd (2 ^ 25 - 3 ^ 13) 9 13 121 12 = true := by decide
theorem b25_0_0_3_6 : noStDvd (2 ^ 25 - 3 ^ 13) 9 12 121 13 = true := by decide
theorem b25_0_0_3_7 : noStDvd (2 ^ 25 - 3 ^ 13) 9 11 121 14 = true := by decide
theorem b25_0_0_3_8 : noStDvd (2 ^ 25 - 3 ^ 13) 9 10 121 15 = true := by decide
theorem b25_0_0_3_9 : noStDvd (2 ^ 25 - 3 ^ 13) 9 9 121 16 = true := by decide

end CollatzThirteenCycle
