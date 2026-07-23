import Propositio.Collatz.CycleUniform
import Propositio.Collatz.CycleEnum

namespace CollatzThirteenCycle
open CollatzCycleDecide (steinerVal compositions)
open CollatzCycleEnum (noStDvd noStDvd_top)
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000000

theorem b23_0_1_0_1 : noStDvd (2 ^ 23 - 3 ^ 13) 9 17 85 6 = true := by decide
theorem b23_0_1_0_2 : noStDvd (2 ^ 23 - 3 ^ 13) 9 16 85 7 = true := by decide
theorem b23_0_1_0_3 : noStDvd (2 ^ 23 - 3 ^ 13) 9 15 85 8 = true := by decide
theorem b23_0_1_0_4 : noStDvd (2 ^ 23 - 3 ^ 13) 9 14 85 9 = true := by decide
theorem b23_0_1_0_5 : noStDvd (2 ^ 23 - 3 ^ 13) 9 13 85 10 = true := by decide
theorem b23_0_1_0_6 : noStDvd (2 ^ 23 - 3 ^ 13) 9 12 85 11 = true := by decide
theorem b23_0_1_0_7 : noStDvd (2 ^ 23 - 3 ^ 13) 9 11 85 12 = true := by decide
theorem b23_0_1_0_8 : noStDvd (2 ^ 23 - 3 ^ 13) 9 10 85 13 = true := by decide
theorem b23_0_1_0_9 : noStDvd (2 ^ 23 - 3 ^ 13) 9 9 85 14 = true := by decide
theorem b23_0_1_1 : noStDvd (2 ^ 23 - 3 ^ 13) 10 18 23 5 = true := by decide
theorem b23_0_1_2 : noStDvd (2 ^ 23 - 3 ^ 13) 10 17 23 6 = true := by decide
theorem b23_0_1_3 : noStDvd (2 ^ 23 - 3 ^ 13) 10 16 23 7 = true := by decide
theorem b23_0_1_4 : noStDvd (2 ^ 23 - 3 ^ 13) 10 15 23 8 = true := by decide
theorem b23_0_1_5 : noStDvd (2 ^ 23 - 3 ^ 13) 10 14 23 9 = true := by decide
theorem b23_0_1_6 : noStDvd (2 ^ 23 - 3 ^ 13) 10 13 23 10 = true := by decide
theorem b23_0_1_7 : noStDvd (2 ^ 23 - 3 ^ 13) 10 12 23 11 = true := by decide
theorem b23_0_1_8 : noStDvd (2 ^ 23 - 3 ^ 13) 10 11 23 12 = true := by decide
theorem b23_0_1_9 : noStDvd (2 ^ 23 - 3 ^ 13) 10 10 23 13 = true := by decide

end CollatzThirteenCycle
