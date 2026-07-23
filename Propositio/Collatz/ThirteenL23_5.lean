import Propositio.Collatz.CycleUniform
import Propositio.Collatz.CycleEnum

namespace CollatzThirteenCycle
open CollatzCycleDecide (steinerVal compositions)
open CollatzCycleEnum (noStDvd noStDvd_top)
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000000

theorem b23_1_0_0_0 : noStDvd (2 ^ 23 - 3 ^ 13) 9 18 103 5 = true := by decide
theorem b23_1_0_0_1 : noStDvd (2 ^ 23 - 3 ^ 13) 9 17 103 6 = true := by decide
theorem b23_1_0_0_2 : noStDvd (2 ^ 23 - 3 ^ 13) 9 16 103 7 = true := by decide
theorem b23_1_0_0_3 : noStDvd (2 ^ 23 - 3 ^ 13) 9 15 103 8 = true := by decide
theorem b23_1_0_0_4 : noStDvd (2 ^ 23 - 3 ^ 13) 9 14 103 9 = true := by decide
theorem b23_1_0_0_5 : noStDvd (2 ^ 23 - 3 ^ 13) 9 13 103 10 = true := by decide
theorem b23_1_0_0_6 : noStDvd (2 ^ 23 - 3 ^ 13) 9 12 103 11 = true := by decide
theorem b23_1_0_0_7 : noStDvd (2 ^ 23 - 3 ^ 13) 9 11 103 12 = true := by decide
theorem b23_1_0_0_8 : noStDvd (2 ^ 23 - 3 ^ 13) 9 10 103 13 = true := by decide
theorem b23_1_0_0_9 : noStDvd (2 ^ 23 - 3 ^ 13) 9 9 103 14 = true := by decide
theorem b23_1_0_1 : noStDvd (2 ^ 23 - 3 ^ 13) 10 18 29 5 = true := by decide

end CollatzThirteenCycle
