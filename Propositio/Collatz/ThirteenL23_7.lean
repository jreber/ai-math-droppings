import Propositio.Collatz.CycleUniform
import Propositio.Collatz.CycleEnum

namespace CollatzThirteenCycle
open CollatzCycleDecide (steinerVal compositions)
open CollatzCycleEnum (noStDvd noStDvd_top)
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000000

theorem b23_1_2 : noStDvd (2 ^ 23 - 3 ^ 13) 11 18 7 5 = true := by decide
theorem b23_1_3 : noStDvd (2 ^ 23 - 3 ^ 13) 11 17 7 6 = true := by decide
theorem b23_1_4 : noStDvd (2 ^ 23 - 3 ^ 13) 11 16 7 7 = true := by decide
theorem b23_1_5 : noStDvd (2 ^ 23 - 3 ^ 13) 11 15 7 8 = true := by decide
theorem b23_1_6 : noStDvd (2 ^ 23 - 3 ^ 13) 11 14 7 9 = true := by decide
theorem b23_1_7 : noStDvd (2 ^ 23 - 3 ^ 13) 11 13 7 10 = true := by decide
theorem b23_1_8 : noStDvd (2 ^ 23 - 3 ^ 13) 11 12 7 11 = true := by decide
theorem b23_1_9 : noStDvd (2 ^ 23 - 3 ^ 13) 11 11 7 12 = true := by decide
theorem b23_2_0 : noStDvd (2 ^ 23 - 3 ^ 13) 11 19 11 4 = true := by decide

end CollatzThirteenCycle
