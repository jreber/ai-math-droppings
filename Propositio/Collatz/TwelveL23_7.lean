import Propositio.Collatz.CycleUniform
import Propositio.Collatz.CycleEnum

namespace CollatzTwelveCycle
open CollatzCycleDecide (steinerVal compositions)
open CollatzCycleEnum (noStDvd noStDvd_top)
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000000

theorem b23_1_2 : noStDvd (2 ^ 23 - 3 ^ 12) 10 18 7 5 = true := by decide
theorem b23_1_3 : noStDvd (2 ^ 23 - 3 ^ 12) 10 17 7 6 = true := by decide
theorem b23_1_4 : noStDvd (2 ^ 23 - 3 ^ 12) 10 16 7 7 = true := by decide
theorem b23_1_5 : noStDvd (2 ^ 23 - 3 ^ 12) 10 15 7 8 = true := by decide
theorem b23_1_6 : noStDvd (2 ^ 23 - 3 ^ 12) 10 14 7 9 = true := by decide
theorem b23_1_7 : noStDvd (2 ^ 23 - 3 ^ 12) 10 13 7 10 = true := by decide
theorem b23_1_8 : noStDvd (2 ^ 23 - 3 ^ 12) 10 12 7 11 = true := by decide
theorem b23_1_9 : noStDvd (2 ^ 23 - 3 ^ 12) 10 11 7 12 = true := by decide
theorem b23_1_10 : noStDvd (2 ^ 23 - 3 ^ 12) 10 10 7 13 = true := by decide
theorem b23_2_0_0 : noStDvd (2 ^ 23 - 3 ^ 12) 9 18 49 5 = true := by decide

end CollatzTwelveCycle
