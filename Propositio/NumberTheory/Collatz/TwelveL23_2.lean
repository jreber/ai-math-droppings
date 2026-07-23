import Propositio.NumberTheory.Collatz.CycleUniform
import Propositio.NumberTheory.Collatz.CycleEnum

namespace CollatzTwelveCycle
open CollatzCycleDecide (steinerVal compositions)
open CollatzCycleEnum (noStDvd noStDvd_top)
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000000

theorem b23_0_0_3 : noStDvd (2 ^ 23 - 3 ^ 12) 9 17 19 6 = true := by decide
theorem b23_0_0_4 : noStDvd (2 ^ 23 - 3 ^ 12) 9 16 19 7 = true := by decide
theorem b23_0_0_5 : noStDvd (2 ^ 23 - 3 ^ 12) 9 15 19 8 = true := by decide
theorem b23_0_0_6 : noStDvd (2 ^ 23 - 3 ^ 12) 9 14 19 9 = true := by decide
theorem b23_0_0_7 : noStDvd (2 ^ 23 - 3 ^ 12) 9 13 19 10 = true := by decide
theorem b23_0_0_8 : noStDvd (2 ^ 23 - 3 ^ 12) 9 12 19 11 = true := by decide
theorem b23_0_0_9 : noStDvd (2 ^ 23 - 3 ^ 12) 9 11 19 12 = true := by decide
theorem b23_0_0_10 : noStDvd (2 ^ 23 - 3 ^ 12) 9 10 19 13 = true := by decide
theorem b23_0_0_11 : noStDvd (2 ^ 23 - 3 ^ 12) 9 9 19 14 = true := by decide
theorem b23_0_1_0 : noStDvd (2 ^ 23 - 3 ^ 12) 9 19 23 4 = true := by decide

end CollatzTwelveCycle
