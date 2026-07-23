import Propositio.Collatz.CycleUniform
import Propositio.Collatz.CycleEnum

namespace CollatzTwelveCycle
open CollatzCycleDecide (steinerVal compositions)
open CollatzCycleEnum (noStDvd noStDvd_top)
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000000

theorem b23_1_0_2 : noStDvd (2 ^ 23 - 3 ^ 12) 9 17 29 6 = true := by decide
theorem b23_1_0_3 : noStDvd (2 ^ 23 - 3 ^ 12) 9 16 29 7 = true := by decide
theorem b23_1_0_4 : noStDvd (2 ^ 23 - 3 ^ 12) 9 15 29 8 = true := by decide
theorem b23_1_0_5 : noStDvd (2 ^ 23 - 3 ^ 12) 9 14 29 9 = true := by decide
theorem b23_1_0_6 : noStDvd (2 ^ 23 - 3 ^ 12) 9 13 29 10 = true := by decide
theorem b23_1_0_7 : noStDvd (2 ^ 23 - 3 ^ 12) 9 12 29 11 = true := by decide
theorem b23_1_0_8 : noStDvd (2 ^ 23 - 3 ^ 12) 9 11 29 12 = true := by decide
theorem b23_1_0_9 : noStDvd (2 ^ 23 - 3 ^ 12) 9 10 29 13 = true := by decide
theorem b23_1_0_10 : noStDvd (2 ^ 23 - 3 ^ 12) 9 9 29 14 = true := by decide
theorem b23_1_1_0 : noStDvd (2 ^ 23 - 3 ^ 12) 9 18 37 5 = true := by decide
theorem b23_1_1_1 : noStDvd (2 ^ 23 - 3 ^ 12) 9 17 37 6 = true := by decide
theorem b23_1_1_2 : noStDvd (2 ^ 23 - 3 ^ 12) 9 16 37 7 = true := by decide
theorem b23_1_1_3 : noStDvd (2 ^ 23 - 3 ^ 12) 9 15 37 8 = true := by decide
theorem b23_1_1_4 : noStDvd (2 ^ 23 - 3 ^ 12) 9 14 37 9 = true := by decide
theorem b23_1_1_5 : noStDvd (2 ^ 23 - 3 ^ 12) 9 13 37 10 = true := by decide
theorem b23_1_1_6 : noStDvd (2 ^ 23 - 3 ^ 12) 9 12 37 11 = true := by decide
theorem b23_1_1_7 : noStDvd (2 ^ 23 - 3 ^ 12) 9 11 37 12 = true := by decide
theorem b23_1_1_8 : noStDvd (2 ^ 23 - 3 ^ 12) 9 10 37 13 = true := by decide
theorem b23_1_1_9 : noStDvd (2 ^ 23 - 3 ^ 12) 9 9 37 14 = true := by decide

end CollatzTwelveCycle
