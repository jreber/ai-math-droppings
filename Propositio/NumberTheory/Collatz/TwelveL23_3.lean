import Propositio.NumberTheory.Collatz.CycleUniform
import Propositio.NumberTheory.Collatz.CycleEnum

namespace CollatzTwelveCycle
open CollatzCycleDecide (steinerVal compositions)
open CollatzCycleEnum (noStDvd noStDvd_top)
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000000

theorem b23_0_1_1 : noStDvd (2 ^ 23 - 3 ^ 12) 9 18 23 5 = true := by decide
theorem b23_0_1_2 : noStDvd (2 ^ 23 - 3 ^ 12) 9 17 23 6 = true := by decide
theorem b23_0_1_3 : noStDvd (2 ^ 23 - 3 ^ 12) 9 16 23 7 = true := by decide
theorem b23_0_1_4 : noStDvd (2 ^ 23 - 3 ^ 12) 9 15 23 8 = true := by decide
theorem b23_0_1_5 : noStDvd (2 ^ 23 - 3 ^ 12) 9 14 23 9 = true := by decide
theorem b23_0_1_6 : noStDvd (2 ^ 23 - 3 ^ 12) 9 13 23 10 = true := by decide
theorem b23_0_1_7 : noStDvd (2 ^ 23 - 3 ^ 12) 9 12 23 11 = true := by decide
theorem b23_0_1_8 : noStDvd (2 ^ 23 - 3 ^ 12) 9 11 23 12 = true := by decide
theorem b23_0_1_9 : noStDvd (2 ^ 23 - 3 ^ 12) 9 10 23 13 = true := by decide
theorem b23_0_1_10 : noStDvd (2 ^ 23 - 3 ^ 12) 9 9 23 14 = true := by decide
theorem b23_0_2_0 : noStDvd (2 ^ 23 - 3 ^ 12) 9 18 31 5 = true := by decide

end CollatzTwelveCycle
