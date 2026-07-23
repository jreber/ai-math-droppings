import Propositio.NumberTheory.Collatz.CycleUniform
import Propositio.NumberTheory.Collatz.CycleEnum

namespace CollatzTwelveCycle
open CollatzCycleDecide (steinerVal compositions)
open CollatzCycleEnum (noStDvd noStDvd_top)
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000000

theorem b23_0_0_0_0 : noStDvd (2 ^ 23 - 3 ^ 12) 8 19 65 4 = true := by decide
theorem b23_0_0_0_1 : noStDvd (2 ^ 23 - 3 ^ 12) 8 18 65 5 = true := by decide
theorem b23_0_0_0_2 : noStDvd (2 ^ 23 - 3 ^ 12) 8 17 65 6 = true := by decide
theorem b23_0_0_0_3 : noStDvd (2 ^ 23 - 3 ^ 12) 8 16 65 7 = true := by decide
theorem b23_0_0_0_4 : noStDvd (2 ^ 23 - 3 ^ 12) 8 15 65 8 = true := by decide
theorem b23_0_0_0_5 : noStDvd (2 ^ 23 - 3 ^ 12) 8 14 65 9 = true := by decide
theorem b23_0_0_0_6 : noStDvd (2 ^ 23 - 3 ^ 12) 8 13 65 10 = true := by decide
theorem b23_0_0_0_7 : noStDvd (2 ^ 23 - 3 ^ 12) 8 12 65 11 = true := by decide
theorem b23_0_0_0_8 : noStDvd (2 ^ 23 - 3 ^ 12) 8 11 65 12 = true := by decide
theorem b23_0_0_0_9 : noStDvd (2 ^ 23 - 3 ^ 12) 8 10 65 13 = true := by decide
theorem b23_0_0_0_10 : noStDvd (2 ^ 23 - 3 ^ 12) 8 9 65 14 = true := by decide
theorem b23_0_0_0_11 : noStDvd (2 ^ 23 - 3 ^ 12) 8 8 65 15 = true := by decide

end CollatzTwelveCycle
