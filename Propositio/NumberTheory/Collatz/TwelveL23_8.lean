import Propositio.NumberTheory.Collatz.CycleUniform
import Propositio.NumberTheory.Collatz.CycleEnum

namespace CollatzTwelveCycle
open CollatzCycleDecide (steinerVal compositions)
open CollatzCycleEnum (noStDvd noStDvd_top)
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000000

theorem b23_2_0_1 : noStDvd (2 ^ 23 - 3 ^ 12) 9 17 49 6 = true := by decide
theorem b23_2_0_2 : noStDvd (2 ^ 23 - 3 ^ 12) 9 16 49 7 = true := by decide
theorem b23_2_0_3 : noStDvd (2 ^ 23 - 3 ^ 12) 9 15 49 8 = true := by decide
theorem b23_2_0_4 : noStDvd (2 ^ 23 - 3 ^ 12) 9 14 49 9 = true := by decide
theorem b23_2_0_5 : noStDvd (2 ^ 23 - 3 ^ 12) 9 13 49 10 = true := by decide
theorem b23_2_0_6 : noStDvd (2 ^ 23 - 3 ^ 12) 9 12 49 11 = true := by decide
theorem b23_2_0_7 : noStDvd (2 ^ 23 - 3 ^ 12) 9 11 49 12 = true := by decide
theorem b23_2_0_8 : noStDvd (2 ^ 23 - 3 ^ 12) 9 10 49 13 = true := by decide
theorem b23_2_0_9 : noStDvd (2 ^ 23 - 3 ^ 12) 9 9 49 14 = true := by decide
theorem b23_2_1 : noStDvd (2 ^ 23 - 3 ^ 12) 10 18 11 5 = true := by decide
theorem b23_2_2 : noStDvd (2 ^ 23 - 3 ^ 12) 10 17 11 6 = true := by decide
theorem b23_2_3 : noStDvd (2 ^ 23 - 3 ^ 12) 10 16 11 7 = true := by decide
theorem b23_2_4 : noStDvd (2 ^ 23 - 3 ^ 12) 10 15 11 8 = true := by decide
theorem b23_2_5 : noStDvd (2 ^ 23 - 3 ^ 12) 10 14 11 9 = true := by decide
theorem b23_2_6 : noStDvd (2 ^ 23 - 3 ^ 12) 10 13 11 10 = true := by decide
theorem b23_2_7 : noStDvd (2 ^ 23 - 3 ^ 12) 10 12 11 11 = true := by decide
theorem b23_2_8 : noStDvd (2 ^ 23 - 3 ^ 12) 10 11 11 12 = true := by decide
theorem b23_2_9 : noStDvd (2 ^ 23 - 3 ^ 12) 10 10 11 13 = true := by decide

end CollatzTwelveCycle
