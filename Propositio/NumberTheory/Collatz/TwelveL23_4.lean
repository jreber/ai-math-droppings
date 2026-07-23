import Propositio.NumberTheory.Collatz.CycleUniform
import Propositio.NumberTheory.Collatz.CycleEnum

namespace CollatzTwelveCycle
open CollatzCycleDecide (steinerVal compositions)
open CollatzCycleEnum (noStDvd noStDvd_top)
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000000

theorem b23_0_2_1 : noStDvd (2 ^ 23 - 3 ^ 12) 9 17 31 6 = true := by decide
theorem b23_0_2_2 : noStDvd (2 ^ 23 - 3 ^ 12) 9 16 31 7 = true := by decide
theorem b23_0_2_3 : noStDvd (2 ^ 23 - 3 ^ 12) 9 15 31 8 = true := by decide
theorem b23_0_2_4 : noStDvd (2 ^ 23 - 3 ^ 12) 9 14 31 9 = true := by decide
theorem b23_0_2_5 : noStDvd (2 ^ 23 - 3 ^ 12) 9 13 31 10 = true := by decide
theorem b23_0_2_6 : noStDvd (2 ^ 23 - 3 ^ 12) 9 12 31 11 = true := by decide
theorem b23_0_2_7 : noStDvd (2 ^ 23 - 3 ^ 12) 9 11 31 12 = true := by decide
theorem b23_0_2_8 : noStDvd (2 ^ 23 - 3 ^ 12) 9 10 31 13 = true := by decide
theorem b23_0_2_9 : noStDvd (2 ^ 23 - 3 ^ 12) 9 9 31 14 = true := by decide
theorem b23_0_3 : noStDvd (2 ^ 23 - 3 ^ 12) 10 18 5 5 = true := by decide
theorem b23_0_4 : noStDvd (2 ^ 23 - 3 ^ 12) 10 17 5 6 = true := by decide
theorem b23_0_5 : noStDvd (2 ^ 23 - 3 ^ 12) 10 16 5 7 = true := by decide
theorem b23_0_6 : noStDvd (2 ^ 23 - 3 ^ 12) 10 15 5 8 = true := by decide
theorem b23_0_7 : noStDvd (2 ^ 23 - 3 ^ 12) 10 14 5 9 = true := by decide
theorem b23_0_8 : noStDvd (2 ^ 23 - 3 ^ 12) 10 13 5 10 = true := by decide
theorem b23_0_9 : noStDvd (2 ^ 23 - 3 ^ 12) 10 12 5 11 = true := by decide
theorem b23_0_10 : noStDvd (2 ^ 23 - 3 ^ 12) 10 11 5 12 = true := by decide
theorem b23_0_11 : noStDvd (2 ^ 23 - 3 ^ 12) 10 10 5 13 = true := by decide

end CollatzTwelveCycle
