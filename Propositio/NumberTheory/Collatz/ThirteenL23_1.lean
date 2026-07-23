import Propositio.NumberTheory.Collatz.CycleUniform
import Propositio.NumberTheory.Collatz.CycleEnum

namespace CollatzThirteenCycle
open CollatzCycleDecide (steinerVal compositions)
open CollatzCycleEnum (noStDvd noStDvd_top)
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000000

theorem b23_0_0_0_2 : noStDvd (2 ^ 23 - 3 ^ 13) 9 17 65 6 = true := by decide
theorem b23_0_0_0_3 : noStDvd (2 ^ 23 - 3 ^ 13) 9 16 65 7 = true := by decide
theorem b23_0_0_0_4 : noStDvd (2 ^ 23 - 3 ^ 13) 9 15 65 8 = true := by decide
theorem b23_0_0_0_5 : noStDvd (2 ^ 23 - 3 ^ 13) 9 14 65 9 = true := by decide
theorem b23_0_0_0_6 : noStDvd (2 ^ 23 - 3 ^ 13) 9 13 65 10 = true := by decide
theorem b23_0_0_0_7 : noStDvd (2 ^ 23 - 3 ^ 13) 9 12 65 11 = true := by decide
theorem b23_0_0_0_8 : noStDvd (2 ^ 23 - 3 ^ 13) 9 11 65 12 = true := by decide
theorem b23_0_0_0_9 : noStDvd (2 ^ 23 - 3 ^ 13) 9 10 65 13 = true := by decide
theorem b23_0_0_0_10 : noStDvd (2 ^ 23 - 3 ^ 13) 9 9 65 14 = true := by decide
theorem b23_0_0_1_0 : noStDvd (2 ^ 23 - 3 ^ 13) 9 18 73 5 = true := by decide
theorem b23_0_0_1_1 : noStDvd (2 ^ 23 - 3 ^ 13) 9 17 73 6 = true := by decide
theorem b23_0_0_1_2 : noStDvd (2 ^ 23 - 3 ^ 13) 9 16 73 7 = true := by decide
theorem b23_0_0_1_3 : noStDvd (2 ^ 23 - 3 ^ 13) 9 15 73 8 = true := by decide
theorem b23_0_0_1_4 : noStDvd (2 ^ 23 - 3 ^ 13) 9 14 73 9 = true := by decide
theorem b23_0_0_1_5 : noStDvd (2 ^ 23 - 3 ^ 13) 9 13 73 10 = true := by decide
theorem b23_0_0_1_6 : noStDvd (2 ^ 23 - 3 ^ 13) 9 12 73 11 = true := by decide
theorem b23_0_0_1_7 : noStDvd (2 ^ 23 - 3 ^ 13) 9 11 73 12 = true := by decide
theorem b23_0_0_1_8 : noStDvd (2 ^ 23 - 3 ^ 13) 9 10 73 13 = true := by decide
theorem b23_0_0_1_9 : noStDvd (2 ^ 23 - 3 ^ 13) 9 9 73 14 = true := by decide

end CollatzThirteenCycle
