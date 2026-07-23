import Propositio.NumberTheory.Collatz.CycleUniform
import Propositio.NumberTheory.Collatz.CycleEnum

namespace CollatzThirteenCycle
open CollatzCycleDecide (steinerVal compositions)
open CollatzCycleEnum (noStDvd noStDvd_top)
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000000

theorem b23_1_0_2 : noStDvd (2 ^ 23 - 3 ^ 13) 10 17 29 6 = true := by decide
theorem b23_1_0_3 : noStDvd (2 ^ 23 - 3 ^ 13) 10 16 29 7 = true := by decide
theorem b23_1_0_4 : noStDvd (2 ^ 23 - 3 ^ 13) 10 15 29 8 = true := by decide
theorem b23_1_0_5 : noStDvd (2 ^ 23 - 3 ^ 13) 10 14 29 9 = true := by decide
theorem b23_1_0_6 : noStDvd (2 ^ 23 - 3 ^ 13) 10 13 29 10 = true := by decide
theorem b23_1_0_7 : noStDvd (2 ^ 23 - 3 ^ 13) 10 12 29 11 = true := by decide
theorem b23_1_0_8 : noStDvd (2 ^ 23 - 3 ^ 13) 10 11 29 12 = true := by decide
theorem b23_1_0_9 : noStDvd (2 ^ 23 - 3 ^ 13) 10 10 29 13 = true := by decide
theorem b23_1_1 : noStDvd (2 ^ 23 - 3 ^ 13) 11 19 7 4 = true := by decide

end CollatzThirteenCycle
