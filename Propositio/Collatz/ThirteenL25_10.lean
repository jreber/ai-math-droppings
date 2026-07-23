import Propositio.Collatz.CycleUniform
import Propositio.Collatz.CycleEnum

namespace CollatzThirteenCycle
open CollatzCycleDecide (steinerVal compositions)
open CollatzCycleEnum (noStDvd noStDvd_top)
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000000

theorem b25_0_1_0_0_1 : noStDvd (2 ^ 25 - 3 ^ 13) 8 18 287 7 = true := by decide
theorem b25_0_1_0_0_2 : noStDvd (2 ^ 25 - 3 ^ 13) 8 17 287 8 = true := by decide
theorem b25_0_1_0_0_3 : noStDvd (2 ^ 25 - 3 ^ 13) 8 16 287 9 = true := by decide
theorem b25_0_1_0_0_4 : noStDvd (2 ^ 25 - 3 ^ 13) 8 15 287 10 = true := by decide
theorem b25_0_1_0_0_5 : noStDvd (2 ^ 25 - 3 ^ 13) 8 14 287 11 = true := by decide
theorem b25_0_1_0_0_6 : noStDvd (2 ^ 25 - 3 ^ 13) 8 13 287 12 = true := by decide
theorem b25_0_1_0_0_7 : noStDvd (2 ^ 25 - 3 ^ 13) 8 12 287 13 = true := by decide
theorem b25_0_1_0_0_8 : noStDvd (2 ^ 25 - 3 ^ 13) 8 11 287 14 = true := by decide
theorem b25_0_1_0_0_9 : noStDvd (2 ^ 25 - 3 ^ 13) 8 10 287 15 = true := by decide
theorem b25_0_1_0_0_10 : noStDvd (2 ^ 25 - 3 ^ 13) 8 9 287 16 = true := by decide
theorem b25_0_1_0_0_11 : noStDvd (2 ^ 25 - 3 ^ 13) 8 8 287 17 = true := by decide

end CollatzThirteenCycle
