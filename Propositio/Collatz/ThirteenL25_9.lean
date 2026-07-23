import Propositio.Collatz.CycleUniform
import Propositio.Collatz.CycleEnum

namespace CollatzThirteenCycle
open CollatzCycleDecide (steinerVal compositions)
open CollatzCycleEnum (noStDvd noStDvd_top)
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000000

theorem b25_0_0_4 : noStDvd (2 ^ 25 - 3 ^ 13) 10 18 19 7 = true := by decide
theorem b25_0_0_5 : noStDvd (2 ^ 25 - 3 ^ 13) 10 17 19 8 = true := by decide
theorem b25_0_0_6 : noStDvd (2 ^ 25 - 3 ^ 13) 10 16 19 9 = true := by decide
theorem b25_0_0_7 : noStDvd (2 ^ 25 - 3 ^ 13) 10 15 19 10 = true := by decide
theorem b25_0_0_8 : noStDvd (2 ^ 25 - 3 ^ 13) 10 14 19 11 = true := by decide
theorem b25_0_0_9 : noStDvd (2 ^ 25 - 3 ^ 13) 10 13 19 12 = true := by decide
theorem b25_0_0_10 : noStDvd (2 ^ 25 - 3 ^ 13) 10 12 19 13 = true := by decide
theorem b25_0_0_11 : noStDvd (2 ^ 25 - 3 ^ 13) 10 11 19 14 = true := by decide
theorem b25_0_0_12 : noStDvd (2 ^ 25 - 3 ^ 13) 10 10 19 15 = true := by decide
theorem b25_0_1_0_0_0 : noStDvd (2 ^ 25 - 3 ^ 13) 8 19 287 6 = true := by decide

end CollatzThirteenCycle
