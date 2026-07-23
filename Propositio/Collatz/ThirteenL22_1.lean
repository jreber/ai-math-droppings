import Propositio.Collatz.CycleUniform
import Propositio.Collatz.CycleEnum

namespace CollatzThirteenCycle
open CollatzCycleDecide (steinerVal compositions)
open CollatzCycleEnum (noStDvd noStDvd_top)
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000000

theorem b22_0_0_2 : noStDvd (2 ^ 22 - 3 ^ 13) 10 17 19 5 = true := by decide
theorem b22_0_0_3 : noStDvd (2 ^ 22 - 3 ^ 13) 10 16 19 6 = true := by decide
theorem b22_0_0_4 : noStDvd (2 ^ 22 - 3 ^ 13) 10 15 19 7 = true := by decide
theorem b22_0_0_5 : noStDvd (2 ^ 22 - 3 ^ 13) 10 14 19 8 = true := by decide
theorem b22_0_0_6 : noStDvd (2 ^ 22 - 3 ^ 13) 10 13 19 9 = true := by decide
theorem b22_0_0_7 : noStDvd (2 ^ 22 - 3 ^ 13) 10 12 19 10 = true := by decide
theorem b22_0_0_8 : noStDvd (2 ^ 22 - 3 ^ 13) 10 11 19 11 = true := by decide
theorem b22_0_0_9 : noStDvd (2 ^ 22 - 3 ^ 13) 10 10 19 12 = true := by decide
theorem b22_0_1 : noStDvd (2 ^ 22 - 3 ^ 13) 11 19 5 3 = true := by decide

end CollatzThirteenCycle
