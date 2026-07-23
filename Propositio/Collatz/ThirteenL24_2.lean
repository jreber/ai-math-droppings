import Propositio.Collatz.CycleUniform
import Propositio.Collatz.CycleEnum

namespace CollatzThirteenCycle
open CollatzCycleDecide (steinerVal compositions)
open CollatzCycleEnum (noStDvd noStDvd_top)
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000000

theorem b24_0_0_0_3 : noStDvd (2 ^ 24 - 3 ^ 13) 9 17 65 7 = true := by decide
theorem b24_0_0_0_4 : noStDvd (2 ^ 24 - 3 ^ 13) 9 16 65 8 = true := by decide
theorem b24_0_0_0_5 : noStDvd (2 ^ 24 - 3 ^ 13) 9 15 65 9 = true := by decide
theorem b24_0_0_0_6 : noStDvd (2 ^ 24 - 3 ^ 13) 9 14 65 10 = true := by decide
theorem b24_0_0_0_7 : noStDvd (2 ^ 24 - 3 ^ 13) 9 13 65 11 = true := by decide
theorem b24_0_0_0_8 : noStDvd (2 ^ 24 - 3 ^ 13) 9 12 65 12 = true := by decide
theorem b24_0_0_0_9 : noStDvd (2 ^ 24 - 3 ^ 13) 9 11 65 13 = true := by decide
theorem b24_0_0_0_10 : noStDvd (2 ^ 24 - 3 ^ 13) 9 10 65 14 = true := by decide
theorem b24_0_0_0_11 : noStDvd (2 ^ 24 - 3 ^ 13) 9 9 65 15 = true := by decide
theorem b24_0_0_1_0 : noStDvd (2 ^ 24 - 3 ^ 13) 9 19 73 5 = true := by decide

end CollatzThirteenCycle
