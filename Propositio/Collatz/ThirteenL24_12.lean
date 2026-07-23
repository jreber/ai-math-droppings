import Propositio.Collatz.CycleUniform
import Propositio.Collatz.CycleEnum

namespace CollatzThirteenCycle
open CollatzCycleDecide (steinerVal compositions)
open CollatzCycleEnum (noStDvd noStDvd_top)
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000000

theorem b24_1_0_2 : noStDvd (2 ^ 24 - 3 ^ 13) 10 18 29 6 = true := by decide
theorem b24_1_0_3 : noStDvd (2 ^ 24 - 3 ^ 13) 10 17 29 7 = true := by decide
theorem b24_1_0_4 : noStDvd (2 ^ 24 - 3 ^ 13) 10 16 29 8 = true := by decide
theorem b24_1_0_5 : noStDvd (2 ^ 24 - 3 ^ 13) 10 15 29 9 = true := by decide
theorem b24_1_0_6 : noStDvd (2 ^ 24 - 3 ^ 13) 10 14 29 10 = true := by decide
theorem b24_1_0_7 : noStDvd (2 ^ 24 - 3 ^ 13) 10 13 29 11 = true := by decide
theorem b24_1_0_8 : noStDvd (2 ^ 24 - 3 ^ 13) 10 12 29 12 = true := by decide
theorem b24_1_0_9 : noStDvd (2 ^ 24 - 3 ^ 13) 10 11 29 13 = true := by decide
theorem b24_1_0_10 : noStDvd (2 ^ 24 - 3 ^ 13) 10 10 29 14 = true := by decide
theorem b24_1_1_0_0 : noStDvd (2 ^ 24 - 3 ^ 13) 9 18 143 6 = true := by decide

end CollatzThirteenCycle
