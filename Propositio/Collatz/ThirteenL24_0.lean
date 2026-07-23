import Propositio.Collatz.CycleUniform
import Propositio.Collatz.CycleEnum

namespace CollatzThirteenCycle
open CollatzCycleDecide (steinerVal compositions)
open CollatzCycleEnum (noStDvd noStDvd_top)
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000000

theorem b24_0_0_0_0_0 : noStDvd (2 ^ 24 - 3 ^ 13) 8 19 211 5 = true := by decide
theorem b24_0_0_0_0_1 : noStDvd (2 ^ 24 - 3 ^ 13) 8 18 211 6 = true := by decide
theorem b24_0_0_0_0_2 : noStDvd (2 ^ 24 - 3 ^ 13) 8 17 211 7 = true := by decide
theorem b24_0_0_0_0_3 : noStDvd (2 ^ 24 - 3 ^ 13) 8 16 211 8 = true := by decide
theorem b24_0_0_0_0_4 : noStDvd (2 ^ 24 - 3 ^ 13) 8 15 211 9 = true := by decide
theorem b24_0_0_0_0_5 : noStDvd (2 ^ 24 - 3 ^ 13) 8 14 211 10 = true := by decide
theorem b24_0_0_0_0_6 : noStDvd (2 ^ 24 - 3 ^ 13) 8 13 211 11 = true := by decide
theorem b24_0_0_0_0_7 : noStDvd (2 ^ 24 - 3 ^ 13) 8 12 211 12 = true := by decide
theorem b24_0_0_0_0_8 : noStDvd (2 ^ 24 - 3 ^ 13) 8 11 211 13 = true := by decide
theorem b24_0_0_0_0_9 : noStDvd (2 ^ 24 - 3 ^ 13) 8 10 211 14 = true := by decide
theorem b24_0_0_0_0_10 : noStDvd (2 ^ 24 - 3 ^ 13) 8 9 211 15 = true := by decide
theorem b24_0_0_0_0_11 : noStDvd (2 ^ 24 - 3 ^ 13) 8 8 211 16 = true := by decide

end CollatzThirteenCycle
