import Propositio.Collatz.CycleUniform
import Propositio.Collatz.CycleEnum

namespace CollatzThirteenCycle
open CollatzCycleDecide (steinerVal compositions)
open CollatzCycleEnum (noStDvd noStDvd_top)
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000000

theorem b25_0_4 : noStDvd (2 ^ 25 - 3 ^ 13) 11 19 5 6 = true := by decide
theorem b25_0_5 : noStDvd (2 ^ 25 - 3 ^ 13) 11 18 5 7 = true := by decide
theorem b25_0_6 : noStDvd (2 ^ 25 - 3 ^ 13) 11 17 5 8 = true := by decide
theorem b25_0_7 : noStDvd (2 ^ 25 - 3 ^ 13) 11 16 5 9 = true := by decide
theorem b25_0_8 : noStDvd (2 ^ 25 - 3 ^ 13) 11 15 5 10 = true := by decide
theorem b25_0_9 : noStDvd (2 ^ 25 - 3 ^ 13) 11 14 5 11 = true := by decide
theorem b25_0_10 : noStDvd (2 ^ 25 - 3 ^ 13) 11 13 5 12 = true := by decide
theorem b25_0_11 : noStDvd (2 ^ 25 - 3 ^ 13) 11 12 5 13 = true := by decide
theorem b25_0_12 : noStDvd (2 ^ 25 - 3 ^ 13) 11 11 5 14 = true := by decide

end CollatzThirteenCycle
