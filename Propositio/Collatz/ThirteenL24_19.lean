import Propositio.Collatz.CycleUniform
import Propositio.Collatz.CycleEnum

namespace CollatzThirteenCycle
open CollatzCycleDecide (steinerVal compositions)
open CollatzCycleEnum (noStDvd noStDvd_top)
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000000

theorem b24_6 : noStDvd (2 ^ 24 - 3 ^ 13) 12 17 1 7 = true := by decide
theorem b24_7 : noStDvd (2 ^ 24 - 3 ^ 13) 12 16 1 8 = true := by decide
theorem b24_8 : noStDvd (2 ^ 24 - 3 ^ 13) 12 15 1 9 = true := by decide
theorem b24_9 : noStDvd (2 ^ 24 - 3 ^ 13) 12 14 1 10 = true := by decide
theorem b24_10 : noStDvd (2 ^ 24 - 3 ^ 13) 12 13 1 11 = true := by decide
theorem b24_11 : noStDvd (2 ^ 24 - 3 ^ 13) 12 12 1 12 = true := by decide

end CollatzThirteenCycle
