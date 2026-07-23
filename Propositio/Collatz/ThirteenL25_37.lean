import Propositio.Collatz.CycleUniform
import Propositio.Collatz.CycleEnum

namespace CollatzThirteenCycle
open CollatzCycleDecide (steinerVal compositions)
open CollatzCycleEnum (noStDvd noStDvd_top)
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000000

theorem b25_3_2 : noStDvd (2 ^ 25 - 3 ^ 13) 11 18 19 7 = true := by decide
theorem b25_3_3 : noStDvd (2 ^ 25 - 3 ^ 13) 11 17 19 8 = true := by decide
theorem b25_3_4 : noStDvd (2 ^ 25 - 3 ^ 13) 11 16 19 9 = true := by decide
theorem b25_3_5 : noStDvd (2 ^ 25 - 3 ^ 13) 11 15 19 10 = true := by decide
theorem b25_3_6 : noStDvd (2 ^ 25 - 3 ^ 13) 11 14 19 11 = true := by decide
theorem b25_3_7 : noStDvd (2 ^ 25 - 3 ^ 13) 11 13 19 12 = true := by decide
theorem b25_3_8 : noStDvd (2 ^ 25 - 3 ^ 13) 11 12 19 13 = true := by decide
theorem b25_3_9 : noStDvd (2 ^ 25 - 3 ^ 13) 11 11 19 14 = true := by decide
theorem b25_4_0 : noStDvd (2 ^ 25 - 3 ^ 13) 11 19 35 6 = true := by decide

end CollatzThirteenCycle
