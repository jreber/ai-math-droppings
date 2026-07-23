import Propositio.Collatz.CycleUniform
import Propositio.Collatz.CycleEnum

namespace CollatzThirteenCycle
open CollatzCycleDecide (steinerVal compositions)
open CollatzCycleEnum (noStDvd noStDvd_top)
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000000

theorem b25_2_0_2 : noStDvd (2 ^ 25 - 3 ^ 13) 10 18 49 7 = true := by decide
theorem b25_2_0_3 : noStDvd (2 ^ 25 - 3 ^ 13) 10 17 49 8 = true := by decide
theorem b25_2_0_4 : noStDvd (2 ^ 25 - 3 ^ 13) 10 16 49 9 = true := by decide
theorem b25_2_0_5 : noStDvd (2 ^ 25 - 3 ^ 13) 10 15 49 10 = true := by decide
theorem b25_2_0_6 : noStDvd (2 ^ 25 - 3 ^ 13) 10 14 49 11 = true := by decide
theorem b25_2_0_7 : noStDvd (2 ^ 25 - 3 ^ 13) 10 13 49 12 = true := by decide
theorem b25_2_0_8 : noStDvd (2 ^ 25 - 3 ^ 13) 10 12 49 13 = true := by decide
theorem b25_2_0_9 : noStDvd (2 ^ 25 - 3 ^ 13) 10 11 49 14 = true := by decide
theorem b25_2_0_10 : noStDvd (2 ^ 25 - 3 ^ 13) 10 10 49 15 = true := by decide
theorem b25_2_1_0_0 : noStDvd (2 ^ 25 - 3 ^ 13) 9 18 259 7 = true := by decide

end CollatzThirteenCycle
