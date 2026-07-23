import Propositio.Collatz.CycleUniform
import Propositio.Collatz.CycleEnum

namespace CollatzThirteenCycle
open CollatzCycleDecide (steinerVal compositions)
open CollatzCycleEnum (noStDvd noStDvd_top)
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000000

theorem b25_0_0_1_2 : noStDvd (2 ^ 25 - 3 ^ 13) 9 18 73 7 = true := by decide
theorem b25_0_0_1_3 : noStDvd (2 ^ 25 - 3 ^ 13) 9 17 73 8 = true := by decide
theorem b25_0_0_1_4 : noStDvd (2 ^ 25 - 3 ^ 13) 9 16 73 9 = true := by decide
theorem b25_0_0_1_5 : noStDvd (2 ^ 25 - 3 ^ 13) 9 15 73 10 = true := by decide
theorem b25_0_0_1_6 : noStDvd (2 ^ 25 - 3 ^ 13) 9 14 73 11 = true := by decide
theorem b25_0_0_1_7 : noStDvd (2 ^ 25 - 3 ^ 13) 9 13 73 12 = true := by decide
theorem b25_0_0_1_8 : noStDvd (2 ^ 25 - 3 ^ 13) 9 12 73 13 = true := by decide
theorem b25_0_0_1_9 : noStDvd (2 ^ 25 - 3 ^ 13) 9 11 73 14 = true := by decide
theorem b25_0_0_1_10 : noStDvd (2 ^ 25 - 3 ^ 13) 9 10 73 15 = true := by decide
theorem b25_0_0_1_11 : noStDvd (2 ^ 25 - 3 ^ 13) 9 9 73 16 = true := by decide

end CollatzThirteenCycle
