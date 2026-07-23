import Propositio.Collatz.CycleUniform
import Propositio.Collatz.CycleEnum

namespace CollatzThirteenCycle
open CollatzCycleDecide (steinerVal compositions)
open CollatzCycleEnum (noStDvd noStDvd_top)
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000000

theorem b25_1_0_1_1 : noStDvd (2 ^ 25 - 3 ^ 13) 9 18 119 7 = true := by decide
theorem b25_1_0_1_2 : noStDvd (2 ^ 25 - 3 ^ 13) 9 17 119 8 = true := by decide
theorem b25_1_0_1_3 : noStDvd (2 ^ 25 - 3 ^ 13) 9 16 119 9 = true := by decide
theorem b25_1_0_1_4 : noStDvd (2 ^ 25 - 3 ^ 13) 9 15 119 10 = true := by decide
theorem b25_1_0_1_5 : noStDvd (2 ^ 25 - 3 ^ 13) 9 14 119 11 = true := by decide
theorem b25_1_0_1_6 : noStDvd (2 ^ 25 - 3 ^ 13) 9 13 119 12 = true := by decide
theorem b25_1_0_1_7 : noStDvd (2 ^ 25 - 3 ^ 13) 9 12 119 13 = true := by decide
theorem b25_1_0_1_8 : noStDvd (2 ^ 25 - 3 ^ 13) 9 11 119 14 = true := by decide
theorem b25_1_0_1_9 : noStDvd (2 ^ 25 - 3 ^ 13) 9 10 119 15 = true := by decide
theorem b25_1_0_1_10 : noStDvd (2 ^ 25 - 3 ^ 13) 9 9 119 16 = true := by decide
theorem b25_1_0_2_0 : noStDvd (2 ^ 25 - 3 ^ 13) 9 18 151 7 = true := by decide

end CollatzThirteenCycle
