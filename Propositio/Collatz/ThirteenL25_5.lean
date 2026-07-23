import Propositio.Collatz.CycleUniform
import Propositio.Collatz.CycleEnum

namespace CollatzThirteenCycle
open CollatzCycleDecide (steinerVal compositions)
open CollatzCycleEnum (noStDvd noStDvd_top)
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000000

theorem b25_0_0_1_0_2 : noStDvd (2 ^ 25 - 3 ^ 13) 8 17 251 8 = true := by decide
theorem b25_0_0_1_0_3 : noStDvd (2 ^ 25 - 3 ^ 13) 8 16 251 9 = true := by decide
theorem b25_0_0_1_0_4 : noStDvd (2 ^ 25 - 3 ^ 13) 8 15 251 10 = true := by decide
theorem b25_0_0_1_0_5 : noStDvd (2 ^ 25 - 3 ^ 13) 8 14 251 11 = true := by decide
theorem b25_0_0_1_0_6 : noStDvd (2 ^ 25 - 3 ^ 13) 8 13 251 12 = true := by decide
theorem b25_0_0_1_0_7 : noStDvd (2 ^ 25 - 3 ^ 13) 8 12 251 13 = true := by decide
theorem b25_0_0_1_0_8 : noStDvd (2 ^ 25 - 3 ^ 13) 8 11 251 14 = true := by decide
theorem b25_0_0_1_0_9 : noStDvd (2 ^ 25 - 3 ^ 13) 8 10 251 15 = true := by decide
theorem b25_0_0_1_0_10 : noStDvd (2 ^ 25 - 3 ^ 13) 8 9 251 16 = true := by decide
theorem b25_0_0_1_0_11 : noStDvd (2 ^ 25 - 3 ^ 13) 8 8 251 17 = true := by decide
theorem b25_0_0_1_1 : noStDvd (2 ^ 25 - 3 ^ 13) 9 19 73 6 = true := by decide

end CollatzThirteenCycle
