import Propositio.Collatz.CycleUniform
import Propositio.Collatz.CycleEnum

namespace CollatzThirteenCycle
open CollatzCycleDecide (steinerVal compositions)
open CollatzCycleEnum (noStDvd noStDvd_top)
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000000

theorem b25_0_0_0_1_0 : noStDvd (2 ^ 25 - 3 ^ 13) 8 19 227 6 = true := by decide
theorem b25_0_0_0_1_1 : noStDvd (2 ^ 25 - 3 ^ 13) 8 18 227 7 = true := by decide
theorem b25_0_0_0_1_2 : noStDvd (2 ^ 25 - 3 ^ 13) 8 17 227 8 = true := by decide
theorem b25_0_0_0_1_3 : noStDvd (2 ^ 25 - 3 ^ 13) 8 16 227 9 = true := by decide
theorem b25_0_0_0_1_4 : noStDvd (2 ^ 25 - 3 ^ 13) 8 15 227 10 = true := by decide
theorem b25_0_0_0_1_5 : noStDvd (2 ^ 25 - 3 ^ 13) 8 14 227 11 = true := by decide
theorem b25_0_0_0_1_6 : noStDvd (2 ^ 25 - 3 ^ 13) 8 13 227 12 = true := by decide
theorem b25_0_0_0_1_7 : noStDvd (2 ^ 25 - 3 ^ 13) 8 12 227 13 = true := by decide
theorem b25_0_0_0_1_8 : noStDvd (2 ^ 25 - 3 ^ 13) 8 11 227 14 = true := by decide
theorem b25_0_0_0_1_9 : noStDvd (2 ^ 25 - 3 ^ 13) 8 10 227 15 = true := by decide
theorem b25_0_0_0_1_10 : noStDvd (2 ^ 25 - 3 ^ 13) 8 9 227 16 = true := by decide
theorem b25_0_0_0_1_11 : noStDvd (2 ^ 25 - 3 ^ 13) 8 8 227 17 = true := by decide

end CollatzThirteenCycle
