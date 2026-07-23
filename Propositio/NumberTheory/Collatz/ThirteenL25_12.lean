import Propositio.NumberTheory.Collatz.CycleUniform
import Propositio.NumberTheory.Collatz.CycleEnum

namespace CollatzThirteenCycle
open CollatzCycleDecide (steinerVal compositions)
open CollatzCycleEnum (noStDvd noStDvd_top)
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000000

theorem b25_0_1_0_3 : noStDvd (2 ^ 25 - 3 ^ 13) 9 17 85 8 = true := by decide
theorem b25_0_1_0_4 : noStDvd (2 ^ 25 - 3 ^ 13) 9 16 85 9 = true := by decide
theorem b25_0_1_0_5 : noStDvd (2 ^ 25 - 3 ^ 13) 9 15 85 10 = true := by decide
theorem b25_0_1_0_6 : noStDvd (2 ^ 25 - 3 ^ 13) 9 14 85 11 = true := by decide
theorem b25_0_1_0_7 : noStDvd (2 ^ 25 - 3 ^ 13) 9 13 85 12 = true := by decide
theorem b25_0_1_0_8 : noStDvd (2 ^ 25 - 3 ^ 13) 9 12 85 13 = true := by decide
theorem b25_0_1_0_9 : noStDvd (2 ^ 25 - 3 ^ 13) 9 11 85 14 = true := by decide
theorem b25_0_1_0_10 : noStDvd (2 ^ 25 - 3 ^ 13) 9 10 85 15 = true := by decide
theorem b25_0_1_0_11 : noStDvd (2 ^ 25 - 3 ^ 13) 9 9 85 16 = true := by decide
theorem b25_0_1_1_0 : noStDvd (2 ^ 25 - 3 ^ 13) 9 19 101 6 = true := by decide

end CollatzThirteenCycle
