import Propositio.Collatz.CycleUniform
import Propositio.Collatz.CycleEnum

namespace CollatzThirteenCycle
open CollatzCycleDecide (steinerVal compositions)
open CollatzCycleEnum (noStDvd noStDvd_top)
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000000

theorem b25_0_3_0_1 : noStDvd (2 ^ 25 - 3 ^ 13) 9 17 205 8 = true := by decide
theorem b25_0_3_0_2 : noStDvd (2 ^ 25 - 3 ^ 13) 9 16 205 9 = true := by decide
theorem b25_0_3_0_3 : noStDvd (2 ^ 25 - 3 ^ 13) 9 15 205 10 = true := by decide
theorem b25_0_3_0_4 : noStDvd (2 ^ 25 - 3 ^ 13) 9 14 205 11 = true := by decide
theorem b25_0_3_0_5 : noStDvd (2 ^ 25 - 3 ^ 13) 9 13 205 12 = true := by decide
theorem b25_0_3_0_6 : noStDvd (2 ^ 25 - 3 ^ 13) 9 12 205 13 = true := by decide
theorem b25_0_3_0_7 : noStDvd (2 ^ 25 - 3 ^ 13) 9 11 205 14 = true := by decide
theorem b25_0_3_0_8 : noStDvd (2 ^ 25 - 3 ^ 13) 9 10 205 15 = true := by decide
theorem b25_0_3_0_9 : noStDvd (2 ^ 25 - 3 ^ 13) 9 9 205 16 = true := by decide
theorem b25_0_3_1 : noStDvd (2 ^ 25 - 3 ^ 13) 10 18 47 7 = true := by decide
theorem b25_0_3_2 : noStDvd (2 ^ 25 - 3 ^ 13) 10 17 47 8 = true := by decide
theorem b25_0_3_3 : noStDvd (2 ^ 25 - 3 ^ 13) 10 16 47 9 = true := by decide
theorem b25_0_3_4 : noStDvd (2 ^ 25 - 3 ^ 13) 10 15 47 10 = true := by decide
theorem b25_0_3_5 : noStDvd (2 ^ 25 - 3 ^ 13) 10 14 47 11 = true := by decide
theorem b25_0_3_6 : noStDvd (2 ^ 25 - 3 ^ 13) 10 13 47 12 = true := by decide
theorem b25_0_3_7 : noStDvd (2 ^ 25 - 3 ^ 13) 10 12 47 13 = true := by decide
theorem b25_0_3_8 : noStDvd (2 ^ 25 - 3 ^ 13) 10 11 47 14 = true := by decide
theorem b25_0_3_9 : noStDvd (2 ^ 25 - 3 ^ 13) 10 10 47 15 = true := by decide

end CollatzThirteenCycle
