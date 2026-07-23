import Propositio.Collatz.CycleUniform
import Propositio.Collatz.CycleEnum

namespace CollatzThirteenCycle
open CollatzCycleDecide (steinerVal compositions)
open CollatzCycleEnum (noStDvd noStDvd_top)
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000000

theorem b24_1_1_0_1 : noStDvd (2 ^ 24 - 3 ^ 13) 9 17 143 7 = true := by decide
theorem b24_1_1_0_2 : noStDvd (2 ^ 24 - 3 ^ 13) 9 16 143 8 = true := by decide
theorem b24_1_1_0_3 : noStDvd (2 ^ 24 - 3 ^ 13) 9 15 143 9 = true := by decide
theorem b24_1_1_0_4 : noStDvd (2 ^ 24 - 3 ^ 13) 9 14 143 10 = true := by decide
theorem b24_1_1_0_5 : noStDvd (2 ^ 24 - 3 ^ 13) 9 13 143 11 = true := by decide
theorem b24_1_1_0_6 : noStDvd (2 ^ 24 - 3 ^ 13) 9 12 143 12 = true := by decide
theorem b24_1_1_0_7 : noStDvd (2 ^ 24 - 3 ^ 13) 9 11 143 13 = true := by decide
theorem b24_1_1_0_8 : noStDvd (2 ^ 24 - 3 ^ 13) 9 10 143 14 = true := by decide
theorem b24_1_1_0_9 : noStDvd (2 ^ 24 - 3 ^ 13) 9 9 143 15 = true := by decide
theorem b24_1_1_1 : noStDvd (2 ^ 24 - 3 ^ 13) 10 18 37 6 = true := by decide
theorem b24_1_1_2 : noStDvd (2 ^ 24 - 3 ^ 13) 10 17 37 7 = true := by decide
theorem b24_1_1_3 : noStDvd (2 ^ 24 - 3 ^ 13) 10 16 37 8 = true := by decide
theorem b24_1_1_4 : noStDvd (2 ^ 24 - 3 ^ 13) 10 15 37 9 = true := by decide
theorem b24_1_1_5 : noStDvd (2 ^ 24 - 3 ^ 13) 10 14 37 10 = true := by decide
theorem b24_1_1_6 : noStDvd (2 ^ 24 - 3 ^ 13) 10 13 37 11 = true := by decide
theorem b24_1_1_7 : noStDvd (2 ^ 24 - 3 ^ 13) 10 12 37 12 = true := by decide
theorem b24_1_1_8 : noStDvd (2 ^ 24 - 3 ^ 13) 10 11 37 13 = true := by decide
theorem b24_1_1_9 : noStDvd (2 ^ 24 - 3 ^ 13) 10 10 37 14 = true := by decide

end CollatzThirteenCycle
