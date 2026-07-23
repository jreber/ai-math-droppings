import Propositio.Collatz.CycleUniform
import Propositio.Collatz.CycleEnum

namespace CollatzThirteenCycle
open CollatzCycleDecide (steinerVal compositions)
open CollatzCycleEnum (noStDvd noStDvd_top)
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000000

theorem b24_0_2_0_1 : noStDvd (2 ^ 24 - 3 ^ 13) 9 17 125 7 = true := by decide
theorem b24_0_2_0_2 : noStDvd (2 ^ 24 - 3 ^ 13) 9 16 125 8 = true := by decide
theorem b24_0_2_0_3 : noStDvd (2 ^ 24 - 3 ^ 13) 9 15 125 9 = true := by decide
theorem b24_0_2_0_4 : noStDvd (2 ^ 24 - 3 ^ 13) 9 14 125 10 = true := by decide
theorem b24_0_2_0_5 : noStDvd (2 ^ 24 - 3 ^ 13) 9 13 125 11 = true := by decide
theorem b24_0_2_0_6 : noStDvd (2 ^ 24 - 3 ^ 13) 9 12 125 12 = true := by decide
theorem b24_0_2_0_7 : noStDvd (2 ^ 24 - 3 ^ 13) 9 11 125 13 = true := by decide
theorem b24_0_2_0_8 : noStDvd (2 ^ 24 - 3 ^ 13) 9 10 125 14 = true := by decide
theorem b24_0_2_0_9 : noStDvd (2 ^ 24 - 3 ^ 13) 9 9 125 15 = true := by decide
theorem b24_0_2_1 : noStDvd (2 ^ 24 - 3 ^ 13) 10 18 31 6 = true := by decide
theorem b24_0_2_2 : noStDvd (2 ^ 24 - 3 ^ 13) 10 17 31 7 = true := by decide
theorem b24_0_2_3 : noStDvd (2 ^ 24 - 3 ^ 13) 10 16 31 8 = true := by decide
theorem b24_0_2_4 : noStDvd (2 ^ 24 - 3 ^ 13) 10 15 31 9 = true := by decide
theorem b24_0_2_5 : noStDvd (2 ^ 24 - 3 ^ 13) 10 14 31 10 = true := by decide
theorem b24_0_2_6 : noStDvd (2 ^ 24 - 3 ^ 13) 10 13 31 11 = true := by decide
theorem b24_0_2_7 : noStDvd (2 ^ 24 - 3 ^ 13) 10 12 31 12 = true := by decide
theorem b24_0_2_8 : noStDvd (2 ^ 24 - 3 ^ 13) 10 11 31 13 = true := by decide
theorem b24_0_2_9 : noStDvd (2 ^ 24 - 3 ^ 13) 10 10 31 14 = true := by decide

end CollatzThirteenCycle
