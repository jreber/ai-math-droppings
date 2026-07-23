import Propositio.NumberTheory.Collatz.CycleUniform
import Propositio.NumberTheory.Collatz.CycleEnum

namespace CollatzThirteenCycle
open CollatzCycleDecide (steinerVal compositions)
open CollatzCycleEnum (noStDvd noStDvd_top)
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000000

theorem b24_0_0_1_1 : noStDvd (2 ^ 24 - 3 ^ 13) 9 18 73 6 = true := by decide
theorem b24_0_0_1_2 : noStDvd (2 ^ 24 - 3 ^ 13) 9 17 73 7 = true := by decide
theorem b24_0_0_1_3 : noStDvd (2 ^ 24 - 3 ^ 13) 9 16 73 8 = true := by decide
theorem b24_0_0_1_4 : noStDvd (2 ^ 24 - 3 ^ 13) 9 15 73 9 = true := by decide
theorem b24_0_0_1_5 : noStDvd (2 ^ 24 - 3 ^ 13) 9 14 73 10 = true := by decide
theorem b24_0_0_1_6 : noStDvd (2 ^ 24 - 3 ^ 13) 9 13 73 11 = true := by decide
theorem b24_0_0_1_7 : noStDvd (2 ^ 24 - 3 ^ 13) 9 12 73 12 = true := by decide
theorem b24_0_0_1_8 : noStDvd (2 ^ 24 - 3 ^ 13) 9 11 73 13 = true := by decide
theorem b24_0_0_1_9 : noStDvd (2 ^ 24 - 3 ^ 13) 9 10 73 14 = true := by decide
theorem b24_0_0_1_10 : noStDvd (2 ^ 24 - 3 ^ 13) 9 9 73 15 = true := by decide
theorem b24_0_0_2_0 : noStDvd (2 ^ 24 - 3 ^ 13) 9 18 89 6 = true := by decide

end CollatzThirteenCycle
