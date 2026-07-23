import Propositio.NumberTheory.Collatz.CycleUniform
import Propositio.NumberTheory.Collatz.CycleEnum

namespace CollatzThirteenCycle
open CollatzCycleDecide (steinerVal compositions)
open CollatzCycleEnum (noStDvd noStDvd_top)
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000000

theorem b24_0_1_2 : noStDvd (2 ^ 24 - 3 ^ 13) 10 18 23 6 = true := by decide
theorem b24_0_1_3 : noStDvd (2 ^ 24 - 3 ^ 13) 10 17 23 7 = true := by decide
theorem b24_0_1_4 : noStDvd (2 ^ 24 - 3 ^ 13) 10 16 23 8 = true := by decide
theorem b24_0_1_5 : noStDvd (2 ^ 24 - 3 ^ 13) 10 15 23 9 = true := by decide
theorem b24_0_1_6 : noStDvd (2 ^ 24 - 3 ^ 13) 10 14 23 10 = true := by decide
theorem b24_0_1_7 : noStDvd (2 ^ 24 - 3 ^ 13) 10 13 23 11 = true := by decide
theorem b24_0_1_8 : noStDvd (2 ^ 24 - 3 ^ 13) 10 12 23 12 = true := by decide
theorem b24_0_1_9 : noStDvd (2 ^ 24 - 3 ^ 13) 10 11 23 13 = true := by decide
theorem b24_0_1_10 : noStDvd (2 ^ 24 - 3 ^ 13) 10 10 23 14 = true := by decide
theorem b24_0_2_0_0 : noStDvd (2 ^ 24 - 3 ^ 13) 9 18 125 6 = true := by decide

end CollatzThirteenCycle
