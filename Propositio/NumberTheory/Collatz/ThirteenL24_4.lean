import Propositio.NumberTheory.Collatz.CycleUniform
import Propositio.NumberTheory.Collatz.CycleEnum

namespace CollatzThirteenCycle
open CollatzCycleDecide (steinerVal compositions)
open CollatzCycleEnum (noStDvd noStDvd_top)
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000000

theorem b24_0_0_2_1 : noStDvd (2 ^ 24 - 3 ^ 13) 9 17 89 7 = true := by decide
theorem b24_0_0_2_2 : noStDvd (2 ^ 24 - 3 ^ 13) 9 16 89 8 = true := by decide
theorem b24_0_0_2_3 : noStDvd (2 ^ 24 - 3 ^ 13) 9 15 89 9 = true := by decide
theorem b24_0_0_2_4 : noStDvd (2 ^ 24 - 3 ^ 13) 9 14 89 10 = true := by decide
theorem b24_0_0_2_5 : noStDvd (2 ^ 24 - 3 ^ 13) 9 13 89 11 = true := by decide
theorem b24_0_0_2_6 : noStDvd (2 ^ 24 - 3 ^ 13) 9 12 89 12 = true := by decide
theorem b24_0_0_2_7 : noStDvd (2 ^ 24 - 3 ^ 13) 9 11 89 13 = true := by decide
theorem b24_0_0_2_8 : noStDvd (2 ^ 24 - 3 ^ 13) 9 10 89 14 = true := by decide
theorem b24_0_0_2_9 : noStDvd (2 ^ 24 - 3 ^ 13) 9 9 89 15 = true := by decide
theorem b24_0_0_3 : noStDvd (2 ^ 24 - 3 ^ 13) 10 18 19 6 = true := by decide
theorem b24_0_0_4 : noStDvd (2 ^ 24 - 3 ^ 13) 10 17 19 7 = true := by decide
theorem b24_0_0_5 : noStDvd (2 ^ 24 - 3 ^ 13) 10 16 19 8 = true := by decide
theorem b24_0_0_6 : noStDvd (2 ^ 24 - 3 ^ 13) 10 15 19 9 = true := by decide
theorem b24_0_0_7 : noStDvd (2 ^ 24 - 3 ^ 13) 10 14 19 10 = true := by decide
theorem b24_0_0_8 : noStDvd (2 ^ 24 - 3 ^ 13) 10 13 19 11 = true := by decide
theorem b24_0_0_9 : noStDvd (2 ^ 24 - 3 ^ 13) 10 12 19 12 = true := by decide
theorem b24_0_0_10 : noStDvd (2 ^ 24 - 3 ^ 13) 10 11 19 13 = true := by decide
theorem b24_0_0_11 : noStDvd (2 ^ 24 - 3 ^ 13) 10 10 19 14 = true := by decide

end CollatzThirteenCycle
