import Propositio.NumberTheory.Collatz.CycleUniform
import Propositio.NumberTheory.Collatz.CycleEnum

namespace CollatzThirteenCycle
open CollatzCycleDecide (steinerVal compositions)
open CollatzCycleEnum (noStDvd noStDvd_top)
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000000

theorem b24_1_0_0_2 : noStDvd (2 ^ 24 - 3 ^ 13) 9 17 103 7 = true := by decide
theorem b24_1_0_0_3 : noStDvd (2 ^ 24 - 3 ^ 13) 9 16 103 8 = true := by decide
theorem b24_1_0_0_4 : noStDvd (2 ^ 24 - 3 ^ 13) 9 15 103 9 = true := by decide
theorem b24_1_0_0_5 : noStDvd (2 ^ 24 - 3 ^ 13) 9 14 103 10 = true := by decide
theorem b24_1_0_0_6 : noStDvd (2 ^ 24 - 3 ^ 13) 9 13 103 11 = true := by decide
theorem b24_1_0_0_7 : noStDvd (2 ^ 24 - 3 ^ 13) 9 12 103 12 = true := by decide
theorem b24_1_0_0_8 : noStDvd (2 ^ 24 - 3 ^ 13) 9 11 103 13 = true := by decide
theorem b24_1_0_0_9 : noStDvd (2 ^ 24 - 3 ^ 13) 9 10 103 14 = true := by decide
theorem b24_1_0_0_10 : noStDvd (2 ^ 24 - 3 ^ 13) 9 9 103 15 = true := by decide
theorem b24_1_0_1_0 : noStDvd (2 ^ 24 - 3 ^ 13) 9 18 119 6 = true := by decide
theorem b24_1_0_1_1 : noStDvd (2 ^ 24 - 3 ^ 13) 9 17 119 7 = true := by decide
theorem b24_1_0_1_2 : noStDvd (2 ^ 24 - 3 ^ 13) 9 16 119 8 = true := by decide
theorem b24_1_0_1_3 : noStDvd (2 ^ 24 - 3 ^ 13) 9 15 119 9 = true := by decide
theorem b24_1_0_1_4 : noStDvd (2 ^ 24 - 3 ^ 13) 9 14 119 10 = true := by decide
theorem b24_1_0_1_5 : noStDvd (2 ^ 24 - 3 ^ 13) 9 13 119 11 = true := by decide
theorem b24_1_0_1_6 : noStDvd (2 ^ 24 - 3 ^ 13) 9 12 119 12 = true := by decide
theorem b24_1_0_1_7 : noStDvd (2 ^ 24 - 3 ^ 13) 9 11 119 13 = true := by decide
theorem b24_1_0_1_8 : noStDvd (2 ^ 24 - 3 ^ 13) 9 10 119 14 = true := by decide
theorem b24_1_0_1_9 : noStDvd (2 ^ 24 - 3 ^ 13) 9 9 119 15 = true := by decide

end CollatzThirteenCycle
