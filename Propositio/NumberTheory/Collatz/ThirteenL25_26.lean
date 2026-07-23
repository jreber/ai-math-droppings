import Propositio.NumberTheory.Collatz.CycleUniform
import Propositio.NumberTheory.Collatz.CycleEnum

namespace CollatzThirteenCycle
open CollatzCycleDecide (steinerVal compositions)
open CollatzCycleEnum (noStDvd noStDvd_top)
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000000

theorem b25_1_1_0_2 : noStDvd (2 ^ 25 - 3 ^ 13) 9 17 143 8 = true := by decide
theorem b25_1_1_0_3 : noStDvd (2 ^ 25 - 3 ^ 13) 9 16 143 9 = true := by decide
theorem b25_1_1_0_4 : noStDvd (2 ^ 25 - 3 ^ 13) 9 15 143 10 = true := by decide
theorem b25_1_1_0_5 : noStDvd (2 ^ 25 - 3 ^ 13) 9 14 143 11 = true := by decide
theorem b25_1_1_0_6 : noStDvd (2 ^ 25 - 3 ^ 13) 9 13 143 12 = true := by decide
theorem b25_1_1_0_7 : noStDvd (2 ^ 25 - 3 ^ 13) 9 12 143 13 = true := by decide
theorem b25_1_1_0_8 : noStDvd (2 ^ 25 - 3 ^ 13) 9 11 143 14 = true := by decide
theorem b25_1_1_0_9 : noStDvd (2 ^ 25 - 3 ^ 13) 9 10 143 15 = true := by decide
theorem b25_1_1_0_10 : noStDvd (2 ^ 25 - 3 ^ 13) 9 9 143 16 = true := by decide
theorem b25_1_1_1_0 : noStDvd (2 ^ 25 - 3 ^ 13) 9 18 175 7 = true := by decide
theorem b25_1_1_1_1 : noStDvd (2 ^ 25 - 3 ^ 13) 9 17 175 8 = true := by decide
theorem b25_1_1_1_2 : noStDvd (2 ^ 25 - 3 ^ 13) 9 16 175 9 = true := by decide
theorem b25_1_1_1_3 : noStDvd (2 ^ 25 - 3 ^ 13) 9 15 175 10 = true := by decide
theorem b25_1_1_1_4 : noStDvd (2 ^ 25 - 3 ^ 13) 9 14 175 11 = true := by decide
theorem b25_1_1_1_5 : noStDvd (2 ^ 25 - 3 ^ 13) 9 13 175 12 = true := by decide
theorem b25_1_1_1_6 : noStDvd (2 ^ 25 - 3 ^ 13) 9 12 175 13 = true := by decide
theorem b25_1_1_1_7 : noStDvd (2 ^ 25 - 3 ^ 13) 9 11 175 14 = true := by decide
theorem b25_1_1_1_8 : noStDvd (2 ^ 25 - 3 ^ 13) 9 10 175 15 = true := by decide
theorem b25_1_1_1_9 : noStDvd (2 ^ 25 - 3 ^ 13) 9 9 175 16 = true := by decide

end CollatzThirteenCycle
