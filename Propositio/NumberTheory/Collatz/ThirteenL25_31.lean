import Propositio.NumberTheory.Collatz.CycleUniform
import Propositio.NumberTheory.Collatz.CycleEnum

namespace CollatzThirteenCycle
open CollatzCycleDecide (steinerVal compositions)
open CollatzCycleEnum (noStDvd noStDvd_top)
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000000

theorem b25_2_0_0_2 : noStDvd (2 ^ 25 - 3 ^ 13) 9 17 179 8 = true := by decide
theorem b25_2_0_0_3 : noStDvd (2 ^ 25 - 3 ^ 13) 9 16 179 9 = true := by decide
theorem b25_2_0_0_4 : noStDvd (2 ^ 25 - 3 ^ 13) 9 15 179 10 = true := by decide
theorem b25_2_0_0_5 : noStDvd (2 ^ 25 - 3 ^ 13) 9 14 179 11 = true := by decide
theorem b25_2_0_0_6 : noStDvd (2 ^ 25 - 3 ^ 13) 9 13 179 12 = true := by decide
theorem b25_2_0_0_7 : noStDvd (2 ^ 25 - 3 ^ 13) 9 12 179 13 = true := by decide
theorem b25_2_0_0_8 : noStDvd (2 ^ 25 - 3 ^ 13) 9 11 179 14 = true := by decide
theorem b25_2_0_0_9 : noStDvd (2 ^ 25 - 3 ^ 13) 9 10 179 15 = true := by decide
theorem b25_2_0_0_10 : noStDvd (2 ^ 25 - 3 ^ 13) 9 9 179 16 = true := by decide
theorem b25_2_0_1_0 : noStDvd (2 ^ 25 - 3 ^ 13) 9 18 211 7 = true := by decide
theorem b25_2_0_1_1 : noStDvd (2 ^ 25 - 3 ^ 13) 9 17 211 8 = true := by decide
theorem b25_2_0_1_2 : noStDvd (2 ^ 25 - 3 ^ 13) 9 16 211 9 = true := by decide
theorem b25_2_0_1_3 : noStDvd (2 ^ 25 - 3 ^ 13) 9 15 211 10 = true := by decide
theorem b25_2_0_1_4 : noStDvd (2 ^ 25 - 3 ^ 13) 9 14 211 11 = true := by decide
theorem b25_2_0_1_5 : noStDvd (2 ^ 25 - 3 ^ 13) 9 13 211 12 = true := by decide
theorem b25_2_0_1_6 : noStDvd (2 ^ 25 - 3 ^ 13) 9 12 211 13 = true := by decide
theorem b25_2_0_1_7 : noStDvd (2 ^ 25 - 3 ^ 13) 9 11 211 14 = true := by decide
theorem b25_2_0_1_8 : noStDvd (2 ^ 25 - 3 ^ 13) 9 10 211 15 = true := by decide
theorem b25_2_0_1_9 : noStDvd (2 ^ 25 - 3 ^ 13) 9 9 211 16 = true := by decide

end CollatzThirteenCycle
