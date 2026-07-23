import Propositio.NumberTheory.Collatz.CycleUniform
import Propositio.NumberTheory.Collatz.CycleEnum

namespace CollatzThirteenCycle
open CollatzCycleDecide (steinerVal compositions)
open CollatzCycleEnum (noStDvd noStDvd_top)
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000000

theorem b25_0_1_1_1 : noStDvd (2 ^ 25 - 3 ^ 13) 9 18 101 7 = true := by decide
theorem b25_0_1_1_2 : noStDvd (2 ^ 25 - 3 ^ 13) 9 17 101 8 = true := by decide
theorem b25_0_1_1_3 : noStDvd (2 ^ 25 - 3 ^ 13) 9 16 101 9 = true := by decide
theorem b25_0_1_1_4 : noStDvd (2 ^ 25 - 3 ^ 13) 9 15 101 10 = true := by decide
theorem b25_0_1_1_5 : noStDvd (2 ^ 25 - 3 ^ 13) 9 14 101 11 = true := by decide
theorem b25_0_1_1_6 : noStDvd (2 ^ 25 - 3 ^ 13) 9 13 101 12 = true := by decide
theorem b25_0_1_1_7 : noStDvd (2 ^ 25 - 3 ^ 13) 9 12 101 13 = true := by decide
theorem b25_0_1_1_8 : noStDvd (2 ^ 25 - 3 ^ 13) 9 11 101 14 = true := by decide
theorem b25_0_1_1_9 : noStDvd (2 ^ 25 - 3 ^ 13) 9 10 101 15 = true := by decide
theorem b25_0_1_1_10 : noStDvd (2 ^ 25 - 3 ^ 13) 9 9 101 16 = true := by decide
theorem b25_0_1_2_0 : noStDvd (2 ^ 25 - 3 ^ 13) 9 18 133 7 = true := by decide

end CollatzThirteenCycle
