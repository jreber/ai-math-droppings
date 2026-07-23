import Propositio.NumberTheory.Collatz.CycleUniform
import Propositio.NumberTheory.Collatz.CycleEnum

namespace CollatzThirteenCycle
open CollatzCycleDecide (steinerVal compositions)
open CollatzCycleEnum (noStDvd noStDvd_top)
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000000

theorem b25_1_1_2 : noStDvd (2 ^ 25 - 3 ^ 13) 10 18 37 7 = true := by decide
theorem b25_1_1_3 : noStDvd (2 ^ 25 - 3 ^ 13) 10 17 37 8 = true := by decide
theorem b25_1_1_4 : noStDvd (2 ^ 25 - 3 ^ 13) 10 16 37 9 = true := by decide
theorem b25_1_1_5 : noStDvd (2 ^ 25 - 3 ^ 13) 10 15 37 10 = true := by decide
theorem b25_1_1_6 : noStDvd (2 ^ 25 - 3 ^ 13) 10 14 37 11 = true := by decide
theorem b25_1_1_7 : noStDvd (2 ^ 25 - 3 ^ 13) 10 13 37 12 = true := by decide
theorem b25_1_1_8 : noStDvd (2 ^ 25 - 3 ^ 13) 10 12 37 13 = true := by decide
theorem b25_1_1_9 : noStDvd (2 ^ 25 - 3 ^ 13) 10 11 37 14 = true := by decide
theorem b25_1_1_10 : noStDvd (2 ^ 25 - 3 ^ 13) 10 10 37 15 = true := by decide
theorem b25_1_2_0_0 : noStDvd (2 ^ 25 - 3 ^ 13) 9 18 223 7 = true := by decide

end CollatzThirteenCycle
