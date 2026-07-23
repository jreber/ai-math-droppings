import Propositio.NumberTheory.Collatz.CycleUniform
import Propositio.NumberTheory.Collatz.CycleEnum

namespace CollatzThirteenCycle
open CollatzCycleDecide (steinerVal compositions)
open CollatzCycleEnum (noStDvd noStDvd_top)
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000000

theorem b25_0_0_0_0_1 : noStDvd (2 ^ 25 - 3 ^ 13) 8 19 211 6 = true := by decide
theorem b25_0_0_0_0_2 : noStDvd (2 ^ 25 - 3 ^ 13) 8 18 211 7 = true := by decide
theorem b25_0_0_0_0_3 : noStDvd (2 ^ 25 - 3 ^ 13) 8 17 211 8 = true := by decide
theorem b25_0_0_0_0_4 : noStDvd (2 ^ 25 - 3 ^ 13) 8 16 211 9 = true := by decide
theorem b25_0_0_0_0_5 : noStDvd (2 ^ 25 - 3 ^ 13) 8 15 211 10 = true := by decide
theorem b25_0_0_0_0_6 : noStDvd (2 ^ 25 - 3 ^ 13) 8 14 211 11 = true := by decide
theorem b25_0_0_0_0_7 : noStDvd (2 ^ 25 - 3 ^ 13) 8 13 211 12 = true := by decide
theorem b25_0_0_0_0_8 : noStDvd (2 ^ 25 - 3 ^ 13) 8 12 211 13 = true := by decide
theorem b25_0_0_0_0_9 : noStDvd (2 ^ 25 - 3 ^ 13) 8 11 211 14 = true := by decide
theorem b25_0_0_0_0_10 : noStDvd (2 ^ 25 - 3 ^ 13) 8 10 211 15 = true := by decide
theorem b25_0_0_0_0_11 : noStDvd (2 ^ 25 - 3 ^ 13) 8 9 211 16 = true := by decide
theorem b25_0_0_0_0_12 : noStDvd (2 ^ 25 - 3 ^ 13) 8 8 211 17 = true := by decide

end CollatzThirteenCycle
