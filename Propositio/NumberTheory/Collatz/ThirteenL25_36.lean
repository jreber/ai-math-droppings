import Propositio.NumberTheory.Collatz.CycleUniform
import Propositio.NumberTheory.Collatz.CycleEnum

namespace CollatzThirteenCycle
open CollatzCycleDecide (steinerVal compositions)
open CollatzCycleEnum (noStDvd noStDvd_top)
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000000

theorem b25_3_0_2 : noStDvd (2 ^ 25 - 3 ^ 13) 10 17 89 8 = true := by decide
theorem b25_3_0_3 : noStDvd (2 ^ 25 - 3 ^ 13) 10 16 89 9 = true := by decide
theorem b25_3_0_4 : noStDvd (2 ^ 25 - 3 ^ 13) 10 15 89 10 = true := by decide
theorem b25_3_0_5 : noStDvd (2 ^ 25 - 3 ^ 13) 10 14 89 11 = true := by decide
theorem b25_3_0_6 : noStDvd (2 ^ 25 - 3 ^ 13) 10 13 89 12 = true := by decide
theorem b25_3_0_7 : noStDvd (2 ^ 25 - 3 ^ 13) 10 12 89 13 = true := by decide
theorem b25_3_0_8 : noStDvd (2 ^ 25 - 3 ^ 13) 10 11 89 14 = true := by decide
theorem b25_3_0_9 : noStDvd (2 ^ 25 - 3 ^ 13) 10 10 89 15 = true := by decide
theorem b25_3_1 : noStDvd (2 ^ 25 - 3 ^ 13) 11 19 19 6 = true := by decide

end CollatzThirteenCycle
