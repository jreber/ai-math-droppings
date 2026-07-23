import Propositio.NumberTheory.Collatz.CycleUniform
import Propositio.NumberTheory.Collatz.CycleEnum

namespace CollatzThirteenCycle
open CollatzCycleDecide (steinerVal compositions)
open CollatzCycleEnum (noStDvd noStDvd_top)
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000000

theorem b25_3_0_0_0 : noStDvd (2 ^ 25 - 3 ^ 13) 9 18 331 7 = true := by decide
theorem b25_3_0_0_1 : noStDvd (2 ^ 25 - 3 ^ 13) 9 17 331 8 = true := by decide
theorem b25_3_0_0_2 : noStDvd (2 ^ 25 - 3 ^ 13) 9 16 331 9 = true := by decide
theorem b25_3_0_0_3 : noStDvd (2 ^ 25 - 3 ^ 13) 9 15 331 10 = true := by decide
theorem b25_3_0_0_4 : noStDvd (2 ^ 25 - 3 ^ 13) 9 14 331 11 = true := by decide
theorem b25_3_0_0_5 : noStDvd (2 ^ 25 - 3 ^ 13) 9 13 331 12 = true := by decide
theorem b25_3_0_0_6 : noStDvd (2 ^ 25 - 3 ^ 13) 9 12 331 13 = true := by decide
theorem b25_3_0_0_7 : noStDvd (2 ^ 25 - 3 ^ 13) 9 11 331 14 = true := by decide
theorem b25_3_0_0_8 : noStDvd (2 ^ 25 - 3 ^ 13) 9 10 331 15 = true := by decide
theorem b25_3_0_0_9 : noStDvd (2 ^ 25 - 3 ^ 13) 9 9 331 16 = true := by decide
theorem b25_3_0_1 : noStDvd (2 ^ 25 - 3 ^ 13) 10 18 89 7 = true := by decide

end CollatzThirteenCycle
