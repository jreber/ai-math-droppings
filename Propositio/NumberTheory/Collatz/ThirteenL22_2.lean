import Propositio.NumberTheory.Collatz.CycleUniform
import Propositio.NumberTheory.Collatz.CycleEnum

namespace CollatzThirteenCycle
open CollatzCycleDecide (steinerVal compositions)
open CollatzCycleEnum (noStDvd noStDvd_top)
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000000

theorem b22_0_2 : noStDvd (2 ^ 22 - 3 ^ 13) 11 18 5 4 = true := by decide
theorem b22_0_3 : noStDvd (2 ^ 22 - 3 ^ 13) 11 17 5 5 = true := by decide
theorem b22_0_4 : noStDvd (2 ^ 22 - 3 ^ 13) 11 16 5 6 = true := by decide
theorem b22_0_5 : noStDvd (2 ^ 22 - 3 ^ 13) 11 15 5 7 = true := by decide
theorem b22_0_6 : noStDvd (2 ^ 22 - 3 ^ 13) 11 14 5 8 = true := by decide
theorem b22_0_7 : noStDvd (2 ^ 22 - 3 ^ 13) 11 13 5 9 = true := by decide
theorem b22_0_8 : noStDvd (2 ^ 22 - 3 ^ 13) 11 12 5 10 = true := by decide
theorem b22_0_9 : noStDvd (2 ^ 22 - 3 ^ 13) 11 11 5 11 = true := by decide
theorem b22_1_0 : noStDvd (2 ^ 22 - 3 ^ 13) 11 19 7 3 = true := by decide

end CollatzThirteenCycle
