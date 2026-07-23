import Propositio.NumberTheory.Collatz.CycleUniform
import Propositio.NumberTheory.Collatz.CycleEnum

namespace CollatzThirteenCycle
open CollatzCycleDecide (steinerVal compositions)
open CollatzCycleEnum (noStDvd noStDvd_top)
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000000

theorem b22_0_0_0_0 : noStDvd (2 ^ 22 - 3 ^ 13) 9 18 65 4 = true := by decide
theorem b22_0_0_0_1 : noStDvd (2 ^ 22 - 3 ^ 13) 9 17 65 5 = true := by decide
theorem b22_0_0_0_2 : noStDvd (2 ^ 22 - 3 ^ 13) 9 16 65 6 = true := by decide
theorem b22_0_0_0_3 : noStDvd (2 ^ 22 - 3 ^ 13) 9 15 65 7 = true := by decide
theorem b22_0_0_0_4 : noStDvd (2 ^ 22 - 3 ^ 13) 9 14 65 8 = true := by decide
theorem b22_0_0_0_5 : noStDvd (2 ^ 22 - 3 ^ 13) 9 13 65 9 = true := by decide
theorem b22_0_0_0_6 : noStDvd (2 ^ 22 - 3 ^ 13) 9 12 65 10 = true := by decide
theorem b22_0_0_0_7 : noStDvd (2 ^ 22 - 3 ^ 13) 9 11 65 11 = true := by decide
theorem b22_0_0_0_8 : noStDvd (2 ^ 22 - 3 ^ 13) 9 10 65 12 = true := by decide
theorem b22_0_0_0_9 : noStDvd (2 ^ 22 - 3 ^ 13) 9 9 65 13 = true := by decide
theorem b22_0_0_1 : noStDvd (2 ^ 22 - 3 ^ 13) 10 18 19 4 = true := by decide

end CollatzThirteenCycle
