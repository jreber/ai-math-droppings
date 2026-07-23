import Propositio.NumberTheory.Collatz.CycleUniform
import Propositio.NumberTheory.Collatz.CycleEnum

namespace CollatzThirteenCycle
open CollatzCycleDecide (steinerVal compositions)
open CollatzCycleEnum (noStDvd noStDvd_top)
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000000

theorem b22_1_1 : noStDvd (2 ^ 22 - 3 ^ 13) 11 18 7 4 = true := by decide
theorem b22_1_2 : noStDvd (2 ^ 22 - 3 ^ 13) 11 17 7 5 = true := by decide
theorem b22_1_3 : noStDvd (2 ^ 22 - 3 ^ 13) 11 16 7 6 = true := by decide
theorem b22_1_4 : noStDvd (2 ^ 22 - 3 ^ 13) 11 15 7 7 = true := by decide
theorem b22_1_5 : noStDvd (2 ^ 22 - 3 ^ 13) 11 14 7 8 = true := by decide
theorem b22_1_6 : noStDvd (2 ^ 22 - 3 ^ 13) 11 13 7 9 = true := by decide
theorem b22_1_7 : noStDvd (2 ^ 22 - 3 ^ 13) 11 12 7 10 = true := by decide
theorem b22_1_8 : noStDvd (2 ^ 22 - 3 ^ 13) 11 11 7 11 = true := by decide
theorem b22_2 : noStDvd (2 ^ 22 - 3 ^ 13) 12 19 1 3 = true := by decide
theorem b22_3 : noStDvd (2 ^ 22 - 3 ^ 13) 12 18 1 4 = true := by decide

end CollatzThirteenCycle
