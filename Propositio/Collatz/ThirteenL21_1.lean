import Propositio.Collatz.CycleUniform
import Propositio.Collatz.CycleEnum

namespace CollatzThirteenCycle
open CollatzCycleDecide (steinerVal compositions)
open CollatzCycleEnum (noStDvd noStDvd_top)
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000000

theorem b21_1 : noStDvd (2 ^ 21 - 3 ^ 13) 12 19 1 2 = true := by decide
theorem b21_2 : noStDvd (2 ^ 21 - 3 ^ 13) 12 18 1 3 = true := by decide
theorem b21_3 : noStDvd (2 ^ 21 - 3 ^ 13) 12 17 1 4 = true := by decide
theorem b21_4 : noStDvd (2 ^ 21 - 3 ^ 13) 12 16 1 5 = true := by decide
theorem b21_5 : noStDvd (2 ^ 21 - 3 ^ 13) 12 15 1 6 = true := by decide
theorem b21_6 : noStDvd (2 ^ 21 - 3 ^ 13) 12 14 1 7 = true := by decide
theorem b21_7 : noStDvd (2 ^ 21 - 3 ^ 13) 12 13 1 8 = true := by decide
theorem b21_8 : noStDvd (2 ^ 21 - 3 ^ 13) 12 12 1 9 = true := by decide

end CollatzThirteenCycle
