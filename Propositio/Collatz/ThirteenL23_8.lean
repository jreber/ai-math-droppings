import Propositio.Collatz.CycleUniform
import Propositio.Collatz.CycleEnum

namespace CollatzThirteenCycle
open CollatzCycleDecide (steinerVal compositions)
open CollatzCycleEnum (noStDvd noStDvd_top)
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000000

theorem b23_2_1 : noStDvd (2 ^ 23 - 3 ^ 13) 11 18 11 5 = true := by decide
theorem b23_2_2 : noStDvd (2 ^ 23 - 3 ^ 13) 11 17 11 6 = true := by decide
theorem b23_2_3 : noStDvd (2 ^ 23 - 3 ^ 13) 11 16 11 7 = true := by decide
theorem b23_2_4 : noStDvd (2 ^ 23 - 3 ^ 13) 11 15 11 8 = true := by decide
theorem b23_2_5 : noStDvd (2 ^ 23 - 3 ^ 13) 11 14 11 9 = true := by decide
theorem b23_2_6 : noStDvd (2 ^ 23 - 3 ^ 13) 11 13 11 10 = true := by decide
theorem b23_2_7 : noStDvd (2 ^ 23 - 3 ^ 13) 11 12 11 11 = true := by decide
theorem b23_2_8 : noStDvd (2 ^ 23 - 3 ^ 13) 11 11 11 12 = true := by decide
theorem b23_3 : noStDvd (2 ^ 23 - 3 ^ 13) 12 19 1 4 = true := by decide
theorem b23_4 : noStDvd (2 ^ 23 - 3 ^ 13) 12 18 1 5 = true := by decide

end CollatzThirteenCycle
