import Propositio.NumberTheory.Collatz.CycleUniform
import Propositio.NumberTheory.Collatz.CycleEnum

namespace CollatzThirteenCycle
open CollatzCycleDecide (steinerVal compositions)
open CollatzCycleEnum (noStDvd noStDvd_top)
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000000

theorem b23_5 : noStDvd (2 ^ 23 - 3 ^ 13) 12 17 1 6 = true := by decide
theorem b23_6 : noStDvd (2 ^ 23 - 3 ^ 13) 12 16 1 7 = true := by decide
theorem b23_7 : noStDvd (2 ^ 23 - 3 ^ 13) 12 15 1 8 = true := by decide
theorem b23_8 : noStDvd (2 ^ 23 - 3 ^ 13) 12 14 1 9 = true := by decide
theorem b23_9 : noStDvd (2 ^ 23 - 3 ^ 13) 12 13 1 10 = true := by decide
theorem b23_10 : noStDvd (2 ^ 23 - 3 ^ 13) 12 12 1 11 = true := by decide

end CollatzThirteenCycle
