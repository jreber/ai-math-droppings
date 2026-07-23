import Propositio.Collatz.CycleUniform
import Propositio.Collatz.CycleEnum

namespace CollatzThirteenCycle
open CollatzCycleDecide (steinerVal compositions)
open CollatzCycleEnum (noStDvd noStDvd_top)
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000000

theorem b23_0_0_0_0 : noStDvd (2 ^ 23 - 3 ^ 13) 9 19 65 4 = true := by decide
theorem b23_0_0_0_1 : noStDvd (2 ^ 23 - 3 ^ 13) 9 18 65 5 = true := by decide

end CollatzThirteenCycle
