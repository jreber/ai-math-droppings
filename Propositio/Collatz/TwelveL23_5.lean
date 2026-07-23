import Propositio.Collatz.CycleUniform
import Propositio.Collatz.CycleEnum

namespace CollatzTwelveCycle
open CollatzCycleDecide (steinerVal compositions)
open CollatzCycleEnum (noStDvd noStDvd_top)
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000000

theorem b23_1_0_0 : noStDvd (2 ^ 23 - 3 ^ 12) 9 19 29 4 = true := by decide
theorem b23_1_0_1 : noStDvd (2 ^ 23 - 3 ^ 12) 9 18 29 5 = true := by decide

end CollatzTwelveCycle
