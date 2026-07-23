import Propositio.Collatz.CycleUniform
import Propositio.Collatz.CycleEnum

namespace CollatzTwelveCycle
open CollatzCycleDecide (steinerVal compositions)
open CollatzCycleEnum (noStDvd noStDvd_top)
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000000

theorem b22_0_0_0 : noStDvd (2 ^ 22 - 3 ^ 12) 9 19 19 3 = true := by decide
theorem b22_0_0_1 : noStDvd (2 ^ 22 - 3 ^ 12) 9 18 19 4 = true := by decide

end CollatzTwelveCycle
