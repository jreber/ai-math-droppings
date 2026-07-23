import Propositio.NumberTheory.Collatz.CycleUniform
import Propositio.NumberTheory.Collatz.CycleEnum

namespace CollatzTwelveCycle
open CollatzCycleDecide (steinerVal compositions)
open CollatzCycleEnum (noStDvd noStDvd_top)
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000000

theorem b23_0_0_1 : noStDvd (2 ^ 23 - 3 ^ 12) 9 19 19 4 = true := by decide
theorem b23_0_0_2 : noStDvd (2 ^ 23 - 3 ^ 12) 9 18 19 5 = true := by decide

end CollatzTwelveCycle
