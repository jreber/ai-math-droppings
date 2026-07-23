import Propositio.NumberTheory.Collatz.CycleUniform
import Propositio.NumberTheory.Collatz.CycleEnum

namespace CollatzThirteenCycle
open CollatzCycleDecide (steinerVal compositions)
open CollatzCycleEnum (noStDvd noStDvd_top)
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000000

theorem b25_0_1_0_1 : noStDvd (2 ^ 25 - 3 ^ 13) 9 19 85 6 = true := by decide
theorem b25_0_1_0_2 : noStDvd (2 ^ 25 - 3 ^ 13) 9 18 85 7 = true := by decide

end CollatzThirteenCycle
