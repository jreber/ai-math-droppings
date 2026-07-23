import Propositio.NumberTheory.Collatz.CycleUniform
import Propositio.NumberTheory.Collatz.CycleEnum

namespace CollatzThirteenCycle
open CollatzCycleDecide (steinerVal compositions)
open CollatzCycleEnum (noStDvd noStDvd_top)
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000000

theorem b24_0_0_0_1 : noStDvd (2 ^ 24 - 3 ^ 13) 9 19 65 5 = true := by decide
theorem b24_0_0_0_2 : noStDvd (2 ^ 24 - 3 ^ 13) 9 18 65 6 = true := by decide

end CollatzThirteenCycle
