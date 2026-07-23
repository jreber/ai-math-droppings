import Propositio.NumberTheory.Collatz.CycleUniform
import Propositio.NumberTheory.Collatz.CycleEnum

namespace CollatzThirteenCycle
open CollatzCycleDecide (steinerVal compositions)
open CollatzCycleEnum (noStDvd noStDvd_top)
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000000

theorem b25_7 : noStDvd (2 ^ 25 - 3 ^ 13) 12 17 1 8 = true := by decide
theorem b25_8 : noStDvd (2 ^ 25 - 3 ^ 13) 12 16 1 9 = true := by decide
theorem b25_9 : noStDvd (2 ^ 25 - 3 ^ 13) 12 15 1 10 = true := by decide
theorem b25_10 : noStDvd (2 ^ 25 - 3 ^ 13) 12 14 1 11 = true := by decide
theorem b25_11 : noStDvd (2 ^ 25 - 3 ^ 13) 12 13 1 12 = true := by decide
theorem b25_12 : noStDvd (2 ^ 25 - 3 ^ 13) 12 12 1 13 = true := by decide

end CollatzThirteenCycle
