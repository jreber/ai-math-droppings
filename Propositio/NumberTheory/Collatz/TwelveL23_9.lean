import Propositio.NumberTheory.Collatz.CycleUniform
import Propositio.NumberTheory.Collatz.CycleEnum

namespace CollatzTwelveCycle
open CollatzCycleDecide (steinerVal compositions)
open CollatzCycleEnum (noStDvd noStDvd_top)
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000000

theorem b23_3 : noStDvd (2 ^ 23 - 3 ^ 12) 11 19 1 4 = true := by decide
theorem b23_4 : noStDvd (2 ^ 23 - 3 ^ 12) 11 18 1 5 = true := by decide
theorem b23_5 : noStDvd (2 ^ 23 - 3 ^ 12) 11 17 1 6 = true := by decide
theorem b23_6 : noStDvd (2 ^ 23 - 3 ^ 12) 11 16 1 7 = true := by decide
theorem b23_7 : noStDvd (2 ^ 23 - 3 ^ 12) 11 15 1 8 = true := by decide
theorem b23_8 : noStDvd (2 ^ 23 - 3 ^ 12) 11 14 1 9 = true := by decide
theorem b23_9 : noStDvd (2 ^ 23 - 3 ^ 12) 11 13 1 10 = true := by decide
theorem b23_10 : noStDvd (2 ^ 23 - 3 ^ 12) 11 12 1 11 = true := by decide
theorem b23_11 : noStDvd (2 ^ 23 - 3 ^ 12) 11 11 1 12 = true := by decide

end CollatzTwelveCycle
