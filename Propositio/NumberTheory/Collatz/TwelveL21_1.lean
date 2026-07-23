import Propositio.NumberTheory.Collatz.CycleUniform
import Propositio.NumberTheory.Collatz.CycleEnum

namespace CollatzTwelveCycle
open CollatzCycleDecide (steinerVal compositions)
open CollatzCycleEnum (noStDvd noStDvd_top)
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000000

theorem b21_0_2 : noStDvd (2 ^ 21 - 3 ^ 12) 10 17 5 4 = true := by decide
theorem b21_0_3 : noStDvd (2 ^ 21 - 3 ^ 12) 10 16 5 5 = true := by decide
theorem b21_0_4 : noStDvd (2 ^ 21 - 3 ^ 12) 10 15 5 6 = true := by decide
theorem b21_0_5 : noStDvd (2 ^ 21 - 3 ^ 12) 10 14 5 7 = true := by decide
theorem b21_0_6 : noStDvd (2 ^ 21 - 3 ^ 12) 10 13 5 8 = true := by decide
theorem b21_0_7 : noStDvd (2 ^ 21 - 3 ^ 12) 10 12 5 9 = true := by decide
theorem b21_0_8 : noStDvd (2 ^ 21 - 3 ^ 12) 10 11 5 10 = true := by decide
theorem b21_0_9 : noStDvd (2 ^ 21 - 3 ^ 12) 10 10 5 11 = true := by decide
theorem b21_1 : noStDvd (2 ^ 21 - 3 ^ 12) 11 19 1 2 = true := by decide

end CollatzTwelveCycle
