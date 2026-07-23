import Propositio.NumberTheory.Collatz.CycleUniform
import Propositio.NumberTheory.Collatz.CycleEnum

namespace CollatzTwelveCycle
open CollatzCycleDecide (steinerVal compositions)
open CollatzCycleEnum (noStDvd noStDvd_top)
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000000

theorem b21_0_0_0 : noStDvd (2 ^ 21 - 3 ^ 12) 9 18 19 3 = true := by decide
theorem b21_0_0_1 : noStDvd (2 ^ 21 - 3 ^ 12) 9 17 19 4 = true := by decide
theorem b21_0_0_2 : noStDvd (2 ^ 21 - 3 ^ 12) 9 16 19 5 = true := by decide
theorem b21_0_0_3 : noStDvd (2 ^ 21 - 3 ^ 12) 9 15 19 6 = true := by decide
theorem b21_0_0_4 : noStDvd (2 ^ 21 - 3 ^ 12) 9 14 19 7 = true := by decide
theorem b21_0_0_5 : noStDvd (2 ^ 21 - 3 ^ 12) 9 13 19 8 = true := by decide
theorem b21_0_0_6 : noStDvd (2 ^ 21 - 3 ^ 12) 9 12 19 9 = true := by decide
theorem b21_0_0_7 : noStDvd (2 ^ 21 - 3 ^ 12) 9 11 19 10 = true := by decide
theorem b21_0_0_8 : noStDvd (2 ^ 21 - 3 ^ 12) 9 10 19 11 = true := by decide
theorem b21_0_0_9 : noStDvd (2 ^ 21 - 3 ^ 12) 9 9 19 12 = true := by decide
theorem b21_0_1 : noStDvd (2 ^ 21 - 3 ^ 12) 10 18 5 3 = true := by decide

end CollatzTwelveCycle
