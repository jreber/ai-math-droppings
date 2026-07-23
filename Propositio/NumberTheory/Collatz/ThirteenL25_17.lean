import Propositio.NumberTheory.Collatz.CycleUniform
import Propositio.NumberTheory.Collatz.CycleEnum

namespace CollatzThirteenCycle
open CollatzCycleDecide (steinerVal compositions)
open CollatzCycleEnum (noStDvd noStDvd_top)
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000000

theorem b25_0_2_2 : noStDvd (2 ^ 25 - 3 ^ 13) 10 18 31 7 = true := by decide
theorem b25_0_2_3 : noStDvd (2 ^ 25 - 3 ^ 13) 10 17 31 8 = true := by decide
theorem b25_0_2_4 : noStDvd (2 ^ 25 - 3 ^ 13) 10 16 31 9 = true := by decide
theorem b25_0_2_5 : noStDvd (2 ^ 25 - 3 ^ 13) 10 15 31 10 = true := by decide
theorem b25_0_2_6 : noStDvd (2 ^ 25 - 3 ^ 13) 10 14 31 11 = true := by decide
theorem b25_0_2_7 : noStDvd (2 ^ 25 - 3 ^ 13) 10 13 31 12 = true := by decide
theorem b25_0_2_8 : noStDvd (2 ^ 25 - 3 ^ 13) 10 12 31 13 = true := by decide
theorem b25_0_2_9 : noStDvd (2 ^ 25 - 3 ^ 13) 10 11 31 14 = true := by decide
theorem b25_0_2_10 : noStDvd (2 ^ 25 - 3 ^ 13) 10 10 31 15 = true := by decide
theorem b25_0_3_0_0 : noStDvd (2 ^ 25 - 3 ^ 13) 9 18 205 7 = true := by decide

end CollatzThirteenCycle
