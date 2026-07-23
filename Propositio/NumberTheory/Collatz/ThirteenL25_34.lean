import Propositio.NumberTheory.Collatz.CycleUniform
import Propositio.NumberTheory.Collatz.CycleEnum

namespace CollatzThirteenCycle
open CollatzCycleDecide (steinerVal compositions)
open CollatzCycleEnum (noStDvd noStDvd_top)
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000000

theorem b25_2_2 : noStDvd (2 ^ 25 - 3 ^ 13) 11 19 11 6 = true := by decide
theorem b25_2_3 : noStDvd (2 ^ 25 - 3 ^ 13) 11 18 11 7 = true := by decide
theorem b25_2_4 : noStDvd (2 ^ 25 - 3 ^ 13) 11 17 11 8 = true := by decide
theorem b25_2_5 : noStDvd (2 ^ 25 - 3 ^ 13) 11 16 11 9 = true := by decide
theorem b25_2_6 : noStDvd (2 ^ 25 - 3 ^ 13) 11 15 11 10 = true := by decide
theorem b25_2_7 : noStDvd (2 ^ 25 - 3 ^ 13) 11 14 11 11 = true := by decide
theorem b25_2_8 : noStDvd (2 ^ 25 - 3 ^ 13) 11 13 11 12 = true := by decide
theorem b25_2_9 : noStDvd (2 ^ 25 - 3 ^ 13) 11 12 11 13 = true := by decide
theorem b25_2_10 : noStDvd (2 ^ 25 - 3 ^ 13) 11 11 11 14 = true := by decide

end CollatzThirteenCycle
