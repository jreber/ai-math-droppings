import Propositio.Collatz.CycleUniform
import Propositio.Collatz.CycleEnum

namespace CollatzThirteenCycle
open CollatzCycleDecide (steinerVal compositions)
open CollatzCycleEnum (noStDvd noStDvd_top)
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000000

theorem b25_4_1 : noStDvd (2 ^ 25 - 3 ^ 13) 11 18 35 7 = true := by decide
theorem b25_4_2 : noStDvd (2 ^ 25 - 3 ^ 13) 11 17 35 8 = true := by decide
theorem b25_4_3 : noStDvd (2 ^ 25 - 3 ^ 13) 11 16 35 9 = true := by decide
theorem b25_4_4 : noStDvd (2 ^ 25 - 3 ^ 13) 11 15 35 10 = true := by decide
theorem b25_4_5 : noStDvd (2 ^ 25 - 3 ^ 13) 11 14 35 11 = true := by decide
theorem b25_4_6 : noStDvd (2 ^ 25 - 3 ^ 13) 11 13 35 12 = true := by decide
theorem b25_4_7 : noStDvd (2 ^ 25 - 3 ^ 13) 11 12 35 13 = true := by decide
theorem b25_4_8 : noStDvd (2 ^ 25 - 3 ^ 13) 11 11 35 14 = true := by decide
theorem b25_5 : noStDvd (2 ^ 25 - 3 ^ 13) 12 19 1 6 = true := by decide
theorem b25_6 : noStDvd (2 ^ 25 - 3 ^ 13) 12 18 1 7 = true := by decide

end CollatzThirteenCycle
