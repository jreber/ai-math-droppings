import Propositio.NumberTheory.Collatz.CycleUniform
import Propositio.NumberTheory.Collatz.CycleEnum

namespace CollatzThirteenCycle
open CollatzCycleDecide (steinerVal compositions)
open CollatzCycleEnum (noStDvd noStDvd_top)
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000000

theorem b24_2_0_0_0 : noStDvd (2 ^ 24 - 3 ^ 13) 9 18 179 6 = true := by decide
theorem b24_2_0_0_1 : noStDvd (2 ^ 24 - 3 ^ 13) 9 17 179 7 = true := by decide
theorem b24_2_0_0_2 : noStDvd (2 ^ 24 - 3 ^ 13) 9 16 179 8 = true := by decide
theorem b24_2_0_0_3 : noStDvd (2 ^ 24 - 3 ^ 13) 9 15 179 9 = true := by decide
theorem b24_2_0_0_4 : noStDvd (2 ^ 24 - 3 ^ 13) 9 14 179 10 = true := by decide
theorem b24_2_0_0_5 : noStDvd (2 ^ 24 - 3 ^ 13) 9 13 179 11 = true := by decide
theorem b24_2_0_0_6 : noStDvd (2 ^ 24 - 3 ^ 13) 9 12 179 12 = true := by decide
theorem b24_2_0_0_7 : noStDvd (2 ^ 24 - 3 ^ 13) 9 11 179 13 = true := by decide
theorem b24_2_0_0_8 : noStDvd (2 ^ 24 - 3 ^ 13) 9 10 179 14 = true := by decide
theorem b24_2_0_0_9 : noStDvd (2 ^ 24 - 3 ^ 13) 9 9 179 15 = true := by decide
theorem b24_2_0_1 : noStDvd (2 ^ 24 - 3 ^ 13) 10 18 49 6 = true := by decide

end CollatzThirteenCycle
