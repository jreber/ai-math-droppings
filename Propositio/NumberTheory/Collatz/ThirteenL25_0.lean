import Propositio.NumberTheory.Collatz.CycleUniform
import Propositio.NumberTheory.Collatz.CycleEnum

namespace CollatzThirteenCycle
open CollatzCycleDecide (steinerVal compositions)
open CollatzCycleEnum (noStDvd noStDvd_top)
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000000

theorem b25_0_0_0_0_0_0 : noStDvd (2 ^ 25 - 3 ^ 13) 7 19 665 6 = true := by decide
theorem b25_0_0_0_0_0_1 : noStDvd (2 ^ 25 - 3 ^ 13) 7 18 665 7 = true := by decide
theorem b25_0_0_0_0_0_2 : noStDvd (2 ^ 25 - 3 ^ 13) 7 17 665 8 = true := by decide
theorem b25_0_0_0_0_0_3 : noStDvd (2 ^ 25 - 3 ^ 13) 7 16 665 9 = true := by decide
theorem b25_0_0_0_0_0_4 : noStDvd (2 ^ 25 - 3 ^ 13) 7 15 665 10 = true := by decide
theorem b25_0_0_0_0_0_5 : noStDvd (2 ^ 25 - 3 ^ 13) 7 14 665 11 = true := by decide
theorem b25_0_0_0_0_0_6 : noStDvd (2 ^ 25 - 3 ^ 13) 7 13 665 12 = true := by decide
theorem b25_0_0_0_0_0_7 : noStDvd (2 ^ 25 - 3 ^ 13) 7 12 665 13 = true := by decide
theorem b25_0_0_0_0_0_8 : noStDvd (2 ^ 25 - 3 ^ 13) 7 11 665 14 = true := by decide
theorem b25_0_0_0_0_0_9 : noStDvd (2 ^ 25 - 3 ^ 13) 7 10 665 15 = true := by decide
theorem b25_0_0_0_0_0_10 : noStDvd (2 ^ 25 - 3 ^ 13) 7 9 665 16 = true := by decide
theorem b25_0_0_0_0_0_11 : noStDvd (2 ^ 25 - 3 ^ 13) 7 8 665 17 = true := by decide
theorem b25_0_0_0_0_0_12 : noStDvd (2 ^ 25 - 3 ^ 13) 7 7 665 18 = true := by decide

end CollatzThirteenCycle
