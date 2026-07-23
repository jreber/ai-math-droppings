import Propositio.NumberTheory.Collatz.CycleUniform
import Propositio.NumberTheory.Collatz.CycleEnum

namespace CollatzTwelveCycle
open CollatzCycleDecide (steinerVal compositions)
open CollatzCycleEnum (noStDvd noStDvd_top)
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000000

theorem b22_1_0_1 : noStDvd (2 ^ 22 - 3 ^ 12) 9 17 29 5 = true := by decide
theorem b22_1_0_2 : noStDvd (2 ^ 22 - 3 ^ 12) 9 16 29 6 = true := by decide
theorem b22_1_0_3 : noStDvd (2 ^ 22 - 3 ^ 12) 9 15 29 7 = true := by decide
theorem b22_1_0_4 : noStDvd (2 ^ 22 - 3 ^ 12) 9 14 29 8 = true := by decide
theorem b22_1_0_5 : noStDvd (2 ^ 22 - 3 ^ 12) 9 13 29 9 = true := by decide
theorem b22_1_0_6 : noStDvd (2 ^ 22 - 3 ^ 12) 9 12 29 10 = true := by decide
theorem b22_1_0_7 : noStDvd (2 ^ 22 - 3 ^ 12) 9 11 29 11 = true := by decide
theorem b22_1_0_8 : noStDvd (2 ^ 22 - 3 ^ 12) 9 10 29 12 = true := by decide
theorem b22_1_0_9 : noStDvd (2 ^ 22 - 3 ^ 12) 9 9 29 13 = true := by decide
theorem b22_1_1 : noStDvd (2 ^ 22 - 3 ^ 12) 10 18 7 4 = true := by decide
theorem b22_1_2 : noStDvd (2 ^ 22 - 3 ^ 12) 10 17 7 5 = true := by decide
theorem b22_1_3 : noStDvd (2 ^ 22 - 3 ^ 12) 10 16 7 6 = true := by decide
theorem b22_1_4 : noStDvd (2 ^ 22 - 3 ^ 12) 10 15 7 7 = true := by decide
theorem b22_1_5 : noStDvd (2 ^ 22 - 3 ^ 12) 10 14 7 8 = true := by decide
theorem b22_1_6 : noStDvd (2 ^ 22 - 3 ^ 12) 10 13 7 9 = true := by decide
theorem b22_1_7 : noStDvd (2 ^ 22 - 3 ^ 12) 10 12 7 10 = true := by decide
theorem b22_1_8 : noStDvd (2 ^ 22 - 3 ^ 12) 10 11 7 11 = true := by decide
theorem b22_1_9 : noStDvd (2 ^ 22 - 3 ^ 12) 10 10 7 12 = true := by decide

end CollatzTwelveCycle
