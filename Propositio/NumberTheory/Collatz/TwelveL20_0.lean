import Propositio.NumberTheory.Collatz.CycleUniform
import Propositio.NumberTheory.Collatz.CycleEnum

namespace CollatzTwelveCycle
open CollatzCycleDecide (steinerVal compositions)
open CollatzCycleEnum (noStDvd noStDvd_top)
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000000

theorem b20_0 : noStDvd (2 ^ 20 - 3 ^ 12) 11 19 1 1 = true := by decide
theorem b20_1 : noStDvd (2 ^ 20 - 3 ^ 12) 11 18 1 2 = true := by decide
theorem b20_2 : noStDvd (2 ^ 20 - 3 ^ 12) 11 17 1 3 = true := by decide
theorem b20_3 : noStDvd (2 ^ 20 - 3 ^ 12) 11 16 1 4 = true := by decide
theorem b20_4 : noStDvd (2 ^ 20 - 3 ^ 12) 11 15 1 5 = true := by decide
theorem b20_5 : noStDvd (2 ^ 20 - 3 ^ 12) 11 14 1 6 = true := by decide
theorem b20_6 : noStDvd (2 ^ 20 - 3 ^ 12) 11 13 1 7 = true := by decide
theorem b20_7 : noStDvd (2 ^ 20 - 3 ^ 12) 11 12 1 8 = true := by decide
theorem b20_8 : noStDvd (2 ^ 20 - 3 ^ 12) 11 11 1 9 = true := by decide

end CollatzTwelveCycle
