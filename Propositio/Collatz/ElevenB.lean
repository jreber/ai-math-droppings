import Propositio.Collatz.CycleUniform
import Propositio.Collatz.CycleEnum

namespace CollatzElevenCycle
open CollatzCycleDecide (steinerVal compositions)
open CollatzCycleEnum (noStDvd noStDvd_top)
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000000

theorem c20_0 : noStDvd (2 ^ 20 - 3 ^ 11) 10 19 1 1 = true := by decide
theorem c20_1 : noStDvd (2 ^ 20 - 3 ^ 11) 10 18 1 2 = true := by decide
theorem c20_2 : noStDvd (2 ^ 20 - 3 ^ 11) 10 17 1 3 = true := by decide
theorem c20_3 : noStDvd (2 ^ 20 - 3 ^ 11) 10 16 1 4 = true := by decide
theorem c20_4 : noStDvd (2 ^ 20 - 3 ^ 11) 10 15 1 5 = true := by decide
theorem c20_5 : noStDvd (2 ^ 20 - 3 ^ 11) 10 14 1 6 = true := by decide
theorem c20_6 : noStDvd (2 ^ 20 - 3 ^ 11) 10 13 1 7 = true := by decide
theorem c20_7 : noStDvd (2 ^ 20 - 3 ^ 11) 10 12 1 8 = true := by decide
theorem c20_8 : noStDvd (2 ^ 20 - 3 ^ 11) 10 11 1 9 = true := by decide
theorem c20_9 : noStDvd (2 ^ 20 - 3 ^ 11) 10 10 1 10 = true := by decide

end CollatzElevenCycle
