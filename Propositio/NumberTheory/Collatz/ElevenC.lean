import Propositio.NumberTheory.Collatz.CycleUniform
import Propositio.NumberTheory.Collatz.CycleEnum

namespace CollatzElevenCycle
open CollatzCycleDecide (steinerVal compositions)
open CollatzCycleEnum (noStDvd noStDvd_top)
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000000

theorem c21a_0 : noStDvd (2 ^ 21 - 3 ^ 11) 9 19 5 2 = true := by decide
theorem c21a_1 : noStDvd (2 ^ 21 - 3 ^ 11) 9 18 5 3 = true := by decide
theorem c21a_2 : noStDvd (2 ^ 21 - 3 ^ 11) 9 17 5 4 = true := by decide
theorem c21a_3 : noStDvd (2 ^ 21 - 3 ^ 11) 9 16 5 5 = true := by decide
theorem c21a_4 : noStDvd (2 ^ 21 - 3 ^ 11) 9 15 5 6 = true := by decide
theorem c21a_5 : noStDvd (2 ^ 21 - 3 ^ 11) 9 14 5 7 = true := by decide
theorem c21a_6 : noStDvd (2 ^ 21 - 3 ^ 11) 9 13 5 8 = true := by decide
theorem c21a_7 : noStDvd (2 ^ 21 - 3 ^ 11) 9 12 5 9 = true := by decide
theorem c21a_8 : noStDvd (2 ^ 21 - 3 ^ 11) 9 11 5 10 = true := by decide
theorem c21a_9 : noStDvd (2 ^ 21 - 3 ^ 11) 9 10 5 11 = true := by decide
theorem c21a_10 : noStDvd (2 ^ 21 - 3 ^ 11) 9 9 5 12 = true := by decide

end CollatzElevenCycle
