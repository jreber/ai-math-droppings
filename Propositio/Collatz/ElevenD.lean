import Propositio.Collatz.CycleUniform
import Propositio.Collatz.CycleEnum

namespace CollatzElevenCycle
open CollatzCycleDecide (steinerVal compositions)
open CollatzCycleEnum (noStDvd noStDvd_top)
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000000

theorem check11_21_p1 : noStDvd (2 ^ 21 - 3 ^ 11) 10 19 1 2 = true := by decide
theorem check11_21_p2 : noStDvd (2 ^ 21 - 3 ^ 11) 10 18 1 3 = true := by decide
theorem check11_21_p3 : noStDvd (2 ^ 21 - 3 ^ 11) 10 17 1 4 = true := by decide
theorem check11_21_p4 : noStDvd (2 ^ 21 - 3 ^ 11) 10 16 1 5 = true := by decide
theorem check11_21_p5 : noStDvd (2 ^ 21 - 3 ^ 11) 10 15 1 6 = true := by decide
theorem check11_21_p6 : noStDvd (2 ^ 21 - 3 ^ 11) 10 14 1 7 = true := by decide
theorem check11_21_p7 : noStDvd (2 ^ 21 - 3 ^ 11) 10 13 1 8 = true := by decide
theorem check11_21_p8 : noStDvd (2 ^ 21 - 3 ^ 11) 10 12 1 9 = true := by decide
theorem check11_21_p9 : noStDvd (2 ^ 21 - 3 ^ 11) 10 11 1 10 = true := by decide
theorem check11_21_p10 : noStDvd (2 ^ 21 - 3 ^ 11) 10 10 1 11 = true := by decide

end CollatzElevenCycle
