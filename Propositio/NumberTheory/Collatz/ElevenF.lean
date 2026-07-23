import Propositio.NumberTheory.Collatz.ElevenC

namespace CollatzElevenCycle
open CollatzCycleDecide (steinerVal compositions)
open CollatzCycleEnum (noStDvd noStDvd_top)
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000000

theorem check11_21_p0 : noStDvd (2 ^ 21 - 3 ^ 11) 10 20 1 1 = true := by
  rw [show (10 : Nat) = 9 + 1 from rfl, noStDvd]
  apply List.all_eq_true.mpr
  intro j hj
  rw [List.mem_range] at hj
  interval_cases j
  · exact c21a_0
  · exact c21a_1
  · exact c21a_2
  · exact c21a_3
  · exact c21a_4
  · exact c21a_5
  · exact c21a_6
  · exact c21a_7
  · exact c21a_8
  · exact c21a_9
  · exact c21a_10
  all_goals decide

end CollatzElevenCycle
