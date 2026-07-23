import Propositio.Collatz.ElevenF
import Propositio.Collatz.ElevenD

namespace CollatzElevenCycle
open CollatzCycleDecide (steinerVal compositions)
open CollatzCycleEnum (noStDvd noStDvd_top)
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000000

theorem check11_21 :
    (compositions 11 21).all (fun as => !decide ((2 ^ 21 - 3 ^ 11) ∣ steinerVal as)) = true := by
  rw [← noStDvd_top, show (11 : Nat) = 10 + 1 from rfl, noStDvd]
  apply List.all_eq_true.mpr
  intro i hi
  rw [List.mem_range] at hi
  interval_cases i
  · exact check11_21_p0
  · exact check11_21_p1
  · exact check11_21_p2
  · exact check11_21_p3
  · exact check11_21_p4
  · exact check11_21_p5
  · exact check11_21_p6
  · exact check11_21_p7
  · exact check11_21_p8
  · exact check11_21_p9
  · exact check11_21_p10
  all_goals decide

end CollatzElevenCycle
