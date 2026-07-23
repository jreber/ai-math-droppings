import Propositio.Collatz.CycleUniform
import Propositio.Collatz.CycleEnum

namespace CollatzElevenCycle
open CollatzCycleDecide (steinerVal compositions)
open CollatzCycleEnum (noStDvd noStDvd_top)
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000000

theorem check11_18 :
    (compositions 11 18).all (fun as => !decide ((2 ^ 18 - 3 ^ 11) ∣ steinerVal as)) = true := by
  rw [← noStDvd_top]; decide

theorem check11_19 :
    (compositions 11 19).all (fun as => !decide ((2 ^ 19 - 3 ^ 11) ∣ steinerVal as)) = true := by
  rw [← noStDvd_top]; decide

end CollatzElevenCycle
