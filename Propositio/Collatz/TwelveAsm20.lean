import Propositio.Collatz.CycleUniform
import Propositio.Collatz.CycleEnum
import Propositio.Collatz.TwelveL20_0
namespace CollatzTwelveCycle
open CollatzCycleDecide (steinerVal compositions)
open CollatzCycleEnum (noStDvd noStDvd_top)
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000000



theorem check12_20 : (compositions 12 20).all (fun as => !decide ((2 ^ 20 - 3 ^ 12) ∣ steinerVal as)) = true := by
  rw [← noStDvd_top, show (12 : Nat) = 11 + 1 from rfl, noStDvd]
  apply List.all_eq_true.mpr
  intro i hi
  rw [List.mem_range] at hi
  interval_cases i
  · exact b20_0
  · exact b20_1
  · exact b20_2
  · exact b20_3
  · exact b20_4
  · exact b20_5
  · exact b20_6
  · exact b20_7
  · exact b20_8
  all_goals decide

end CollatzTwelveCycle
