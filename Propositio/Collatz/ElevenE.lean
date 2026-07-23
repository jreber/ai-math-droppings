import Propositio.Collatz.ElevenB

namespace CollatzElevenCycle
open CollatzCycleDecide (steinerVal compositions)
open CollatzCycleEnum (noStDvd noStDvd_top)
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000000

/-- `A = 20` assembled from `c20_*` via POSITIONAL bullets: each branch does exactly one
`exact` (no `first`/failed-exact backtracking, which would whnf-evaluate `noStDvd`). -/
theorem check11_20 :
    (compositions 11 20).all (fun as => !decide ((2 ^ 20 - 3 ^ 11) ∣ steinerVal as)) = true := by
  rw [← noStDvd_top, show (11 : Nat) = 10 + 1 from rfl, noStDvd]
  apply List.all_eq_true.mpr
  intro i hi
  rw [List.mem_range] at hi
  interval_cases i
  · exact c20_0
  · exact c20_1
  · exact c20_2
  · exact c20_3
  · exact c20_4
  · exact c20_5
  · exact c20_6
  · exact c20_7
  · exact c20_8
  · exact c20_9
  all_goals decide

end CollatzElevenCycle
