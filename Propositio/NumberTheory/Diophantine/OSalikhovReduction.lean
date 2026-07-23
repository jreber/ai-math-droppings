import Propositio.NumberTheory.Diophantine.OSalikhovHeight
import Propositio.NumberTheory.Diophantine.OSalikhovDecomp
import Propositio.NumberTheory.Diophantine.OrderThreeRecurrence

/-!
# The decomposition reduces to Phase 3 + base cases

`E1 = A1 + B·log(2/3)` (and `E2 = A2 − B·log2`) need NOT be proved by a general partial-fraction
argument.  Once `E1` is shown to satisfy the order-3 recurrence (Phase 3, the Gosper certificate)
and to match `A1 + B·log(2/3)` at the base window `n = 0,1,2`, the recurrence-uniqueness engine
(`OrderThreeRecurrence.recurrence_unique`) forces equality for all `n` — exactly the
`WeightedDiagonalLog43.J_decomp` strategy.

This file packages that reduction, isolating the integral decomposition to:
(a) **Phase 3**: `E1, E2` satisfy the recurrence, and
(b) **base cases** `E1(0..2)`, `E2(0..2)` (`E1(0)`, `E2(0)` already proved in `OSalikhovDecomp`).
-/

namespace OSalikhovTwoLog

open OSalikhovHeight OrderThreeRecurrence

/-- **Decomposition of `E1` from the recurrence + base window.** -/
theorem E1_decomp_of_rec (A1 B : ℕ → ℝ)
    (hA1 : Recurrence p0R p1R p2R p3R A1) (hB : Recurrence p0R p1R p2R p3R B)
    (hE1 : Recurrence p0R p1R p2R p3R E1)
    (h0 : E1 0 = A1 0 + B 0 * Real.log (2 / 3))
    (h1 : E1 1 = A1 1 + B 1 * Real.log (2 / 3))
    (h2 : E1 2 = A1 2 + B 2 * Real.log (2 / 3)) :
    ∀ n, E1 n = A1 n + B n * Real.log (2 / 3) := by
  have hcomb : Recurrence p0R p1R p2R p3R (fun n => A1 n + Real.log (2 / 3) * B n) :=
    Recurrence.add_smul p0R p1R p2R p3R A1 B (Real.log (2 / 3)) hA1 hB
  have hp3 : ∀ n, p3R n ≠ 0 := fun n => (p3R_pos n).ne'
  have huniq := recurrence_unique p0R p1R p2R p3R E1 (fun n => A1 n + Real.log (2 / 3) * B n)
    hE1 hcomb hp3 (by rw [h0]; ring) (by rw [h1]; ring) (by rw [h2]; ring)
  intro n; rw [huniq n]; ring

/-- **Decomposition of `E2` from the recurrence + base window.** -/
theorem E2_decomp_of_rec (A2 B : ℕ → ℝ)
    (hA2 : Recurrence p0R p1R p2R p3R A2) (hB : Recurrence p0R p1R p2R p3R B)
    (hE2 : Recurrence p0R p1R p2R p3R E2)
    (h0 : E2 0 = A2 0 - B 0 * Real.log 2)
    (h1 : E2 1 = A2 1 - B 1 * Real.log 2)
    (h2 : E2 2 = A2 2 - B 2 * Real.log 2) :
    ∀ n, E2 n = A2 n - B n * Real.log 2 := by
  have hcomb : Recurrence p0R p1R p2R p3R (fun n => A2 n + (-Real.log 2) * B n) :=
    Recurrence.add_smul p0R p1R p2R p3R A2 B (-Real.log 2) hA2 hB
  have hp3 : ∀ n, p3R n ≠ 0 := fun n => (p3R_pos n).ne'
  have huniq := recurrence_unique p0R p1R p2R p3R E2 (fun n => A2 n + (-Real.log 2) * B n)
    hE2 hcomb hp3 (by rw [h0]; ring) (by rw [h1]; ring) (by rw [h2]; ring)
  intro n; rw [huniq n]; ring

end OSalikhovTwoLog
