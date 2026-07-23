import Propositio.NumberTheory.Diophantine.WeightedDiagonalLog43MeasureReduced
import Propositio.NumberTheory.Diophantine.WeightedDiagonalLog43Integrality
import Mathlib.Tactic

/-!
# μ(log 4/3) conditional on a SINGLE arithmetic fact

Integrality `α₁(n) ∈ ℤ` is now PROVED unconditionally (`Jα_int`, via the Zeilberger recurrence for
`α₁(n) = Pₙ(7) = Σ C(n,k)C(n+k,k)3ᵏ`).  Discharging `hint` in `log43_measure_of_int_hstep` leaves an
effective irrationality measure of `log(4/3)` conditional on JUST the per-step denominator fact:

  `hstep : ∀ n, (Pₙ₊₂).den ∣ lcm(lcm((Pₙ₊₁).den, (Pₙ).den), n+2)`

— a single finite, transcendence-free divisibility statement (verified numerically n≤38).  This is
the entire residual frontier of the unconditional `μ(log 4/3)`: every other ingredient (the
construction, the Gosper/creative-telescoping recurrence, the single-log decomposition, the
integrality Zeilberger recurrence, and ALL analysis) is proved axiom-clean.
-/

namespace WeightedDiagonalLog43

/-- **μ(log 4/3) from the per-step denominator divisibility alone** (integrality now discharged). -/
theorem log43_measure_of_hstep
    (hstep : ∀ n, (JP (n + 2)).den ∣ Nat.lcm (Nat.lcm (JP (n + 1)).den (JP n).den) (n + 2)) :
    ∃ A ρ Q : ℝ, 0 < A ∧ 0 < ρ ∧ ρ < 1 ∧ 1 < Q ∧
      ∃ C > 0, ∀ (p q : ℤ), 1 ≤ q → (1 : ℝ) ≤ 2 * A * q →
        C / (q : ℝ) ^ (1 + Real.log Q / Real.log ρ⁻¹) ≤ |Real.log (4 / 3) - (p : ℝ) / q| :=
  log43_measure_of_int_hstep Jα_int hstep

end WeightedDiagonalLog43
