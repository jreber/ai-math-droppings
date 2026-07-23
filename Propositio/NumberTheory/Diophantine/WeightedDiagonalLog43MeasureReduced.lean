import Propositio.NumberTheory.Diophantine.WeightedDiagonalLog43Measure
import Propositio.NumberTheory.Diophantine.WeightedDiagonalLog43Denominator
import Mathlib.Tactic

/-!
# μ(log 4/3) reduced to two clean arithmetic facts

Composing `log43_measure_of_int_den` (the analytic assembly) with `JP_den` (the denominator
reduction) discharges the `hden_q` hypothesis, leaving an effective irrationality measure of
`log(4/3)` conditional on JUST:
* `hint`  : `α₁(n) ∈ ℤ`  (the log-coefficient is an integer — `= Pₙ(7)`, Legendre/Zeilberger), and
* `hstep` : `(Pₙ₊₂).den ∣ lcm(lcm((Pₙ₊₁).den, (Pₙ).den), n+2)`  (the per-step denominator bound — the
  genuine 2,3-adic miracle, since the numerator shares a `gcd(·, n+2)` factor).

Both are finite, transcendence-free arithmetic statements (verified numerically n≤20/38). This is
the precise residual frontier of the unconditional `μ(log 4/3)` (and the template for the Collatz
`log₂3` wall): NO analysis remains, only these two divisibility facts.
-/

namespace WeightedDiagonalLog43

/-- **μ(log 4/3) from integrality + the per-step denominator divisibility.** -/
theorem log43_measure_of_int_hstep
    (hint : ∀ n, ∃ m : ℤ, Jα n = (m : ℚ))
    (hstep : ∀ n, (JP (n + 2)).den ∣ Nat.lcm (Nat.lcm (JP (n + 1)).den (JP n).den) (n + 2)) :
    ∃ A ρ Q : ℝ, 0 < A ∧ 0 < ρ ∧ ρ < 1 ∧ 1 < Q ∧
      ∃ C > 0, ∀ (p q : ℤ), 1 ≤ q → (1 : ℝ) ≤ 2 * A * q →
        C / (q : ℝ) ^ (1 + Real.log Q / Real.log ρ⁻¹) ≤ |Real.log (4 / 3) - (p : ℝ) / q| :=
  log43_measure_of_int_den hint (fun n => JP_den hstep n)

end WeightedDiagonalLog43
