import Propositio.Collatz.Chebyshev30PsiThetaGap
import Propositio.Collatz.Chebyshev30ThetaTelescope
import Propositio.NumberTheory.Diophantine.LcmGrowthBound

/-!
# Chebyshev-30 lcm bound with a *small* additive error

`CollatzChebyshev30.log_lcmUpto_le_cheb30` (in `CollatzChebyshev30Lcm.lean`) bounds
`log(lcm(1..n))` with leading slope `≈ 1.1455` but two crippling sub-exponential terms:
the additive constant `θ(57600) ≈ 57600` (from `theta_tight`'s threshold telescoping) and
the lossy `2√n·log n` ψ−θ gap (mathlib's `abs_psi_sub_theta_le_sqrt_mul_log`).  Exponentiated
for the denominator bound, the `θ(57600)` factor `e^{57600}` pushes the `native_decide` handoff
window past `2×10⁵`, which the KB recorded as "genuinely walled / multi-week".

This file composes the two *sharp* replacements proved in this corpus:

* `theta_loglin`  : `θ(n) ≤ (6A/5)·n + (log n/log 6 + 1)(4 log n + 4) + θ(30)`
  — slope `6A/5 ≈ 1.1055`, additive `O(log² n)` with the *small* base `θ(30) ≈ 22.6`;
* `psi_sub_theta_le_tight` : `ψ(n) − θ(n) ≤ log 4·(√n + n^{1/3} + n^{1/4} + (log n/log 2)·n^{1/5})`
  — the ψ−θ gap with the spurious `log n` factor removed from the `√n`-scale terms.

Adding them (`ψ = θ + (ψ−θ)`, and `log(lcm(1..n)) = ψ(n)` by `log_lcmUpto_eq_psi`) yields a
tight lcm bound whose every error term is `o(n)` with a small constant.  A numeric computation
(`crossover.clj`) shows the resulting bound already beats the prize's target
`30·lcm(1..2n) ≤ 6·10ⁿ` (i.e. `ψ(2n) ≤ n·log 10 − log 5`) for all `n ≥ 6879`, leaving a
`native_decide`-feasible handoff window `n < 6879` (≈ 2.8 h census, vs. the old ≈ 2×10⁵).
Sharpening the `4 log n` Stirling junk in `logM_le_linear` to `log n` would drop the window
to `n ≈ 3900` (≈ 40 min).
-/

namespace CollatzChebyshev30

open Chebyshev Real LcmGrowthBound

/-- **Tight Chebyshev-30 lcm bound (small additive).**  Composes the `O(log²)`-additive
telescoping `theta_loglin` with the sharper gap `psi_sub_theta_le_tight`.  Leading slope
`6·Aentropy/5 ≈ 1.1055`; every other term is `o(n)` with a small constant (base `θ(30) ≈ 22.6`,
*not* `θ(57600)`). -/
theorem log_lcmUpto_le_cheb30_tight (n : ℕ) (hn : 2 ≤ n) :
    Real.log (lcmUpto n)
      ≤ (6 * Aentropy / 5) * n
        + (Real.log n / Real.log 6 + 1) * (4 * Real.log n + 4) + theta 30
        + Real.log 4 * (Real.sqrt n + (n : ℝ) ^ ((1:ℝ)/3) + (n : ℝ) ^ ((1:ℝ)/4)
            + (Real.log n / Real.log 2) * (n : ℝ) ^ ((1:ℝ)/5)) := by
  have hx2 : (2:ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hx1 : (1:ℝ) ≤ (n : ℝ) := by linarith
  rw [log_lcmUpto_eq_psi]
  have ht := theta_loglin (n : ℝ) hx1
  have hg := psi_sub_theta_le_tight (n : ℝ) hx2
  linarith [ht, hg]

#print axioms log_lcmUpto_le_cheb30_tight

end CollatzChebyshev30
