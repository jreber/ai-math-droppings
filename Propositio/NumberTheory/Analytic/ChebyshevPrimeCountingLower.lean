import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.PrimeCounting
import Propositio.NumberTheory.Analytic.ChebyshevThetaLower

/-!
# Chebyshev's lower bound for the prime-counting function `π`

mathlib's `Mathlib/NumberTheory/PrimeCounting.lean` provides only an *upper* bound
(`Nat.primeCounting'_add_le`) and monotonicity for the prime-counting function `π`.
This file supplies the matching **lower bound** `π(⌊x⌋) ≥ c·x / log x` for large `x`,
Chebyshev's classical estimate.

The bridge is elementary:
`θ(x) = ∑_{p ≤ x prime} log p ≤ ∑_{p ≤ x prime} log x = π(⌊x⌋)·log x`,
since `log p ≤ log x` for `0 < p ≤ x`, and there are exactly `π(⌊x⌋)` primes `≤ ⌊x⌋`.
Dividing by `log x > 0` and using the previously-established linear lower bound
`c·x ≤ θ(x)` (`ChebyshevThetaLower.chebyshev_theta_ge`) gives the result.

## Main result

* `ChebyshevPrimeCountingLower.chebyshev_primeCounting_ge` :
  `∃ c > 0, ∃ x₀, ∀ x ≥ x₀, c·x / log x ≤ π(⌊x⌋)`.
-/

open Chebyshev Finset Real

namespace ChebyshevPrimeCountingLower

/-- The number of primes in `Ioc 0 m` is exactly `Nat.primeCounting m` (= `π m`).
The interval `Ioc 0 m` cuts out `0 < p ≤ m`; for a prime `p` the lower constraint is
automatic, so this is the same finset as `{p < m+1 | p.Prime}` = `primesBelow (m+1)`. -/
theorem card_primes_Ioc (m : ℕ) :
    ((Finset.Ioc 0 m).filter Nat.Prime).card = Nat.primeCounting m := by
  rw [Nat.primeCounting, ← Nat.primesBelow_card_eq_primeCounting', Nat.primesBelow]
  congr 1
  ext p
  simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_range, Nat.lt_succ_iff]
  constructor
  · rintro ⟨⟨_, hpm⟩, hp⟩; exact ⟨hpm, hp⟩
  · rintro ⟨hpm, hp⟩; exact ⟨⟨hp.pos, hpm⟩, hp⟩

/-- **The bridge.** `θ x ≤ π(⌊x⌋) · log x` for `0 < x`. Each prime `p ≤ ⌊x⌋ ≤ x`
contributes `log p ≤ log x`, and there are `π(⌊x⌋)` such primes. -/
theorem theta_le_primeCounting_mul_log {x : ℝ} (hx : 0 < x) :
    Chebyshev.theta x ≤ (Nat.primeCounting ⌊x⌋₊ : ℝ) * Real.log x := by
  rw [Chebyshev.theta]
  calc ∑ p ∈ Finset.Ioc 0 ⌊x⌋₊ with p.Prime, Real.log (p : ℝ)
      ≤ ∑ _p ∈ (Finset.Ioc 0 ⌊x⌋₊).filter Nat.Prime, Real.log x := by
        apply Finset.sum_le_sum
        intro p hp
        rw [Finset.mem_filter, Finset.mem_Ioc] at hp
        obtain ⟨⟨hp0, hpm⟩, _hpp⟩ := hp
        refine Real.log_le_log (by exact_mod_cast hp0) ?_
        calc (p : ℝ) ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast hpm
          _ ≤ x := Nat.floor_le hx.le
    _ = ((Finset.Ioc 0 ⌊x⌋₊).filter Nat.Prime).card • Real.log x := by
        rw [Finset.sum_const]
    _ = (Nat.primeCounting ⌊x⌋₊ : ℝ) * Real.log x := by
        rw [card_primes_Ioc, nsmul_eq_mul]

/-- **Chebyshev's lower bound for the prime-counting function.**  There is an explicit
positive constant `c` and a threshold `x₀` with `c·x / log x ≤ π(⌊x⌋)` for all `x ≥ x₀`. -/
theorem chebyshev_primeCounting_ge :
    ∃ c : ℝ, 0 < c ∧ ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
      c * x / Real.log x ≤ (Nat.primeCounting ⌊x⌋₊ : ℝ) := by
  obtain ⟨c, hcpos, x₀, hθ⟩ := ChebyshevThetaLower.chebyshev_theta_ge
  refine ⟨c, hcpos, max x₀ 2, ?_⟩
  intro x hx
  have hx0 : x₀ ≤ x := le_trans (le_max_left _ _) hx
  have hx2 : 2 ≤ x := le_trans (le_max_right _ _) hx
  have hxpos : 0 < x := by linarith
  have hlogpos : 0 < Real.log x := Real.log_pos (by linarith)
  have hθx : c * x ≤ Chebyshev.theta x := hθ x hx0
  have hbridge := theta_le_primeCounting_mul_log hxpos
  rw [div_le_iff₀ hlogpos]
  calc c * x ≤ Chebyshev.theta x := hθx
    _ ≤ (Nat.primeCounting ⌊x⌋₊ : ℝ) * Real.log x := hbridge

end ChebyshevPrimeCountingLower
