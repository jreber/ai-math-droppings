import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic

/-!
# Primes in the true dyadic interval `(x, 2x]` via Bertrand's postulate

The companion file `PrimesDyadicInterval` proves a *quantitative* `c·x/log x` lower
bound on the prime count of a dilation interval `(x, K·x]`, but only for a very wide
factor `K ≈ 2789`, because the project's recorded Chebyshev constants are too loose to
close the dyadic margin `K = 2`.

This file supplies the honest **existence** companion at the true dyadic factor `K = 2`,
which mathlib already gives unconditionally through Bertrand's postulate
(`Nat.exists_prime_lt_and_le_two_mul`, alias `Nat.bertrand`): for every `N ≥ 1` there is
a prime in `(N, 2N]`.  We restate it in the project's real-argument prime-counting
notation (`Nat.primeCounting ⌊·⌋₊`) so it composes with the analytic-NT cluster.

## Main results

* `BertrandDyadicInterval.exists_prime_in_dyadic` (Deliverable A, existence):
  for `x ≥ 1` there is a prime `p` with `x < p ≤ 2x`.
* `BertrandDyadicInterval.primeCounting_two_mul_lt` (Deliverable B, counting `≥ 1`):
  `π(⌊x⌋₊) < π(⌊2x⌋₊)` — the prime-counting function strictly increases across the
  dyadic interval `(x, 2x]`, i.e. it contains at least one (new) prime.
-/

namespace BertrandDyadicInterval

open scoped Nat

/-- **Deliverable A — existence of a prime in the dyadic interval `(x, 2x]`.**
For every real `x ≥ 1` there is a prime `p` with `x < p ≤ 2x`.  This is Bertrand's
postulate applied to `N = ⌊x⌋₊`, transported to the real interval: `⌊x⌋₊ < p` forces
`x < p` (as `p ≥ ⌊x⌋₊ + 1 > x`), and `p ≤ 2⌊x⌋₊ ≤ 2x`. -/
theorem exists_prime_in_dyadic (x : ℝ) (hx : 1 ≤ x) :
    ∃ p : ℕ, p.Prime ∧ (x : ℝ) < p ∧ (p : ℝ) ≤ 2 * x := by
  have hx0 : (0 : ℝ) ≤ x := le_trans zero_le_one hx
  -- `⌊x⌋₊ ≥ 1`, in particular `≠ 0`, so Bertrand applies.
  have hfloor1 : 1 ≤ ⌊x⌋₊ := Nat.one_le_floor_iff x |>.mpr hx
  obtain ⟨p, hp, hNp, hp2N⟩ :=
    Nat.exists_prime_lt_and_le_two_mul ⌊x⌋₊ (Nat.one_le_iff_ne_zero.mp hfloor1)
  refine ⟨p, hp, ?_, ?_⟩
  · -- `x < ⌊x⌋₊ + 1 ≤ p`.
    have h1 : x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x
    have h2 : (⌊x⌋₊ : ℝ) + 1 ≤ (p : ℝ) := by
      have : ⌊x⌋₊ + 1 ≤ p := hNp
      exact_mod_cast this
    linarith
  · -- `p ≤ 2⌊x⌋₊ ≤ 2x`.
    have hpc : (p : ℝ) ≤ (2 * ⌊x⌋₊ : ℕ) := by exact_mod_cast hp2N
    have hfx : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx0
    calc (p : ℝ) ≤ (2 * ⌊x⌋₊ : ℕ) := hpc
      _ = 2 * (⌊x⌋₊ : ℝ) := by push_cast; ring
      _ ≤ 2 * x := by linarith

/-- **Deliverable B — the prime-counting function strictly increases across `(x, 2x]`.**
For every real `x ≥ 1`, `π(⌊x⌋₊) < π(⌊2x⌋₊)`: the dyadic interval `(x, 2x]` contains at
least one prime not counted at `x`.  Bertrand gives a prime `p` with `⌊x⌋₊ < p ≤ 2⌊x⌋₊`,
and `2⌊x⌋₊ ≤ ⌊2x⌋₊`, so `p` lies in `(⌊x⌋₊, ⌊2x⌋₊]` and increments the count. -/
theorem primeCounting_two_mul_lt (x : ℝ) (hx : 1 ≤ x) :
    Nat.primeCounting ⌊x⌋₊ < Nat.primeCounting ⌊2 * x⌋₊ := by
  have hx0 : (0 : ℝ) ≤ x := le_trans zero_le_one hx
  have hfloor1 : 1 ≤ ⌊x⌋₊ := Nat.one_le_floor_iff x |>.mpr hx
  obtain ⟨p, hp, hNp, hp2N⟩ :=
    Nat.exists_prime_lt_and_le_two_mul ⌊x⌋₊ (Nat.one_le_iff_ne_zero.mp hfloor1)
  -- `2⌊x⌋₊ ≤ ⌊2x⌋₊`, hence `p ≤ ⌊2x⌋₊`.
  have hdouble : 2 * ⌊x⌋₊ ≤ ⌊2 * x⌋₊ := by
    have hle : ((2 * ⌊x⌋₊ : ℕ) : ℝ) ≤ 2 * x := by
      have hfx : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx0
      push_cast; linarith
    exact Nat.le_floor hle
  have hp2x : p ≤ ⌊2 * x⌋₊ := le_trans hp2N hdouble
  -- `π n = count Prime (n + 1)`; reduce to the `Nat.count` API.
  unfold Nat.primeCounting Nat.primeCounting'
  calc Nat.count Nat.Prime (⌊x⌋₊ + 1)
      ≤ Nat.count Nat.Prime p := Nat.count_monotone _ (by omega)
    _ < Nat.count Nat.Prime (⌊2 * x⌋₊ + 1) := Nat.count_strict_mono hp (by omega)

end BertrandDyadicInterval
