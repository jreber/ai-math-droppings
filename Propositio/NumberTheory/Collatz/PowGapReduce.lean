import Propositio.NumberTheory.Collatz.DescentDichotomy

/-!
# `PowGap` is monotone in `k` — its hard content is the minimal-`k` instance

`CollatzDescentDichotomy.PowGap` (`∀ a k, 3^a < 2^k → 2^a·(2^k − 3^a + 1) > 3^a`) is the
single isolated power inequality to which the Everett–Terras capstone's `hpow` reduces.
`powGap_of_two_a_le` proves it for `k ≥ 2a`; the residual `k < 2a` range is
transcendence-adjacent (a Baker-type lower bound on `|2^k − 3^a|`).

This file records that the inner inequality is **monotone in `k`**: the term
`2^a·(2^k − 3^a + 1)` strictly increases with `k`, so once the inequality holds at some
`k₀` it holds at every `k ≥ k₀`. Consequently the entire hard content of `PowGap`
collapses to, for each `a`, the SINGLE instance at the minimal `k` with `3^a < 2^k`
(every larger `k` then follows for free). This pinpoints exactly which inequalities a
future elementary or transcendence-based proof of `PowGap` must establish.
-/

namespace CollatzPowGapReduce

/-- **The `PowGap` term is monotone in `k`.** If `2^a·(2^k − 3^a + 1) > 3^a` then the
same holds with `k+1`. (Pure `Nat` arithmetic: `2^k ≤ 2^(k+1)` and Nat-subtraction
monotonicity.) -/
theorem powGap_term_succ (a k : Nat)
    (h : 3 ^ a < 2 ^ a * (2 ^ k - 3 ^ a + 1)) :
    3 ^ a < 2 ^ a * (2 ^ (k + 1) - 3 ^ a + 1) := by
  have hle : 2 ^ k ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (Nat.le_succ k)
  have hmono : 2 ^ k - 3 ^ a + 1 ≤ 2 ^ (k + 1) - 3 ^ a + 1 := by omega
  calc 3 ^ a < 2 ^ a * (2 ^ k - 3 ^ a + 1) := h
    _ ≤ 2 ^ a * (2 ^ (k + 1) - 3 ^ a + 1) := Nat.mul_le_mul_left _ hmono

/-- **`PowGap` propagates upward in `k`.** If the inequality holds at `k₀`, it holds at
every `k ≥ k₀` (iterate `powGap_term_succ`). So `PowGap` is equivalent to its restriction
to the minimal `k` (per `a`) with `3^a < 2^k`. -/
theorem powGap_term_of_le (a k₀ k : Nat) (hk : k₀ ≤ k)
    (h : 3 ^ a < 2 ^ a * (2 ^ k₀ - 3 ^ a + 1)) :
    3 ^ a < 2 ^ a * (2 ^ k - 3 ^ a + 1) := by
  induction k with
  | zero => obtain rfl : k₀ = 0 := Nat.le_zero.mp hk; exact h
  | succ k ih =>
    rcases Nat.lt_or_ge k₀ (k + 1) with hlt | hge
    · exact powGap_term_succ a k (ih (Nat.lt_succ_iff.mp hlt))
    · obtain rfl : k₀ = k + 1 := Nat.le_antisymm hk hge; exact h

end CollatzPowGapReduce
