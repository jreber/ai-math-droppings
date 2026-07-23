import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Tactic

/-!
# A prime-counting corollary of Bertrand's postulate

Bertrand's postulate (`Nat.exists_prime_lt_and_le_two_mul`) guarantees a prime in the
interval `(N, 2N]` for every `N ≥ 1`. As an immediate consequence, the prime-counting
function `Nat.primeCounting` is strictly larger at `2N` than at `N`: the prime supplied by
Bertrand is counted at `2N` but not at `N`.
-/

namespace Nat

open scoped Nat.Prime

/-- **Bertrand, prime-counting form.** For every `N ≥ 1` there is at least one prime in
`(N, 2N]`, hence `π(N) < π(2N)`. -/
theorem primeCounting_lt_primeCounting_two_mul (N : ℕ) (hN : 1 ≤ N) :
    Nat.primeCounting N < Nat.primeCounting (2 * N) := by
  -- Bertrand's postulate: a prime `p` with `N < p ≤ 2N`.
  obtain ⟨p, hp, hNp, hp2N⟩ := exists_prime_lt_and_le_two_mul N (Nat.one_le_iff_ne_zero.mp hN)
  -- `π n = count Prime (n + 1)` by definition; reduce to the `Nat.count` API.
  unfold Nat.primeCounting Nat.primeCounting'
  -- `count Prime (N+1) ≤ count Prime p < count Prime (2N+1)`.
  calc Nat.count Nat.Prime (N + 1)
      ≤ Nat.count Nat.Prime p := count_monotone _ (by omega)
    _ < Nat.count Nat.Prime (2 * N + 1) := count_strict_mono hp (by omega)

end Nat
