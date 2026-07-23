/-
Zsygmondy existence for a LARGE BASE — an unconditional, exception-free corollary of
`primitive_prime_exists_of_size` (in `ZsygmondyEvenPrime`).

`primitive_prime_exists_of_size` requires two hypotheses beyond `n ≥ 2`, `a ≥ 2`:
the size bound `n ≤ (a-1)^φ(n)` and the carve-out `¬ (n = 2 ∧ a+1 a power of two)`.

Both are automatically discharged once the base is large relative to the exponent:

  * If `a ≥ n + 1` then `a - 1 ≥ n ≥ 1`, so (since `φ(n) ≥ 1` for `n ≥ 1`)
    `(a-1)^φ(n) ≥ (a-1)^1 = a - 1 ≥ n`, giving the size bound directly — no need for
    any genuine growth in `φ(n)`.
  * If additionally `n ≥ 3`, the carve-out's first conjunct `n = 2` is simply false,
    so the whole exception is vacuous.

This gives a clean, hypothesis-light Zsygmondy existence statement: for every `n ≥ 3`
and every base `a ≥ n + 1`, `a^n - 1` has a primitive prime divisor. No exceptional
pair, no size side-condition beyond the explicit linear bound on `a`.
-/
import Propositio.NumberTheory.Zsygmondy.ZsygmondyEvenPrime

/-- **Zsygmondy existence for a large base.**  For `n ≥ 3` and integer base `a ≥ n + 1`,
`a^n - 1` has a primitive prime divisor: a prime `p` dividing `a^n - 1` but none of
`a^m - 1` for `0 < m < n`.  Unconditional — no size hypothesis or exceptional pair,
only the explicit linear bound `a ≥ n + 1` on the base. -/
theorem primitive_prime_exists_of_large_base {n : ℕ} (hn : 3 ≤ n) {a : ℤ}
    (ha : (n : ℤ) + 1 ≤ a) :
    ∃ p : ℕ, p.Prime ∧ (p : ℤ) ∣ a ^ n - 1 ∧
      ∀ m, 0 < m → m < n → ¬ (p : ℤ) ∣ a ^ m - 1 := by
  have hn' : 1 < n := by omega
  have hn3 : (3 : ℤ) ≤ (n : ℤ) := by exact_mod_cast hn
  have ha2 : (2 : ℤ) ≤ a := by omega
  -- size bound: `n ≤ (a-1)^φ(n)`, via `a - 1 ≤ (a-1)^φ(n)` (φ(n) ≥ 1) and `n ≤ a - 1`.
  have htot_ne : Nat.totient n ≠ 0 := by
    have : 0 < Nat.totient n := Nat.totient_pos.mpr (by omega)
    omega
  have h1a : (1 : ℤ) ≤ a - 1 := by omega
  have hstep : (a - 1) ≤ (a - 1) ^ Nat.totient n := le_self_pow₀ h1a htot_ne
  have hnle : (n : ℤ) ≤ a - 1 := by omega
  have hsize : (n : ℤ) ≤ (a - 1) ^ Nat.totient n := le_trans hnle hstep
  -- exception vacuous: `n ≠ 2` since `n ≥ 3`.
  have hexc : ¬ (n = 2 ∧ ∃ t : ℕ, (a + 1).natAbs = 2 ^ t) := by
    rintro ⟨hn2, -⟩; omega
  exact primitive_prime_exists_of_size hn' ha2 hsize hexc
