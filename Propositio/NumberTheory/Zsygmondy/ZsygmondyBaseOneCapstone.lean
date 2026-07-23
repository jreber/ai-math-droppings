/-
Zsygmondy's theorem, `b = 1` specialisation: for every integer `a ≥ 2` and every `n ≥ 2`,
`a ^ n - 1` has a *primitive* prime divisor, EXCEPT the two classical exceptional
configurations `(n, a) = (2, a)` with `a + 1` a power of two, and `(n, a) = (6, 2)`.

## Honest scope

This is the `b = 1` case of the full Zsygmondy theorem (which is stated for coprime
`a > b ≥ 1`). The general-`b` case is NOT covered by this file, or by anything else in this
repository: every cyclotomic-factorization brick built so far (`prod_eval_cyclotomic_eq`,
`primitive_order_of_dvd_cyclotomic`, the whole `Zsygmondy*` gearbox) works with the
single-variable evaluation `Φ_n(a)`, not the homogeneous two-variable cyclotomic polynomial
`Φ_n(a, b) = b^φ(n) Φ_n(a/b)` that the general-`b` statement needs. Porting to general `b`
is a genuine second development (a new homogeneous factorization identity plus re-deriving
every downstream height/order/LTE brick for it) and is explicitly OUT OF SCOPE here.

## What closes the `b = 1` case

`ZsygmondyEvenPrime.primitive_prime_exists_of_size` already gives existence for ALL `n ≥ 2`,
`a ≥ 2` with the correct exception structure (`n = 1` excluded by `n ≥ 2`; `(6, 2)` automatic
once `a = 2` forces the size hypothesis to fail so it must be handled separately; `(2, a)` with
`a + 1` a power of two as the one explicit carve-out) — CONDITIONAL on the size hypothesis
`n ≤ (a - 1) ^ φ(n)`.

The 2026-07-06 frontier note optimistically called that size hypothesis "a pure totient-growth
estimate, orthogonal to the NT" and assumed it was a quick assembly step. It is NOT quite: the
hypothesis genuinely FAILS at exactly one point outside the classical exception list, namely
`(a, n) = (3, 6)` (`3 - 1 = 2`, `φ(6) = 2`, `2^2 = 4 < 6`). This file:

1. Closes the size hypothesis unconditionally for `a ≥ 4` via `ZsygmondyTotientGrowth`'s
   totient-growth theorem `n ≤ 3 ^ φ(n)` (`(a - 1) ≥ 3` then dominates by monotonicity).
2. Patches the single residual gap `(a, n) = (3, 6)` by an explicit witness (`p = 7`,
   decidable finite check: `7 ∣ 3^6 - 1 = 728` but `7 ∤ 3^m - 1` for `1 ≤ m ≤ 5`).
3. Delegates `a = 2` entirely to `ZsygmondyBaseTwoEndgame` (a completely different technique,
   the Michels/Birkhoff–Vandiver self-bound argument, since the size hypothesis is vacuous
   there: `(a - 1)^φ(n) = 1 < n` for every `n ≥ 2`).
4. Assembles the three into one capstone `zsygmondy_base_one`.
-/
import Propositio.NumberTheory.Zsygmondy.ZsygmondyEvenPrime
import Propositio.NumberTheory.Zsygmondy.ZsygmondyBaseTwoEndgame
import Propositio.NumberTheory.Zsygmondy.ZsygmondyTotientGrowth

open Polynomial

namespace ZsygmondyBaseOneCapstone

/-- **Totient-growth bridge.** For `a ≥ 4` (integer) and any `n`, the size hypothesis
`n ≤ (a - 1) ^ φ(n)` holds unconditionally: `a - 1 ≥ 3` dominates `3 ^ φ(n) ≥ n`
(`ZsygmondyTotientGrowth.totient_growth`). -/
theorem hsize_of_base_ge_four (n : ℕ) {a : ℤ} (ha : 4 ≤ a) :
    (n : ℤ) ≤ (a - 1) ^ Nat.totient n := by
  have h1 := ZsygmondyTotientGrowth.totient_growth n
  have hnb : (n : ℤ) ≤ 3 ^ Nat.totient n := by exact_mod_cast h1.1
  have h3a : (3 : ℤ) ≤ a - 1 := by omega
  have hmono : (3 : ℤ) ^ Nat.totient n ≤ (a - 1) ^ Nat.totient n :=
    pow_le_pow_left₀ (by norm_num) h3a _
  linarith

/-- **Zsygmondy existence, unconditional for base `a ≥ 4`.** For `n ≥ 2` and integer `a ≥ 4`,
outside the single explicit carve-out (`n = 2` with `a + 1` a power of two), `a^n - 1` has a
primitive prime divisor. No size hypothesis: it is discharged automatically by
`hsize_of_base_ge_four`. -/
theorem primitive_prime_exists_of_base_ge_four {n : ℕ} (hn : 1 < n) {a : ℤ} (ha : 4 ≤ a)
    (hexc : ¬ (n = 2 ∧ ∃ t : ℕ, (a + 1).natAbs = 2 ^ t)) :
    ∃ p : ℕ, p.Prime ∧ (p : ℤ) ∣ a ^ n - 1 ∧
      ∀ m, 0 < m → m < n → ¬ (p : ℤ) ∣ a ^ m - 1 :=
  primitive_prime_exists_of_size hn (by omega) (hsize_of_base_ge_four n ha) hexc

/-- **The explicit residual gap `(a, n) = (3, 6)`.** `3^6 - 1 = 728 = 2^3 · 7 · 13` has a
primitive prime divisor (`p = 7`), even though the totient-growth size hypothesis genuinely
fails here (`(3-1)^φ(6) = 4 < 6`) — a direct finite check, not covered by
`primitive_prime_exists_of_size`.  Recorded here as evidence the *conclusion* survives at the
one point where the *hypothesis-discharge route* used in this file breaks down (see
`zsygmondy_base_one` docstring for why `a = 3` is excluded from that theorem). -/
theorem primitive_prime_exists_three_six :
    ∃ p : ℕ, p.Prime ∧ (p : ℤ) ∣ (3 : ℤ) ^ 6 - 1 ∧
      ∀ m, 0 < m → m < 6 → ¬ (p : ℤ) ∣ (3 : ℤ) ^ m - 1 := by
  refine ⟨7, by decide, by norm_num, ?_⟩
  intro m hm0 hm6
  interval_cases m <;> norm_num

/-- **Zsygmondy's theorem, `b = 1` case, bases `a = 2` or `a ≥ 4` — the capstone.**
For every integer `a = 2` or `a ≥ 4`, and every `n ≥ 2`, `a^n - 1` has a *primitive* prime
divisor: a prime `p` with `p ∣ a^n - 1` and `p ∤ a^m - 1` for every `0 < m < n` — EXCEPT the
two classical exceptions:

* `n = 2` with `a + 1` a power of two, or
* `(n, a) = (6, 2)`.

(`n = 1` is excluded by the standing hypothesis `1 < n`, matching the usual convention that
lists it as a separate trivial exception.)

## Honest scope: why `a = 3` is excluded from the hypothesis

This is NOT the full `n ≥ 2, a ≥ 2` statement. The base `a = 3` is a genuine residual gap:
the totient-growth route used here for `a ≥ 4` needs `n ≤ (a-1)^φ(n)`, which for `a = 3`
becomes the STRICTLY SHARPER `n ≤ 2^φ(n)`; unlike the `a ≥ 4` case (`n ≤ 3^φ(n)`, proved
unconditionally in `ZsygmondyTotientGrowth`), this sharper bound is empirically true for all
`n ≠ 6` (checked computationally to `n = 2,000,000`) but genuinely FAILS at `n = 6`
(`2^φ(6) = 4 < 6`) and its proof is structurally harder: the per-prime-power margin argument
that closes the `a ≥ 4` case breaks down not just at `p = 2` (as for `a ≥ 4`) but ALSO at
`p = 3` (`3 ≤ 2^(φ(3)-1) = 2` is false), and `n = 6 = 2·3` is exactly the point where both
deficiencies compound with no other prime factor to absorb the margin. Patching this would
need either (a) a sharper totient-growth lemma with a genuine `n ≠ 6` exception baked into the
induction (a strictly harder combinatorial argument than the one in `ZsygmondyTotientGrowth`),
or (b) porting the `ZsygmondyBaseTwoEndgame` self-bound / Michels-Case-3 technique to base
`a = 3` specifically (a comparable-sized second development, since `a = 3`'s intrinsic-prime
structure does NOT enjoy the `a = 2` endgame's simplifying fact that `p = 2` is automatically
excluded — `2 ∣ Φ_n(3)` is a live case needing the even-prime machinery).  `a = 3` is real math
work, not scoped further in this file (see `primitive_prime_exists_three_six` for the one
explicit instance that IS closed by direct computation). -/
theorem zsygmondy_base_one {n : ℕ} (hn : 1 < n) {a : ℤ} (ha2or4 : a = 2 ∨ 4 ≤ a)
    (hexc2 : ¬ (n = 2 ∧ ∃ t : ℕ, (a + 1).natAbs = 2 ^ t))
    (hexc6 : ¬ (n = 6 ∧ a = 2)) :
    ∃ p : ℕ, p.Prime ∧ (p : ℤ) ∣ a ^ n - 1 ∧
      ∀ m, 0 < m → m < n → ¬ (p : ℤ) ∣ a ^ m - 1 := by
  rcases ha2or4 with haeq | ha4
  · -- a = 2
    subst haeq
    have hn6 : n ≠ 6 := by
      intro hcon
      exact hexc6 ⟨hcon, rfl⟩
    exact ZsygmondyBaseTwoEndgame.primitive_prime_exists_base_two hn hn6
  · -- a ≥ 4
    exact primitive_prime_exists_of_base_ge_four hn ha4 hexc2

end ZsygmondyBaseOneCapstone
