/-
  Erdős–Straus: the Mordell-ladder rung output is never prime.

  `ErdosStrausMordellGeneral.hasRep_of_mordell_general` proves, for every
  `k ≥ 1` and `t ≥ 0`, that `n = 24*(4*k-1)*t + (4*k-1)^2` has a unit-fraction
  representation `4/n = 1/a + 1/b + 1/c`. This file observes that `n` is
  *already composite* for every such `k, t`: writing `r = 4*k-1`,

    n = 24*r*t + r^2 = r * (24*t + r),

  and both factors `r` and `24*t + r` are `≥ r ≥ 3` (since `k ≥ 1`), hence
  neither factor is `1`, so `n` is never prime by `Nat.not_prime_of_mul_eq`.

  Consequence: the entire `k`-parametrized Mordell-ladder family (and every
  future single-rung instantiation `k = 7, 8, 9, ...`) produces numbers
  already covered by `ErdosStrausDivisorReduction.prime_of_minimal_nonRep`'s
  prime-case reduction — i.e. the ladder family contributes ZERO net
  progress toward the genuinely open target (primes `p ≡ 1 (mod 24)`). This
  is a formal "stop digging here" theorem redirecting future sessions away
  from "just add another rung" toward genuinely new covering identities or a
  different attack.
-/
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.Ring

namespace ErdosStrausMordellNeverPrime

/-- **Core composite-ness fact**, parametrized directly by `r`, `t` (no
`k`-side condition needed beyond `r ≥ 3`): `r * (24*t + r)` is never prime,
since both factors are `≥ r ≥ 3 ≥ 2`. -/
theorem not_prime_mordell_ladder_output_of_r (r t : ℕ) (hr : 3 ≤ r) :
    ¬ Nat.Prime (r * (24 * t + r)) :=
  Nat.not_prime_of_mul_eq rfl (by omega) (by omega)

/-- **Main theorem**: for every `k ≥ 1` and `t ≥ 0`, the Mordell-ladder rung
output `n = 24*(4*k-1)*t + (4*k-1)^2` is never prime — it factors as
`r * (24*t + r)` with `r = 4*k-1 ≥ 3`, and both factors are `≥ r ≥ 3`. -/
theorem not_prime_mordell_ladder_output (k t : ℕ) (hk : 1 ≤ k) :
    ¬ Nat.Prime (24 * (4 * k - 1) * t + (4 * k - 1) ^ 2) := by
  set r := 4 * k - 1 with hr_def
  have hr : 3 ≤ r := by omega
  have heq : r * (24 * t + r) = 24 * (4 * k - 1) * t + (4 * k - 1) ^ 2 := by
    rw [hr_def]; ring
  have h := not_prime_mordell_ladder_output_of_r r t hr
  rwa [heq] at h

end ErdosStrausMordellNeverPrime
