/-
  Erdős–Straus residue brick: `n ≡ 2 (mod 3)`.

  The Erdős–Straus conjecture: for every n ≥ 2 there are positive integers
  a, b, c with 4/n = 1/a + 1/b + 1/c.

  Here we prove the elementary residue case `n ≡ 2 (mod 3)` via an explicit
  witness. Writing `k = (n+1)/3` (an integer since `3 ∣ n+1`):

    1/n + 1/k + 1/(k*n) = (k + n + 1)/(k*n) = 4k/(k*n) = 4/n

  since `3*k = n + 1` gives `k + n + 1 = k + 3*k = 4*k`.

  This class overlaps the even and `n ≡ 3 (mod 4)` cases in `ErdosStrausResidue.lean`
  but is disjoint from `3 ∣ n`; combined with the reduction to primes `p ≡ 1 (mod 4)`,
  it closes the sub-case `p ≡ 5 (mod 12)` (a prime `p ≡ 1 (mod 4)` with `p ≡ 2 (mod 3)`
  is `p ≡ 5 (mod 12)` by CRT).
-/
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Propositio.NumberTheory.ErdosStraus.ErdosStrausResidue

namespace ErdosStrausTwoMod3

/-- **`n ≡ 2 (mod 3)` case**, explicit witness: writing `k = (n+1)/3` (so
`3*k = n+1`), `4/n = 1/n + 1/k + 1/(k*n)`.

(Indeed `1/n + 1/k + 1/(k*n) = (k + n + 1)/(k*n) = 4*k/(k*n) = 4/n`, using
`k + n + 1 = k + 3*k = 4*k`.) -/
theorem erdos_straus_two_mod_three {n : ℕ} (h : n % 3 = 2) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧
      (4 : ℚ) / n = 1 / a + 1 / b + 1 / c := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 3 * k + 2 := ⟨n / 3, by omega⟩
  refine ⟨3 * k + 2, k + 1, (k + 1) * (3 * k + 2), by omega, by omega, by positivity, ?_⟩
  have hk1 : ((k : ℚ) + 1) ≠ 0 := by positivity
  have hn3 : (3 * (k : ℚ) + 2) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-- `n ≡ 2 (mod 3)` case, `HasRep` form. -/
theorem hasRep_of_two_mod_three {n : ℕ} (h : n % 3 = 2) :
    ErdosStrausResidue.HasRep n :=
  erdos_straus_two_mod_three h

/-- Sanity: explicit numeric instances of the identity. -/
example : (4 : ℚ) / 2 = 1 / 2 + 1 / 1 + 1 / (1 * 2) := by norm_num
example : (4 : ℚ) / 5 = 1 / 5 + 1 / 2 + 1 / (2 * 5) := by norm_num

end ErdosStrausTwoMod3
