/-
  Erdős–Straus residue brick: `n ≡ 13 (mod 24)`.

  The Erdős–Straus conjecture: for every n ≥ 2 there are positive integers
  a, b, c with 4/n = 1/a + 1/b + 1/c.

  Here we prove the elementary residue case `n ≡ 13 (mod 24)` via an explicit
  witness, the classical Mordell/Ionascu–Wilson covering identity. Writing
  `n = 24*m + 13` and `a = 6*m + 4` (so `a` is even, `a = 2*(3*m+2)`):

    1/a + 1/(a*n) + 1/((a/2)*n) = 1/a + (1/a + 2/a)/n = 1/a + 3/(a*n)
      = (n + 3)/(a*n) = (24*m + 16)/(a*n) = 4*a/(a*n) = 4/n

  since `4*a = 4*(6*m+4) = 24*m + 16 = n + 3`.

  `n = 24*m+13` is always odd and ≡ 1 (mod 4), so this class is DISJOINT from
  the even, `n ≡ 3 (mod 4)`, and `3 ∣ n` cases in `ErdosStrausResidue.lean` —
  it is genuinely new territory inside the previously-open gap
  `{n | n % 4 = 1 ∧ ¬ 3 ∣ n}` (`nonRep_subset_one_mod_four_not_three_dvd`).
  Restricted to primes `p ≡ 1 (mod 4)` (the residue the whole conjecture
  reduces to), it covers the sub-case `p ≡ 13 (mod 24)`, i.e. the odd-`l`
  half of `p ≡ 1 (mod 12)` written as `p = 12*l + 1` (since
  `24*m + 13 = 12*(2*m+1) + 1`).
-/
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Propositio.NumberTheory.ErdosStraus.ErdosStrausResidue

namespace ErdosStrausThirteenMod24

/-- **`n ≡ 13 (mod 24)` case**, explicit witness: writing `n = 24*m + 13`,
`a = 6*m + 4`, `4/n = 1/a + 1/(a*n) + 1/((3*m+2)*n)`.

(Indeed, since `a = 2*(3*m+2)`, `1/(a*n) + 1/((3*m+2)*n) = (1/a + 2/a)/n
= 3/(a*n)`, so `1/a + 1/(a*n) + 1/((3*m+2)*n) = (n+3)/(a*n) = 4*a/(a*n) = 4/n`
using `4*a = 24*m + 16 = n + 3`.) -/
theorem erdos_straus_thirteen_mod_24 (m : ℕ) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧
      (4 : ℚ) / (24 * m + 13) = 1 / a + 1 / b + 1 / c := by
  refine ⟨6 * m + 4, (6 * m + 4) * (24 * m + 13), (3 * m + 2) * (24 * m + 13),
    by omega, by positivity, by positivity, ?_⟩
  have ha : ((6 : ℚ) * m + 4) ≠ 0 := by positivity
  have hn : ((24 : ℚ) * m + 13) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-- `n ≡ 13 (mod 24)` case, `HasRep` form. -/
theorem hasRep_of_thirteen_mod_24 (m : ℕ) :
    ErdosStrausResidue.HasRep (24 * m + 13) := by
  unfold ErdosStrausResidue.HasRep
  push_cast
  exact erdos_straus_thirteen_mod_24 m

/-- Sanity: explicit numeric instances of the identity. -/
example : (4 : ℚ) / 13 = 1 / 4 + 1 / 52 + 1 / 26 := by norm_num
example : (4 : ℚ) / 37 = 1 / 10 + 1 / 370 + 1 / 185 := by norm_num

end ErdosStrausThirteenMod24
