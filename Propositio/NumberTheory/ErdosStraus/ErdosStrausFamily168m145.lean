/-
  Erdős–Straus residue brick: `n = 168*m + 145`.

  The Erdős–Straus conjecture: for every n ≥ 2 there are positive integers
  a, b, c with 4/n = 1/a + 1/b + 1/c.

  Here we prove the family `n = 168*m + 145` via an explicit NEW covering
  identity, structurally different from the Mordell ladder
  (`ErdosStrausMordellGeneral.lean`): there is no `r ∣ n` side condition,
  `a` is divisible by 42 *unconditionally* by construction (not because a
  fixed factor of `n` forces it). Writing `n = 168*m + 145`, `a = 42*(m+1)`,
  `b = 21*(m+1)*n`, `c = 2*(m+1)*n`:

    1/b + 1/c = 2/(a*n) + 21/(a*n) = 23/(a*n)

  (since `b = (a/2)*n` and `c = (a/21)*n`, using `a = 42*(m+1)` so
  `a/2 = 21*(m+1) = b/n` and `a/21 = 2*(m+1) = c/n`), so

    1/a + 1/b + 1/c = (n + 23)/(a*n) = 4*a/(a*n) = 4/n

  using the core linear identity `4*a = 168*(m+1) = 168*m + 168 = n + 23`
  (since `n = 168*m + 145`).

  `n = 168*m + 145` is always `≡ 1 (mod 24)` and never divisible by 3 (since
  `145 ≡ 1 (mod 24)` and `145 ≡ 1 (mod 3)`), so this class lies in the
  genuinely open residue `{n | n % 4 = 1 ∧ ¬ 3 ∣ n}` from
  `ErdosStrausResidue.lean`, and is disjoint from the `13 mod 24` family in
  `ErdosStrausThirteenMod24.lean` (a different residue mod 24 entirely).
  Unlike the Mordell ladder (which always outputs composite `n`), this
  family hits genuine primes, e.g. `n = 313` (`m = 1`), `n = 1153` (`m = 6`).
-/
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Propositio.NumberTheory.ErdosStraus.ErdosStrausResidue

namespace ErdosStrausFamily168m145

/-- **`n = 168*m + 145` family**, explicit witness: writing `n = 168*m + 145`,
`a = 42*(m+1)`, `b = 21*(m+1)*n`, `c = 2*(m+1)*n`,
`4/n = 1/a + 1/b + 1/c`.

(Indeed `1/b + 1/c = 2/(a*n) + 21/(a*n) = 23/(a*n)`, so
`1/a + 1/b + 1/c = (n+23)/(a*n) = 4*a/(a*n) = 4/n`, using
`4*a = 168*(m+1) = n + 23`.) -/
theorem erdos_straus_family_168m145 (m : ℕ) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧
      (4 : ℚ) / (168 * m + 145) =
        1 / a + 1 / b + 1 / c := by
  refine ⟨42 * (m + 1), 21 * (m + 1) * (168 * m + 145),
    2 * (m + 1) * (168 * m + 145),
    by omega, by positivity, by positivity, ?_⟩
  have ha : ((42 : ℚ) * (m + 1)) ≠ 0 := by positivity
  have hn : ((168 : ℚ) * m + 145) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-- `n = 168*m + 145` family, `HasRep` form. -/
theorem hasRep_of_family_168m145 (m : ℕ) :
    ErdosStrausResidue.HasRep (168 * m + 145) := by
  unfold ErdosStrausResidue.HasRep
  push_cast
  exact erdos_straus_family_168m145 m

/-- Sanity: explicit numeric instances of the identity, including the
prime instance `n = 313` (`m = 1`). -/
example : (4 : ℚ) / 145 = 1 / 42 + 1 / 3045 + 1 / 290 := by norm_num
example : (4 : ℚ) / 313 = 1 / 84 + 1 / 13146 + 1 / 1252 := by norm_num

end ErdosStrausFamily168m145
