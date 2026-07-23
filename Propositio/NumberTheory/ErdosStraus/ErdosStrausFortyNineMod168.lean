/-
  Erdős–Straus residue brick: `n ≡ 49 (mod 168)`.

  The Erdős–Straus conjecture: for every n ≥ 2 there are positive integers
  a, b, c with 4/n = 1/a + 1/b + 1/c.

  Background / why this class needs a NEW identity. The residue `n ≡ 1 (mod 24)`
  (i.e. `n = 24m+1`) is the genuinely hard remaining sub-case of the conjecture:
  the classical Mordell first step `a = (n+3)/4` (writing `n = 4k+3`... here
  `n = 4k+1`, `a = k+1`) forces `a = 6m+1`, which is *always odd* for
  `n = 24m+1` (since `n ≡ 1 (mod 8)` here, unlike the `n ≡ 13 (mod 24)` case
  where the analogous `a` is always even). Worse: `a = 6m+1 ≡ 1 (mod 3)` and
  `n ≡ 1 (mod 3)` *identically* (both forced by `3 ∣ 24`), so the leftover
  `3/(an)` can never be split into two unit fractions via the standard
  Simon's-Favorite-Factoring-Trick divisor argument — every divisor of
  `(an)^2` built from the natural factors `a, n` is `≡ 1 (mod 3)`, never the
  needed `≡ 2 (mod 3)`. This is a genuine, `m`-independent algebraic
  obstruction, not a missing trick. So `n ≡ 1 (mod 24)` in full is NOT
  attacked here (and resists this style of identity in general — this is
  exactly the boundary where Erdős–Straus becomes hard, matching Mordell's
  classical finding that a handful of quadratic-residue classes mod 840
  resist elementary covering identities).

  Instead we move to the *next rung* of the same ladder: `a = (n+7)/4 = 6m+2`
  (remainder numerator `7` instead of `3`; note `a` is now even, avoiding the
  mod-3 obstruction, since `6m+2 ≡ 2 (mod 3) ≠ n mod 3`). This does not split
  cleanly in general (splitting `7/(an)` needs a real divisibility condition,
  not just parity) — UNLESS `7 ∣ n`. Since `n = 4a - 7`, `7 ∣ n ⟺ 7 ∣ a`, and
  both happen exactly when `m ≡ 2 (mod 7)`, i.e. `n ≡ 49 (mod 168)`
  (`168 = 24·7`). Writing `n = 168j + 49 = 7·(24j+7)` and `a = 42j+14`, the
  remainder collapses to a SINGLE unit fraction:

    4/n − 1/a = 7/(a n) = 7/(a · 7 · (24j+7)) = 1/(a·(24j+7))

  which we then split trivially in half: `1/N = 1/(2N) + 1/(2N)`. So:

    4/n = 1/a + 1/(2·a·(24j+7)) + 1/(2·a·(24j+7)),   a = 42j+14.

  Algebraic check: `1/a + 1/(a n') = (n'+1)/(a n')` where `n' = 24j+7`, and
  `4a = 4(42j+14) = 168j+56 = 7(24j+8) = 7(n'+1)`, so `(n'+1)/(a n') = 4/(7n')
  = 4/n`, confirming the identity holds for every `j ≥ 0` — no factorization
  luck required, purely from `168j+49` and `168j+56` both being divisible by
  `7` and `4` respectively, by construction.

  `n = 168j + 49 ≡ 1 (mod 24)` (disjoint from the `n ≡ 13 (mod 24)` class
  already covered in `ErdosStrausThirteenMod24.lean`) and `n ≡ 1 (mod 3)`
  (so `3 ∤ n`), i.e. this class sits genuinely inside the previously-open
  gap `{n | n % 4 = 1 ∧ ¬ 3 ∣ n}`
  (`ErdosStrausResidue.nonRep_subset_one_mod_four_not_three_dvd`).
-/
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Propositio.NumberTheory.ErdosStraus.ErdosStrausResidue

namespace ErdosStrausFortyNineMod168

/-- **`n ≡ 49 (mod 168)` case**, explicit witness: writing `n = 168*j + 49`,
`a = 42*j + 14`, `n' = 24*j + 7` (so `n = 7*n'` and `4*a = 7*(n'+1)`),
`4/n = 1/a + 1/(2*a*n') + 1/(2*a*n')`. -/
theorem erdos_straus_fortyNine_mod_168 (j : ℕ) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧
      (4 : ℚ) / (168 * j + 49) = 1 / a + 1 / b + 1 / c := by
  refine ⟨42 * j + 14, 2 * (42 * j + 14) * (24 * j + 7),
    2 * (42 * j + 14) * (24 * j + 7), by omega, by positivity, by positivity, ?_⟩
  have ha : ((42 : ℚ) * j + 14) ≠ 0 := by positivity
  have hn' : ((24 : ℚ) * j + 7) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-- `n ≡ 49 (mod 168)` case, `HasRep` form. -/
theorem hasRep_of_fortyNine_mod_168 (j : ℕ) :
    ErdosStrausResidue.HasRep (168 * j + 49) := by
  unfold ErdosStrausResidue.HasRep
  push_cast
  exact erdos_straus_fortyNine_mod_168 j

/-- Sanity: explicit numeric instances of the identity. -/
example : (4 : ℚ) / 49 = 1 / 14 + 1 / 196 + 1 / 196 := by norm_num
example : (4 : ℚ) / 217 = 1 / 56 + 1 / 3472 + 1 / 3472 := by norm_num
example : (4 : ℚ) / 385 = 1 / 98 + 1 / 10780 + 1 / 10780 := by norm_num

end ErdosStrausFortyNineMod168
