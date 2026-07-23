/-
  Erdős–Straus residue brick: `n ≡ 361 (mod 456)`.

  The Erdős–Straus conjecture: for every n ≥ 2 there are positive integers
  a, b, c with 4/n = 1/a + 1/b + 1/c.

  This is the *fourth rung* of the Mordell ladder inside the hard sub-case
  `n ≡ 1 (mod 24)` (n = 24m+1), continuing `ErdosStrausFortyNineMod168.lean`
  (k = 2, numerator 7, `a = 6m+2`) and `ErdosStrausElevenMod264.lean`
  (k = 3, numerator 11, `a = 6m+3`). Rung `k` takes `a = 6m + k` (so
  `4a - n = 4k-1`, i.e. the leftover-fraction numerator is `4k-1`):

    k = 1 : a = 6m+1, numerator 3  — the mod-3 obstruction documented in
            `ErdosStrausFortyNineMod168.lean` (blocked identically for
            every m).
    k = 2 : a = 6m+2, numerator 7  — splits when `7 ∣ n`, giving
            `n ≡ 49 (mod 168)`.
    k = 3 : a = 6m+3, numerator 11 — splits when `11 ∣ n`, giving
            `n ≡ 121 (mod 264)`.
    k = 4 : a = 6m+4, numerator 15 — NOT a viable rung: `gcd(24,15) = 3`,
            the SAME mod-3 obstruction as k = 1 (since `15 = 3·5` shares
            the factor 3, and `n = 24m+1 ≡ 1 (mod 3)` always, so `3 ∣ n`
            is never possible).
    k = 5 : a = 6m+5, numerator 19 — prime, `gcd(24,19) = 1`, genuinely
            viable. THIS brick.

  Writing `n = 24m+1`, `a = 6m+5`, the leftover is `19/(an)` (since
  `4a - n = 24m+20 - 24m-1 = 19`). This splits into a single unit fraction
  exactly when `19 ∣ n`. Since `n = 4a - 19`, `19 ∣ n ⟺ 19 ∣ a`, and
  (checking residues mod 19, using `24 ≡ 5 (mod 19)`) `19 ∣ n ⟺
  6m+5 ≡ 0 (mod 19) ⟺ m ≡ 15 (mod 19)`, i.e. `n ≡ 361 (mod 456)`
  (`456 = 24·19`).

  Writing `n = 456s + 361 = 19·(24s+19)` and `a = 114s+95 = 19·(6s+5)`, set
  `n' = 24s+19` (so `n = 19 n'`). Then:

    4/n − 1/a = 19/(a n) = 19/(a · 19 · n') = 1/(a n')

  which splits trivially in half: `1/(a n') = 1/(2 a n') + 1/(2 a n')`. So:

    4/n = 1/a + 1/(2 a n') + 1/(2 a n'),   a = 114s+95,  n' = 24s+19.

  Algebraic check: `4a = 456s + 380` and `19·(n'+1) = 19·(24s+20) =
  456s + 380`, so `4a = 19(n'+1)`, hence `1/a + 1/(a n') = (n'+1)/(a n')
  = 4a/(19 a n') = 4/(19 n') = 4/n` for every `s ≥ 0` — no factorization
  luck required.

  `n = 456s+361 ≡ 1 (mod 24)` and `≡ 1 (mod 3)`, so this class sits inside
  the previously-open gap `{n | n % 4 = 1 ∧ ¬ 3 ∣ n}`
  (`ErdosStrausResidue.nonRep_subset_one_mod_four_not_three_dvd`), disjoint
  from `ErdosStrausThirteenMod24` (which needs `n ≡ 13 (mod 24)`). As with
  the earlier rungs, it is NOT fully disjoint from `ErdosStrausFortyNineMod168`
  or `ErdosStrausElevenMod264` mod smaller moduli — such overlaps are
  harmless (a second, different witness) and the bulk of instances give
  genuinely new coverage.
-/
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Propositio.NumberTheory.ErdosStraus.ErdosStrausResidue

namespace ErdosStrausThreeSixtyOneMod456

/-- **`n ≡ 361 (mod 456)` case**, explicit witness: writing `n = 456*s + 361`,
`a = 114*s + 95`, `n' = 24*s + 19` (so `n = 19*n'` and `4*a = 19*(n'+1)`),
`4/n = 1/a + 1/(2*a*n') + 1/(2*a*n')`. -/
theorem erdos_straus_threeSixtyOne_mod_456 (s : ℕ) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧
      (4 : ℚ) / (456 * s + 361) = 1 / a + 1 / b + 1 / c := by
  refine ⟨114 * s + 95, 2 * (114 * s + 95) * (24 * s + 19),
    2 * (114 * s + 95) * (24 * s + 19), by omega, by positivity, by positivity, ?_⟩
  have ha : ((114 : ℚ) * s + 95) ≠ 0 := by positivity
  have hn' : ((24 : ℚ) * s + 19) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-- `n ≡ 361 (mod 456)` case, `HasRep` form. -/
theorem hasRep_of_threeSixtyOne_mod_456 (s : ℕ) :
    ErdosStrausResidue.HasRep (456 * s + 361) := by
  unfold ErdosStrausResidue.HasRep
  push_cast
  exact erdos_straus_threeSixtyOne_mod_456 s

/-- Sanity: explicit numeric instances of the identity. -/
example : (4 : ℚ) / 361 = 1 / 95 + 1 / 3610 + 1 / 3610 := by norm_num
example : (4 : ℚ) / 817 = 1 / 209 + 1 / 17974 + 1 / 17974 := by norm_num
example : (4 : ℚ) / 1273 = 1 / 323 + 1 / 43282 + 1 / 43282 := by norm_num

end ErdosStrausThreeSixtyOneMod456
